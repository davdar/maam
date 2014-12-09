// This file contains the definitions of the notJS abstract semantics
// domains. See the notJS semantics document Section 3.1 for the
// specification. The State definition is in interpreter.scala since
// the state transition rules are implemented as a method of State.

package notjs.abstracted.domains

import notjs.util._
import notjs.syntax._
import notjs.abstracted.init._
import notjs.abstracted.traces._
import notjs.abstracted.helpers.Fields._
import notjs.abstracted.helpers.Filters._
import notjs.abstracted.interpreter._
import scala.collection.mutable.HashSet

// defined below
import AddressSpace._

//——————————————————————————————————————————————————————————————————————————————
// Term

// since the AST treats Decl as a Stmt we don't need a separate case
// for it here.
sealed abstract class Term extends SmartHash
case class StmtT( s:Stmt ) extends Term
case class ValueT( v:Value ) extends Term

object Term {
  implicit def s2t( s:Stmt ): Term = StmtT(s)
  implicit def v2t( v:Value ): Term = ValueT(v)
}

//——————————————————————————————————————————————————————————————————————————————
// Environment

case class Env( env:Map[PVar, Addresses] = Map() )  extends SmartHash {
  // lattice join
  def ⊔( ρ:Env ): Env = {
    assert( env.keys == ρ.env.keys )
    if (this == ρ) this
    else Env(for ( (k, v) ← ρ.env ) yield (k, v ++ env(k)))
  }
  
  // retrieve a variable's addresses
  def apply( x:PVar ): Addresses =
    env(x)
  
  // add new bindings (converting each Address to Addresses)
  def ++( bind:List[(PVar, Address)] ): Env = {
    val conv = bind map ( (tup) ⇒ (tup._1, Addresses(tup._2)) )
    Env( env ++ conv )
  }
  
  // filter the map to contain only relevant entries. we explicitly
  // construct a new Map because otherwise filterKeys may return a
  // view of the original Map instead of a new Map
  def filter( f:PVar ⇒ Boolean ): Env =
    Env( (env filterKeys f) map (x ⇒ x) )
  
  // return the co-domain
  def addrs: Addresses =
    env.values.toSet.flatten
}

//——————————————————————————————————————————————————————————————————————————————
// Store

// we maintain separate maps from addresses to base values, addresses
// to objects, and addresses to sets of continuations. we also
// implement abstract counting by maintaining a set of weak addresses
// (those addresses that are allocated into the store more than once)
//
// !! OPT: depending on their relative sizes, it might be more
//         efficient to explicitly track strong addresses rather than
//         weak addresses
//
case class Store( a2v:Map[Address, BValue] = Map(), 
                  a2o:Map[Address, Object] = Map(),
                  a2k:Map[Address, Set[KStack]] = Map(),
                  weak:Set[Address] = Set() )  extends SmartHash {
  // lattice join
  def ⊔( σ:Store ): Store = {
    val _a2v =
      if ( a2v == σ.a2v ) a2v
      else σ.a2v ++ (a2v map {
        case (a, bv) ⇒ σ.a2v get a match {
          case Some(bv1) ⇒ (a, bv ⊔ bv1)
          case None ⇒ (a, bv)
        }
      })
    
    val _a2o =
      if ( a2o == σ.a2o ) a2o
      else σ.a2o ++ (a2o map {
        case (a, o) ⇒ σ.a2o get a match {
          case Some(o1) ⇒ (a, o ⊔ o1)
          case None ⇒ (a, o)
        }
      })
    
    val _a2k =
      if ( a2k == σ.a2k ) a2k
      else σ.a2k ++ (a2k map {
        case (a, κs) ⇒ σ.a2k get a match {
          case Some(κs1) ⇒ (a, κs ++ κs1)
          case None ⇒ (a, κs)
        }
      })
    
    Store( _a2v, _a2o, _a2k, σ.weak ++ weak )
  }
  
  // allocate values into the store at the given addresses, performing
  // abstract counting
  def alloc( bind:List[(Address,BValue)] ): Store = {
    assert( bind.nonEmpty )
    
    // bindw contains the addresses that already exist in the store;
    // bindn contains all the other addresses. it is possible when
    // using store pruning for both kinds of addresses to be in bind.
    val (bindw, bindn) = bind partition {
      case (a, _) ⇒ a2v contains a
    }

    // for the weak addresses, join in the old values
    val w_a2v = bindw map ( (av) ⇒ (av._1, a2v(av._1) ⊔ av._2) )
    
    Store( a2v ++ bindn ++ w_a2v, a2o, a2k, weak ++ bindw.unzip._1.toSet )
  }
  
  // allocate an object into the store at the given address,
  // performing abstract counting
  def alloc( a:Address, o:Object ): Store = {
    val (cod, wk) = a2o get a match {
      case Some(o1) ⇒ (o ⊔ o1, weak + a)
      case None ⇒ (o, weak)
    }
    Store( a2v, a2o + (a → cod), a2k, wk )
  }
  
  // allocate a continuation stack into the store at the given
  // address; this is always a weak update
  def alloc( a:Address, κs:KStack ): Store = {
    val cod = a2k get a match {
      case Some(κss) ⇒ κss + κs
      case None ⇒ Set(κs)
    }
    Store( a2v, a2o, a2k + (a → cod), weak )
  }
  
  // retrieve a base value
  def apply( as:Addresses ): BValue = {
    assert( as.nonEmpty )
    if ( as.size == 1 ) apply(as.head)
    else (as map (apply(_))).reduceLeft( (acc, bv) ⇒ acc ⊔ bv )
  }

  def apply( a: Address ): BValue = {
    a2v get a match {
      case Some(bv) ⇒ bv
      case None ⇒ throw Store.AddrNotFound
    }
  }
  
  // retrieve an object
  def getObj( a:Address, shint: Str = Str.⊤ ): Object = {
    a2o get a match {
      case Some(o) ⇒ o
      case None ⇒ throw Store.AddrNotFound
    }
  }

  // retrieve a set of continuations
  def getKont( a:Address ): Set[KStack] =
    a2k(a)
  
  // replace a base value, using either a strong or weak update as
  // appropriate
  def +( av:(Addresses,BValue), shint: Str = Str.⊤ ): Store = {
    assert( av._1.map( (a) ⇒ assert(a2v contains a) ).nonEmpty )
    val as = av._1
    val _a2v = 
      if ( as.size == 1 && !weak(as.head) ) a2v + (as.head → av._2)
      else as.foldLeft( a2v )( (acc, a) ⇒ acc + (a → (av._2 ⊔ a2v(a))) )
    Store( _a2v, a2o, a2k, weak )
  }
  
  // replace an object using a strong update if possible
  def putObj( a:Address, o:Object, shint: Str = Str.⊤ ): Store = {
    if ( weak(a) ) putObjWeak( a, o, shint )
    else putObjStrong( a, o, shint )
  }
  
  // replace an object using a strong update
  def putObjStrong( a:Address, o:Object, shint: Str = Str.⊤ ): Store = {
    // we should be guaranteed that the address is strong, except if
    // we're adding a constructor internal field to an object (which
    // is sound to do strongly even if the address is weak)
    assert( (a2o contains a) && (!weak(a) || (o.intern contains constructor)) )
    Store( a2v, a2o + (a → o), a2k, weak )
  }
  
  // replace an object using a weak update
  def putObjWeak( a:Address, o:Object, shint: Str = Str.⊤): Store = {
    assert( a2o contains a )
    Store( a2v, a2o + (a → (o ⊔ a2o(a))), a2k, weak )
  }
  
  // does this address correspond to a single concrete memory location?
  def isStrong( a:Address ): Boolean =
    !weak(a)
  
  // does the a2v part of the store contain any of the given
  // addresses? used by applyClo for pruning.
  def a2v_contains( as:Addresses ): Boolean =
    as exists ( a ⇒ a2v contains a )

  // take the sets of ids (divided into those for values and those for
  // objects) and make any corresponding addresses that are present in
  // this store weak
  def weaken( varids:Set[Int], objids:Set[Int] ): Store = {
    val wkn = a2v.keySet.filter( (a) ⇒ varids(Trace.getBase(a)) ) ++
              a2o.keySet.filter( (a) ⇒ objids(Trace.getBase(a)) )
    Store( a2v, a2o, a2k, weak ++ wkn )
  }
  
  // lightweight garbage collection: we can safely collect any local
  // variable addresses that definitely can't escape and that are not
  // already weak. this ignores local variable addresses captured in a
  // closure and any object addresses.
  def lightgc( ids:Set[Int] ): Store = {
    val tokeep = a2v.filterKeys( 
      (a:Address) ⇒ !ids(Trace.getBase(a)) || weak(a) ) map (x ⇒ x)
    Store( tokeep, a2o, a2k, weak )
  }
  
  // full garbage collection: we trace and collect the store given a
  // root-set. we divide the roots into values, objects, and
  // continuations to reflect the individual maps that make up the
  // store. value roots come from environments; object roots come from
  // base values; continuation roots come from addrK continuations.
  def fullgc( vroots:Addresses, oroots:Addresses, kroots:Addresses ): Store = {
    // value addresses
    val todoV = HashSet[Address]() ++ vroots
    val doneV = HashSet[Address]()
    
    // object addresses
    val todoO = HashSet[Address]() ++ oroots
    val doneO = HashSet[Address]()
    
    // continuation addresses
    val todoK = HashSet[Address]() ++ kroots
    val doneK = HashSet[Address]()
    
    // convenient initializer for various foldLefts
    val empty = Set[Address]()
    
    // trace a2k first, because it can contain value and object
    // addresses but a2v and a2o can't contain continuation addresses
    
    while ( todoK.nonEmpty ) {
      val a = todoK.head ; todoK -= a ; doneK += a
      
      val (vas, oas, kas) = a2k get a match {
        case Some(κss) ⇒ κss.foldLeft( (empty, empty, empty) )(
          (acc, κs) ⇒ κs.κs.foldLeft( acc )(
            // technically ForK contains a BValue, but it is guaranteed
            // to be only a Str and so we don't need to look at it
            (acc, kont) ⇒ kont match {
              case AddrK(a, _) ⇒ (acc._1, acc._2, acc._3 + a)
              case RetK(_, ρ, _, τ) ⇒ 
                val oas = 
                  if ( notJS.Mutable.pruneStore ) PruneStoreToo(τ)._2.addrs
                  else PruneScratch(τ).addrs
                (acc._1 ++ ρ.addrs, acc._2 ++ oas, acc._3)
              case FinK(vs) ⇒ vs.foldLeft( acc )(
                (acc, v) ⇒ v match {
                  case bv:BValue ⇒ (acc._1, acc._2 ++ bv.as, acc._3)
                  case EValue(bv) ⇒ (acc._1, acc._2 ++ bv.as, acc._3)
                  case JValue(_, bv) ⇒ (acc._1, acc._2 ++ bv.as, acc._3)
                })
              case _ ⇒ acc
            }))

        case None ⇒
          // if we're doing both store pruning and fullGC then there
          // may be dangling addresses in the store because of the
          // pruning; these are safe to ignore. if we're not doing
          // store pruning then dangling addresses mean there's an
          // error somewhere.
          if ( notJS.Mutable.pruneStore ) (empty, empty, empty)
          else throw new Exception("dangling address in store")
      }
      
      todoV ++= vas
      todoO ++= oas
      todoK ++= (kas -- doneK)
    }
    
    // the extra map is because otherwise filterKeys can return a view
    // of the original map instead of a new map
    val _a2k = (a2k filterKeys doneK) map (x ⇒ x)
    
    // a2v contains object addresses, while a2o contains value and
    // object addresses, so we need to trace them concurrently
    
    while ( todoV.nonEmpty || todoO.nonEmpty ) {
      // ditto comment about store pruning
      if ( notJS.Mutable.pruneStore )
        todoV retain ( a2v contains _ )

      // trace a2v
      todoO ++= (todoV.foldLeft(empty)( (acc, a) ⇒ acc ++ a2v(a).as ) -- doneO)
      
      doneV ++= todoV
      todoV.clear()
      
      // trace a2o
      while (todoO.nonEmpty) {
        val a = todoO.head ; todoO -= a ; doneO += a

        a2o get a match {
          case Some(o) ⇒
            val bvs = o.getAllValues
        
            todoO ++= (bvs.foldLeft(empty)((acc, bv) ⇒ acc ++ bv.as) -- doneO)
          
            todoV ++= (o.getCode.foldLeft( empty )(
              (acc, clo) ⇒ clo match {
                case Clo(ρ, _) ⇒ acc ++ ρ.addrs
                case _ ⇒ acc
              }) -- doneV)
          
          case None ⇒
            // ditto comment about store pruning
            if ( notJS.Mutable.pruneStore ) (empty, empty, empty)
            else throw new Exception("dangling address in store")
        }
      }
    }
    
    // same comment about the extra map as for _a2k
    val _a2v = (a2v filterKeys doneV) map (x ⇒ x)
    val _a2o = (a2o filterKeys doneO) map (x ⇒ x)

    Store( _a2v, _a2o, _a2k, weak & (doneV ++ doneO) )
  }
  
  // trace through the store and partition it into reachable and
  // unreachable addresses. the continuation store is counted as
  // unreachable. the root-sets are divided into value addresses and
  // object addresses to reflect the individual maps that make up the
  // store. value roots come from environments; object roots come
  // from base values.
  def prune( vroots:Addresses, oroots:Addresses ): (Store, Store) = {
    // value addresses
    val todoV = HashSet[Address]() ++ vroots
    val doneV = HashSet[Address]()
    
    // object addresses
    val todoO = HashSet[Address]() ++ oroots
    val doneO = HashSet[Address]()
    
    // convenient initializer for various foldLefts
    val empty = Set[Address]()
    
    while ( todoV.nonEmpty || todoO.nonEmpty ) {
      // trace a2v
      todoV foreach (
        a ⇒ apply(a).as foreach (
          a1 ⇒ if ( !doneO(a1) ) todoO += a1 ) )
      
      doneV ++= todoV
      todoV.clear()
      
      // trace a2o
      while (todoO.nonEmpty) {
        val a = todoO.head ; todoO -= a ; doneO += a
        val o = getObj(a, Str.⊥)
          
        val bvs = o.getAllValues
        
        bvs foreach (
          bv ⇒ bv.as foreach (
            a ⇒ if ( !doneO(a) ) todoO += a ) )
        
        o.getCode foreach (
          clo ⇒ clo match {
            case Clo(ρ, _) ⇒ ρ.addrs foreach (
              a ⇒ if ( !doneV(a) ) todoV += a )
            case _ ⇒ ()
          } )
      }
    }
    
    val (reach_a2v, unreach_a2v) = a2v partition {
      case (a, _) ⇒ doneV contains a
    }
    
    val (reach_a2o, unreach_a2o) = a2o partition {
      case (a, _) ⇒ doneO contains a
    }
    
    val (reach_a2k, unreach_a2k) = ( Map[Address,Set[KStack]](), a2k )
      
      val (reach_weak, unreach_weak) = weak partition (
        (a) ⇒ doneV(a) || doneO(a)
      )
    
    ( Store(reach_a2v, reach_a2o, reach_a2k, reach_weak),
      Store(unreach_a2v, unreach_a2o, unreach_a2k, unreach_weak) )
  }
} 

object Store {
  case object AddrNotFound extends Exception 
}

//——————————————————————————————————————————————————————————————————————————————
// Scratchpad memory

case class Scratchpad( mem:IndexedSeq[BValue] ) extends SmartHash {
  def ⊔( pad:Scratchpad ): Scratchpad = {
    assert( mem.length == pad.mem.length )
    if (this == pad) this
    else Scratchpad(for ( (bv1, bv2) ← (mem zip pad.mem) ) yield bv1 ⊔ bv2)
  }
  
  def apply( x:Scratch ): BValue =
    mem(x.n)
  
  def update( x:Scratch, bv:BValue ): Scratchpad =
    Scratchpad( mem.updated(x.n, bv) )

  // return all the addresses contained the Scratchpad memory (used for GC)
  def addrs: Addresses =
    mem.foldLeft( Addresses() )( (acc, bv) ⇒ acc ++ bv.as )
}

object Scratchpad {
  def apply( len:Int ): Scratchpad =
    Scratchpad( IndexedSeq[BValue]().padTo(len, Undef.BV) )
}

//——————————————————————————————————————————————————————————————————————————————
// Value: BValue, EValue, JValue

sealed abstract class Value extends SmartHash

case class EValue( bv:BValue ) extends Value
case class JValue( lbl:String, bv:BValue ) extends Value

// we take advantage of the translator guarantees to refine operator
// results by ignoring types that aren't defined for a given operator
case class BValue( n:Num, b:Bool, str:Str, as:Addresses, nil:Null, undef:Undef ) extends Value {
  // lattice join
  def ⊔( bv:BValue ): BValue =
    BValue( n ⊔ bv.n, b ⊔ bv.b, str ⊔ bv.str, as ++ bv.as, 
            nil ⊔ bv.nil, undef ⊔ bv.undef )
  
  // binary operators
  def +( bv:BValue ): BValue = 
    Num.inject( n + bv.n )
  
  def −( bv:BValue ): BValue = 
    Num.inject( n − bv.n )
  
  def ×( bv:BValue ): BValue = 
    Num.inject( n × bv.n )
  
  def ÷( bv:BValue ): BValue = 
    Num.inject( n ÷ bv.n )
  
  def %( bv:BValue ): BValue = 
    Num.inject( n % bv.n )
  
  def <<( bv:BValue ): BValue = 
    Num.inject( n << bv.n )
  
  def >>( bv:BValue ): BValue = 
    Num.inject( n >> bv.n )
  
  def >>>( bv:BValue ): BValue = 
    Num.inject( n >>> bv.n )
  
  def <( bv:BValue ): BValue = 
    Bool.inject( n < bv.n )
  
  def ≤( bv:BValue ): BValue = 
    Bool.inject( n ≤ bv.n )
  
  def &( bv:BValue ): BValue = 
    Num.inject( n & bv.n )
  
  def |( bv:BValue ): BValue = 
    Num.inject( n | bv.n )
  
  def ⊻( bv:BValue ): BValue = 
    Num.inject( n ⊻ bv.n )
  
  def and( bv:BValue ): BValue =
    Bool.inject( b and bv.b )
  
  def or( bv:BValue ): BValue =
    Bool.inject( b or bv.b )
  
  def ++( bv:BValue ): BValue = 
    Str.inject( str ++ bv.str )
  
  def ≺( bv:BValue ): BValue = 
    Bool.inject( str ≺ bv.str )
  
  def ≼( bv:BValue ): BValue = 
    Bool.inject( str ≼ bv.str )
  
  // unary operators
  def negate: BValue = 
    Num.inject( n.negate )
  
  def bitwisenot: BValue = 
    Num.inject( n.bitwisenot )
  
  def logicnot: BValue = 
    Bool.inject( b.logicnot )
  
  def isprim: BValue = {
    assert( sorts.nonEmpty )
    val notaddr = Bool.α( !sorts(DAddr) )
    val hasprim = Bool.α( !defAddr )
    Bool.inject( notaddr ⊔ hasprim )
  }
  
  def tobool: BValue =
    Bool.inject( 
      sorts.foldLeft[Bool]( Bool.⊥ )(
        (acc, dom) ⇒
        if ( acc == Bool.⊤ ) Bool.⊤
        else acc ⊔ (dom match {
          case DNum ⇒
            if ( n.defNaN || n.def0 ) Bool.False
            else if ( n.defNotNaN && n.defNot0 ) Bool.True
            else Bool.⊤
          case DBool ⇒ 
            b
          case DStr ⇒ 
            if ( str.defEmpty ) Bool.False
            else if ( str.defNotEmpty ) Bool.True
            else Bool.⊤
          case DAddr ⇒ 
            Bool.True
          case DNull | DUndef ⇒ 
            Bool.False
        }))
    )

  def tostr: BValue =
    Str.inject(
      sorts.foldLeft[Str]( Str.⊥ )(
        (acc, dom) ⇒ acc ⊔ (dom match {
          case DNum ⇒ n.toStr
          case DBool ⇒ b.toStr
          case DStr ⇒ str
          case DNull ⇒ Str.α("null")
          case DUndef ⇒ Str.α("undefined")
          case _ ⇒ Str.⊥
        }))
    )

  def tonum: BValue =
    Num.inject(
      sorts.foldLeft[Num]( Num.⊥ )(
	(acc, dom) ⇒ acc ⊔ (dom match {
	  case DNum ⇒ n
	  case DBool ⇒ b.toNum
	  case DStr ⇒ str.toNum
	  case DNull ⇒ Num.α(0)
	  case DUndef ⇒ Num.α(Double.NaN)
	  case _ ⇒ Num.⊥
	}))
    )
  
  // other useful information
  // keep track of non-⊥ domains (only computed if we ever ask for it)
  lazy val sorts: Set[Domain] =
    (if (n == Num.⊥)       Set() else Set(DNum))  ++
    (if (b == Bool.⊥)      Set() else Set(DBool)) ++
    (if (str == Str.⊥)     Set() else Set(DStr))  ++
    (if (as.isEmpty)       Set() else Set(DAddr)) ++
    (if (nil == Null.⊥)    Set() else Set(DNull)) ++
    (if (undef == Undef.⊥) Set() else Set(DUndef))
  
  def isBot: Boolean =
    sorts.isEmpty
  
  def defAddr: Boolean =
    (sorts.size == 1) && (sorts contains DAddr)
  
  def defNum: Boolean =
    (sorts.size == 1) && (sorts contains DNum)
  
  def defStr: Boolean =
    (sorts.size == 1) && (sorts contains DStr)
  
  def defBool: Boolean =
    (sorts.size == 1) && (sorts contains DBool)
  
  def defNull: Boolean =
    (sorts.size == 1) && (sorts contains DNull)
  
  def onlyNum: BValue =
    Num.inject( n )
  
  def onlyBool: BValue =
    Bool.inject( b )
  
  def onlyStr: BValue =
    Str.inject( str )
  
  def onlyAddr: BValue = 
    Addresses.inject( as )

  def removeNullAndUndef: BValue = 
    BValue(n, b, str, as, Null.⊥, Undef.⊥)

  // refine this base value by the filter
  // one for the true case, one for the false case
  def filterBy(bvf:BVFilter, σ:Store): (BValue, BValue) = {
    bvf match {
      case IsFunc ⇒ (onlyAddr, this)
      case IsUndefNull ⇒ (removeNullAndUndef, this)
    }
  } 
    
  override def toString =
    (sorts map {
      case DNum ⇒ "DNum:" + n.toString
      case DBool ⇒ "DBool:" + b.toString
      case DStr ⇒ "DStr:" + str.toString
      case DAddr ⇒ "DAddr:" + as.toString
      case DNull ⇒ "DNull"
      case DUndef ⇒ "DUndef"
    }).mkString("|")
}

object BValue {
  val ⊥ = BValue( Num.⊥, Bool.⊥, Str.⊥, Addresses(), Null.⊥, Undef.⊥ )
}

// useful for listing the non-empty subdomains of a BValue
sealed abstract class Domain
case object DNum extends Domain
case object DBool extends Domain
case object DStr extends Domain
case object DAddr extends Domain
case object DNull extends Domain
case object DUndef extends Domain

//——————————————————————————————————————————————————————————————————————————————
// Num

sealed abstract class Num extends SmartHash {
  def ⊔( n:Num ): Num =
    (this, n) match {
      case (x, y) if x == y ⇒ this
      case (NBot, x) ⇒ x
      case (x, NBot) ⇒ x
      case (NTop,_) | (_,NTop) ⇒ NTop
      case (Num.NaN,_) | (_,Num.NaN) ⇒ NTop
      case (Num.Inf,_) | (_,Num.Inf) ⇒ NTop
      case (Num.NInf,_) | (_,Num.NInf) ⇒ NTop
      case _ ⇒ NReal
    }

  def ≡( n:Num ): Bool =
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ Bool.⊥
      case (Num.NaN,_) | (_,Num.NaN) ⇒ Bool.False
      case (NTop,_) | (_,NTop) ⇒ Bool.⊤
      case (NConst(d1), NConst(d2)) ⇒ Bool.α(d1 == d2)
      case (Num.Inf, NReal) | (NReal, Num.Inf) ⇒ Bool.False
      case (Num.NInf, NReal) | (NReal, Num.NInf) ⇒ Bool.False
      case _ ⇒ Bool.⊤
    }

  def +( n:Num ): Num =
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ NBot
      case (Num.NaN,_) | (_,Num.NaN) ⇒ Num.NaN
      case (NTop,_) | (_,NTop) ⇒ NTop
      case (NConst(d1), NConst(d2)) ⇒ NConst(d1 + d2)
      case (NReal, Num.Inf) | (Num.Inf, NReal) ⇒ Num.Inf
      case (NReal, Num.NInf) | (Num.NInf, NReal) ⇒ Num.NInf
      case (NReal,_) | (_,NReal) ⇒ NReal
    }

  def −( n:Num ): Num = 
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ NBot
      case (Num.NaN,_) | (_,Num.NaN) ⇒ Num.NaN
      case (NTop,_) | (_,NTop) ⇒ NTop
      case (NConst(d1), NConst(d2)) ⇒ NConst(d1 - d2)
      case (NReal, Num.Inf) | (Num.NInf, NReal) ⇒ Num.NInf
      case (Num.Inf, NReal) | (NReal, Num.NInf) ⇒ Num.Inf
      case (NReal,_) | (_,NReal) ⇒ NReal
    }

  def ×( n:Num ): Num =
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ NBot
      case (Num.NaN,_) | (_,Num.NaN)  ⇒ Num.NaN
      case (NTop,_) | (_,NTop) ⇒ NTop
      case (NConst(d1), NConst(d2)) ⇒ NConst(d1 * d2)
      case (NReal, Num.Inf) | (Num.Inf, NReal) ⇒ NTop
      case (NReal, Num.NInf) | (Num.NInf, NReal) ⇒ NTop
      case (NReal,_) | (_,NReal) ⇒ NReal
    }

  def ÷( n:Num ): Num =
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ NBot
      case (Num.NaN,_) | (_,Num.NaN) ⇒ Num.NaN
      case (NTop,_) | (_,NTop) ⇒ NTop
      case (NConst(d1), NConst(d2)) ⇒ NConst(d1 / d2)
      case (NReal, Num.Inf) | (NReal, Num.NInf) ⇒ NConst(0)
      case _ ⇒ NTop
    }

  def %( n:Num ): Num = 
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ NBot
      case (Num.NaN,_) | (_,Num.NaN) ⇒ Num.NaN
      case (NTop,_) | (_,NTop) ⇒ NTop
      case (NConst(d1), NConst(d2)) ⇒ NConst(d1 % d2)
      case (Num.Inf, NReal) | (Num.NInf, NReal) ⇒ Num.NaN
      case _ ⇒ NReal
    }

  def <<( n:Num ): Num =
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ NBot
      case (NConst(d1), NConst(d2)) ⇒ NConst((d1.toInt << d2.toInt).toDouble)
      case _ ⇒ NReal
    }

  def >>( n:Num ): Num =
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ NBot
      case (NConst(d1), NConst(d2)) ⇒ NConst((d1.toInt >> d2.toInt).toDouble)
      case _ ⇒ NReal
    }

  def >>>( n:Num ): Num =
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ NBot
      case (NConst(d1), NConst(d2)) ⇒ NConst((d1.toInt >>> d2.toInt).toDouble)
      case _ ⇒ NReal
    }

  def <( n:Num ): Bool =
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ Bool.⊥
      case (Num.NaN,_) | (_,Num.NaN) ⇒ Bool.False
      case (NTop,_) | (_,NTop) ⇒ Bool.⊤
      case (NConst(d1), NConst(d2)) ⇒ Bool.α(d1 < d2)
      case (NReal, Num.Inf) | (Num.NInf, NReal) ⇒ Bool.True
      case (Num.Inf, NReal) | (NReal, Num.NInf) ⇒ Bool.False
      case _ ⇒ Bool.⊤
    }

  def ≤( n:Num ): Bool =
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ Bool.⊥
      case (Num.NaN,_) | (_,Num.NaN) ⇒ Bool.False
      case (NTop,_) | (_,NTop) ⇒ Bool.⊤
      case (NConst(d1), NConst(d2)) ⇒ Bool.α(d1 <= d2)
      case (NReal, Num.Inf) | (Num.NInf, NReal) ⇒ Bool.True
      case (Num.Inf, NReal) | (NReal, Num.NInf) ⇒ Bool.False
      case _ ⇒ Bool.⊤
    }

  def &( n:Num ): Num = 
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ NBot
      case (Num.NaN,_) | (_,Num.NaN) ⇒ Num.Zero
      case (NConst(d1), NConst(d2)) ⇒ NConst((d1.toInt & d2.toInt).toDouble)
      case _ ⇒ NReal
    }

  def |( n:Num ): Num = 
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ NBot
      case (NConst(d1), NConst(d2)) ⇒ NConst((d1.toInt | d2.toInt).toDouble)
      case _ ⇒ NReal
    }

  def ⊻( n:Num ): Num = 
    (this, n) match {
      case (NBot,_) | (_,NBot) ⇒ NBot
      case (NConst(d1), NConst(d2)) ⇒ NConst((d1.toInt ^ d2.toInt).toDouble)
      case _ ⇒ NReal
    }

  def negate: Num =
    this match {
      case NConst(d) ⇒ NConst(-d)
      case _ ⇒ this
    }

  def bitwisenot: Num =
    this match {
      case NConst(d) ⇒ NConst((~d.toInt).toDouble)
      case _ ⇒ this
    }

  def toStr: Str =
    this match {
      case n:NConst ⇒ Str.α(n.toString)
      case NTop ⇒ Str.⊤ // because it includes "NaN" and "[-]Infinity"
      case NReal ⇒ Str.numStr
      case NBot ⇒ Str.⊥
    }

  def defNaN: Boolean =
    this == Num.NaN

  def defNotNaN: Boolean =
    this match {
      case Num.NaN | NTop ⇒ false
      case _ ⇒ true
    }

  def def0: Boolean =
    this == Num.Zero

  def defNot0: Boolean =
    this match {
      case NBot ⇒ true
      case NConst(d) if d != 0 ⇒ true
      case _ ⇒ false
    }
}

case object NBot extends Num

case object NTop extends Num {
  override def toString = "NTop"
}

case object NReal extends Num {
  override def toString = "NReal"
}

case class NConst(d:Double) extends Num {
  // this makes NConst(NaN) == NConst(NaN), which allows
  // pattern-matching to succeed when matching against Num.NaN. ≡
  // still gives the behavior that NaN ≠ NaN.
  override def equals( a:Any ) =
    a match {
      case NConst(d1) if (d == d1) || (d.isNaN && d1.isNaN) ⇒ true
      case _ ⇒ false
    }

  override def toString = 
    if (d.toLong == d) d.toLong.toString else d.toString
}

object Num {
  val ⊤ = NTop
  val ⊥ = NBot
  val Zero = NConst(0)
  val NaN = NConst( Double.NaN )
  val Inf = NConst( Double.PositiveInfinity )
  val NInf = NConst( Double.NegativeInfinity )
  val U32 = NReal // closest approximation to a unsigned 32-bit integer
  val maxU32 = 4294967295L

  def α( d:Double ): Num = 
    NConst(d)

  def maybeU32( bv:BValue ): Boolean =
    bv.n match {
      case NTop | NReal ⇒ true
      case NConst(d) if d.toLong == d && d >= 0 && d <= maxU32 ⇒ true
      case _ ⇒ false
    }

  def maybenotU32( bv:BValue ): Boolean =
    !(bv.defNum) || (bv.n match {
      case NConst(d) if d.toLong == d && d >= 0 && d <= maxU32 ⇒ false
      case _ ⇒ true
    })

  def inject( n:Num ): BValue =
    BValue( n, Bool.⊥, Str.⊥, Addresses(), Null.⊥, Undef.⊥ )
}

//——————————————————————————————————————————————————————————————————————————————
// Bool

sealed abstract class Bool extends SmartHash {
  def ⊔( b:Bool ): Bool =
    (this, b) match {
      case (x, y) if x == y ⇒ this
      case (BTop,_) | (_,BTop) | (BTrue, BFalse) | (BFalse, BTrue) ⇒ BTop
      case (BBot, x) ⇒ x
      case (x, BBot) ⇒ x
      case _ ⇒ sys.error("suppress false compiler warning")
    }

  def and( b:Bool ): Bool =
    (this, b) match {
      case (BBot,_) | (_,BBot) ⇒ BBot
      case (BFalse, _) | (_, BFalse) ⇒ BFalse
      case (BTop,_) | (_,BTop) ⇒ BTop
      case (BTrue, BTrue) ⇒ BTrue
    }

  def or( b:Bool ): Bool =
    (this, b) match {
      case (BBot,_) | (_,BBot) ⇒ BBot
      case (BTrue, _) | (_, BTrue) ⇒ BTrue
      case (BTop,_) | (_,BTop) ⇒ BTop
      case _ ⇒ BFalse
    }
  
  def ≡( b:Bool ): Bool =
    (this, b) match {
      case (BBot,_) | (_,BBot) ⇒ BBot
      case (BTop,_) | (_,BTop) ⇒ BTop
      case (BTrue, BTrue) | (BFalse, BFalse) ⇒ BTrue
      case _ ⇒ BFalse
    }

  def logicnot: Bool =
    this match {
      case BBot ⇒ BBot
      case BTrue ⇒ BFalse
      case BFalse ⇒ BTrue
      case BTop ⇒ BTop
    }

  // technically the BTop case should be "Str.α("true") ⊔
  // Str.α("false")", but since the default Str domain results in
  // Str.⊤ we'll just use that. we can revisit this decision if it
  // becomes important later.
  def toStr: Str =
    this match {
      case BBot ⇒ Str.⊥
      case BTrue ⇒ Str.α("true")
      case BFalse ⇒ Str.α("false")
      case BTop ⇒ Str.⊤
    }

  def toNum: Num =
    this match {
      case BBot ⇒ Num.⊥
      case BTrue ⇒ Num.α(1)
      case BFalse ⇒ Num.α(0)
      case BTop ⇒ Num.α(0) ⊔ Num.α(1)
    }
}

case object BBot extends Bool 

case object BTrue extends Bool {
 override def toString = "true" 
}

case object BFalse extends Bool {
  override def toString = "false"
}

case object BTop extends Bool {
  override def toString = "BTop"
}

object Bool {
  val ⊤ = BTop
  val ⊥ = BBot
  val True = BTrue
  val False = BFalse
  val TrueBV = inject(True)
  val FalseBV = inject(False)
  val TopBV = inject(⊤)

  def α( b:Boolean ): Bool =
    if (b) BTrue else BFalse

  def inject( b:Bool ): BValue =
    BValue( Num.⊥, b, Str.⊥, Addresses(), Null.⊥, Undef.⊥ )
}

//——————————————————————————————————————————————————————————————————————————————
// Str

sealed abstract class Str extends SmartHash {
  def ⊔( str:Str ): Str =
    (this, str) match {
      case (x, y) if x == y ⇒ this
      case (SBot, x) ⇒ x
      case (x, SBot) ⇒ x
      case (_:SConstNum, _:SConstNum) ⇒ SNum
      case (_:SConstNum, _:SConstNotSplNorNum) |
           (_:SConstNotSplNorNum, _:SConstNum) ⇒ SNotSpl
      case (_:SConstNum, _:SConstSpl) |
           (_:SConstSpl, _:SConstNum) ⇒ STop
      case (_:SConstNum, SNotSplNorNum) |
           (SNotSplNorNum, _:SConstNum) ⇒ SNotSpl
      case (_:SConstNum, SSpl) |
           (SSpl, _:SConstNum) ⇒ STop
      case (_:SConstNum, SNotNum) |
           (SNotNum, _:SConstNum) ⇒ STop
      case (_:SConstNotSplNorNum, _:SConstNotSplNorNum) ⇒ SNotSplNorNum
      case (_:SConstNotSplNorNum, _:SConstSpl) |
           (_:SConstSpl, _:SConstNotSplNorNum) ⇒ SNotNum
      case (_:SConstNotSplNorNum, SNum) |
           (SNum, _:SConstNotSplNorNum) ⇒ SNotSpl
      case (_:SConstNotSplNorNum, SSpl) |
           (SSpl, _:SConstNotSplNorNum) ⇒ SNotNum
      case (_:SConstSpl, _:SConstSpl) ⇒ SSpl     
      case (_:SConstSpl, SNum) |
           (SNum, _: SConstSpl) ⇒ STop
      case (_:SConstSpl, SNotSplNorNum) |
           (SNotSplNorNum, _:SConstSpl) ⇒ SNotNum     
      case (_:SConstSpl, SNotSpl) |
           (SNotSpl, _: SConstSpl) ⇒ STop
      case (SNum, SNotSplNorNum) |
           (SNotSplNorNum, SNum) ⇒ SNotSpl
      case (SNum, SSpl) |
           (SSpl, SNum) ⇒ STop
      case (SNum, SNotNum) |
           (SNotNum, SNum) ⇒ STop
      case (SNotSplNorNum, SSpl) |
           (SSpl, SNotSplNorNum) ⇒ SNotNum
      case (SSpl, SNotSpl) |
           (SNotSpl, SSpl) ⇒ STop
      case (SNotSpl, SNotNum) |
           (SNotNum, SNotSpl) ⇒ STop                         
      case (x, y) if x ⊑ y ⇒ y
      case (x, y) if y ⊑ x ⇒ x
      case _ ⇒ sys.error("Incorrect implementation of string lattice: " + (this, str))
    }

  // string partial order
  def ⊑( str:Str ): Boolean =
    (this, str) match {
      case (SBot,_) | (_,STop) ⇒ true
      case (x, y) if x == y ⇒ true
      case (_:SConstNum, SNum) |
           (_:SConstNum, SNotSpl) |
           (_:SConstNotSplNorNum, SNotSplNorNum) |
           (_:SConstNotSplNorNum, SNotNum) |
           (_:SConstNotSplNorNum, SNotSpl) |
           (_:SConstSpl, SSpl) |
           (_:SConstSpl, SNotNum) |
           (SNum, SNotSpl) |
           (SNotSplNorNum, SNotSpl) |
           (SNotSplNorNum, SNotNum) |
           (SSpl, SNotNum) ⇒ true
      case _ ⇒ false
    }

  // negation of ⊑ operator  
  def ≰( str: Str ): Boolean = 
    !(⊑(str)) 
    
  def ≡( str:Str ): Bool =
    (this, str) match {
      case (SConstNum(str1), SConstNum(str2)) ⇒ Bool.α(str1 == str2)
      case (SConstNotSplNorNum(str1), SConstNotSplNorNum(str2)) ⇒
        Bool.α(str1 == str2)
      case (SConstSpl(str1), SConstSpl(str2)) ⇒ 
        Bool.α(str1 == str2)
      // definitely unequal if the meet of two elements is ⊥
      // 1. only case where non-comparable elements meet is not ⊥
      case (SNotSpl, SNotNum) |
           (SNotNum, SNotSpl) ⇒ Bool.⊤  
      // 2. non-comparable
      case (x, y) if x ≰ y && y ≰ x ⇒ Bool.False
      case (SBot,_) | (_,SBot) ⇒ Bool.⊥
      case _ ⇒ Bool.⊤
    }

  def ++( str:Str ): Str = 
    (this, str) match {
      case (SBot,_) | (_,SBot) ⇒ SBot
      
      case (STop, _:SConstNum) ⇒ SNotSpl
      case (STop, _:SConstSpl) ⇒ SNotNum
      case (STop, SNum) ⇒ SNotSpl
      case (STop, SSpl) ⇒ SNotNum
      case (STop, _) ⇒ STop
      
      case (Str.Empty, x) ⇒ x 
      case (x, Str.Empty) ⇒ x

      case (x, y) if (Str.isExact(x) && Str.isExact(y)) ⇒ {
        Str.α(Str.getExact(x).get + Str.getExact(y).get)
      }
      case (_:SConstNum, SNum) ⇒ SNotSpl
      case (_:SConstNum, SNotSplNorNum) ⇒ SNotSpl
      case (_:SConstNum, SSpl) ⇒ SNotSpl
      case (_:SConstNum, SNotSpl) ⇒ SNotSpl
      case (_:SConstNum, SNotNum) ⇒ SNotSpl
      case (_:SConstNum, STop) ⇒ SNotSpl

      case (_:SConstNotSplNorNum, SNum) ⇒ SNotSpl
      case (_:SConstNotSplNorNum, SNotSplNorNum) ⇒ SNotNum
      case (_:SConstNotSplNorNum, SSpl) ⇒ SNotNum
      case (_:SConstNotSplNorNum, SNotSpl) ⇒ STop
      case (_:SConstNotSplNorNum, SNotNum) ⇒ SNotNum
      case (_:SConstNotSplNorNum, STop) ⇒ STop

      case (_:SConstSpl, SNum) ⇒ SNotSpl
      case (_:SConstSpl, SNotSplNorNum) ⇒ SNotNum
      case (_:SConstSpl, SSpl) ⇒ SNotSplNorNum
      case (_:SConstSpl, SNotSpl) ⇒ SNotNum
      case (_:SConstSpl, SNotNum) ⇒ SNotNum
      case (_:SConstSpl, STop) ⇒ SNotNum

      case (SNum, _:SConstNum) ⇒ SNotSpl
      case (SNum, _:SConstNotSplNorNum) ⇒ SNotSpl
      case (SNum, _:SConstSpl) ⇒ SNotSplNorNum
      case (SNum, SNum) ⇒ SNotSpl
      case (SNum, SNotSplNorNum) ⇒ SNotSpl
      case (SNum, SSpl) ⇒ SNotSplNorNum
      case (SNum, SNotSpl) ⇒ SNotSpl
      case (SNum, SNotNum) ⇒ SNotSpl
      case (SNum, STop) ⇒ SNotSpl

      case (SNotSplNorNum, _:SConstNum) ⇒ SNotSpl
      case (SNotSplNorNum, _:SConstNotSplNorNum) ⇒  SNotNum
      case (SNotSplNorNum, _:SConstSpl) ⇒ SNotNum
      case (SNotSplNorNum, SNum) ⇒ SNotSpl
      case (SNotSplNorNum, SNotSplNorNum) ⇒ SNotNum
      case (SNotSplNorNum, SSpl) ⇒ SNotNum
      case (SNotSplNorNum, SNotSpl) ⇒ STop
      case (SNotSplNorNum, SNotNum) ⇒ SNotNum
      case (SNotSplNorNum, STop) ⇒ STop

      case (SSpl, _:SConstNum) ⇒ SNotSplNorNum
      case (SSpl, _:SConstNotSplNorNum) ⇒ SNotNum
      case (SSpl, _:SConstSpl) ⇒ SNotSplNorNum
      case (SSpl, SNum) ⇒ SNotSplNorNum
      case (SSpl, SNotSplNorNum) ⇒ SNotNum
      case (SSpl, SSpl) ⇒ SNotSplNorNum
      case (SSpl, SNotSpl) ⇒ SNotNum
      case (SSpl, SNotNum) ⇒ SNotNum
      case (SSpl, STop) ⇒ SNotNum

      case (SNotSpl, _:SConstNum) ⇒ SNotSpl
      case (SNotSpl, _:SConstNotSplNorNum) ⇒ STop 
      case (SNotSpl, _:SConstSpl) ⇒ SNotNum
      case (SNotSpl, SNum) ⇒ SNotSpl
      case (SNotSpl, SNotSplNorNum) ⇒ STop
      case (SNotSpl, SSpl) ⇒ SNotNum
      case (SNotSpl, SNotSpl) ⇒ STop
      case (SNotSpl, SNotNum) ⇒ STop
      case (SNotSpl, STop) ⇒ STop

      case (SNotNum, _:SConstNum) ⇒ SNotSpl
      case (SNotNum, _:SConstNotSplNorNum) ⇒ SNotNum
      case (SNotNum, _:SConstSpl) ⇒ SNotNum
      case (SNotNum, SNum) ⇒ SNotSpl
      case (SNotNum, SNotSplNorNum) ⇒ SNotNum 
      case (SNotNum, SSpl) ⇒ SNotNum
      case (SNotNum, SNotSpl) ⇒ STop
      case (SNotNum, SNotNum) ⇒ SNotNum
      case (SNotNum, STop) ⇒ STop

      case _ ⇒ sys.error("Incorrect implementation of string lattice")
    }

  def ≺( str:Str ): Bool = 
    (this, str) match {
      case (SBot,_) | (_,SBot) ⇒ Bool.⊥
      case (x, y) if (Str.isExact(x) && Str.isExact(y)) ⇒ {
        Bool.α(Str.getExact(x).get < Str.getExact(y).get)
      }
      case (_:SConstNum, _:SConstSpl) |
           (_:SConstNum, SSpl) |
           (SNum, _:SConstSpl) |
           (SNum, SSpl) ⇒ Bool.True
      case (_:SConstSpl, _:SConstNum) |
           (SSpl, _:SConstNum) |
           (_:SConstSpl, SNum) |
           (SSpl, SNum) ⇒ Bool.False     
      case _ ⇒ Bool.⊤
    }

  def ≼( str:Str ): Bool =
    (this, str) match {
      case (SBot,_) | (_,SBot) ⇒ Bool.⊥
      case (x, y) if (Str.isExact(x) && Str.isExact(y)) ⇒ {
        Bool.α(Str.getExact(x).get <= Str.getExact(y).get)
      }
      case (_:SConstNum, _:SConstSpl) |
           (_:SConstNum, SSpl) |
           (SNum, _:SConstSpl) |
           (SNum, SSpl) ⇒ Bool.True
      case (_:SConstSpl, _:SConstNum) |
           (SSpl, _:SConstNum) |
           (_:SConstSpl, SNum) |
           (SSpl, SNum) ⇒ Bool.False     
      case _ ⇒ Bool.⊤
    }

  def toNum: Num =
    this match {
      case SBot ⇒ Num.⊥
      case STop | SNum | SNotSpl ⇒ Num.⊤
      case SNotNum | SSpl | SNotSplNorNum ⇒ Num.NaN
      case _:SConstNotSplNorNum | _:SConstSpl ⇒ Num.NaN
      case SConstNum(str) ⇒ Num.α(str.toDouble)
    }

  def defEmpty: Boolean =
    this == Str.Empty

  def defNotEmpty: Boolean =
    this match {
      case SBot | SNum | _:SConstNum | _:SConstSpl | SSpl ⇒ true
      case SConstNotSplNorNum(str) if str != "" ⇒ true
      case _ ⇒ false
    }
}

case object SBot extends Str {
  override def toString = "SBot"
}

case object STop extends Str {
  override def toString = "STop"
}

case object SNum extends Str {
  override def toString = "SNum"
}

case object SNotNum extends Str {
  override def toString = "SNotNum"
}

case object SSpl extends Str {
  override def toString = "SSpl"
}

case object SNotSplNorNum extends Str {
  override def toString = "SNotSplNorNum"
}

case object SNotSpl extends Str {
  override def toString = "SNotSpl"
}

case class SConstNum( str:String ) extends Str {
  assert(Str.isNum(str), "SConstNum instantiated incorrectly: " + str)
  override def toString = str
}

case class SConstNotSplNorNum( str:String ) extends Str {
  assert(!Str.isNum(str) && !Str.isSpl(str),  
    "SConstNotSplNorNum instantiated incorrectly: " + str)
  override def toString = str
}

case class SConstSpl( str:String ) extends Str {
  assert(Str.isSpl(str), 
    "SConstSpl instantiated incorrectly: " +  str)
  override def toString = str
}

object Str {
  lazy val ⊤ = STop
  lazy val ⊥ = SBot
  lazy val u32 = SNum
  lazy val numStr = SNum
  lazy val Empty = SConstNotSplNorNum("")
  // single character string
  lazy val SingleChar = SNotSpl
  // string representation of a date
  lazy val DateStr = SNotSplNorNum
  // string representation of a function
  lazy val FunctionStr = SNotSplNorNum
  // the val below MUST lazy
  // else it causes a crash
  // some weird Scala object initialization issue
  lazy val SplStrings = Set("valueOf", 
                            "toString", 
                            "length",
                            "constructor",
                            "toLocaleString",
                            "hasOwnProperty",
                            "isPrototypeOf",
                            "propertyIsEnumerable",
                            "concat",
                            "indexOf",
                            "join",
                            "lastIndexOf",
                            "pop",
                            "push",
                            "reverse",
                            "shift",
                            "sort",
                            "splice")

  // the SplStrings are baked in with the following assumptions:
  // 1. They consist of more than 1 character
  // 2. They only consist of alphabets
  // 3. None is a substring of the other
  assert(SplStrings.forall(x ⇒ {
    x.length > 1 && 
    x.forall(c ⇒ Character.isLetter(c)) && 
    !SplStrings.filter(_!=x).contains(x)
  }), "Special strings do not conform to the assertion")

  def α( str:String ): Str = {
    if ( isNum(str) ) SConstNum(str) 
    else if ( isSpl(str) ) SConstSpl(str)
    else SConstNotSplNorNum(str)
  }

  def inject( str:Str ): BValue =
    BValue( Num.⊥, Bool.⊥, str, Addresses(), Null.⊥, Undef.⊥ )

  // is this an exact string?
  def isExact( str:Str ): Boolean =
    str match {
      case _:SConstSpl | 
           _:SConstNum |
           _:SConstNotSplNorNum ⇒ true
      case _ ⇒ false
    }
  
  // get an exact string if possible
  def getExact( str:Str ): Option[String] = {
    str match {
      case SConstNotSplNorNum(s) ⇒ Some(s)
      case SConstNum(s) ⇒ Some(s)
      case SConstSpl(s) ⇒ Some(s)
      case _ ⇒ None
    }
  }    

  // does this concrete string represent a number?
  def isNum( str:String ): Boolean =
    try { str.toDouble; true } 
    catch { case e: java.lang.NumberFormatException ⇒ false }

  // is this in the list of Spl strings?  
  def isSpl( str: String ): Boolean = 
    Str.SplStrings(str)
    
  // does this abstract string represent an exact number  
  def isExactNum( str:Str ): Boolean =
    str match {
      case SConstNum(_) ⇒ true
      case _ ⇒ false
    }

  // does this abstract string represent an exact non-number  
  def isExactNotNum( str: Str ): Boolean = 
    str match {
      case SConstNotSplNorNum(_) |
           SConstSpl(_) ⇒ true
      case _ ⇒ false
    }

  // given a set of Str, eliminate the elements that are
  // over-approximated by other elements
  def minimize( strs:Set[Str] ): Set[Str] = {
    assert( !strs(Str.⊥) )
    if ( strs contains Str.⊤ ) Set(Str.⊤)
    else {
      val hasSNum = strs contains SNum
      val hasSNotSpl = strs contains SNotSpl
      val hasSNotSplNorNum = strs contains SNotSplNorNum
      val hasSSpl = strs contains SSpl
      val hasSNotNum = strs contains SNotNum

      strs.foldLeft( Set[Str]() )( (acc, str) ⇒ str match {
        case _:SConstNum if hasSNum || hasSNotSpl ⇒ acc
        case _:SConstNotSplNorNum 
          if hasSNotSplNorNum || hasSNotSpl || hasSNotNum ⇒ acc
        case _:SConstSpl if hasSSpl || hasSNotNum ⇒ acc
        case SNum if hasSNotSpl ⇒ acc
        case SNotSplNorNum if hasSNotSpl || hasSNotNum ⇒ acc
        case SSpl if hasSNotNum ⇒ acc
        case SBot ⇒ acc
        case _ ⇒ acc + str
      })
    }
  }
}

//——————————————————————————————————————————————————————————————————————————————
// Address, Addresses

object AddressSpace {
  case class Address( loc:BigInt ) extends SmartHash

  object Address {
    def apply( x:Int ): Address = new Address(BigInt(x))
    
    def inject( a:Address ): BValue =
      BValue( Num.⊥, Bool.⊥, Str.⊥, Set(a), Null.⊥, Undef.⊥ )
  }

  implicit def bigint2a( loc:BigInt ): Address = Address( loc )

  type Addresses = Set[Address]

  object Addresses {
    def apply(): Addresses = Set[Address]()
    def apply( a:Address ): Addresses = Set[Address](a)

    def inject(as:Addresses): BValue =
      BValue( Num.⊥, Bool.⊥, Str.⊥, as, Null.⊥, Undef.⊥ )
  }
}

//——————————————————————————————————————————————————————————————————————————————
// Null and Undef

sealed abstract class Null {
  def ⊔( nil:Null ): Null =
    (this, nil) match {
      case (MaybeNull,_) | (_,MaybeNull) ⇒ MaybeNull
      case _ ⇒ NotNull
    }
}

case object MaybeNull extends Null {
  override def toString = "null"
}

case object NotNull extends Null {
  override def toString = "Null.⊥"
}

object Null {
  val ⊥ = NotNull
  val ⊤ = MaybeNull
  val BV = BValue( Num.⊥, Bool.⊥, Str.⊥, Addresses(), ⊤, Undef.⊥ )
}

sealed abstract class Undef {
  def ⊔( nil:Undef ): Undef =
    (this, nil) match {
      case (MaybeUndef,_) | (_,MaybeUndef) ⇒ MaybeUndef
      case _ ⇒ NotUndef
    }
}

case object MaybeUndef extends Undef {
  override def toString = "undefined"
}

case object NotUndef extends Undef {
  override def toString = "Undef.⊥"
}

object Undef {
  val ⊥ = NotUndef
  val ⊤ = MaybeUndef
  val BV = BValue( Num.⊥, Bool.⊥, Str.⊥, Addresses(), Null.⊥, ⊤ )
}

//——————————————————————————————————————————————————————————————————————————————
// Closure. We use both regular closures and native Scala methods.

sealed abstract class Closure extends SmartHash
case class Clo( ρ:Env, m:Method ) extends Closure
object Native {
  private var hashCounter = 0
  // for getting deterministic hash codes
  def freshHash(): Int = {
    val retval = hashCounter
    hashCounter += 1
    retval
  }
}
case class Native( f:(BValue, BValue, Var, Env, Store, Scratchpad, KStack, Trace) ⇒ Set[State] ) extends Closure {
  val hash = Native.freshHash()
  override def hashCode(): Int = hash
}

//——————————————————————————————————————————————————————————————————————————————
// Object

// the intern map has Any as its co-domain because it needs to store
// BValues, Closures, and JSClasses
case class Object( extern:ExternMap, intern:Map[Str, Any], present:Set[Str] ) extends SmartHash {
  assert( present forall ( (str) ⇒ Str.isExact(str) ) )

  // store this object's JS class and prototype for easy reference
  val myClass = intern(classname).asInstanceOf[JSClass]
  val myProto = intern(proto).asInstanceOf[BValue]

  // lattice join
  def ⊔( o:Object ): Object =
    if ( this == o ) this
    else {
      // can only join objects from the same class
      assert(myClass == o.myClass)

      val extern1 = extern ⊔ o.extern
      val present1 = present & o.present

      val intern1 = for ( (k, v) ← o.intern ) yield k match {
        case `code` ⇒ 
          val me = intern(code).asInstanceOf[Set[Closure]]
          val that = v.asInstanceOf[Set[Closure]]
          (k, me ++ that )
        case `classname` ⇒
          assert( v.asInstanceOf[JSClass] == myClass )
          (k, myClass)
        case `constructor` ⇒
          (k, true) // value of constructor doesn't matter, only its presence
        case bv ⇒
          // there can be a period of time when the internal value field is not
          // set for some objects, we use ⊥ for that period of time
          val me = intern get (k) match {
            case Some(iv) ⇒ iv.asInstanceOf[BValue]
            case None ⇒ BValue.⊥
          }
          val that = v.asInstanceOf[BValue]
          (k, me ⊔ that)
      }

      // since there is a period of time between when we allocate an
      // Arguments object for a New and the time we set its
      // constructor field, it is possible to allocate the same
      // Arguments object at the same address, but the new version
      // doesn't have the constructor field yet; it is always safe to
      // ensure that the joined object has the constructor field if
      // either of them do (the new Arguments object will get its
      // constructor field set eventually anyway).
      val intern2 = 
        if ( intern contains constructor ) intern1 + (constructor → true)
        else intern1

      Object( extern1, intern2, present1 )
    }

  // retrieve a field's value. this is _not_ the complete field lookup
  // semantics, which includes looking up the prototype chain
  def apply( str:Str ): Option[BValue] =
    extern(str)

  // strongly update a field of the object if the given field is
  // exact, otherwise weakly update it. depending on the object's
  // class some fields are non-updateable; we check for that here
  def ++( sv:(Str, BValue) ): Object =
    sv match {
      case (str, bv) if Str.isExact(str) ⇒
        if ( Init.noupdate(myClass) contains str ) this
        else Object( extern ++ sv, intern, present + str )

      case _ ⇒ 
        Object( extern + sv, intern, present )
    }

  // weakly update a field of the object. depending on the object's
  // class some fields are non-updateable; we check for that here
  def +( sv:(Str, BValue) ): Object = 
    sv match {
      case (str, bv) if Str.isExact(str) ⇒
        if ( Init.noupdate(myClass) contains str ) this
        else Object( extern + sv, intern, present )

      case (str, bv) ⇒
        Object( extern + sv, intern, present )
    }

  // strongly delete a field from the object; we should be guaranteed
  // that the field is there (implying the Str is exact) and that it
  // is deleteable
  def −−( str:Str ): Object = {
    assert( present(str) && !(Init.nodelete(myClass) contains str) )
    Object( extern − str, intern, present - str )
  }

  // weakly delete the given field from the object if possible
  def −( str:Str ): Object =
    if ( Str.isExact(str) ) {
      if ( !(Init.nodelete(myClass) contains str) )
        Object( extern, intern, present - str )
      else this
    }
    else {
      val lte = extern.exactlte( str ) -- Init.nodelete(myClass)
      Object( extern, intern, present -- lte )
    }

  // enumerate the fields of the object. skip non-enumerable fields
  def fields: Set[Str] = 
    extern.reducedKeys -- Init.noenum(myClass)

  // get this object's internal class
  def getJSClass: JSClass =
    myClass

  // get this object's internal prototype
  def getProto: BValue =
    myProto

  // get this object's internal value
  def getValue: BValue =
    intern(value).asInstanceOf[BValue]

  // return the set of closures (empty if this isn't a function class)
  def getCode: Set[Closure] =
    intern get code match {
      case Some(anyset) ⇒ anyset.asInstanceOf[Set[Closure]]
      case _ ⇒ Set[Closure]()
    }

  def calledAsCtor: Boolean = 
    // the value of constructor doesn't matter, just whether it is
    // present or not
    intern.contains(constructor) 
    
  // is the given string definitely a field of this object?
  def defField( str:Str ): Boolean =
    present(str)

  // is the given string definitely not a field of this object?
  def defNotField( str:Str ): Boolean =
    extern notcontains str

  // return all the base values contained by the object,
  // that is, the co-domain of extern and intern maps
  // this interface is used by prune and fullgc  
  def getAllValues: Set[BValue] = 
    extern.getAllValues ++ (intern.values.flatMap { 
      (x) ⇒ if (x.isInstanceOf[BValue]) Some(x.asInstanceOf[BValue])
            else None
      })
}

// object operations are critical for performance; we could write a
// generic version that would work with any abstract string domain,
// but the cost would be prohibitive. instead we Splize the
// external map implementation to the specific string domain we're
// using. if we change the abstract string domain, we'll need to
// change this external map implementation.
//
// in this case, we'll store the values (if any) for the inexact
// strings separately from the exact strings, and exact non-numeric
// strings separately from exact numeric strings. this will make
// various operations more efficient, as we don't have to search
// through all the keys every time to figure out their relative
// ordering.
//
// !! PROFILE: we are trading off a somewhat more expensive lookup for
//             a simpler and less expensive update and join; it would
//             be worth exploring the other direction
//
// !! OPT: object ⊔ might be a good place to look for and remove
//         redundant entries (i.e., entries with exactly the same
//         value as a less-precise entry)
//
case class ExternMap( top:Option[BValue] = None, 
                      notnum:Option[BValue] = None, 
                      num:Option[BValue] = None, 
                      exactnotnum:Map[Str, BValue] = Map(),
                      exactnum:Map[Str, BValue] = Map() ) 
     extends SmartHash {

  assert(exactnotnum.keys.forall(Str.isExactNotNum(_)) &&
         exactnum.keys.forall(Str.isExactNum(_)))    

  def ⊔( ext:ExternMap ): ExternMap = {
    val top1 = (top, ext.top) match {
      case (Some(bv1), Some(bv2)) ⇒ Some(bv1 ⊔ bv2)
      case (_:Some[_], None) ⇒ top
      case (None, _:Some[_]) ⇒ ext.top
      case _ ⇒ None
    }

    val notnum1 = (notnum, ext.notnum) match {
      case (Some(bv1), Some(bv2)) ⇒ Some(bv1 ⊔ bv2)
      case (_:Some[_], None) ⇒ notnum
      case (None, _:Some[_]) ⇒ ext.notnum
      case _ ⇒ None
    }

    val num1 = (num, ext.num) match {
      case (Some(bv1), Some(bv2)) ⇒ Some(bv1 ⊔ bv2)
      case (_:Some[_], None) ⇒ num
      case (None, _:Some[_]) ⇒ ext.num
      case _ ⇒ None
    }

    val _exactnotnum =
      if ( exactnotnum == ext.exactnotnum ) exactnotnum
      else ext.exactnotnum ++ (exactnotnum map {
        case (k, bv) ⇒ ext.exactnotnum get k match {
          case Some(bv1) ⇒ (k, bv ⊔ bv1)
          case _ ⇒ (k, bv)
        }
      })

    val _exactnum =
      if ( exactnum == ext.exactnum ) exactnum
      else ext.exactnum ++ (exactnum map {
        case (k, bv) ⇒ ext.exactnum get k match {
          case Some(bv1) ⇒ (k, bv ⊔ bv1)
          case _ ⇒ (k, bv)
        }
      })

    ExternMap( top1, notnum1, num1, _exactnotnum, _exactnum )
  }

  // return the value of the given key joined with the values of all
  // comparable keys (or None if none of those things exist)
  def apply( str:Str ): Option[BValue] = {
    lazy val splValues = exactnotnum.filterKeys(x ⇒ Str.SplStrings(Str.getExact(x).get)).values
    lazy val nonSplValues = exactnotnum.filterKeys(x ⇒ !Str.SplStrings(Str.getExact(x).get)).values

    val vs = (str match {
      case s:SConstNotSplNorNum ⇒ 
        top ++ notnum ++ (exactnotnum get s)
      case s:SConstSpl ⇒
        top ++ notnum ++ (exactnotnum get s)  
      case s:SConstNum ⇒ 
        top ++ num ++ (exactnum get s)
      case SNum ⇒ 
        top ++ num ++ exactnum.values
      case SNotSplNorNum ⇒  
        top ++ notnum ++ nonSplValues
      case SSpl ⇒
        top ++ notnum ++ splValues
      case SNotSpl ⇒
        top ++ num ++ notnum ++ exactnum.values ++ nonSplValues   
      case SNotNum ⇒
        top ++ notnum ++ exactnotnum.values
      case STop ⇒
        top ++ notnum ++ num ++ exactnotnum.values ++ exactnum.values
      case _ ⇒ sys.error("tried to use Str.⊥ with an object")
    }).toSet

    if ( vs.isEmpty ) None else Some(vs.reduceLeft( (acc, bv) ⇒ acc ⊔ bv ))
  }

  // strong update of field to value
  def ++( sv:(Str,BValue) ): ExternMap =
    sv match {
      case (s:SConstNotSplNorNum, bv) ⇒
        val exactnotnum1 = exactnotnum + (s → bv)
        ExternMap( top, notnum, num, exactnotnum1, exactnum )

      case (s:SConstSpl, bv) ⇒
        val exactnotnum1 = exactnotnum + (s → bv)  
        ExternMap( top, notnum, num, exactnotnum1, exactnum )

      case (s:SConstNum, bv) ⇒
        val exactnum1 = exactnum + (s → bv)
        ExternMap( top, notnum, num, exactnotnum, exactnum1 )

      case _ ⇒ sys.error("tried to add inexact string using ++")
    }

  // weak update of field to value
  def +( sv:(Str,BValue) ): ExternMap =
    sv match {
      case (str:SConstNotSplNorNum, bv) ⇒
        val bv1 = exactnotnum get str match {
          case Some(_bv) ⇒ bv ⊔ _bv
          case _ ⇒ bv
        }
        val exactnotnum1 = exactnotnum + (str → bv1)
        ExternMap( top, notnum, num, exactnotnum1, exactnum )

      case (str:SConstSpl, bv) ⇒
        val bv1 = exactnotnum get str match {
          case Some(_bv) ⇒ bv ⊔ _bv
          case _ ⇒ bv
        }
        val exactnotnum1 = exactnotnum + (str → bv1)
        ExternMap( top, notnum, num, exactnotnum1, exactnum )

      case (str:SConstNum, bv) ⇒
        val bv1 = exactnum get str match {
          case Some(_bv) ⇒ bv ⊔ _bv
          case _ ⇒ bv
        }
        val exactnum1 = exactnum + (str → bv1)
        ExternMap( top, notnum, num, exactnotnum, exactnum1 )

      case (SNum, bv) ⇒
        val num1 = num match {
          case Some(bv1) ⇒ Some(bv ⊔ bv1)
          case _ ⇒ Some(bv)
        }
        ExternMap( top, notnum, num1, exactnotnum, exactnum )

      case (SNotSplNorNum, bv) ⇒
        val notnum1 = notnum match {
          case Some(bv1) ⇒ Some(bv ⊔ bv1)
          case _ ⇒ Some(bv)
        }
        ExternMap( top, notnum1, num, exactnotnum, exactnum )

      case (SSpl, bv) ⇒
        val notnum1 = notnum match {
          case Some(bv1) ⇒ Some(bv ⊔ bv1)
          case _ ⇒ Some(bv)
        }
        ExternMap( top, notnum1, num, exactnotnum, exactnum )
  
      case (SNotSpl, bv) ⇒
        val top1 = top match {
          case Some(bv1) ⇒ Some(bv ⊔ bv1)
          case _ ⇒ Some(bv)
        }
        ExternMap( top1, notnum, num, exactnotnum, exactnum )
  
      case (SNotNum, bv) ⇒
        val notnum1 = notnum match {
          case Some(bv1) ⇒ Some(bv ⊔ bv1)
          case _ ⇒ Some(bv)
        }
        ExternMap( top, notnum1, num, exactnotnum, exactnum )

      case (STop, bv) ⇒
        val top1 = top match {
          case Some(bv1) ⇒ Some(bv ⊔ bv1)
          case _ ⇒ Some(bv)
        }
        ExternMap( top1, notnum, num, exactnotnum, exactnum )

      case _ ⇒ sys.error("tried to use Str.⊥ with an object")
    }

  // remove this exact string from the map
  def −( str:Str ): ExternMap =
    str match {
      case s:SConstNotSplNorNum ⇒
        ExternMap( top, notnum, num, exactnotnum - s, exactnum )

      case s:SConstSpl ⇒
        ExternMap( top, notnum, num, exactnotnum - s, exactnum )

      case s:SConstNum ⇒
        ExternMap( top, notnum, num, exactnotnum, exactnum - s )

      case _ ⇒ sys.error("tried to remove inexact string")
    }

  // true iff there is no key that is comparable to str
  def notcontains( str:Str ): Boolean = {
    lazy val splValues = exactnotnum.filterKeys(x ⇒ Str.SplStrings(Str.getExact(x).get)).values 
    lazy val nonSplValues = exactnotnum.filterKeys(x ⇒ !Str.SplStrings(Str.getExact(x).get)).values

    str match {
      case s:SConstNotSplNorNum ⇒
        top.isEmpty && notnum.isEmpty && !(exactnotnum contains s)

      case s:SConstSpl ⇒
        top.isEmpty && notnum.isEmpty && !(exactnotnum contains s)

      case s:SConstNum ⇒ 
        top.isEmpty && num.isEmpty && !(exactnum contains s)

      case SNotSplNorNum ⇒
        top.isEmpty && notnum.isEmpty && nonSplValues.isEmpty

      case SSpl ⇒
        top.isEmpty && notnum.isEmpty && splValues.isEmpty

      case SNum ⇒
        top.isEmpty && num.isEmpty && exactnum.isEmpty

      case SNotSpl ⇒
        top.isEmpty && num.isEmpty && notnum.isEmpty && 
        exactnum.isEmpty && nonSplValues.isEmpty

      case SNotNum ⇒
        top.isEmpty && notnum.isEmpty && exactnotnum.isEmpty

      case STop ⇒
        top.isEmpty && notnum.isEmpty && num.isEmpty &&
        exactnotnum.isEmpty && exactnum.isEmpty

      case _ ⇒ sys.error("tried to use Str.⊥ with an object")
    }
  }

  // return all exact keys ⊑ str. the annoying asInstanceOf is
  // required because Set is invariant instead of covariant
  def exactlte( str:Str ): Set[Str] = {
    lazy val nonSplKeys = exactnotnum.keySet.filter(x ⇒ !Str.SplStrings(Str.getExact(x).get))

    str match {
      case s:SConstNotSplNorNum ⇒
        if ( exactnotnum contains s ) Set(str) else Set()

      case s:SConstSpl ⇒
        if ( exactnotnum contains s ) Set(str) else Set()

      case s:SConstNum ⇒ 
        if ( exactnum contains s ) Set(str) else Set()

      case SNum ⇒
        exactnum.keySet

      case SNotSplNorNum ⇒
        nonSplKeys

      case SSpl ⇒
        exactnotnum.keySet.filter(x ⇒ Str.SplStrings(Str.getExact(x).get))

      case SNotSpl ⇒ 
        (exactnum.keySet ++ nonSplKeys)  

      case SNotNum ⇒
        exactnotnum.keySet

      case STop ⇒
        (exactnotnum.keySet ++ exactnum.keySet)

      case _ ⇒ sys.error("tried to use Str.⊥ with an object")
    }
  }

  // return the set of keys, reduced by removing any keys that are
  // over-approximated by other keys
  def reducedKeys: Set[Str] =
    top match {
      case Some(_) ⇒ 
        Set( STop )

      case None ⇒
        (notnum match {
          case Some(_) ⇒ Set( SNotNum )
          case None ⇒ exactnotnum.keySet
        }) ++ (num match {
          case Some(_) ⇒ Set( SNum )
          case None ⇒ exactnum.keySet
        })
    }

  // return all the base values contained by the extern map
  // that is, the co-domain of extern map
  def getAllValues: Set[BValue] = 
    top.toSet ++ notnum ++ num ++ exactnotnum.values ++ exactnum.values   
}

//——————————————————————————————————————————————————————————————————————————————
// Kont

// we'll implement the continuation stack as an actual stack, so these
// definitions don't include the Kont parameters that are in the
// semantics definitions (which only serve to simulate a stack)
//
// the RetK/AddrK continuations include a trace τ and method m that
// aren't in the semantics document; τ is for control-flow
// sensitivity, while m is so that we can track information useful for
// garbage collection and pruning. RetK also includes a boolean isctor
// that tells whether we are returning from a constructor or returning
// from a method call.
//
sealed abstract class Kont extends SmartHash
case object HaltK extends Kont
case class SeqK( ss:List[Stmt] ) extends Kont
case class WhileK( e:Exp, s:Stmt ) extends Kont
case class ForK( bv:BValue, x:Var, s:Stmt ) extends Kont
case class RetK( x:Var, ρ:Env, isctor:Boolean, τ:Trace ) extends Kont
case class TryK( x:PVar, sc:Stmt, sf:Stmt ) extends Kont
case class CatchK( sf:Stmt ) extends Kont
case class FinK( vs:Set[Value] ) extends Kont
case class LblK( lbl:String ) extends Kont
case class AddrK( a:Address, m:Method ) extends Kont

// continuation stack; exc indicates the presence of an exception
// handler:
//
// 0: no exception handler anywhere on continuation stack
// 1: exception handler in some caller of this function
// 2: exception handler inside the current function
//
case class KStack( κs:List[Kont], exc:List[Int] = List(0) ) extends SmartHash {
  def ⊔( rhs:KStack ): KStack = {
    // continuation stacks being joined should be exactly the same
    // except perhaps different values inside FinK and ForK
    assert( κs.size == rhs.κs.size &&
      (κs zip rhs.κs).foldLeft( true )( (acc, kk) ⇒ kk match {
        case (_:FinK, _:FinK) ⇒ acc && true
        case (_:ForK, _:ForK) ⇒ acc && true
        case (x, y) if x == y ⇒ acc && true
        case _ ⇒ false
      }) )

    val newks = (κs zip rhs.κs) map {
      case (FinK(vs1), FinK(vs2)) ⇒
        val bv = (vs1 find (_.isInstanceOf[BValue]),
            vs2 find (_.isInstanceOf[BValue])) match {
          case (None, None) ⇒ Set()
          case (Some(bv1:BValue), Some(bv2:BValue)) ⇒ Set(bv1 ⊔ bv2)
          case (Some(bv1),_) ⇒ Set(bv1)
          case (_,Some(bv2)) ⇒ Set(bv2)
        }

        val ev = (vs1 find (_.isInstanceOf[EValue]),
                  vs2 find (_.isInstanceOf[EValue])) match {
          case (None, None) ⇒ Set()
          case (Some(ev1:EValue), Some(ev2:EValue)) ⇒
            Set(EValue(ev1.bv ⊔ ev2.bv))
          case (Some(ev1),_) ⇒ Set(ev1)
          case (_,Some(ev2)) ⇒ Set(ev2)
        }

        val jv = (vs1 find (_.isInstanceOf[JValue]),
            vs2 find (_.isInstanceOf[JValue])) match {
          case (None, None) ⇒ Set()
          case (Some(jv1:JValue), Some(jv2:JValue)) ⇒
            if ( jv1.lbl == jv2.lbl ) Set(JValue(jv1.lbl, jv1.bv ⊔ jv2.bv))
            else Set(jv1, jv2)
          case (Some(jv1),_) ⇒ Set(jv1)
          case (_,Some(jv2)) ⇒ Set(jv2)
        }

        FinK(bv ++ ev ++ jv)

      case (ForK(bv1, x1, s1), ForK(bv2, x2, s2)) ⇒
        assert( x1 == x2 && s1 == s2 )
        ForK(bv1 ⊔ bv2, x1, s1)

      case (k1, _) ⇒
        k1
    }

    // EITHER both exception handler stacks are the same 
    // OR they are both of the same size, with everything 
    // except the bottom of the stacks being same and
    // the bottom of the stacks are both not exception handlers
    // inside the current function
    assert( exc == rhs.exc || (exc.size == rhs.exc.size &&
      exc.init == rhs.exc.init && exc.last < 2 && rhs.exc.last < 2) )

    // pick the one whose bottom of the stack is higher
    val newexc = 
      if (exc.last < rhs.exc.last) rhs.exc
      else exc 

    KStack( newks, newexc )
  }

  def push( κ:Kont ): KStack = {
    val newexc = κ match {
      case _:TryK | _:CatchK ⇒ 2 :: exc
      case _ ⇒ exc
    }
    KStack( κ :: κs, newexc )
  }

  def pop: KStack = {
    val newexc = κs.head match {
      case _:TryK | _:CatchK ⇒ exc.tail
      case _ ⇒ exc
    }
    KStack( κs.tail, newexc )
  }

  // replace the top of the stack (i.e., pop then push)
  def repl( κ:Kont ): KStack = {
    assert( (κs.head, κ) match {
      case (_:TryK, _:TryK) | (_:CatchK, _:TryK) | (_:CatchK, _:CatchK) ⇒ false
      case _ ⇒ true
    })

    val newexc = (κs.head, κ) match {
      case (_:TryK, _:CatchK) ⇒ exc
      case (_, _:TryK) ⇒ 2 :: exc
      case (_:TryK, _) | (_:CatchK, _) ⇒ exc.tail
      case _ ⇒ exc
    }
    KStack( κ :: κs.tail, newexc )
  }

  def top: Kont =
    κs.head

  def last: Kont =
    κs.last

  def toHandler: KStack = {
    val newks = κs dropWhile ( _ match {
      case _:TryK | _:CatchK ⇒ false
      case _ ⇒ true
    } )
    KStack( newks, exc )
  }

  def toSpecial( lbl:String ): KStack = {
    val newks = κs dropWhile ( _ match {
      case _:TryK | _:CatchK | HaltK ⇒ false
      case LblK(lbl1) if lbl1 == lbl ⇒ false
      case _ ⇒ true
    } )
    KStack( newks, exc )
  }
}

object KStack {
  def apply( κ:Kont ): KStack = KStack( List(κ) )
  def apply( κ:Kont, exc:Int ): KStack = KStack( List(κ), List(exc) )
}
