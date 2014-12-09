// This file contains the definitions of the abstract helper
// functions. See the notJS semantics document Section 3.5 for the
// specifications.

package notjs.abstracted.helpers

import notjs.syntax._
import notjs.abstracted.init.Init._
import notjs.abstracted.traces._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.interpreter._

import scala.collection.mutable.{ HashMap }

//——————————————————————————————————————————————————————————————————————————————
// handy definitions

// exceptions that can be thrown implicitly
object Errors {
  val typeError   = EValue(Str.inject(Str.α("TypeError")))
  val rangeError  = EValue(Str.inject(Str.α("RangeError")))
  val uriError    = EValue(Str.inject(Str.α("URIError")))
  val syntaxError = EValue(Str.inject(Str.α("SyntaxError")))
}

// builtin object fields
object Fields {
  val proto       = Str.α("proto")
  val classname   = Str.α("class")
  val code        = Str.α("code")
  val prototype   = Str.α("prototype")
  val length      = Str.α("length")
  val value       = Str.α("value")
  val message     = Str.α("message")
  val constructor = Str.α("constructor")
}

// filters on base values used for value refinement

object Filters {
  sealed abstract class BVFilter
  case object IsFunc extends BVFilter 
  case object IsUndefNull extends BVFilter 
}

import Errors._
import Fields._
import Filters._

//——————————————————————————————————————————————————————————————————————————————
// helper functions

object Helpers {

  // deviation from the semantics document: we don't generate
  // addresses here, instead we generate them using the trace and pass
  // them in here
  def alloc( σ:Store, as:List[Address], bvs:List[BValue] ): Store =
    σ alloc (as zip bvs)

  def alloc( σ:Store, a:Address, κs:KStack ): Store =
    σ alloc( a, κs )

  
  // deviation from the semantics document: we don't generate the
  // address here, instead we generate it using the trace and pass it
  // in here.
  def allocFun( clo:Closure, n:BValue, a:Address, σ:Store ): Store = {
    val intern = Map(
      proto → Address.inject(Function_prototype_Addr),
      classname → CFunction,
      code → Set(clo)
    )
    val extern = ExternMap() ++ (length → n)
    σ alloc (a, Object(extern, intern, Set(length)))
  }


  // deviation from the semantics document: we don't generate the
  // address here, instead we generate it using the trace and pass it
  // in here. it is possible for one allocation site to allocate more
  // than one class of object, but we need to guarantee that each
  // address maps to only one class of object. therefore we reserve a
  // range of |JSClass| possible addresses for each object allocation
  // site——the address passed in is the first element in that range,
  // and we modify it as needed for each class allocated here.
  def allocObj(bv:BValue, a:Address, σ:Store, τ:Trace): (Store, BValue) = {
    val class1 = bv.as.groupBy[JSClass]( classFromAddress(_) )
    val classes = 
      if ( bv.defAddr ) class1
      else class1 get CObject match {
        case Some(as) ⇒ class1 + (CObject → (as + Object_prototype_Addr))
        case None ⇒ class1 + (CObject → Set(Object_prototype_Addr))
      }

    val addrs:Map[JSClass, Address] = classes map {
      case (c, _) ⇒ (c, τ.modAddr(a, c))
    }

    val pas:Map[JSClass,BValue] = classes map {
      case (c, as) ⇒ c → Addresses.inject(as.foldLeft( Addresses() )(
        (acc, a) ⇒ (σ getObj a)(prototype) match {
          case Some(proto) ⇒
            if ( proto.defAddr ) acc ++ proto.as
            else acc ++ proto.as + Object_prototype_Addr

          case _ ⇒ acc + Object_prototype_Addr
        }))
    }

    val intern:Map[JSClass,Map[Str,Any]] = classes map {
      case (c, _) ⇒ c → Map(proto → pas(c), classname → c)
    }

    val σ1 = classes.keys.foldLeft( σ )( (acc, c) ⇒ {
      val o = Object(ExternMap(), intern(c), Set())
      acc alloc( addrs(c), o )
    })

    val bv1 = Addresses.inject( addrs.values.toSet )
    
    (σ1, bv1)
  }


  def applyClo( bv1:BValue, bv2:BValue, bv3:BValue, x:Var, ρ:Env, σ:Store, ß:Scratchpad, κs:KStack, τ:Trace ): Set[State] = {
    if ( notJS.Mutable.splitStates )
      return applyCloWithSplits(bv1, bv2, bv3, x, ρ, σ, ß, κs, τ)  
    // until we do value refinement, we are going to cast bv2 to addresses
    // TODO: change bv2as back to bv2 after value refinement
    val bv2as = Addresses.inject(bv2.as)
    // the translator should guarantee that bv2 and bv3 do contain
    // addresses and only addresses, and the args address is a singleton
    assert( bv2as.defAddr && bv3.defAddr && bv3.as.size == 1 )

    val isctor = (σ getObj bv3.as.head) calledAsCtor

    // for store pruning (if enabled): get the set of object roots,
    // which will be the same for all callees. note that we don't
    // include ß, since that is unreachable by the callee.
    //
    // !! OPT: we could go ahead and prune the store based on oas here
    // and then prune the reachable result for vas for each
    // closure, rather than pruning for both oas and vas every
    // time from scratch.
    //
    val oas =
      if ( notJS.Mutable.pruneStore ) bv2.as ++ bv3.as ++ keepInStore
      else Addresses()

    // memoize the pruned store info based on the set of free
    // variables (specifically their addresses); if we have multiple
    // callees with the same set of free variables then we don't need
    // to prune separately for each one
    val memo = HashMap[Addresses, Store]()

    val (ςs, nonfun) = bv1.as.foldLeft( (Set[State](), false) )(
      (acc, a) ⇒ {
       (σ getObj a).getCode match {
       case clos if clos.nonEmpty ⇒ (acc._1 ++ (clos flatMap {
       case Clo(ρc, m @ Method(self, args, s)) ⇒
              // are we doing store pruning?
              if ( notJS.Mutable.pruneStore ) { // yes, prune store
                val vas = ρc.addrs
                val reach_σ = memo get vas match { // check the cache
                    case None ⇒ // prune to get reachable/unreachable stores
                      val (rσ, uσ) = σ.prune( vas, oas )
                      PruneStoreToo(τ) = (uσ, ß)
                      memo(vas) = rσ
                      rσ

                    case Some(stored) ⇒ // retrieve from memo
                      stored
                  }
                val τ1 = τ.update(ρc, σ, bv2as, bv3, s)
                val ka = τ1.toAddr
                val as = List(τ1.makeAddr(self), τ1.makeAddr(args))
                val rσ1 = alloc( reach_σ, as, List(bv2as, bv3) )
                val rσ2 = alloc( rσ1, ka, κs push RetK(x, ρ, isctor, τ))
                val ρc1 = ρc ++ (List(self, args) zip as)
                // if there was an exception handler in the current function
                // update it to say that exception handler is some where up 
                // in the call stack
                val exc = if (κs.exc.head != 0) 1 else 0
                Set(
                  State(s, ρc1, rσ2, Scratchpad(0), KStack(AddrK(ka,m),exc), τ1)
                )
              }
              else { // no, only prune scratchpad
               val τ1 = τ.update(ρc, σ, bv2as, bv3, s)
               val ka = τ1.toAddr
               val as = List(τ1.makeAddr(self), τ1.makeAddr(args))
               val σ1 = alloc( σ, as, List(bv2as, bv3) )
               val σ2 = alloc( σ1, ka, κs push RetK(x, ρ, isctor, τ))
               val ρc1 = ρc ++ (List(self, args) zip as)
                val exc = if (κs.exc.head != 0) 1 else 0
                PruneScratch(τ) = ß
                Set(
                  State(s, ρc1, σ2, Scratchpad(0), KStack(AddrK(ka,m),exc), τ1)
                )
              }

            case Native(f) ⇒
              f( bv2as, bv3, x, ρ, σ, ß, κs, τ )
          }), acc._2)

       case _ ⇒ (acc._1, true)
        }
      })

    // if we're pruning then we need to worry about the following
    // problem: if this is the first time we're processing a callee
    // we're guaranteed that we'll eventually get to the corresponding
    // RetK (because the AddrK given to the callee will have never
    // been seen before). however, if it isn't the first time for any
    // of the callees then they could all converge, thus never getting
    // to the corresponding RetK. if that happens _and_ there is new
    // information in the unreachable store/ß then the analysis will
    // prematurely converge. to prevent this, we will compute the
    // trace for the immediately following Merge (guaranteed to be
    // there by the translator) and remember it in
    // notJS.Mutable.prunedInfo along with the current trace. after
    // the analysis converges, we will iterate through all of the
    // saved pruned information in PruneStoreToo and join it into the
    // appropriate memoized Merge states (determined by the merge
    // traces saved here) and if any of them change we'll add them
    // back to the worklist.
    //
    // IMPORTANT NOTE: this strategy only works if we're using a
    // stack-based trace, guaranteeing that the merge_τ we compute
    // below is the same one that will be computed by the callee's
    // corresponding RetK. if we're using a non-stack-based trace then
    // the trace returned from a call can be completely different, and
    // this solution breaks.
    //
    // the second clause of the guard below that checks whether τ is
    // in PruneStoreToo is needed because the callees could all have
    // been Native closures, in which case we never pruned anything.
    //
    if ( notJS.Mutable.pruneStore && (PruneStoreToo contains τ) ) {
      val merge_τ = κs.top match {
        case SeqK((s:Merge) :: tl) ⇒ τ update s
        case _ ⇒ sys.error("translator reneged")
      }
      val as = x match {
        case pv:PVar ⇒ ρ(pv)
        case _ ⇒ Addresses()
      }
      notJS.Mutable.prunedInfo(merge_τ) = (τ, x, as)
    }

    // return the callee states plus potentially a typeError state
    ςs ++ (
      if ( nonfun ) Some(State(typeError, ρ, σ, ß, κs, τ))
      else None
    )
  }

  def applyCloWithSplits( bv1:BValue, bv2:BValue, bv3:BValue, x:Var, ρ:Env, σ:Store, ß:Scratchpad, κs:KStack, τ:Trace ): Set[State] = {
    // until we do value refinement, we are going to cast bv2 to addresses
    // TODO: change bv2as back to bv2 after value refinement
    val bv2as = Addresses.inject(bv2.as)
    // the translator should guarantee that bv2 and bv3 do contain
    // addresses and only addresses, and the args address is a singleton
    assert( bv2as.defAddr && bv3.defAddr && bv3.as.size == 1 )

    val isctor = (σ getObj bv3.as.head) calledAsCtor

    // for store pruning (if enabled): get the set of object roots,
    // which will be the same for all callees. note that we don't
    // include ß, since that is unreachable by the callee.
    //
    // !! OPT: we could go ahead and prune the store based on oas here
    // and then prune the reachable result for vas for each
    // closure, rather than pruning for both oas and vas every
    // time from scratch.
    //
    val oas =
      if ( notJS.Mutable.pruneStore ) bv2.as ++ bv3.as ++ keepInStore
      else Addresses()

    // memoize the pruned store info based on the set of free
    // variables (specifically their addresses); if we have multiple
    // callees with the same set of free variables then we don't need
    // to prune separately for each one
    val memo = HashMap[Addresses, Store]()

    val (ςs, nonfun) = bv1.as.foldLeft( (Set[State](), false) )(
      (acc, a) ⇒ {
       (σ getObj a).getCode match {
       case clos if clos.nonEmpty ⇒ (acc._1 ++ (clos flatMap {
       case Clo(ρc, m @ Method(self, args, s)) ⇒
              // are we doing store pruning?
              if ( notJS.Mutable.pruneStore ) { // yes, prune store
                val vas = ρc.addrs
                val reach_σ = memo get vas match { // check the cache
                    case None ⇒ // prune to get reachable/unreachable stores
                      val (rσ, uσ) = σ.prune( vas, oas )
                      PruneStoreToo(τ) = (uσ, ß)
                      memo(vas) = rσ
                      rσ

                    case Some(stored) ⇒ // retrieve from memo
                      stored
                  }
                bv2.as.map {
                 case selfAddr ⇒
                  val selfBV = Address.inject(selfAddr)
                  val τ1 = τ.update(ρc, σ, selfBV, bv3, s)
                  val ka = τ1.toAddr
                  val as = List(τ1.makeAddr(self), τ1.makeAddr(args))
                  val rσ1 = alloc( reach_σ, ka, κs push RetK(x, ρ, isctor, τ) )
                  val rσ2 = alloc( rσ1, as, List(selfBV, bv3) )
                  val ρc1 = ρc ++ (List(self, args) zip as)
                  // if there was an exception handler in the current function
                  // update it to say that exception handler is some where up
                  // in the call stack
                  val exc = if (κs.exc.head != 0) 1 else 0
                  State(s, ρc1, rσ2, Scratchpad(0), KStack(AddrK(ka,m),exc), τ1)
                }
              }
              else { // no, only prune scratchpad
               bv2.as.map {
                case selfAddr ⇒
                  val selfBV = Address.inject(selfAddr)
                  val τ1 = τ.update(ρc, σ, selfBV, bv3, s)
                  val ka = τ1.toAddr
                  val as = List(τ1.makeAddr(self), τ1.makeAddr(args))
                  val σ1 = alloc( σ, ka, κs push RetK(x, ρ, isctor, τ))
                  val σ2 = alloc( σ1, as, List(selfBV, bv3) )
                  val ρc1 = ρc ++ (List(self, args) zip as)
                  val exc = if (κs.exc.head != 0) 1 else 0
                  PruneScratch(τ) = ß
                  State(s, ρc1, σ2, Scratchpad(0), KStack(AddrK(ka,m),exc), τ1)
               }
              }

            case Native(f) ⇒
              bv2.as.flatMap {
                selfAddr ⇒ f( Address.inject(selfAddr), bv3, x, ρ, σ, ß, κs, τ )
              }
              
          }), acc._2)

       case _ ⇒ (acc._1, true)
        }
      })

    // if we're pruning then we need to worry about the following
    // problem: if this is the first time we're processing a callee
    // we're guaranteed that we'll eventually get to the corresponding
    // RetK (because the AddrK given to the callee will have never
    // been seen before). however, if it isn't the first time for any
    // of the callees then they could all converge, thus never getting
    // to the corresponding RetK. if that happens _and_ there is new
    // information in the unreachable store/ß then the analysis will
    // prematurely converge. to prevent this, we will compute the
    // trace for the immediately following Merge (guaranteed to be
    // there by the translator) and remember it in
    // notJS.Mutable.prunedInfo along with the current trace. after
    // the analysis converges, we will iterate through all of the
    // saved pruned information in PruneStoreToo and join it into the
    // appropriate memoized Merge states (determined by the merge
    // traces saved here) and if any of them change we'll add them
    // back to the worklist.
    //
    // IMPORTANT NOTE: this strategy only works if we're using a
    // stack-based trace, guaranteeing that the merge_τ we compute
    // below is the same one that will be computed by the callee's
    // corresponding RetK. if we're using a non-stack-based trace then
    // the trace returned from a call can be completely different, and
    // this solution breaks.
    //
    // the second clause of the guard below that checks whether τ is
    // in PruneStoreToo is needed because the callees could all have
    // been Native closures, in which case we never pruned anything.
    //
    if ( notJS.Mutable.pruneStore && (PruneStoreToo contains τ) ) {
      val merge_τ = κs.top match {
        case SeqK((s:Merge) :: tl) ⇒ τ update s
        case _ ⇒ sys.error("translator reneged")
      }
      val as = x match {
        case pv:PVar ⇒ ρ(pv)
        case _ ⇒ Addresses()
      }
      notJS.Mutable.prunedInfo(merge_τ) = (τ, x, as)
    }

    // return the callee states plus potentially a typeError state
    ςs ++ (
      if ( !bv1.defAddr || nonfun ) Some(State(typeError, ρ, σ, ß, κs, τ))
      else None
    )
  }



  def delete(bv1:BValue, bv2:BValue, x:Scratch, ρ:Env, σ:Store, ß:Scratchpad): (Option[(Store, Scratchpad)], Option[EValue]) = {
    val isStrong = bv1.as.size == 1 && σ.isStrong(bv1.as.head)

    val (defPresent, defAbsent) = bv1.as.foldLeft( (true, true) )(
      (acc, a) ⇒ {
        val o = σ getObj a
        val dp = 
          if ( acc._1 )
            o.defField(bv2.str) && 
            !(nodelete(o.getJSClass) contains bv2.str)
          else false
        val da = 
          if ( acc._2 && !dp ) 
            o.defNotField(bv2.str) ||
            (nodelete(o.getJSClass) contains bv2.str)
          else false

        (dp, da)
      })

    val noexc =
      if ( bv1.as.isEmpty )
        None
      else if ( defAbsent ) {
        Some((σ, ß(x) = Bool.FalseBV))
      }
      else if ( defPresent ) {
        if ( isStrong ) {
          val a = bv1.as.head
          val σ1 = σ putObjStrong(a, (σ getObj a) −− bv2.str)
          Some((σ1, ß(x) = Bool.TrueBV))
        }
        else {
          val σ1 = bv1.as.foldLeft( σ )(
            (acc, a) ⇒ acc putObjWeak(a, (acc getObj a) − bv2.str) )
          Some((σ1, ß(x) = Bool.TrueBV))
        }
      }
      else {
        val σ1 = bv1.as.foldLeft( σ )(
          (acc, a) ⇒ acc putObjWeak(a, (acc getObj a) − bv2.str) )
        Some((σ1, ß(x) = Bool.TopBV))
      }

    val exc =
      if ( bv1.nil == Null.⊤ || bv1.undef == Undef.⊤ )
        Some(typeError)
      else
        None

    (noexc, exc)
  }


  // NOTE: getProto and getJSClass are implemented in the Object class
  // NOTE: initState is contained in init.scala
  // NOTE: inject is implemented either in the subdomain's companion
  //       object or, for addresses, in BValue's companion object


  def lookup( as:Addresses, str:Str, σ:Store ): BValue = {
    def look( o:Object ): BValue = {
      val local = o(str).toSet
      val chain = 
      	if ( !o.defField(str) )
      	  o.getProto.as.map( (a) ⇒ look(σ getObj a) )
      	else
      	  Set()
      val fin =
      	if ( !o.defField(str) && o.getProto.nil == Null.⊤ )
      	  Set(Undef.BV)
      	else
      	  Set()

      (local ++ chain ++ fin).reduceLeft( (acc, bv) ⇒ acc ⊔ bv )
    }

    as.foldLeft( BValue.⊥ )( (acc, a) ⇒ acc ⊔ look(σ getObj a) )
  }


  // NOTE: there is no nextK; that functionality is implemented
  //       directly in the transition rules in interpreter.scala


  // retrieve all keys accessible via this object, including ones in
  // the prototype chain. we optimize the keyset by removing keys that
  // are over-approximated by other keys in the set
  def objAllKeys( bv:BValue, σ:Store ): Set[Str] = {
    def recur( a:Address ): Set[Str] = {
      val o = σ getObj a
      o.getProto.as.foldLeft( o.fields )(
        (acc, a) ⇒ acc ++ recur(a) )
    }

    val keys = bv.as.flatMap( recur(_) )
    Str.minimize( keys )
  }


  // note that we add the constructor with a strong update to the
  // object and address without checking whether the address is weak;
  // this is OK because the translator guarantees that all concrete
  // addresses represented by the abstract address would also be
  // marked as constructors.
  def setConstr( σ:Store, bv:BValue ): Store = {
    assert( bv.as.size == 1 )
    val o = σ getObj bv.as.head
    val o1 = Object( o.extern, o.intern + (constructor → true), o.present )
    σ putObjStrong( bv.as.head, o1 )
  }

  
  // NOTE: there is no specialK; that functionality is implemented
  //       directly in the transition rules in interpreter.scala


  // factored out of toObj to avoid duplication in Object constructor
  // this implements most of toObj's functionality
  def toObjBody(bv: BValue, σ: Store, τ: Trace, a: Address): (BValue, Store, Set[Domain]) = {
    val sorts = bv.sorts & Set( DAddr, DNum, DBool, DStr )

    val (bv1, σ1) = sorts.foldLeft( (BValue.⊥, σ) )(
      (acc, sort) ⇒ sort match {
        case DAddr ⇒
          (acc._1 ⊔ Addresses.inject(bv.as), acc._2)

        case DNum ⇒
          val (σ2, bv2) = allocObj(Address.inject(Number_Addr), a, acc._2, τ)
          assert( bv2.as.size == 1 )
          val o = σ2 getObj bv2.as.head
          val o1 = Object(o.extern, o.intern + (value → bv.onlyNum), o.present)
          (acc._1 ⊔ bv2, σ2 putObj( bv2.as.head, o1 ))

        case DBool ⇒
          val (σ2, bv2) = allocObj(Address.inject(Boolean_Addr), a, acc._2, τ)
          assert( bv2.as.size == 1 )
          val o = σ2 getObj bv2.as.head
          val o1 = Object(o.extern, o.intern + (value → bv.onlyBool), o.present)
          (acc._1 ⊔ bv2, σ2 putObj( bv2.as.head, o1 ))

        case DStr ⇒
          val (σ2, bv2) = allocObj(Address.inject(String_Addr), a, acc._2, τ)
          assert( bv2.as.size == 1 )
          val o = σ2 getObj bv2.as.head
          // set the external fields length and indices 0 to length-1
          val exactStr = Str.getExact(bv.str)
          val extern = exactStr match {
            case Some(s) ⇒ 
              List.range(0, s.length).foldLeft(
                o.extern ++ (length → Num.inject(Num.α(s.length))))(
                  (acc, e) ⇒ acc ++ 
                    (Str.α(e.toString) → Str.inject(Str.α(s(e).toString))))

            case None ⇒ 
              (o.extern + (length → Num.inject(NReal))) + 
                (SNum → Str.inject(Str.SingleChar))
          }
          val intern1 = o.intern + (value → bv.onlyStr)
          val o1 = Object(extern, intern1, o.present + length)
          (acc._1 ⊔ bv2, σ2 putObj( bv2.as.head, o1 ))

        case DUndef | DNull ⇒
          sys.error("suppresses compiler warning; this case can't happen")
      })

    (bv1, σ1, sorts)
  }

  def toObj( bv:BValue, x:Var, ρ:Env, σ:Store, ß:Scratchpad, τ:Trace ): (Option[(BValue, Store, Scratchpad)], Option[EValue]) = {
    val (bv1, σ1, sorts) = toObjBody(bv, σ, τ, τ makeAddr x)

    val noexc =
      if ( sorts.nonEmpty ) x match {
        case pv:PVar ⇒
          Some((bv1, σ1 + (ρ(pv) → bv1), ß))

        case sc:Scratch ⇒
          Some((bv1, σ1, ß(sc) = bv1))
      }
      else None

    val exc = 
      if ( bv.nil == Null.⊤ || bv.undef == Undef.⊤ ) Some(typeError)
      else None

    (noexc, exc)
  }


  // NOTE: there is no update; that functionaliy is implemented
  //       directly in the store


  // this isn't quite the same as the semantics for efficiency
  // reasons: rather than creating a bunch of objects using strong
  // updates and then joining them together to account for weak
  // updates, we figure out which one we're doing from the start.
  def updateObj(bv1:BValue, bv2:BValue, bv3:BValue, σ:Store): (Option[(BValue, Store)], Option[EValue]) = {
    val str = bv2.str
    val maybeLength = length ⊑ str
    val isStrong = bv1.as.size == 1 && σ.isStrong(bv1.as.head)
    val bv3num = bv3.tonum
    lazy val maybeArray = bv1.as exists (a ⇒ (σ getObj a).getJSClass == CArray)
    lazy val rhsMaybeU32 = Num.maybeU32( bv3num )
    lazy val propertyMaybeU32 = Num.maybeU32( Num.inject(str.toNum) )

    val noexc =
      if ( isStrong ) {
        val o = σ getObj bv1.as.head
        val o1 =
          if ( !maybeArray ) o ++ (str → bv3)
          else if ( !maybeLength ) 
            o ++ (str → bv3) ++ (length → Num.inject(Num.U32))
          else if ( str != length ) 
            (o − Str.u32) ++ (str → bv3) ++ (length → Num.inject(Num.U32))
          else 
            // !!TODO: we can be more precise in this else case
            (o − Str.u32) ++ (str → Num.inject(Num.U32)) 
        val σ1 = σ putObjStrong( bv1.as.head, o1 )
        Some((bv3, σ1))
      }
      else if ( bv1.as.nonEmpty ) {
       	val σ1 = bv1.as.foldLeft( σ )(
          (acc, a) ⇒ {
            val o = acc getObj a

            if ( o.getJSClass == CArray ) {
              val o1 = 
                if ( maybeLength && rhsMaybeU32 )
                  (o − Str.u32) + (str → bv3)
                else 
                  o + (str → bv3)
              val o2 =     
                if ( propertyMaybeU32 )
                  o1 + (length → Num.inject(Num.U32))
                else 
                  o1 
              acc putObjWeak(a, o2)
            }
            else 
              acc putObjWeak(a, o + (str → bv3))
        })
        Some((bv3, σ1))
      }
      else
        None

    val exc =
      if ( bv1.nil == Null.⊤ || bv1.undef == Undef.⊤ )
        Some(typeError)
      else if ( maybeArray && maybeLength && Num.maybenotU32( bv3 ) )
        Some(rangeError)
      else
        None

    (noexc, exc)
  }

  // perform value refinement on store and scratchpad 
  // for a given expression e base on bv filter
  // for exceptional branches
  def refineExc(e:Exp, σ:Store, ρ:Env, ß:Scratchpad, bvf:BVFilter) = {
    val res = refine(bvf, e, σ, ρ, ß)
    (res._1, res._2)
  }

  // driver function for refinement
  // given input simple expression, store, scratchpad, and filter,
  // return refined stores and scratchpads, in format
  // (σT, ßT, σF, ßF)
  def refine(bvf:BVFilter, e:Exp, σ:Store, ρ:Env, ß:Scratchpad) = e match {
    case x:PVar ⇒
      // if it is a single address (strong)
      val as = ρ(x)
      if (as.size == 1) {
        val (newBVT, newBVF) = σ(as).filterBy(bvf, σ)
        (σ + (as → newBVT), ß, σ + (as → newBVF), ß)
      } else (σ, ß, σ, ß)
    
    case x:Scratch ⇒
      val (newBVT, newBVF) = ß(x).filterBy(bvf, σ)
      (σ, ß(x) = newBVT, σ, ß(x) = newBVF)
    

    case Binop(⌜⋆⌝, el, er) ⇒
      import notjs.abstracted.eval.Eval
      val objbv = Eval.eval(el, ρ, σ, ß )
      val strbv = Eval.eval(er, ρ, σ, ß )
      refineableAddrObj(objbv, strbv.str, σ) match {
        case Some((addr, o)) ⇒ {
          val oldBV = o(strbv.str) match {
            case Some(bv) ⇒ bv
            case _ ⇒ sys.error("refineableAddrObj returned bad object")
          }
          // create the new BV
          val (newBVT, newBVF) = oldBV.filterBy(bvf, σ)
          // create the new objects
          val oT = o copy (extern = o.extern ++ (strbv.str -> newBVT))
          val σT = σ.putObjStrong(addr, oT)
          val oF = o copy (extern = o.extern ++ (strbv.str -> newBVF))
          val σF = σ.putObjStrong(addr, oF)
          (σT, ß, σF, ß)
        }
        case None ⇒ (σ, ß, σ, ß)
      }
      
    case _ ⇒ // a case where we do not refine
      (σ, ß, σ, ß)  
  }

  // helper function for value refinement
  // given base value for object in refinement,
  // check if refinement is doable. if doable, return (address, object) for object
  // that will receive refinement. if not doable, return None
  def refineableAddrObj(bv:BValue, str:Str, σ:Store): Option[(Address, Object)] = {
    // we can refine iff
    // 0: str is exact
    // 1: bv points to a single address
    // 2: bv.a is strong
    if ((bv.as.size == 1) && (σ.isStrong(bv.as.head)) && (Str.isExact(str))) {
      val obj = σ.getObj(bv.as.head)
      // 3: the object pointed to by a definitely contains str
      if (obj.defField(str)) Some(bv.as.head, obj)
      // else if definitely not a field on this obj lookup prototype chain
      else if (obj.defNotField(str)) refineableAddrObj(obj.getProto, str, σ)
      // otherwise, we cannot refine, the field may be present on this obj
      else None
      
    } else None // we cannot do refinement
  }

}
