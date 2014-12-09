// This file contains the definitions of the trace abstractions used
// for control-flow sensitivity according to the paper Hardekopf et al
// "Tunable Control-Flow Sensitivity for Program Analysis".
//
// IMPORTANT NOTE
//
// currently we assume that the trace is stack-based, i.e., the trace
// uses the default implementation of 'update(τ:Trace)' in the Trace
// abstract base class. any non-stack-based trace will not work with
// the current implementation of pruning (for both scratchpad and
// store, so regardless of whether the --prune option is given since
// the scratchpad is always pruned), because that implementation
// assumes that the trace after the call will be identical to the
// trace before the call.
//
// there is a more general pruning strategy that uses the first time
// through the callee to figure out the possible exit traces and
// stores those in a global map, however this is more complicated and
// not yet implemented.
//
// a corollary: if we do allow non-stack-based traces, we need to
// modify AddrK to take a set of addresses instead of a single address
// because non-stack-based traces allow for continuation stacks with
// different AddrK addresses to be joined.

package notjs.abstracted.traces

import notjs.util._
import notjs.syntax._
import notjs.abstracted.helpers.Fields._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.init.Init

import scala.collection.{ Seq ⇒ Sequence, SortedSet }
import scala.collection.mutable.{ListBuffer ⇒ MList}

import TraceHelper._ // defined below

//——————————————————————————————————————————————————————————————————————————————
// Abstract trace base class

sealed abstract class Trace extends SmartHash {
  // update on intraprocedural step
  def update( s:Stmt ): Trace

  // update for function call
  def update( ρ:Env, σ: Store, self:BValue, args:BValue, s:Stmt ): Trace

  // update for function return; default implementation is stack-based
  def update( τ:Trace ): Trace =
    τ

  // convert trace to address
  def toAddr: Address

  // make a new address
  def makeAddr( x:Var ): Address

  // make several new addresses
  def makeAddrs( xs:List[Var] ): List[Address] =
    xs map ( makeAddr(_) )

  // modify an address to account for an object's class
  def modAddr( a:Address, c:JSClass ): Address =
      Trace.c2off get c match {
      	case Some(i) ⇒ Address(a.loc + i)
      	case _ ⇒ a
      }
}

// For adding in requirement that the same trace be returned.
// Multiple bugs have sneaked in the past due to this not being respected
abstract class SameTrace[T <: SameTrace[T]] extends Trace {
  // update on intraprocedural step
  def updateSame(s: Stmt): T
  def update(s: Stmt) = updateSame(s)

  // update for function call
  def updateSame(ρ:Env, σ: Store, self:BValue, args:BValue, s:Stmt): T
  def update( ρ:Env, σ: Store, self:BValue, args:BValue, s:Stmt ) =
    updateSame(ρ, σ, self, args, s)
}

object Trace {
  // map JSClass to address offset; used in modAddr to ensure objects
  // with different JSClass get different addresses. we only need
  // offsets for classes allocated using new, where the class is
  // statically unknown; CFunction is always allocated by newfun and
  // doesn't need an offset.
  val c2off:Map[JSClass, Int] = Map(
    CObject    → 0,
    CArguments → 1,
    CArray     → 2,
    CString    → 3,
    CBoolean   → 4,
    CNumber    → 5,
    CDate      → 6,
    CError     → 7,
    CRegexp    → 8
  )

  // we require that all traces have the base id (i.e., the id of the
  // variable used to create the address) as the lower 32 bits; thus
  // we can always retrieve that base no matter what trace we're using
  def getBase( a:Address ): Int =
    a.loc.intValue()
}

object TraceHelper {

  def IntsToBigInt(tr: Sequence[Int], pp: Int): BigInt = {
    val tracePart = tr.foldLeft( BigInt(0) )(
      (acc, e) ⇒ (acc << 32) + e )
    (tracePart << 32) + pp
  }

  def SortedIntSetsToBigInt(tr: Sequence[SortedSet[Int]], pp: Int): BigInt = {
    // we use separator 0 (32 bits) between each element of the
    // sequence hence the << with 64
    val tracePart = tr.foldLeft( BigInt(0) )(
      (acc, e) ⇒ {
        val setToAddress = e.foldLeft( BigInt(0) )( (acc, e) ⇒ (acc << 32) + e )
        (acc << 64) + setToAddress
      })
    (tracePart << 64) + pp
  }

  def BigIntToSeqInt(tr: BigInt): Sequence[Int] = {
    // these are well packed (without any zero bytes)
    var otr = tr
    val trlist = MList[Int]()
    while (otr != 0 && otr != -1) {
      trlist += otr.intValue()
      otr = otr >> 32
    }
    trlist.reverse.toSeq
  }
}

//——————————————————————————————————————————————————————————————————————————————
// Flow-sensitive, context-insensitive trace

case class FSCI( pp:Int ) extends SameTrace[FSCI] {

  // flow-sensitive
  def updateSame( s:Stmt ) =
    FSCI( s.id )

  // context-insensitive
  def updateSame( ρ:Env, σ: Store, self:BValue, args:BValue, s:Stmt ) =
    FSCI( s.id )

  def toAddr =
    Address(pp)

  def makeAddr( x:Var ) = 
    Address(x.id)
}

object FSCI {
  def apply(): FSCI = FSCI(0)
}

//——————————————————————————————————————————————————————————————————————————————
// Flow-sensitive stack-based k-CFA with h-sensitive heap

case class StackCFA(k: Int, h: Int, pp: Int, tr: Sequence[Int]) extends SameTrace[StackCFA] {
  assert(k >= h, "Heap sensitivity cannot be more than context sensitivity")

  // flow-sensitive
  def updateSame( s: Stmt ) = 
    StackCFA(k, h, s.id, tr)

  // the program point of the current trace is the caller site
  // push caller site to the call history, take top k  
  def updateSame( ρ:Env, σ: Store, self: BValue, args:BValue, s:Stmt ) = 
    StackCFA(k, h, s.id, (pp +: tr) take k) 
    
  def toAddr = 
    IntsToBigInt(tr take h, pp)  

  def makeAddr( x:Var ) = 
    IntsToBigInt(tr take h, x.id)    
}

object StackCFA {
  def apply( k:Int, h:Int ): StackCFA =
    StackCFA(k, h, 0, Sequence[Int]())
}

//——————————————————————————————————————————————————————————————————————————————
// Flow-sensitive, k-object-sensitive with h-sensitive heap. The trace
// is made of the allocation site of the self address. Since we can
// have multiple self addresses, we keep them as a sorted set. We only
// consider the allocation site of the self addresses, not including
// the heap-sensitivity.

case class ObjCFA(k: Int, h: Int, pp: Int, tr: Sequence[SortedSet[Int]]) extends SameTrace[ObjCFA] {
  assert(k >= h, "Heap sensitivity cannot be more than context sensitivity")

  // flow-sensitive
  def updateSame( s: Stmt ) = 
    ObjCFA(k, h, s.id, tr)

  // note: we used to return a set of traces that was the
  // cross-product of self addresses and tr, which is silly
  def updateSame( ρ:Env, σ: Store, self: BValue, args:BValue, s:Stmt ) = 
    ObjCFA(k, h, s.id, 
           ((SortedSet[Int]() ++ self.as.map(Trace.getBase(_))) +: tr) take k)
    
  def toAddr = 
    SortedIntSetsToBigInt(tr take h, pp)  

  def makeAddr( x:Var ) = 
    SortedIntSetsToBigInt(tr take h, x.id)    
}

object ObjCFA {
  def apply( k:Int, h:Int ): ObjCFA =
    ObjCFA(k, h, 0, Sequence[SortedSet[Int]]())
}

//——————————————————————————————————————————————————————————————————————————————
// Flow-sensitive, k-object-sensitive with h-sensitive heap.
// What is called the full object sensitivity.

case class ObjFullCFA(k: Int, pp: Int, tr: Sequence[Int]) extends SameTrace[ObjFullCFA] {
  assert(k > 0, "k needs to be at least 1")

  // flow-sensitive
  def updateSame( s: Stmt ) =
    ObjFullCFA(k, s.id, tr)

  def updateSame( ρ:Env, σ: Store, self: BValue, args:BValue, s:Stmt ) = {
    assert(self.as.size == 1)
    ObjFullCFA(k, s.id, BigIntToSeqInt(self.as.head.loc))
  }
    
  def toAddr =
    IntsToBigInt((tr.reverse take (k-1)).reverse, pp)

  def makeAddr( x:Var ) =
    IntsToBigInt((tr.reverse take (k-1)).reverse, x.id)
}

object ObjFullCFA {
  def apply( k:Int ): ObjFullCFA =
    ObjFullCFA(k, 0, Sequence[Int]())
}

//——————————————————————————————————————————————————————————————————————————————
// Flow-sensitive acyclic-CFA with h-sensitive heap

case class AcyclicCFA(h: Int, pp: Int, tr: Sequence[Int]) extends SameTrace[AcyclicCFA] {

  // flow-sensitive
  def updateSame( s: Stmt ) = 
    AcyclicCFA(h, s.id, tr)

  // the program point of the current trace is the caller site;
  // push caller site to the call history, collapse cycles
  def updateSame( ρ:Env, σ: Store, self: BValue, args:BValue, s:Stmt ) = {
    if (tr contains pp) 
      AcyclicCFA(h, s.id, tr.dropWhile(_ != pp))
    else 
      AcyclicCFA(h, s.id, (pp +: tr))
  }
    
  def toAddr = 
    IntsToBigInt(tr take h, pp)

  def makeAddr( x:Var ) = 
    IntsToBigInt(tr take h, x.id)
}

object AcyclicCFA {
  def apply( h:Int ): AcyclicCFA =
    AcyclicCFA(h, 0, Sequence[Int]())
}

//——————————————————————————————————————————————————————————————————————————————
// Flow-sensitive, k-type-based CFA with h-sensitive heap (adapted
// from Smaragdakis et al)
//
// !! TODO: we would use the prototype of the reciever object as its
//          type (so like object sensitivity except using the self
//          object's prototype instead of its address); except we
//          can't so that with the current interface because we need
//          the store to get the self object's prototype.

//——————————————————————————————————————————————————————————————————————————————
// Flow-sensitive, k-signature-based CFA with h-sensitive heap

case class SigCFA(k:Int, h:Int, pp:Int, tr:Sequence[Int]) extends SameTrace[SigCFA] {
  import SigCFA._

  def updateSame( s:Stmt ) =
    SigCFA(k, h, s.id, tr)

  // the new trace element is 32 bits s.t. for each argument up to and
  // including the fourth there are 7 bits with the first bit being 1
  // and the next 6 bits corresponding to the tuple (Num, Bool,
  // String, Addresses, Null, Undef) s.t. a bit is 1 iff the
  // corresponding domain in the argument is not ⊥.
  def updateSame( ρ:Env, σ:Store, self:BValue, args:BValue, s:Stmt ) = {
    assert( args.as.size == 1 && 
           (σ getObj args.as.head).getJSClass == CArguments )
    val argo = σ getObj args.as.head
    val numargs = argo(length) match {
      case Some(bv) ⇒ bv.n match {
	case NConst(d) ⇒ if (d.toInt > 4) 4 else d.toInt
	case _ ⇒ 0
      }
      case _ ⇒ 0
    }
    var el = 0
    for ( i ← (0 until numargs) ) {
      val bv = argo(Str.α(i.toString)).get
      val bits = bv.sorts.foldLeft( 0x40 )(
	(acc, dom) ⇒ dom match {
	  case DNum   ⇒ acc | 0x20
	  case DBool  ⇒ acc | 0x10
	  case DStr   ⇒ acc | 0x08
	  case DAddr  ⇒ acc | 0x04
	  case DNull  ⇒ acc | 0x02
	  case DUndef ⇒ acc | 0x01
	})
      el = (el << 7) | bits
    }
    SigCFA(k, h, s.id, (el +: tr) take k)
  }

  def toAddr =
    IntsToBigInt(tr take h, pp)

  def makeAddr( x:Var ) = 
    IntsToBigInt(tr take h, x.id)
}

object SigCFA {
  def apply( k:Int, h:Int ): SigCFA =
    SigCFA(k, h, 0, Sequence[Int]())
}

//——————————————————————————————————————————————————————————————————————————————
// Product of stack-based k-CFA and object sensitivity

case class CFAxObj(kCFA: Int, kObj:Int, hCFA: Int, hObj: Int, pp: Int, trCFA: Sequence[Int], trObj: Sequence[SortedSet[Int]]) extends SameTrace[CFAxObj] {
  assert(kCFA >= hCFA && kObj > hObj, 
         "Heap sensitivity cannot be more than context sensitivity")

  // flow-sensitive
  def updateSame( s: Stmt ) = 
    CFAxObj(kCFA, kObj, hCFA, hObj, s.id, trCFA, trObj)

  def updateSame( ρ:Env, σ: Store, self: BValue, args:BValue, s:Stmt ) = 
    CFAxObj(kCFA, kObj, hCFA, hObj, s.id, 
            (pp +: trCFA) take kCFA,
            ((SortedSet[Int]() ++ self.as.map(Trace.getBase(_))) +: trObj) take kObj)
    
  def toAddr = {
    val cfaa = IntsToBigInt(trCFA take hCFA, pp)
    val obja = SortedIntSetsToBigInt(trObj take hObj, pp)
    (cfaa << obja.bitLength) + obja
  }

  def makeAddr( x:Var ) = {
    val cfaa = IntsToBigInt(trCFA take hCFA, x.id)
    val obja = SortedIntSetsToBigInt(trObj take hObj, x.id)
    (cfaa << obja.bitLength) + obja
  }
}

object CFAxObj {
  def apply( kCFA:Int, kObj:Int, hCFA:Int, hObj:Int ): CFAxObj =
    CFAxObj(kCFA, kObj, hCFA, hObj, 0, Sequence[Int](), Sequence[SortedSet[Int]]())
}


//——————————————————————————————————————————————————————————————————————————————
// Smart combination of stack-based k-CFA and object sensitivity

case class CFAnObj(k: Int, h: Int, pp: Int, tr: Sequence[Int]) extends SameTrace[CFAnObj] {
  assert(k > h, "k should be greater than h")

  // flow-sensitive
  def updateSame( s: Stmt ) =
    CFAnObj(k, h, s.id, tr)

  // note: we used to return a set of traces that was the
  // cross-product of self addresses and tr, which is silly
  def updateSame( ρ:Env, σ: Store, self: BValue, args:BValue, s:Stmt ) =
    if ( self.as contains Init.window_Addr )
      CFAnObj(k, h, s.id, ((BigIntToSeqInt(self.as.head.loc) :+ pp).reverse take k).reverse)
    else
      CFAnObj(k, h, s.id, BigIntToSeqInt(self.as.head.loc))
    

  def toAddr =
    IntsToBigInt((tr.reverse take h).reverse, pp)

  def makeAddr( x:Var ) =
    IntsToBigInt((tr.reverse take h).reverse, x.id)
}

object CFAnObj {
  def apply( k:Int, h:Int ): CFAnObj =
    CFAnObj(k, h, 0, Sequence[Int]())
}