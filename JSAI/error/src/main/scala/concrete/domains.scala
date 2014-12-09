// This file contains the definitions of the notJS concrete semantics
// domains. See the notJS semantics document Section 2.1 for the
// specification. The State definition is in interpreter.scala since
// the state transition rules are implemented as a method of State.

package notjs.concrete.domains

import notjs.syntax._
import notjs.concrete.init._
import notjs.concrete.helpers.Fields._
import notjs.concrete.interpreter.State

//——————————————————————————————————————————————————————————————————————————————
// Term

// since the AST treats Decl as a Stmt we don't need a separate case
// for it here.
sealed abstract class Term
case class StmtT( s:Stmt ) extends Term
case class ValueT( v:Value ) extends Term

object Term {
  implicit def s2t( s:Stmt ): Term = StmtT(s)
  implicit def v2t( v:Value ): Term = ValueT(v)
}

//——————————————————————————————————————————————————————————————————————————————
// Environment

case class Env( env:Map[PVar, Address] = Map() ) {
  // retrieve a variable's address
  def apply( x:PVar ): Address =
    env(x)

  // add new bindings
  def ++( bind:List[(PVar, Address)] ): Env =
    Env( env ++ bind )

  // filter the map to contain only relevant entries. we explicitly
  // construct a new Map because otherwise filterKeys may return a
  // view of the original Map instead of a new Map
  def filter( f:PVar ⇒ Boolean ): Env =
    Env( (env filterKeys f) map (x ⇒ x) )
}

//——————————————————————————————————————————————————————————————————————————————
// Store

// we maintain separate maps from addresses to base values and
// addresses to objects
case class Store( a2v:Map[Address, BValue] = Map(), 
                  a2o:Map[Address, Object] = Map() ) {
  // retrieve a base value
  def apply( a:Address ): BValue =
    a2v(a)

  // retrieve an object
  def getObj( a:Address ): Object =
    a2o(a)

  // add/replace a base value
  def +( av:(Address,BValue) ): Store =
    Store( a2v + av, a2o )

  // add/replace a sequence of base values
  def ++( avs:List[(Address,BValue)] ): Store =
    Store( a2v ++ avs, a2o )

  // add/replace an object
  def putObj( a:Address, o:Object ): Store =
    Store( a2v, a2o + (a → o) )
} 

//——————————————————————————————————————————————————————————————————————————————
// Scratchpad memory

case class Scratchpad( mem:IndexedSeq[BValue] ) {
  def apply( x:Scratch ): BValue =
    mem(x.n)

  def update( x:Scratch, bv:BValue ): Scratchpad =
    Scratchpad( mem.updated(x.n, bv) )
}

object Scratchpad {
  def apply( len:Int ): Scratchpad =
    Scratchpad( IndexedSeq[BValue]().padTo(len, Undef) )
}

//——————————————————————————————————————————————————————————————————————————————
// Value: BValue, EValue, JValue

sealed abstract class Value

case class EValue( bv:BValue ) extends Value
case class JValue( lbl:String, bv:BValue ) extends Value

sealed abstract class BValue extends Value {
  // binary operators: type specific
  def +( bv:BValue ): BValue = sys.error("translator reneged")
  def −( bv:BValue ): BValue = sys.error("translator reneged")
  def ×( bv:BValue ): BValue = sys.error("translator reneged")
  def ÷( bv:BValue ): BValue = sys.error("translator reneged")
  def %( bv:BValue ): BValue = sys.error("translator reneged")
  def <<( bv:BValue ): BValue = sys.error("translator reneged")
  def >>( bv:BValue ): BValue = sys.error("translator reneged")
  def >>>( bv:BValue ): BValue = sys.error("translator reneged")
  def <( bv:BValue ): BValue = sys.error("translator reneged")
  def ≤( bv:BValue ): BValue = sys.error("translator reneged")
  def &( bv:BValue ): BValue = sys.error("translator reneged")
  def |( bv:BValue ): BValue = sys.error("translator reneged")
  def ⊻( bv:BValue ): BValue = sys.error("translator reneged")
  def and( bv:BValue ): BValue = sys.error("translator reneged")
  def or( bv:BValue ): BValue = sys.error("translator reneged")
  def ++( bv:BValue ): BValue = sys.error("translator reneged")
  def ≺( bv:BValue ): BValue = sys.error("translator reneged")
  def ≼( bv:BValue ): BValue = sys.error("translator reneged")

  // binary operators: all types
  def ≈( bv:BValue ): BValue = 
    (this ≡ bv) or ((this, bv) match {
      case (Null, Undef) | (Undef, Null) ⇒ Bool.True
      case (n:Num, str:Str) ⇒ n ≡ str.tonum
      case (str:Str, n:Num) ⇒ str.tonum ≡ n
      case _ ⇒ Bool.False
    })

  def ≡( bv:BValue ): BValue = Bool(this == bv)

  // unary operators: type specific
  def negate: BValue = sys.error("translator reneged")
  def bitwisenot: BValue = sys.error("translator reneged")
  def logicnot: BValue = sys.error("translator reneged")

  // unary operators: all types
  def isprim: BValue = Bool.True
  def tobool: BValue
  def tostr: Str
  def tonum: Num
}

//——————————————————————————————————————————————————————————————————————————————
// Num

case class Num( n:Double ) extends BValue {
  override def +( bv:BValue ) = bv match {
    case Num(n2) ⇒ Num(n + n2)
    case _ ⇒ sys.error("translator reneged")
  }

  override def −( bv:BValue ) = bv match {
    case Num(n2) ⇒ Num(n - n2)
    case _ ⇒ sys.error("translator reneged")
  }

  override def ×( bv:BValue ) = bv match {
    case Num(n2) ⇒ Num(n * n2)
    case _ ⇒ sys.error("translator reneged")
  }

  override def ÷( bv:BValue ) = bv match {
    case Num(n2) ⇒ Num(n / n2)
    case _ ⇒ sys.error("translator reneged")
  }

  override def %( bv:BValue ) = bv match {
    case Num(n2) ⇒ Num(n % n2)
    case _ ⇒ sys.error("translator reneged")
  }

  override def <<( bv:BValue ) = bv match {
    case Num(n2) ⇒ Num( (n.toInt << n2.toInt).toDouble )
    case _ ⇒ sys.error("translator reneged")
  }

  override def >>( bv:BValue ) = bv match {
    case Num(n2) ⇒ Num( (n.toInt >> n2.toInt).toDouble )
    case _ ⇒ sys.error("translator reneged")
  }

  override def >>>( bv:BValue ) = bv match {
    case Num(n2) ⇒ Num( (n.toInt >>> n2.toInt).toDouble )
    case _ ⇒ sys.error("translator reneged")
  }

  override def <( bv:BValue ) = bv match {
    case Num(n2) ⇒ Bool(n < n2)
    case _ ⇒ sys.error("translator reneged")
  }

  override def ≤( bv:BValue ) = bv match {
    case Num(n2) ⇒ Bool(n <= n2)
    case _ ⇒ sys.error("translator reneged")
  }

  override def &( bv:BValue ) = bv match {
    case Num(n2) ⇒ Num( (n.toInt & n2.toInt).toDouble )
    case _ ⇒ sys.error("translator reneged")
  }

  override def |( bv:BValue ) = bv match {
    case Num(n2) ⇒ Num( (n.toInt | n2.toInt).toDouble )
    case _ ⇒ sys.error("translator reneged")
  }

  override def ⊻( bv:BValue ) = bv match {
    case Num(n2) ⇒ Num( (n.toInt ^ n2.toInt).toDouble )
    case _ ⇒ sys.error("translator reneged")
  }

  override def negate = Num(-n)
  override def bitwisenot = Num( (~(n.toInt)).toDouble )

  def tobool = Bool( (n != 0) && !n.isNaN )
  def tostr = if (n.toLong == n) Str(n.toLong.toString) else Str(n.toString)
  def tonum = this

  override def toString = 
    this.tostr.str
}

object Num {
  // maximum u32 value
  val maxU32 = 4294967295L

  // is this value an unsigned 32-bit integer?
  def isU32( bv:BValue ): Boolean =
    bv match {
      case Num(n) ⇒ n.toLong == n && n >= 0 && n <= maxU32 
      case _ ⇒ false
    }
}

//——————————————————————————————————————————————————————————————————————————————
// Bool

case class Bool( b:Boolean ) extends BValue {
  override def and( bv:BValue ) =
    if (!b) this else bv

  override def or( bv:BValue ) =
    if (b) this else bv

  override def logicnot = Bool(!b)

  def tobool = this
  def tostr = Str(b.toString)
  def tonum = if (b) Num(1) else Num(0)

  override def toString = 
    b.toString
}

object Bool {
  val True = Bool(true)
  val False = Bool(false)
}

//——————————————————————————————————————————————————————————————————————————————
// Str

case class Str( str:String ) extends BValue {
  override def ++( bv:BValue ) : Str = bv match {
    case Str(str2) ⇒ Str(str + str2)
    case _ ⇒ sys.error("translator reneged")
  }

  override def ≺( bv:BValue ) = bv match {
    case Str(str2) ⇒ Bool(str < str2)
    case _ ⇒ sys.error("translator reneged")
  }

  override def ≼( bv:BValue ) = bv match {
    case Str(str2) ⇒ Bool(str <= str2)
    case _ ⇒ sys.error("translator reneged")
  }

  def tobool = Bool(str != "")
  def tostr = this
  def tonum = try { Num(str.toDouble) } catch { case e: java.lang.NumberFormatException ⇒ Num(Double.NaN) }

  override def toString = str
}

//——————————————————————————————————————————————————————————————————————————————
// Address

case class Address( a:Int ) extends BValue {
  override def isprim = Bool.False

  def tobool = Bool(true)
  def tostr = sys.error("translator reneged")
  def tonum = sys.error("translator reneged")
}

object Address {
  // helper to provide fresh addresses
  var genAddr = 0
  def apply(): Address = { genAddr += 1; Address( genAddr ) }
}

//——————————————————————————————————————————————————————————————————————————————
// Null and Undef

case object Null extends BValue {
  def tobool = Bool.False
  def tostr = Str( "null" )
  def tonum = Num(0)
  override def toString = "null"
}

case object Undef extends BValue {
  def tobool = Bool.False
  def tostr = Str( "undefined" )
  def tonum = Num(Double.NaN)
  override def toString = "undefined"
}

//——————————————————————————————————————————————————————————————————————————————
// Closure. We use both regular closures and native Scala methods.

sealed abstract class Closure
case class Clo( ρ:Env, m:Method ) extends Closure
case class Native( f:(Address, Address, Var, Env, Store, Scratchpad, KStack) ⇒ State ) extends Closure

//——————————————————————————————————————————————————————————————————————————————
// Object

// the intern map has Any as its co-domain because it needs to store
// BValues, Closures, and JSClasses
case class Object( extern:Map[Str, BValue], intern:Map[Str, Any] ) {
  // store this object's JS class and prototype for easy reference
  val myClass = intern(classname).asInstanceOf[JSClass]
  val myProto = intern(proto).asInstanceOf[BValue]

  // retrieve a field's value. this is _not_ the complete field lookup
  // semantics, which includes looking up the prototype chain; here we
  // only look inside this object's extern map
  def apply( str:Str ): Option[BValue] =
    extern get str

  // update a field of the object. depending on the object's class
  // some fields are non-updateable; we check for that here
  def upd( str:Str, bv:BValue ): Object =
    if ( Init.noupdate(myClass) contains str ) this
    else Object( extern + (str → bv), intern )

  // try to remove the given field from the object; return false if
  // the field wasn't present or it's non-deletable, otherwise return
  // true.
  def −( str:Str ): (Object, Boolean) =
    if ( (Init.nodelete(myClass) contains str) || !(extern contains str) )
      (this, false)
    else
	(Object(extern - str, intern), true)

  // enumerate the fields of the object. skip non-enumerable fields
  def fields: Set[Str] =
    extern.keySet -- Init.noenum(myClass)

  // get this object's internal class
  def getJSClass: JSClass =
    myClass

  // get this object's internal prototype
  def getProto: BValue =
    myProto

  def calledAsCtor: Boolean = 
    // the value of constructor doesn't matter, just whether it is
    // present or not
    intern.contains(constructor) 
    
  // if this object is a Function class return the closure, else None
  def getCode: Option[Closure] =
    intern get code match {
      case Some(any) ⇒ Some(any.asInstanceOf[Closure])
      case _ ⇒ None
    }

  def getValue: Option[BValue] = {
    intern get value match {
      case Some(any) ⇒ Some(any.asInstanceOf[BValue])
      case _ ⇒ None
    }
  }
}

//——————————————————————————————————————————————————————————————————————————————
// Kont

// we'll implement the continuation stack as an actual stack, so these
// definitions don't include the Kont parameters that are in the
// semantics definitions (which only serve to simulate a stack) note:
// retk contains a boolean isctor that tells whether we are returning
// from a constructor or a normal method call, and a scratchpad memory
// ß to preserve the scratchpad across calls.
sealed abstract class Kont
case object HaltK extends Kont
case class SeqK( ss:List[Stmt] ) extends Kont
case class WhileK( e:Exp, s:Stmt ) extends Kont
case class ForK( strs:List[Str], x:Var, s:Stmt ) extends Kont
case class RetK( x:Var, ρ:Env, isctor:Boolean, ß:Scratchpad ) extends Kont
case class TryK( x:PVar, sc:Stmt, sf:Stmt ) extends Kont
case class CatchK( sf:Stmt ) extends Kont
case class FinK( v:Value ) extends Kont
case class LblK( lbl:String ) extends Kont

// continuation stack
case class KStack( κs:List[Kont] ) {
  def push( κ:Kont ): KStack =
    KStack( κ :: κs )

  def pop: KStack =
    KStack( κs.tail )

  // replace the top of the stack (i.e., pop then push)
  def repl( κ:Kont ): KStack =
    KStack( κ :: κs.tail )

  def top: Kont =
    κs.head

  def dropWhile( f:Kont ⇒ Boolean ): KStack =
    KStack( κs dropWhile f )
}
