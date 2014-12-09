// This file contains the definitions of the concrete helper
// functions. See the notJS semantics document Section 2.4 for the
// specifications.

package notjs.concrete.helpers

import notjs.syntax._
import notjs.concrete.init.Init._
import notjs.concrete.domains._
import notjs.concrete.interpreter.State

//——————————————————————————————————————————————————————————————————————————————
// handy definitions

// exceptions that can be thrown implicitly
object Errors {
  val typeError = EValue(Str("TypeError"))
  val rangeError = EValue(Str("RangeError"))
}

// builtin object fields
object Fields {
  val proto = Str("proto")
  val classname = Str("class")
  val code = Str("code")
  val prototype = Str("prototype")
  val length = Str("length")
  val value = Str("value")
  val message = Str("message")
  val constructor = Str("constructor")
}

import Errors._
import Fields._

//——————————————————————————————————————————————————————————————————————————————
// helper functions

object Helpers {

  def alloc( σ:Store, bvs:List[BValue] ): (Store, List[Address]) = {
    val as = bvs map ( _ ⇒ Address() )
    val σ1 = σ ++ (as zip bvs)
    (σ1, as)
  }


  def allocFun(clo:Closure, n:BValue, σ:Store): (Store, Address) = {
    val a1 = Address()
    val intern = Map(
      proto → Function_prototype_Addr,
      classname → CFunction,
      code → clo
    )
    val extern = Map( length → n )
    (σ putObj(a1, Object(extern, intern)), a1)
  }


  def allocObj(a:Address, σ:Store): (Store, Address) = {
    val c = classFromAddress(a)
    val a1 = Address()
    val a2 =
      (σ getObj a)(prototype) match {
        case Some(a3:Address) ⇒ a3
        case _ ⇒ Object_prototype_Addr
      }
    val intern = Map( proto → a2, classname → c )
    val σ1 = σ putObj(a1, Object(Map(), intern))
    (σ1, a1)
  }


  // for some of the builtin methods we use native Scala closures
  // instead of notJS closures, so this isn't exactly like in the
  // semantics document. we also don't directly use the 'callable'
  // helper, instead we just check whether there is a closure
  def applyClo( bv1:BValue, bv2:BValue, bv3:BValue, x:Var, ρ:Env, σ:Store, ß:Scratchpad, κs:KStack ): State =
    (bv1, bv2, bv3) match {
      case (a1:Address, a2:Address, a3:Address) ⇒
        val o = σ getObj a1
        val isCtor = (σ getObj a3) calledAsCtor

        o.getCode match {
          case Some( Clo(ρc, Method(self, args, s)) ) ⇒
            val (σ1, as) = alloc( σ, List(a2, a3) )
            val ρc1 = ρc ++ (List(self, args) zip as)
            State(s, ρc1, σ1, Scratchpad(0), κs push RetK(x, ρ, isCtor, ß))

          case Some( Native(f) ) ⇒
            f( a2, a3, x, ρ, σ, ß, κs )

          case _ ⇒ 
            State(typeError, ρ, σ, ß, κs)
        }

      case _ ⇒ 
        State(typeError, ρ, σ, ß, κs)
    }


  def delete(bv1:BValue, bv2:BValue, x:Scratch, ρ:Env, σ:Store, ß:Scratchpad): (Value, Store, Scratchpad) = 
    (bv1, bv2) match {
      case (Null, _) | (Undef, _) ⇒ 
        (typeError, σ, ß)

      case (a:Address, str:Str) ⇒
      	val (o1, del) = (σ getObj a) − str
      	if ( del ) (Undef, σ.putObj(a, o1), ß(x) = Bool.True)
      	else (Undef, σ, ß(x) = Bool.False)

      case _ ⇒ 
      	(Undef, σ, ß(x) = Bool.True)
    }


  // NOTE: getProto and getJSClass are implemented in the Object class
  // NOTE: initState is contained in init.scala


  def lookup( o:Object, str:Str, σ:Store ): BValue = {
    def innerLookup( o:Object ): BValue =
      o(str) match {
      	case Some(bv) ⇒ bv
      	case None ⇒ o.getProto match {
      	  case a:Address ⇒ innerLookup( σ.getObj(a) )
      	  case _ ⇒ Undef
      	}
      }

    innerLookup( o )
  }


  // NOTE: there is no nextK; that functionality is implemented
  // directly in the transition rules in interpreter.scala


  // retrieve all keys accessible via this object, including ones in
  // the prototype chain.
  def objAllKeys( bv:BValue, σ:Store ): List[Str] = {
    def recur( a:Address ): Set[Str] = {
      val o = σ getObj a
      val flds = o.fields
      val pflds = o.intern(proto) match {
      	case a1:Address ⇒ recur(a1)
      	case _ ⇒ Set[Str]()
      }
      flds ++ pflds
    }

    bv match {
      case a:Address ⇒ recur(a).toList
      case _ ⇒ List()
    }    
  }
    

  def setConstr( σ:Store, a:Address ): Store = {
    val o = σ getObj a
    σ putObj( a, Object(o.extern, o.intern + (constructor → true)) )
  }


  // NOTE: there is no specialK; that functionality is implemented
  // directly in the transition rules in interpreter.scala


  def toObj( bv:BValue, x:Var, ρ:Env, σ:Store, ß:Scratchpad ): (Value, Store, Scratchpad) = 
    bv match {
      case Null | Undef ⇒
        (typeError, σ, ß)

      case a:Address ⇒
        x match {
          case pv:PVar ⇒
            (bv, σ + (ρ(pv) → bv), ß)

          case sc:Scratch ⇒
            (bv, σ, ß(sc) = bv)
        }

      case _ ⇒
      	val a = bv match {
      	  case _:Num ⇒ Number_Addr
      	  case _:Bool ⇒ Boolean_Addr
      	  case _:Str ⇒ String_Addr
      	  case _ ⇒ sys.error("can't happen")
      	}
        val (σ1, a1) = allocObj(a, σ)
        val o = σ1 getObj a1
        // if the value is a string, update external length field
        // and 0 to length-1 fields
        val updatedO = bv match {
          case s: Str ⇒ Object(o.extern ++ 
            List.range(0, s.str.length).foldLeft(Map[Str, BValue](length → Num(s.str.length)))(
              (acc, e) ⇒ acc + (Str(e.toString) → Str(s.str(e).toString))), o.intern)
          case _ ⇒ o
        }
        val σ2 = σ1 putObj(a1, Object(updatedO.extern, updatedO.intern + (value → bv)))

        x match {
          case pv:PVar ⇒
            (a1, σ2 + (ρ(pv) → a1), ß)

          case sc:Scratch ⇒
            (a1, σ2, ß(sc) = a1)
        }
    }


  def updateObj(bv1:BValue, bv2:BValue, bv3:BValue, σ:Store): (Value, Store) = {
    (bv1, bv2) match {
      case (a:Address, str:Str) ⇒
        val o = σ getObj a
        val o1 = o.upd(str, bv3)
        if ( o1.getJSClass == CArray ) {
          val (bv2num, bv3num) = (bv2.tonum, bv3 match {
            case _:Address ⇒ bv3
            case _ ⇒ bv3.tonum
            })
          if ( str == length && !Num.isU32(bv3num) )
            (rangeError, σ)
          else if ( str == length ) {
            if ( (o(length).get ≤ bv3num) == Bool.True ) 
              (bv3, σ.putObj(a, o.upd(str, bv3num)))
            else {
              val (n1, n2) = (bv3num, o(length).get) match {
                  case (Num(_n1), Num(_n2)) ⇒ (_n1.toLong, _n2.toLong)
                case _ ⇒ sys.error("inconceivable")
              }

              val o2 = (n1 until n2).toList.foldLeft( o.upd(str, bv3num) )(
                (acc, n) ⇒ (acc − Str(n.toString))._1 )
              (bv3, σ.putObj(a, o2))
            }
          }
          else if ( Num.isU32(bv2num) ) {
            if ( (bv2num < o(length).get) == Bool.True || bv2num == Num(Num.maxU32) )
              (bv3, σ.putObj(a, o1))
            else {
              val o2 = o1.upd(length, bv2num + Num(1))
              (bv3, σ.putObj(a, o2))
            }
          }
          else 
            (bv3, σ.putObj(a, o1))
        }
        else 
          (bv3, σ.putObj(a, o1))

      case _ ⇒ 
        (typeError, σ)
    }
  }
}
