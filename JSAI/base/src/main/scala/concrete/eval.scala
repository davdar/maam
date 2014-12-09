// This file contains the definitions of the concrete expression
// evaluation functions. See the notJS semantics document Section 2.2
// for the specifications.

package notjs.concrete.eval

import notjs.syntax._
import notjs.concrete.domains._
import notjs.concrete.helpers.Helpers._

//——————————————————————————————————————————————————————————————————————————————
// Expression evaluation

object Eval {
  def eval( e:Exp, ρ:Env, σ:Store, ß:Scratchpad ): BValue = {
    def innerEval( e:Exp ): BValue =
      e match {
      	case NumAST(d) ⇒ 
      	  Num(d)
      	
      	case BoolAST(b) ⇒ 
      	  Bool(b)
      	
      	case StrAST(str) ⇒ 
      	  Str(str)

      	case UndefAST() ⇒ 
      	  Undef

      	case NullAST() ⇒ 
      	  Null

      	case x:PVar ⇒ 
      	  σ(ρ(x))

      	case x:Scratch ⇒ 
      	  ß(x)

      	case Binop(op, e1, e2) ⇒ 
      	  val (bv1, bv2) = (innerEval(e1), innerEval(e2))
      	  op match { 
      	    case ⌜+⌝ ⇒ bv1 + bv2
      	    case ⌜−⌝ ⇒ bv1 − bv2
      	    case ⌜×⌝ ⇒ bv1 × bv2
      	    case ⌜÷⌝ ⇒ bv1 ÷ bv2
      	    case ⌜%⌝ ⇒ bv1 % bv2
      	    case ⌜<<⌝ ⇒ bv1 << bv2
      	    case ⌜>>⌝ ⇒ bv1 >> bv2
      	    case ⌜>>>⌝ ⇒ bv1 >>> bv2
      	    case ⌜<⌝ ⇒ bv1 < bv2
      	    case ⌜≤⌝ ⇒ bv1 ≤ bv2
      	    case ⌜&⌝ ⇒ bv1 & bv2
      	    case ⌜|⌝ ⇒ bv1 | bv2
      	    case ⌜⊻⌝ ⇒ bv1 ⊻ bv2
      	    case ⌜&&⌝ ⇒ bv1 and bv2
      	    case ⌜||⌝ ⇒ bv1 or bv2
      	    case ⌜++⌝ ⇒ bv1 ++ bv2
      	    case ⌜≺⌝ ⇒ bv1 ≺ bv2
      	    case ⌜≼⌝ ⇒ bv1 ≼ bv2
      	    case ⌜≈⌝ ⇒ bv1 ≈ bv2
      	    case ⌜≡⌝ ⇒ bv1 ≡ bv2
      	    case ⌜⋆⌝ ⇒ (bv1, bv2) match {
      	      case (a:Address, str:Str) ⇒ lookup( σ getObj a, str, σ )
      	      case _ ⇒ 
            		sys.error("translator reneged: "+bv1.toString+"⋆"+bv2.toString)
      	    }
      	    case InstanceOf ⇒ (bv1, bv2) match {
      	      case (a1:Address, a2:Address) ⇒ instance(a1, a2)
      	      case _ ⇒ Bool.False
      	    }
      	    case In ⇒ (bv1, bv2) match {
      	      case (str:Str, a:Address) ⇒ find(str, a)
      	      case _ ⇒ sys.error("translator reneged")
      	    }
      	  }

      	case Unop(op, e) ⇒ 
      	  val bv = innerEval(e)
      	  op match { 
      	    case ⌞−⌟ ⇒ bv negate
      	    case ⌞~⌟ ⇒ bv bitwisenot
      	    case ⌞¬⌟ ⇒ bv logicnot
      	    case Typeof ⇒ bv match {
      	      case _:Num ⇒ Str("number")
      	      case _:Bool ⇒ Str("boolean")
      	      case _:Str ⇒ Str("string")
      	      case Null ⇒ Str("object")
      	      case Undef ⇒ Str("undefined")
      	      case a:Address ⇒ (σ getObj a).getCode match {
      		case Some(_) ⇒ Str("function")
      		case None ⇒ Str("object")
      	      }
      	    }
      	    case ToBool ⇒ bv tobool
      	    case IsPrim ⇒ bv isprim
      	    case ToStr ⇒ bv tostr
      	    case ToNum ⇒ bv tonum
      	  }
      }

    // for InstanceOf
    def instance(a1:Address, a2:Address): Bool =
      (σ getObj a1).getProto match {
      	case a:Address ⇒ if (a == a2) Bool.True else instance(a, a2)
      	case Null ⇒ Bool.False
      	case _ ⇒ sys.error("undefined")
      }

    // for In
    def find(str:Str, a:Address): Bool = {
      val o = σ getObj a
      o(str) match {
      	case Some(_) ⇒ Bool.True
      	case None ⇒ o.getProto match {
      	  case a:Address ⇒ find(str, a)
      	  case _ ⇒ Bool.False
      	}
      }
    }

    innerEval(e)
  }
}
