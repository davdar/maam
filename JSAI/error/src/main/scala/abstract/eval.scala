// This file contains the definitions of the abstract expression
// evaluation functions. See the notJS semantics document Section 3.3
// for the specifications.

package notjs.abstracted.eval

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.helpers.Helpers._

//——————————————————————————————————————————————————————————————————————————————
// Expression evaluation

object Eval {
  def eval( e:Exp, ρ:Env, σ:Store, ß:Scratchpad ): BValue = {
    def innerEval( e:Exp ): BValue =
      e match {
        case NumAST(d) ⇒ 
          Num.inject(Num.α(d))

        case BoolAST(b) ⇒ 
          if (b) Bool.TrueBV else Bool.FalseBV

        case StrAST(str) ⇒ 
          Str.inject(Str.α(str))

        case UndefAST() ⇒ 
          Undef.BV

        case NullAST() ⇒ 
          Null.BV

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
            case ⌜≈⌝ ⇒ ≈(bv1, bv2)
            case ⌜≡⌝ ⇒ ≡(bv1, bv2)
            case ⌜⋆⌝ ⇒ lookup( bv1.as, bv2.str, σ )
            case InstanceOf ⇒ 
              if (bv1.isBot || bv2.isBot) BValue.⊥ 
              else Bool.inject(
                (if (!bv1.defAddr) Bool.False else Bool.⊥) ⊔ 
                instance( bv1.as, bv2.as ))
            case In ⇒ 
              Bool.inject( 
                bv2.as.foldLeft[Bool]( Bool.⊥ )(
                  (acc, a) ⇒ 
                    if ( acc == Bool.⊤ ) Bool.⊤
                    else acc ⊔ find( σ getObj(a, bv1.str), bv1.str ) 
                ))
	       }

        case Unop(op, e) ⇒ 
          val bv = innerEval(e)
          op match { 
            case ⌞−⌟ ⇒ bv negate
            case ⌞~⌟ ⇒ bv bitwisenot
            case ⌞¬⌟ ⇒ bv logicnot
            case Typeof ⇒ Str.inject(typeof(bv))
            case ToBool ⇒ bv tobool
            case IsPrim ⇒ bv isprim
            case ToStr ⇒ bv tostr
            case ToNum ⇒ bv tonum
          }
      }

    // for InstanceOf operator
    def instance(as1:Addresses, as2:Addresses, seen: Addresses = Addresses()): Bool = {
      val as1Unseen = as1 -- seen
      if ( as1Unseen.isEmpty || as2.isEmpty ) 
        Bool.⊥ 
      else {
        val bv = as1Unseen.foldLeft( BValue.⊥ )( 
          (acc, a) ⇒ acc ⊔ (σ getObj(a, Str.⊥)).getProto )
        val protos = bv.as
        val isnull = (bv.nil == Null.⊤)

      	if ( !isnull && protos.size == 1 && protos == as2 &&
      	     σ.isStrong(protos.head) )
      	  Bool.True
      	else if ( isnull && protos.isEmpty )
      	  Bool.False
      	else {
      	  val overlap = (protos & as2).nonEmpty

      	  if ( isnull && overlap )
      	    Bool.⊤
      	  else if ( !isnull && overlap )
      	    Bool.True ⊔ instance(protos, as2, seen ++ as1Unseen)
      	  else if ( isnull && protos.nonEmpty )
      	    Bool.False ⊔ instance(protos, as2, seen ++ as1Unseen)
      	  else {
      	    // it should be that there is no Null, there are proto
      	    // addresses, and there is no overlap
      	    assert( !isnull && protos.nonEmpty && !overlap )
      	    instance(protos, as2, seen ++ as1Unseen)
          }
        }
      }
    }

    // for In operator
    def find(o:Object, str:Str): Bool =
      if ( o.defField(str) ) 
        Bool.True
      else {
        val bv = o.getProto
      	val notField = o.defNotField(str)
        val maybeField = !notField

        if ( notField && bv.as.isEmpty )
          Bool.False
        else if ( maybeField && bv.nil == Null.⊤ )
          Bool.⊤
        else {
          val proto = bv.as.foldLeft[Bool]( Bool.⊥ )( 
            (acc, a) ⇒
              if ( acc == Bool.⊤ ) Bool.⊤
              else acc ⊔ find(σ getObj(a, str), str) )

          if ( maybeField && bv.nil == Null.⊥ )
            Bool.True ⊔ proto
          else if ( notField && bv.as.nonEmpty && bv.nil == Null.⊤ )
            Bool.False ⊔ proto
          else
            proto
        }
      }

    // for Typeof operator
    def typeof(bv:BValue): Str =
      bv.sorts.foldLeft[Str]( Str.⊥ )(
        (acc, dom) ⇒ dom match {
          case DNum ⇒ acc ⊔ Str.α("number")
          case DBool ⇒ acc ⊔ Str.α("boolean")
          case DStr ⇒ acc ⊔ Str.α("string")
          case DNull ⇒ acc ⊔ Str.α("object")
          case DUndef ⇒ acc ⊔ Str.α("undefined")
          case _ ⇒
            val otype = 
              if (bv.as.exists ( (a) ⇒ (σ getObj (a, Str.⊥)).getCode.isEmpty ))
        	Str.α("object") 
              else Str.⊥ 

            val ftype = 
              if (bv.as.exists ( (a) ⇒ (σ getObj (a, Str.⊥)).getCode.nonEmpty ))
        	Str.α("function") 
              else Str.⊥ 

            acc ⊔ otype ⊔ ftype
        })

    // for ⌜≡⌝ operator; we can't put this into BValue because it
    // needs the store to determine if an address is strong or weak
    def ≡( bv1:BValue, bv2:BValue ): BValue = 
      if ( bv1.isBot || bv2.isBot )
        BValue.⊥
      else {
        val bothdom = bv1.sorts & bv2.sorts
        if ( bothdom.isEmpty )
          Bool.FalseBV
        else {
          val diff = 
            if ( bv1.sorts.size == 1 && bv1.sorts == bv2.sorts ) Bool.⊥
            else Bool.False
          
          Bool.inject( bothdom.foldLeft[Bool]( diff )(
            (acc, dom) ⇒ 
              if ( acc == Bool.⊤ ) Bool.⊤
              else acc ⊔ (dom match {
              	case DNum ⇒ bv1.n ≡ bv2.n
              	case DBool ⇒ bv1.b ≡ bv2.b
              	case DStr ⇒ bv1.str ≡ bv2.str
              	case DAddr ⇒
              	  if ( (bv1.as & bv2.as).isEmpty ) Bool.False
              	  else if ( bv1.as.size == 1 && 
              		    bv1.as == bv2.as && 
              		    σ.isStrong(bv1.as.head) ) Bool.True
              	  else Bool.⊤
              	case DNull ⇒ Bool.True
              	case DUndef ⇒ Bool.True
            })))
        }
      }

    // for ⌜≈⌝ operator; we can't put this into BValue because it uses ≡
    def ≈( bv1:BValue, bv2:BValue ): BValue = {
      val equiv = ≡(bv1, bv2)
      equiv.b match {
        case Bool.False ⇒ {
          val case12 =
            if ((bv1.nil == Null.⊤ && bv2.undef == Undef.⊤) ||
        	(bv1.undef == Undef.⊤ && bv2.nil == Null.⊤))
              Bool.TrueBV
            else BValue.⊥
          
          val case3 =
            if (bv1.n != Num.⊥ && bv2.str != Str.⊥)
              ≡(Num.inject(bv1.n), Str.inject(bv2.str).tonum)
            else BValue.⊥

          val case4 =
            if (bv1.str != Str.⊥ && bv2.n != Num.⊥)
              ≡(Str.inject(bv1.str).tonum, Num.inject(bv2.n))
            else BValue.⊥
          
          equiv ⊔ case12 ⊔ case3 ⊔ case4
        }
        case _ ⇒ equiv
      }
    }

    innerEval(e)
  }
}
