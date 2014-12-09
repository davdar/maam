package notjs.translator

import notjs.syntax.{Seq => SyntaxSeq, _}

object ConstantFolding {
  // using the concrete interpreter domains in order to prevent duplication
  // and ensure that this will do the exact same thing the concrete interpreter
  // would do
  import notjs.concrete.domains._

  def toAST(bv: BValue): Exp =
    bv match {
      case Num(n) => NumAST(n)
      case Bool(b) => BoolAST(b)
      case Str(s) => StrAST(s)
      case Undef => UndefAST()
      case Null => NullAST()
      case _ => sys.error("Passed a value that cannot be converted into an AST")
    }

  def toConcreteVal(e: Exp): Option[BValue] =
    e match {
      case NumAST(n) => Some(Num(n))
      case BoolAST(b) => Some(Bool(b))
      case StrAST(s) => Some(Str(s))
      case UndefAST() => Some(Undef)
      case NullAST() => Some(Null)
      case _ => None
    }

  // returns a version of the given expression,
  // simplified as much as possible
  def foldConstants(e: Exp, varTransform: Var => Exp): Exp = {
    def fold(e: Exp): Exp =
      foldConstants(e, varTransform)

    e match {
      case n: NumAST => n
      case b: BoolAST => b
      case s: StrAST => s
      case u: UndefAST => u
      case n: NullAST => n
      case v: Var => varTransform(v)

      case Binop(op, e1, e2) => {
        val e1Final = fold(e1)
        val e2Final = fold(e2)

        val result = 
          for {
            bv1 <- toConcreteVal(e1Final)
            bv2 <- toConcreteVal(e2Final)
            finalVal <- op match {
      	      case ⌜+⌝ ⇒ Some(bv1 + bv2)
      	      case ⌜−⌝ ⇒ Some(bv1 − bv2)
      	      case ⌜×⌝ ⇒ Some(bv1 × bv2)
      	      case ⌜÷⌝ ⇒ Some(bv1 ÷ bv2)
      	      case ⌜%⌝ ⇒ Some(bv1 % bv2)
      	      case ⌜<<⌝ ⇒ Some(bv1 << bv2)
      	      case ⌜>>⌝ ⇒ Some(bv1 >> bv2)
      	      case ⌜>>>⌝ ⇒ Some(bv1 >>> bv2)
      	      case ⌜<⌝ ⇒ Some(bv1 < bv2)
      	      case ⌜≤⌝ ⇒ Some(bv1 ≤ bv2)
      	      case ⌜&⌝ ⇒ Some(bv1 & bv2)
      	      case ⌜|⌝ ⇒ Some(bv1 | bv2)
      	      case ⌜⊻⌝ ⇒ Some(bv1 ⊻ bv2)
      	      case ⌜&&⌝ ⇒ Some(bv1 and bv2)
      	      case ⌜||⌝ ⇒ Some(bv1 or bv2)
      	      case ⌜++⌝ ⇒ Some(bv1 ++ bv2)
      	      case ⌜≺⌝ ⇒ Some(bv1 ≺ bv2)
      	      case ⌜≼⌝ ⇒ Some(bv1 ≼ bv2)
      	      case ⌜≈⌝ ⇒ Some(bv1 ≈ bv2)
      	      case ⌜≡⌝ ⇒ Some(bv1 ≡ bv2)
              case _ ⇒ None
            }
          } yield toAST(finalVal)

        result.getOrElse(Binop(op, e1Final, e2Final))
      } // case Binop

      case Unop(op, e) => {
        val eFinal = fold(e)

        val result =
          for {
            bv <- toConcreteVal(eFinal)
            finalVal <- op match {
              case ⌞−⌟ ⇒ Some(bv negate)
      	      case ⌞~⌟ ⇒ Some(bv bitwisenot)
      	      case ⌞¬⌟ ⇒ Some(bv logicnot)
      	      case Typeof ⇒ 
                bv match {
      	          case _:Num ⇒ Some(Str("number"))
      	          case _:Bool ⇒ Some(Str("boolean"))
      	          case _:Str ⇒ Some(Str("string"))
      	          case Null ⇒ Some(Str("object"))
      	          case Undef ⇒ Some(Str("undefined"))
                  case _ => None
                }
      	      case ToBool ⇒ Some(bv tobool)
      	      case IsPrim ⇒ Some(bv isprim)
      	      case ToStr ⇒ Some(bv tostr)
      	      case ToNum ⇒ Some(bv tonum)
            }
          } yield toAST(finalVal)
        
        result.getOrElse(Unop(op, eFinal))
      }
    } // e match
  } // foldConstants

  def foldConstants(e: Exp): Exp =
    foldConstants(e, (v: Var) => v)

  def apply(e: Exp): Exp =
    foldConstants(e)
} // ConstantFolding
