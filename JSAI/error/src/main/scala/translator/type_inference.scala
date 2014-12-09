package notjs.translator

import notjs.syntax.{Seq => SyntaxSeq, _}

sealed trait JSType {
  def ⊔(τ: JSType): JSType
  def isPrim(): Option[Boolean]
}

case object Top extends JSType {
  def ⊔(τ: JSType): JSType = Top
  def isPrim(): Option[Boolean] = None
}

case object AddrT extends JSType {
  def isPrim(): Option[Boolean] = Some(false)

  def ⊔(τ: JSType): JSType =
    τ match {
      case AddrT => AddrT
      case _ => Top
    }
}

sealed trait Prim extends JSType {
  def isPrim(): Option[Boolean] = Some(true)
}

case object OnlyPrim extends Prim {
  def ⊔(τ: JSType): JSType =
    τ match {
      case _: Prim => OnlyPrim
      case _ => Top
    }
}

case object NumT extends Prim {
  def ⊔(τ: JSType): JSType =
    τ match {
      case NumT => NumT
      case _: Prim => OnlyPrim
      case _ => Top
    }
}

case object BoolT extends Prim {
  def ⊔(τ: JSType): JSType =
    τ match {
      case BoolT => BoolT
      case _: Prim => OnlyPrim
      case _ => Top
    }
}

case object StrT extends Prim {
  def ⊔(τ: JSType): JSType =
    τ match {
      case StrT => StrT
      case _: Prim => OnlyPrim
      case _ => Top
    }
}

case object NullT extends Prim {
  def ⊔(τ: JSType): JSType =
    τ match {
      case NullT => NullT
      case _: Prim => OnlyPrim
      case _ => Top
    }
}

case object UndefT extends Prim {
  def ⊔(τ: JSType): JSType = 
    τ match {
      case UndefT => UndefT
      case _: Prim => OnlyPrim
      case _ => Top
    }
}

object TypeInferencer {
  // Gets the type of a given expression.  Assumes that the given notJS expressions don't
  // have type errors in them, which should be guarenteed by the translator.
  def typeof(e: Exp, typeofVar: Var => JSType): JSType =
    e match {
      case NumAST(_) => NumT
      case BoolAST(_) => BoolT
      case StrAST(_) => StrT
      case UndefAST() => UndefT
      case NullAST() => NullT
      case v: Var => typeofVar(v)

      case Binop(op, _, _) =>
        op match {
          case ⌜+⌝ | ⌜−⌝ | ⌜×⌝ | ⌜÷⌝ | ⌜%⌝ | ⌜<<⌝ | ⌜>>⌝ | ⌜>>>⌝ | ⌜&⌝ | ⌜|⌝ | ⌜⊻⌝ =>
            NumT
          case ⌜++⌝ =>
            StrT
          case ⌜<⌝ | ⌜≤⌝ | ⌜&&⌝ | ⌜||⌝ | ⌜≺⌝ | ⌜≼⌝ | InstanceOf | In | ⌜≈⌝ | ⌜≡⌝ =>
            BoolT
          case ⌜⋆⌝ =>
            Top
        }
      
      case Unop(op, _) => 
        op match {
          case ⌞−⌟ | ⌞~⌟ | ToNum => NumT
          case ⌞¬⌟ | ToBool | IsPrim => BoolT
          case Typeof | ToStr => StrT
        }
    }

  // if a variable is encountered, it simply returns Top for the variable
  def typeof(e: Exp): JSType =
    typeof(e, (_: Var) => Top)

  def apply(e: Exp): JSType =
    typeof(e)
}
