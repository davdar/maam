// notJS initial state: Math

package notjs.concrete.init

import notjs.syntax._
import notjs.concrete.domains._
import notjs.concrete.interpreter.State
import notjs.concrete.helpers.Fields
import notjs.concrete.helpers.Errors._
import notjs.concrete.helpers.Helpers._

import notjs.concrete.init.Init._
import notjs.concrete.init.InitHelpers._


object InitMath {


  val Math_Obj = createObj(Map(
    Str("E")       → Num(2.7182818284590452354),
    Str("LN10")    → Num(2.302585092994046),
    Str("LN2")     → Num(0.6931471805599453),
    Str("LOG2E")   → Num(1.4426950408889634),
    Str("LOG10E")  → Num(0.4342944819032518),
    Str("PI")      → Num(3.1415926535897932),
    Str("SQRT1_2") → Num(0.7071067811865476),
    Str("SQRT2")   → Num(1.4142135623730951),
    Str("abs")     → Math_abs_Addr,
    Str("acos")    → Math_acos_Addr,
    Str("asin")    → Math_asin_Addr,
    Str("atan")    → Math_atan_Addr,
    Str("atan2")   → Math_atan2_Addr,
    Str("ceil")    → Math_ceil_Addr,
    Str("cos")     → Math_cos_Addr,
    Str("exp")     → Math_exp_Addr,
    Str("floor")   → Math_floor_Addr,
    Str("log")     → Math_log_Addr,
    Str("max")     → Math_max_Addr,
    Str("min")     → Math_min_Addr,
    Str("pow")     → Math_pow_Addr,
    Str("random")  → Math_random_Addr,
    Str("round")   → Math_round_Addr,
    Str("sin")     → Math_sin_Addr,
    Str("sqrt")    → Math_sqrt_Addr,
    Str("tan")     → Math_tan_Addr
  ), internal = Map(Fields.classname → CMath_Obj))

  val Math_abs_Obj = makeMath(math.abs)

  val Math_acos_Obj = makeMath(math.acos)

  val Math_asin_Obj = makeMath(math.asin)

  val Math_atan_Obj = makeMath(math.atan)

  val Math_atan2_Obj = approx_num

  val Math_ceil_Obj = makeMath(math.ceil)

  val Math_cos_Obj = makeMath(math.cos)

  val Math_exp_Obj = makeMath(math.exp)

  val Math_floor_Obj = makeMath(math.floor)

  val Math_log_Obj = makeMath(math.log)

  val Math_max_Obj = approx_num

  val Math_min_Obj = approx_num

  val Math_pow_Obj = approx_num

  val Math_random_Obj = approx_num

  val Math_round_Obj = makeMath((x:Double) ⇒ math.round(x.toFloat)) // TODO we're losing precision here.

  val Math_sin_Obj = makeMath(math.sin)

  val Math_sqrt_Obj = makeMath(math.sqrt)

  val Math_tan_Obj = makeMath(math.tan)


}
