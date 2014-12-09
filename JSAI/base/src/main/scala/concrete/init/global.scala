// initial notJS state: global object

package notjs.concrete.init

import notjs.syntax._
import notjs.concrete.domains._
import notjs.concrete.interpreter.State
import notjs.concrete.helpers.Fields
import notjs.concrete.helpers.Errors._
import notjs.concrete.helpers.Helpers._

import notjs.concrete.init.Init._
import notjs.concrete.init.InitHelpers._


object InitGlobal {

    val window_Obj = createObj(Map(
      Str("window") → window_Addr,
      Str("Infinity") → Num(Double.PositiveInfinity),
      Str("NaN") → Num(Double.NaN),
      Str("undefined") → Undef,
      Str("decodeURI") → decodeURI_Addr,
      Str("decodeURIComponent") → decodeURIComponent_Addr,
      Str("encodeURI") → encodeURI_Addr,
      Str("encodeURIComponent") → encodeURIComponent_Addr,
      Str("escape") → escape_Addr,
      Str("isFinite") → isFinite_Addr,
      Str("isNaN") → isNaN_Addr,
      Str("parseFloat") → parseFloat_Addr,
      Str("parseInt") → parseInt_Addr,
      Str("unescape") → unescape_Addr,
      Str("Array") → Array_Addr,
      Str("Boolean") → Boolean_Addr,
      Str("Date") → Date_Addr,
      Str("Error") → Error_Addr,
      Str("EvalError") → EvalError_Addr,
      Str("RangeError") → RangeError_Addr,
      Str("ReferenceError") → ReferenceError_Addr,
      Str("TypeError") → TypeError_Addr,
      Str("URIError") → URIError_Addr,
      Str("Function") → Function_Addr,
      Str("JSON") → JSON_Addr,
      Str("Math") → Math_Addr,
      Str("Number") → Number_Addr,
      Str("Object") → Object_Addr,
      Str("RegExp") → RegExp_Addr,
      Str("String") → String_Addr,
      Str("Arguments") → Arguments_Addr,
      Str("dummyAddress") → Dummy_Addr
  ))


    

  val decodeURI_Obj = approx_str
  
  val decodeURIComponent_Obj = approx_str

  val encodeURI_Obj = approx_str

  val encodeURIComponent_Obj = approx_str

  val escape_Obj = approx_str

  val unescape_Obj = approx_str

  val isFinite_Obj = makeNativeValue(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val args = σ.getObj(argArrayAddr)
        val input = ToNumber(args(Str("0")).getOrElse(Undef), σ)
        Bool(input == Num(Double.PositiveInfinity) || input == Num(Double.NegativeInfinity) || input == Num(Double.NaN))
      }, Map(Str("length") → Num(1))
    )

  val isNaN_Obj =  makeNativeValue(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val args = σ.getObj(argArrayAddr)
        val input = ToNumber(args(Str("0")).getOrElse(Undef), σ)
        Bool(input.n.isNaN)
      }, Map(Str("length") → Num(1))
    )

  val parseFloat_Obj = approx_num

  val parseInt_Obj = approx_num



}
