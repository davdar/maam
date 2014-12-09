// initial notJS state: global object

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.helpers.Errors._
import notjs.abstracted.init.Init._
import notjs.abstracted.init.InitHelpers._
import notjs.abstracted.init.StringHelpers._


object InitGlobal {

  val window_Obj = createInitObj(Map(
    "window" → Address.inject(window_Addr),
    "Arguments" → Address.inject(Arguments_Addr),
    "undefined" → Undef.BV,
    "decodeURI" → Address.inject(decodeURI_Addr),
    "decodeURIComponent" → Address.inject(decodeURIComponent_Addr),
    "encodeURI" → Address.inject(encodeURI_Addr),
    "encodeURIComponent" → Address.inject(encodeURIComponent_Addr),
    "escape" → Address.inject(escape_Addr),
    "isFinite" → Address.inject(isFinite_Addr),
    "isNaN" → Address.inject(isNaN_Addr),
    "parseFloat" → Address.inject(parseFloat_Addr),
    "parseInt" → Address.inject(parseInt_Addr),
    "unescape" → Address.inject(unescape_Addr),
    "Array" → Address.inject(Array_Addr),
    "Boolean" → Address.inject(Boolean_Addr),
    "Number" → Address.inject(Number_Addr),
    "Object" → Address.inject(Object_Addr),
    "String" → Address.inject(String_Addr),
    "Date" → Address.inject(Date_Addr), // TODO
    "JSON" → Address.inject(JSON_Addr), // TODO
    "Math" → Address.inject(Math_Addr),
    "RegExp" → Address.inject(RegExp_Addr),
    // typed array extensions
    "ArrayBuffer" → Address.inject(ArrayBuffer_Addr), 
    "Int8Array" → Address.inject(Int8Array_Addr), 
    "Uint8Array" → Address.inject(Uint8Array_Addr), 
    "Int16Array" → Address.inject(Int16Array_Addr), 
    "Uint16Array" → Address.inject(Uint16Array_Addr), 
    "Int32Array" → Address.inject(Int32Array_Addr), 
    "Uint32Array" → Address.inject(Uint32Array_Addr), 
    "Float32Array" → Address.inject(Float32Array_Addr), 
    "Float64Array" → Address.inject(Float64Array_Addr), 
    // dummy address given so that arguments constructor can use them
    "dummyAddress" → Address.inject(Dummy_Addr),
    "Infinity" → Num.inject(Num.α(Double.PositiveInfinity)),
    "NaN" → Num.inject(Num.α(Double.NaN))
) ++ dangleMap(Map(
    "Error" → Address.inject(Error_Addr), // TODO
    "EvalError" → Address.inject(EvalError_Addr), // TODO
    "RangeError" → Address.inject(RangeError_Addr), // TODO
    "ReferenceError" → Address.inject(ReferenceError_Addr), // TODO
    "TypeError" → Address.inject(TypeError_Addr), // TODO
    "URIError" → Address.inject(URIError_Addr), // TODO
    "Function" → Address.inject(Function_Addr) // TODO
  )))

  val uriMethodObj : Object =
    pureFunctionObj(ezSig(NoConversion, List(StringHint))) { _ ⇒
      Set(Str.inject(STop), uriError)
    }
  val decodeURI_Obj = uriMethodObj
  val decodeURIComponent_Obj = uriMethodObj
  val encodeURI_Obj = uriMethodObj
  val encodeURIComponent_Obj = uriMethodObj
  val compatabilityURIMethodObj : Object =
    constFunctionObj(ezSig(NoConversion, List(StringHint)),
      Str.inject(STop))
  val escape_Obj = compatabilityURIMethodObj
  val unescape_Obj = compatabilityURIMethodObj

  val isFinite_Obj = pureFunctionObj(ezSig(NoConversion, List(NumberHint))) {
    case List(_, bv) ⇒ {
      assert(bv.defNum, "isFinite: conversion should guarante argument must be a number")
      Set(Bool.inject(bv.n match {
        case NBot ⇒ BBot
        case NTop ⇒ BTop
        case NReal ⇒ BTrue
        case NConst(d) ⇒ d match {
          case Double.PositiveInfinity | Double.NegativeInfinity ⇒ BFalse
          case _ ⇒ if (d.isNaN) BFalse else BTrue
        }
      }))
    }
    case _ ⇒ sys.error("isFinite: signature conformance error")
  }
  val isNaN_Obj = pureFunctionObj(ezSig(NoConversion, List(NumberHint))) {
    case List(_, bv) ⇒ {
      assert(bv.defNum, "isNaN: conversion should guarantee argument must be a number")
      Set(Bool.inject(bv.n match {
        case NBot ⇒ BBot
        case NTop ⇒ BTop
        case NReal ⇒ BFalse
        case NConst(d) ⇒ if (d.isNaN) BTrue else BFalse
      }))
    }
    case _ ⇒ sys.error("isNaN: signature conformance error")
  }

  val parseFloat_Obj =
    constFunctionObj(ezSig(NoConversion, List(StringHint)), Num.inject(NTop))
  val parseInt_Obj =
    constFunctionObj(ezSig(NoConversion, List(StringHint, NumberHint)), Num.inject(NTop))

}
