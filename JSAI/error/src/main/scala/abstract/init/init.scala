// This file contains the definition of the notJS initState function
// that creates the initial state containing the language's builtin
// resources. See the builtin.pdf document for the specification.

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.traces._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.helpers.Errors._
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.interpreter.State

import notjs.abstracted.init.InitArguments._
import notjs.abstracted.init.InitArrays._
import notjs.abstracted.init.InitBoolean._
import notjs.abstracted.init.InitDate._
import notjs.abstracted.init.InitFunction._
import notjs.abstracted.init.InitGlobal._
import notjs.abstracted.init.InitJSON._
import notjs.abstracted.init.InitMath._
import notjs.abstracted.init.InitNumber._
import notjs.abstracted.init.InitObject._
import notjs.abstracted.init.InitRegExp._
import notjs.abstracted.init.InitString._
import notjs.abstracted.init.InitTypedArrays._

//——————————————————————————————————————————————————————————————————————————————
// initializer

object Init {

  // note: interface with the translator
  val window_Variable = PVar(0)

  // window addresses
  val window_binding_Addr = NewAbstractAddress()
  val window_Addr = NewAbstractAddress()

  // window properties NewAbstractAddresses
  val decodeURI_Addr = NewAbstractAddress()
  val decodeURIComponent_Addr = NewAbstractAddress()
  val encodeURI_Addr = NewAbstractAddress()
  val encodeURIComponent_Addr = NewAbstractAddress()
  val escape_Addr = NewAbstractAddress()
  val isFinite_Addr = NewAbstractAddress()
  val isNaN_Addr = NewAbstractAddress()
  val parseFloat_Addr = NewAbstractAddress()
  val parseInt_Addr = NewAbstractAddress()
  val unescape_Addr = NewAbstractAddress()
  val Array_Addr = NewAbstractAddress()
  val Boolean_Addr = NewAbstractAddress()
  val Date_Addr = NewAbstractAddress()
  val Error_Addr = NewAbstractAddress()
  val EvalError_Addr = NewAbstractAddress()
  val RangeError_Addr = NewAbstractAddress()
  val ReferenceError_Addr = NewAbstractAddress()
  val TypeError_Addr = NewAbstractAddress()
  val URIError_Addr = NewAbstractAddress()
  val Function_Addr = NewAbstractAddress()
  val JSON_Addr = NewAbstractAddress()
  val Math_Addr = NewAbstractAddress()
  val Number_Addr = NewAbstractAddress()
  val RegExp_Addr = NewAbstractAddress()
  val String_Addr = NewAbstractAddress()


  // Arguments NewAbstractAddresses (only for notJS)
  val Arguments_Addr = NewAbstractAddress()

  // Object NewAbstractAddresses
  val Object_Addr = NewAbstractAddress()
  val Object_create_Addr = NewAbstractAddress()
  val Object_defineProperties_Addr = NewAbstractAddress()
  val Object_defineProperty_Addr = NewAbstractAddress()
  val Object_freeze_Addr = NewAbstractAddress()
  val Object_getOwnPropertyDescriptor_Addr = NewAbstractAddress()
  val Object_getOwnPropertyNames_Addr = NewAbstractAddress()
  val Object_getPrototypeOf_Addr = NewAbstractAddress()
  val Object_isExtensible_Addr = NewAbstractAddress()
  val Object_isFrozen_Addr = NewAbstractAddress()
  val Object_isSealed_Addr = NewAbstractAddress()
  val Object_keys_Addr = NewAbstractAddress()
  val Object_preventExtensions_Addr = NewAbstractAddress()
  val Object_seal_Addr = NewAbstractAddress()

  // Object.prototype NewAbstractAddresses
  val Object_prototype_Addr = NewAbstractAddress()
  val Object_prototype_valueOf_Addr = NewAbstractAddress()
  val Object_prototype_toString_Addr = NewAbstractAddress()
  val Object_prototype_isPrototypeOf_Addr = NewAbstractAddress()
  val Object_prototype_propertyIsEnumerable_Addr = NewAbstractAddress()
  val Object_prototype_hasOwnProperty_Addr = NewAbstractAddress()
  val Object_prototype_toLocaleString_Addr = NewAbstractAddress()

  // Array NewAbstractAddresses
  val Array_prototype_Addr = NewAbstractAddress()
  val Array_isArray_Addr = NewAbstractAddress()

  // Array.prototype NewAbstractAddresses
  val Array_prototype_concat_Addr = NewAbstractAddress()
  val Array_prototype_every_Addr = NewAbstractAddress()
  val Array_prototype_filter_Addr = NewAbstractAddress()
  val Array_prototype_forEach_Addr = NewAbstractAddress()
  val Array_prototype_indexOf_Addr = NewAbstractAddress()
  val Array_prototype_join_Addr = NewAbstractAddress()
  val Array_prototype_lastIndexOf_Addr = NewAbstractAddress()
  val Array_prototype_map_Addr = NewAbstractAddress()
  val Array_prototype_pop_Addr = NewAbstractAddress()
  val Array_prototype_push_Addr = NewAbstractAddress()
  val Array_prototype_reduce_Addr = NewAbstractAddress()
  val Array_prototype_reduceRight_Addr = NewAbstractAddress()
  val Array_prototype_reverse_Addr = NewAbstractAddress()
  val Array_prototype_shift_Addr = NewAbstractAddress()
  val Array_prototype_slice_Addr = NewAbstractAddress()
  val Array_prototype_some_Addr = NewAbstractAddress()
  val Array_prototype_sort_Addr = NewAbstractAddress()
  val Array_prototype_splice_Addr = NewAbstractAddress()
  val Array_prototype_toLocaleString_Addr = NewAbstractAddress()
  val Array_prototype_toString_Addr = NewAbstractAddress()
  val Array_prototype_unshift_Addr = NewAbstractAddress()


  // Math NewAbstractAddresses
  val Math_abs_Addr = NewAbstractAddress()
  val Math_acos_Addr = NewAbstractAddress()
  val Math_asin_Addr = NewAbstractAddress()
  val Math_atan_Addr = NewAbstractAddress()
  val Math_atan2_Addr = NewAbstractAddress()
  val Math_ceil_Addr = NewAbstractAddress()
  val Math_cos_Addr = NewAbstractAddress()
  val Math_exp_Addr = NewAbstractAddress()
  val Math_floor_Addr = NewAbstractAddress()
  val Math_log_Addr = NewAbstractAddress()
  val Math_max_Addr = NewAbstractAddress()
  val Math_min_Addr = NewAbstractAddress()
  val Math_pow_Addr = NewAbstractAddress()
  val Math_random_Addr = NewAbstractAddress()
  val Math_round_Addr = NewAbstractAddress()
  val Math_sin_Addr = NewAbstractAddress()
  val Math_sqrt_Addr = NewAbstractAddress()
  val Math_tan_Addr = NewAbstractAddress()

  // Function NewAbstractAddresses
  val Function_prototype_Addr = NewAbstractAddress()

  // Function.prototype NewAbstractAddresses
  val Function_prototype_toString_Addr = NewAbstractAddress()
  val Function_prototype_apply_Addr = NewAbstractAddress()
  val Function_prototype_call_Addr = NewAbstractAddress()

  // Number NewAbstractAddresses
  val Number_prototype_Addr = NewAbstractAddress()

  // Number prototype NewAbstractAddresses
  val Number_prototype_toString_Addr = NewAbstractAddress()
  val Number_prototype_toLocaleString_Addr = NewAbstractAddress()
  val Number_prototype_valueOf_Addr = NewAbstractAddress()
  val Number_prototype_toFixed_Addr = NewAbstractAddress()
  val Number_prototype_toExponential_Addr = NewAbstractAddress()
  val Number_prototype_toPrecision_Addr = NewAbstractAddress()

  // String NewAbstractAddresses
  val String_prototype_Addr = NewAbstractAddress()
  val String_fromCharCode_Addr = NewAbstractAddress()

  // String.prototype NewAbstractAddresses
  val String_prototype_charAt_Addr = NewAbstractAddress()
  val String_prototype_charCodeAt_Addr = NewAbstractAddress()
  val String_prototype_concat_Addr = NewAbstractAddress()
  val String_prototype_indexOf_Addr = NewAbstractAddress()
  val String_prototype_lastIndexOf_Addr = NewAbstractAddress()
  val String_prototype_localeCompare_Addr = NewAbstractAddress()
  val String_prototype_match_Addr = NewAbstractAddress()
  val String_prototype_replace_Addr = NewAbstractAddress()
  val String_prototype_search_Addr = NewAbstractAddress()
  val String_prototype_slice_Addr = NewAbstractAddress()
  val String_prototype_split_Addr = NewAbstractAddress()
  val String_prototype_substr_Addr = NewAbstractAddress()
  val String_prototype_substring_Addr = NewAbstractAddress()
  val String_prototype_toLocaleLowerCase_Addr = NewAbstractAddress()
  val String_prototype_toLocaleUpperCase_Addr = NewAbstractAddress()
  val String_prototype_toLowerCase_Addr = NewAbstractAddress()
  val String_prototype_toString_Addr = NewAbstractAddress()
  val String_prototype_toUpperCase_Addr = NewAbstractAddress()
  val String_prototype_trim_Addr = NewAbstractAddress()
  val String_prototype_valueOf_Addr = NewAbstractAddress()

  // Boolean NewAbstractAddresses
  val Boolean_prototype_Addr = NewAbstractAddress()

  // Boolean.prototype NewAbstractAddresses
  val Boolean_prototype_toString_Addr = NewAbstractAddress()
  val Boolean_prototype_valueOf_Addr = NewAbstractAddress()

  // Error NewAbstractAddresses
  val Error_prototype_Addr = NewAbstractAddress()

  // Error.prototype NewAbstractAddresses
  val Error_prototype_toString_Addr = NewAbstractAddress()

  // JSON NewAbstractAddresses
  val JSON_parse_Addr = NewAbstractAddress()
  val JSON_stringify_Addr = NewAbstractAddress()

  // Date NewAbstractAddresses
  val Date_now_Addr = NewAbstractAddress()
  val Date_parse_Addr = NewAbstractAddress()
  val Date_prototype_Addr = NewAbstractAddress()

  // Date.prototype NewAbstractAddresses
  // TODO: Date's prototype has a lot more than just this in it!
  val Date_prototype_toString_Addr = NewAbstractAddress()
  val Date_prototype_valueOf_Addr = NewAbstractAddress()
  val Date_prototype_toLocaleString_Addr = NewAbstractAddress()

  // RegExp NewAbstractAddresses
  val RegExp_prototype_Addr = NewAbstractAddress()
  val RegExp_prototype_exec_Addr = NewAbstractAddress()
  val RegExp_prototype_test_Addr = NewAbstractAddress()
  val RegExp_prototype_toString_Addr = NewAbstractAddress()

  // Needed for internal functions
  val Dummy_Arguments_Addr = NewAbstractAddress()

  // typed array addresses:
  val ArrayBuffer_Addr = NewAbstractAddress()
  val ArrayBuffer_prototype_Addr = NewAbstractAddress()
  val Int8Array_Addr = NewAbstractAddress()
  val Uint8Array_Addr = NewAbstractAddress()
  val Int16Array_Addr = NewAbstractAddress()
  val Uint16Array_Addr = NewAbstractAddress()
  val Int32Array_Addr = NewAbstractAddress()
  val Uint32Array_Addr = NewAbstractAddress()
  val Float32Array_Addr = NewAbstractAddress()
  val Float64Array_Addr = NewAbstractAddress()
  val Int8Array_prototype_Addr = NewAbstractAddress()
  val Uint8Array_prototype_Addr = NewAbstractAddress()
  val Int16Array_prototype_Addr = NewAbstractAddress()
  val Uint16Array_prototype_Addr = NewAbstractAddress()
  val Int32Array_prototype_Addr = NewAbstractAddress()
  val Uint32Array_prototype_Addr = NewAbstractAddress()
  val Float32Array_prototype_Addr = NewAbstractAddress()
  val Float64Array_prototype_Addr = NewAbstractAddress()
  val Int8Array_prototype_set_Addr = NewAbstractAddress()
  val Uint8Array_prototype_set_Addr = NewAbstractAddress()
  val Int16Array_prototype_set_Addr = NewAbstractAddress()
  val Uint16Array_prototype_set_Addr = NewAbstractAddress()
  val Int32Array_prototype_set_Addr = NewAbstractAddress()
  val Uint32Array_prototype_set_Addr = NewAbstractAddress()
  val Float32Array_prototype_set_Addr = NewAbstractAddress()
  val Float64Array_prototype_set_Addr = NewAbstractAddress()
  val Int8Array_prototype_subarray_Addr = NewAbstractAddress()
  val Uint8Array_prototype_subarray_Addr = NewAbstractAddress()
  val Int16Array_prototype_subarray_Addr = NewAbstractAddress()
  val Uint16Array_prototype_subarray_Addr = NewAbstractAddress()
  val Int32Array_prototype_subarray_Addr = NewAbstractAddress()
  val Uint32Array_prototype_subarray_Addr = NewAbstractAddress()
  val Float32Array_prototype_subarray_Addr = NewAbstractAddress()
  val Float64Array_prototype_subarray_Addr = NewAbstractAddress()

  // dummy address used to pass to arguments object
  val Dummy_Addr = NewAbstractAddress()

  // we are allocating negative abstract addresses the special addresses
  // allocated inititially
  object NewAbstractAddress {
    private var inverseCounter = -2

    def apply(): Address = {
      inverseCounter = inverseCounter - 1
      Address(inverseCounter)
    }
  }

  // because we're treating scratch variables specially from program
  // variables, initState actually takes a Program, not a Stmt
  def initState( s:Stmt, τ: Trace ): State = {

    val initρ = Env() ++ List(window_Variable → window_binding_Addr)

    val initσ = Store(
      a2v = Map(window_binding_Addr → Address.inject(window_Addr)),
      a2o = Map(
             window_Addr → window_Obj,
             decodeURI_Addr → decodeURI_Obj,
             decodeURIComponent_Addr → decodeURIComponent_Obj,
             encodeURI_Addr → encodeURI_Obj,
             encodeURIComponent_Addr → encodeURIComponent_Obj,
             escape_Addr → escape_Obj,
             isFinite_Addr → isFinite_Obj,
             isNaN_Addr → isNaN_Obj,
             parseFloat_Addr → parseFloat_Obj,
             parseInt_Addr → parseInt_Obj,
             unescape_Addr → unescape_Obj,
             Array_Addr → Array_Obj,
             Boolean_Addr → Boolean_Obj,
             Arguments_Addr → Arguments_Obj,
             Date_Addr → Date_Obj,
             // Error_Addr → Error_Obj,
             // EvalError_Addr → EvalError_Obj,
             // RangeError_Addr → RangeError_Obj,
             // ReferenceError_Addr → ReferenceError_Obj,
             // TypeError_Addr → TypeError_Obj,
             // URIError_Addr → URIError_Obj,
             // Function_Addr → Function_Obj,
             JSON_Addr → JSON_Obj,
             Math_Addr → Math_Obj,
             Number_Addr → Number_Obj,
             RegExp_Addr → RegExp_Obj,
             String_Addr → String_Obj,
             Object_Addr → Object_Obj,
             // Object_create_Addr → Object_create_Obj,
             // Object_defineProperties_Addr → Object_defineProperties_Obj,
             // Object_defineProperty_Addr → Object_defineProperty_Obj,
             // Object_freeze_Addr → Object_freeze_Obj,
             // Object_getOwnPropertyDescriptor_Addr → Object_getOwnPropertyDescriptor_Obj,
             // Object_getOwnPropertyNames_Addr → Object_getOwnPropertyNames_Obj,
             // Object_getPrototypeOf_Addr → Object_getPrototypeOf_Obj,
             // Object_isExtensible_Addr → Object_isExtensible_Obj,
             // Object_isFrozen_Addr → Object_isFrozen_Obj,
             // Object_isSealed_Addr → Object_isSealed_Obj,
             // Object_keys_Addr → Object_keys_Obj,
             // Object_preventExtensions_Addr → Object_preventExtensions_Obj,
             // Object_seal_Addr → Object_seal_Obj,
             Object_prototype_Addr → Object_prototype_Obj,
             Object_prototype_valueOf_Addr → Object_prototype_valueOf_Obj,
             Object_prototype_toString_Addr → Object_prototype_toString_Obj,
             Object_prototype_isPrototypeOf_Addr → Object_prototype_isPrototypeOf_Obj,
             Object_prototype_propertyIsEnumerable_Addr → Object_prototype_propertyIsEnumerable_Obj,
             Object_prototype_hasOwnProperty_Addr → Object_prototype_hasOwnProperty_Obj,
             Object_prototype_toLocaleString_Addr → Object_prototype_toLocaleString_Obj,
             Array_prototype_Addr → Array_prototype_Obj,
             // Array_isArray_Addr → Array_isArray_Obj,
             Array_prototype_concat_Addr → Array_prototype_concat_Obj,
             Array_prototype_every_Addr → Array_prototype_every_Obj,
             Array_prototype_filter_Addr → Array_prototype_filter_Obj,
             Array_prototype_forEach_Addr → Array_prototype_forEach_Obj,
             Array_prototype_indexOf_Addr → Array_prototype_indexOf_Obj,
             Array_prototype_join_Addr → Array_prototype_join_Obj,
             Array_prototype_lastIndexOf_Addr → Array_prototype_lastIndexOf_Obj,
             Array_prototype_map_Addr → Array_prototype_map_Obj,
             Array_prototype_pop_Addr → Array_prototype_pop_Obj,
             Array_prototype_push_Addr → Array_prototype_push_Obj,
             Array_prototype_reduce_Addr → Array_prototype_reduce_Obj,
             Array_prototype_reduceRight_Addr → Array_prototype_reduceRight_Obj,
             Array_prototype_reverse_Addr → Array_prototype_reverse_Obj,
             Array_prototype_shift_Addr → Array_prototype_shift_Obj,
             Array_prototype_slice_Addr → Array_prototype_slice_Obj,
             Array_prototype_some_Addr → Array_prototype_some_Obj,
             Array_prototype_sort_Addr → Array_prototype_sort_Obj,
             Array_prototype_splice_Addr → Array_prototype_splice_Obj,
             Array_prototype_toLocaleString_Addr → Array_prototype_toLocaleString_Obj,
             Array_prototype_toString_Addr → Array_prototype_toString_Obj,
             Array_prototype_unshift_Addr → Array_prototype_unshift_Obj,
             Math_abs_Addr → Math_abs_Obj,
             Math_acos_Addr → Math_acos_Obj,
             Math_asin_Addr → Math_asin_Obj,
             Math_atan_Addr → Math_atan_Obj,
             Math_atan2_Addr → Math_atan2_Obj,
             Math_ceil_Addr → Math_ceil_Obj,
             Math_cos_Addr → Math_cos_Obj,
             Math_exp_Addr → Math_exp_Obj,
             Math_floor_Addr → Math_floor_Obj,
             Math_log_Addr → Math_log_Obj,
             Math_max_Addr → Math_max_Obj,
             Math_min_Addr → Math_min_Obj,
             Math_pow_Addr → Math_pow_Obj,
             Math_random_Addr → Math_random_Obj,
             Math_round_Addr → Math_round_Obj,
             Math_sin_Addr → Math_sin_Obj,
             Math_sqrt_Addr → Math_sqrt_Obj,
             Math_tan_Addr → Math_tan_Obj,
             Function_prototype_Addr → Function_prototype_Obj,
             Function_prototype_toString_Addr → Function_prototype_toString_Obj,
             Function_prototype_apply_Addr → Function_prototype_apply_Obj,
             Function_prototype_call_Addr → Function_prototype_call_Obj,
             Number_prototype_Addr → Number_prototype_Obj,
             Number_prototype_toString_Addr → Number_prototype_toString_Obj,
             // Number_prototype_toLocaleString_Addr → Number_prototype_toLocaleString_Obj,
             Number_prototype_valueOf_Addr → Number_prototype_valueOf_Obj,
             // Number_prototype_toFixed_Addr → Number_prototype_toFixed_Obj,
             // Number_prototype_toExponential_Addr → Number_prototype_toExponential_Obj,
             // Number_prototype_toPrecision_Addr → Number_prototype_toPrecision_Obj,
             String_prototype_Addr → String_prototype_Obj,
             String_fromCharCode_Addr → String_fromCharCode_Obj,
             String_prototype_charAt_Addr → String_prototype_charAt_Obj,
             String_prototype_charCodeAt_Addr → String_prototype_charCodeAt_Obj,
             String_prototype_concat_Addr → String_prototype_concat_Obj,
             String_prototype_indexOf_Addr → String_prototype_indexOf_Obj,
             String_prototype_lastIndexOf_Addr → String_prototype_lastIndexOf_Obj,
             String_prototype_localeCompare_Addr → String_prototype_localeCompare_Obj,
             String_prototype_match_Addr → String_prototype_match_Obj,
             String_prototype_replace_Addr → String_prototype_replace_Obj,
             String_prototype_search_Addr → String_prototype_search_Obj,
             String_prototype_slice_Addr → String_prototype_slice_Obj,
             String_prototype_split_Addr → String_prototype_split_Obj,
             String_prototype_substr_Addr → String_prototype_substr_Obj,
             String_prototype_substring_Addr → String_prototype_substring_Obj,
             String_prototype_toLocaleLowerCase_Addr → String_prototype_toLocaleLowerCase_Obj,
             String_prototype_toLocaleUpperCase_Addr → String_prototype_toLocaleUpperCase_Obj,
             String_prototype_toLowerCase_Addr → String_prototype_toLowerCase_Obj,
             String_prototype_toString_Addr → String_prototype_toString_Obj,
             String_prototype_toUpperCase_Addr → String_prototype_toUpperCase_Obj,
             String_prototype_trim_Addr → String_prototype_trim_Obj,
             String_prototype_valueOf_Addr → String_prototype_valueOf_Obj,
             Boolean_prototype_Addr → Boolean_prototype_Obj,
             Boolean_prototype_toString_Addr → Boolean_prototype_toString_Obj,
             Boolean_prototype_valueOf_Addr → Boolean_prototype_valueOf_Obj,
             // Error_prototype_Addr → Error_prototype_Obj,
             // Error_prototype_toString_Addr → Error_prototype_toString_Obj,
             JSON_parse_Addr → JSON_parse_Obj,
             JSON_stringify_Addr → JSON_stringify_Obj,
             Date_now_Addr → Date_now_Obj,
             Date_parse_Addr → Date_parse_Obj,
             Date_prototype_Addr → Date_prototype_Obj,
             Date_prototype_toString_Addr → Date_prototype_toString_Obj,
             Date_prototype_valueOf_Addr → Date_prototype_valueOf_Obj,
             Date_prototype_toLocaleString_Addr → Date_prototype_toLocaleString_Obj,
             RegExp_prototype_Addr → RegExp_prototype_Obj,
             RegExp_prototype_exec_Addr → RegExp_prototype_exec_Obj,
             RegExp_prototype_test_Addr → RegExp_prototype_test_Obj,
             RegExp_prototype_toString_Addr → RegExp_prototype_toString_Obj,
             Dummy_Arguments_Addr → Dummy_Arguments_Obj,
             ArrayBuffer_Addr → ArrayBuffer_Obj,
             ArrayBuffer_prototype_Addr → ArrayBuffer_prototype_Obj,
             Int8Array_Addr → Int8Array_Obj,
             Uint8Array_Addr → Uint8Array_Obj,
             Int16Array_Addr → Int16Array_Obj,
             Uint16Array_Addr → Uint16Array_Obj,
             Int32Array_Addr → Int32Array_Obj,
             Uint32Array_Addr → Uint32Array_Obj,
             Float32Array_Addr → Float32Array_Obj,
             Float64Array_Addr → Float64Array_Obj,
             Int8Array_prototype_Addr → Int8Array_prototype_Obj,
             Uint8Array_prototype_Addr → Uint8Array_prototype_Obj,
             Int16Array_prototype_Addr → Int16Array_prototype_Obj,
             Uint16Array_prototype_Addr → Uint16Array_prototype_Obj,
             Int32Array_prototype_Addr → Int32Array_prototype_Obj,
             Uint32Array_prototype_Addr → Uint32Array_prototype_Obj,
             Float32Array_prototype_Addr → Float32Array_prototype_Obj,
             Float64Array_prototype_Addr → Float64Array_prototype_Obj,
             Int8Array_prototype_set_Addr → Int8Array_prototype_set_Obj,
             Uint8Array_prototype_set_Addr → Uint8Array_prototype_set_Obj,
             Int16Array_prototype_set_Addr → Int16Array_prototype_set_Obj,
             Uint16Array_prototype_set_Addr → Uint16Array_prototype_set_Obj,
             Int32Array_prototype_set_Addr → Int32Array_prototype_set_Obj,
             Uint32Array_prototype_set_Addr → Uint32Array_prototype_set_Obj,
             Float32Array_prototype_set_Addr → Float32Array_prototype_set_Obj,
             Float64Array_prototype_set_Addr → Float64Array_prototype_set_Obj,
             Int8Array_prototype_subarray_Addr → Int8Array_prototype_subarray_Obj,
             Uint8Array_prototype_subarray_Addr → Uint8Array_prototype_subarray_Obj,
             Int16Array_prototype_subarray_Addr → Int16Array_prototype_subarray_Obj,
             Uint16Array_prototype_subarray_Addr → Uint16Array_prototype_subarray_Obj,
             Int32Array_prototype_subarray_Addr → Int32Array_prototype_subarray_Obj,
             Uint32Array_prototype_subarray_Addr → Uint32Array_prototype_subarray_Obj,
             Float32Array_prototype_subarray_Addr → Float32Array_prototype_subarray_Obj,
             Float64Array_prototype_subarray_Addr → Float64Array_prototype_subarray_Obj,
             Dummy_Addr → Dummy_Obj
            )
    )
    
    State(StmtT(s), initρ, initσ, Scratchpad(0), KStack(HaltK), τ)
  }

  val keepInStore: Addresses = Set(Dummy_Arguments_Addr, Number_Addr)

    // TODO: fill in special classes  
    // map each class to its set of non-enumerable fields
  val noenum = Map[JSClass, Set[Str]](
      CFunction → Set(Str.α("length")), // in ES3, prototype is in fact enumerable: see 15.3.5.2
      CArray → Set(Str.α("length")),
      CString → Set(Str.α("length")),
      CArguments → Set(Str.α("length")),
      CRegexp → Set(Str.α("source"), Str.α("global"), Str.α("ignoreCase"), Str.α("multiline"), Str.α("lastIndex")),
      CObject_Obj → Set(
        Str.α("prototype"),
        Str.α("create"),
        Str.α("defineProperties"),
        Str.α("defineProperty"),
        Str.α("freeze"),
        Str.α("getOwnPropertyDescriptor"),
        Str.α("getOwnPropertyNames"),
        Str.α("getPrototypeOf"),
        Str.α("isExtensible"),
        Str.α("isFrozen"),
        Str.α("isSealed"),
        Str.α("keys"),
        Str.α("length"),
        Str.α("preventExtensions"),
        Str.α("seal")
      ),
      CObject_prototype_Obj → Set(
        Str.α("constructor"),
        Str.α("valueOf"),
        Str.α("toString"),
        Str.α("isPrototypeOf"),
        Str.α("propertyIsEnumerable"),
        Str.α("hasOwnProperty"),
        Str.α("toLocaleString")
      ),
      CArray_Obj → Set(
        Str.α("prototype"),
        Str.α("isArray"),
        Str.α("length")
      ),
      CArray_prototype_Obj → Set(
        Str.α("constructor"),
        Str.α("concat"),
        Str.α("every"),
        Str.α("filter"),
        Str.α("forEach"),
        Str.α("indexOf"),
        Str.α("join"),
        Str.α("lastIndexOf"),
        Str.α("map"),
        Str.α("pop"),
        Str.α("push"),
        Str.α("reduce"),
        Str.α("reduceRight"),
        Str.α("reverse"),
        Str.α("shift"),
        Str.α("slice"),
        Str.α("some"),
        Str.α("sort"),
        Str.α("splice"),
        Str.α("toLocaleString"),
        Str.α("toString"),
        Str.α("unshift")
      ),
      CFunction_Obj → Set(
        Str.α("prototype"),
        Str.α("length")
      ),
      CFunction_prototype_Obj → Set(
        Str.α("constructor"),
        Str.α("apply"),
        Str.α("call"),
        Str.α("toString"),
        Str.α("length")
      ),
      CMath_Obj → Set(
        Str.α("E"),
        Str.α("LN10"),
        Str.α("LN2"),
        Str.α("LOG2E"),
        Str.α("LOG10E"),
        Str.α("PI"),
        Str.α("SQRT1_2"),
        Str.α("SQRT2"),
        Str.α("abs"),
        Str.α("acos"),
        Str.α("asin"),
        Str.α("atan"),
        Str.α("atan2"),
        Str.α("ceil"),
        Str.α("cos"),
        Str.α("exp"),
        Str.α("floor"),
        Str.α("log"),
        Str.α("max"),
        Str.α("min"),
        Str.α("pow"),
        Str.α("random"),
        Str.α("round"),
        Str.α("sin"),
        Str.α("sqrt"),
        Str.α("tan")
      ),
      CNumber_Obj → Set(
        Str.α("prototype"),
        Str.α("length"),
        Str.α("MAX_VALUE"),
        Str.α("MIN_VALUE"),
        Str.α("NaN"),
        Str.α("NEGATIVE_INFINITY"),
        Str.α("POSITIVE_INFINITY")
      ),
      CNumber_prototype_Obj → Set(
        Str.α("constructor"),
        Str.α("toString"),
        Str.α("toLocaleString"),
        Str.α("valueOf"),
        Str.α("toFixed"),
        Str.α("toExponential"),
        Str.α("toPrecision")
      ),
      CString_Obj → Set(
        Str.α("prototype"),
        Str.α("length"),
        Str.α("fromCharCode")
      ),
      CString_prototype_Obj → Set(
        Str.α("constructor"),
        Str.α("charAt"),
        Str.α("charCodeAt"),
        Str.α("concat"),
        Str.α("indexOf"),
        Str.α("lastIndexOf"),
        Str.α("localeCompare"),
        Str.α("match"),
        Str.α("replace"),
        Str.α("search"),
        Str.α("slice"),
        Str.α("split"),
        Str.α("substr"),
        Str.α("substring"),
        Str.α("toLocaleLowerCase"),
        Str.α("toLocaleUpperCase"),
        Str.α("toLowerCase"),
        Str.α("toString"),
        Str.α("toUpperCase"),
        Str.α("trim"),
        Str.α("valueOf")
      )
    ).withDefaultValue(Set())
  
    // TODO: fill in special classes  
    // map each class to its set of non-deleteable fields
  val nodelete = Map[JSClass, Set[Str]](
      CFunction → Set(Str.α("length"), Str.α("prototype")),
      CArray → Set(Str.α("length")),
      CString → Set(Str.α("length")),
      CRegexp → Set(Str.α("source"), Str.α("global"), Str.α("ignoreCase"), Str.α("multiline"), Str.α("lastIndex")),
      // Note that the prototypes do not typically have _any_ non-modifiable properties.
      CObject_Obj → Set(
        Str.α("prototype"),
        Str.α("length")
      ),
      CArray_Obj → Set(
        Str.α("prototype"),
        Str.α("length")
      ),
      CFunction_Obj → Set(
        Str.α("prototype"),
        Str.α("length")
      ),
      CMath_Obj → Set(
        Str.α("E"),
        Str.α("LN10"),
        Str.α("LN2"),
        Str.α("LOG2E"),
        Str.α("LOG10E"),
        Str.α("PI"),
        Str.α("SQRT1_2"),
        Str.α("SQRT2")
      ),
      CNumber_Obj → Set(
        Str.α("prototype"),
        Str.α("length")
      ),
      CString_Obj → Set(
        Str.α("prototype"),
        Str.α("length")
      )
    ).withDefaultValue(Set())
  
  
  // TODO: fill in special classes
  // map each class to its set of non-updateable fields
  val noupdate = Map[JSClass, Set[Str]](
      CFunction → Set(Str.α("length")),
      CString → Set(Str.α("length")),
      CRegexp → Set(Str.α("source"), Str.α("global"), Str.α("ignoreCase"), Str.α("multiline")),
     // Note that the prototypes do not typically have _any_ non-modifiable properties.
      CObject_Obj → Set(
        Str.α("prototype"),
        Str.α("length")
      ),
      CArray_Obj → Set(
        Str.α("prototype"),
        Str.α("length")
      ),
      CFunction_Obj → Set(
        Str.α("prototype"),
        Str.α("length")
      ),
      CMath_Obj → Set(
        Str.α("E"),
        Str.α("LN10"),
        Str.α("LN2"),
        Str.α("LOG2E"),
        Str.α("LOG10E"),
        Str.α("PI"),
        Str.α("SQRT1_2"),
        Str.α("SQRT2")
      ),
      CNumber_Obj → Set(
        Str.α("prototype"),
        Str.α("length")
      ),
      CString_Obj → Set(
        Str.α("prototype"),
        Str.α("length")
      )
    ).withDefaultValue(Set())
  
  // map the addresses assigned to the special objects by initState to
  // the classes they represent; used by allocObj to determine an
  // object's class based on its prototype
  // TODO: probably a better way of doing this
  val classFromAddress = Map[Address, JSClass](
      Function_Addr → CFunction,
      Array_Addr → CArray,
      String_Addr → CString,
      Boolean_Addr → CBoolean,
      Number_Addr → CNumber,
      Date_Addr → CDate,
      Error_Addr → CError,
      EvalError_Addr → CError,
      RangeError_Addr → CError,
      ReferenceError_Addr → CError,
      TypeError_Addr → CError,
      RegExp_Addr → CRegexp,
      Arguments_Addr → CArguments
    ).withDefaultValue(CObject)
}
