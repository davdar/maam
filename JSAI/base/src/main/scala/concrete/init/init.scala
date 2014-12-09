// This file contains the definition of the notJS initState function
// that creates the initial state containing the language's builtin
// resources. See the builtin.pdf document for the specification.

package notjs.concrete.init

import notjs.syntax._
import notjs.concrete.domains._
import notjs.concrete.interpreter.State
import notjs.concrete.helpers.Errors._
import notjs.concrete.helpers.Helpers._

import notjs.concrete.init.InitArguments._
import notjs.concrete.init.InitArrays._
import notjs.concrete.init.InitFunction._
import notjs.concrete.init.InitGlobal._
import notjs.concrete.init.InitHelpers._
import notjs.concrete.init.InitMath._
import notjs.concrete.init.InitMisc._
import notjs.concrete.init.InitNumber._
import notjs.concrete.init.InitObject._
import notjs.concrete.init.InitString._

//——————————————————————————————————————————————————————————————————————————————
// initializer

object Init {

    // IMPORTANT NOTE: window name  
    val window_Variable = PVar(0)

    // window addresses
    val window_binding_Addr = Address()
    val window_Addr         = Address()

    // window properties addresses
    val decodeURI_Addr          = Address()
    val decodeURIComponent_Addr = Address()
    val encodeURI_Addr          = Address()
    val encodeURIComponent_Addr = Address()
    val escape_Addr             = Address()
    val isFinite_Addr           = Address()
    val isNaN_Addr              = Address()
    val parseFloat_Addr         = Address()
    val parseInt_Addr           = Address()
    val unescape_Addr           = Address()
    val Array_Addr              = Address()
    val Boolean_Addr            = Address()
    val Date_Addr               = Address()
    val Error_Addr              = Address()
    val EvalError_Addr          = Address()
    val RangeError_Addr         = Address()
    val ReferenceError_Addr     = Address()
    val TypeError_Addr          = Address()
    val URIError_Addr           = Address()
    val Function_Addr           = Address()
    val JSON_Addr               = Address()
    val Math_Addr               = Address()
    val Number_Addr             = Address()
    val RegExp_Addr             = Address()
    val String_Addr             = Address()

    // Object addresses
    val Object_Addr                                 = Address()
    val Object_create_Addr                          = Address()
    val Object_defineProperties_Addr                = Address()
    val Object_defineProperty_Addr                  = Address()
    val Object_freeze_Addr                          = Address()
    val Object_getOwnPropertyDescriptor_Addr        = Address()
    val Object_getOwnPropertyNames_Addr             = Address()
    val Object_getPrototypeOf_Addr                  = Address()
    val Object_isExtensible_Addr                    = Address()
    val Object_isFrozen_Addr                        = Address()
    val Object_isSealed_Addr                        = Address()
    val Object_keys_Addr                            = Address()
    val Object_preventExtensions_Addr               = Address()
    val Object_seal_Addr                            = Address()

    // Object.prototype addresses
    val Object_prototype_Addr                       = Address()
    val Object_prototype_valueOf_Addr               = Address()
    val Object_prototype_toString_Addr              = Address()
    val Object_prototype_isPrototypeOf_Addr         = Address()
    val Object_prototype_propertyIsEnumerable_Addr  = Address()
    val Object_prototype_hasOwnProperty_Addr        = Address()
    val Object_prototype_toLocaleString_Addr        = Address()

    // Array addresses
    val Array_prototype_Addr = Address()
    val Array_isArray_Addr   = Address()

    // Array.prototype addresses
    val Array_prototype_concat_Addr         = Address()
    val Array_prototype_every_Addr          = Address()
    val Array_prototype_filter_Addr         = Address()
    val Array_prototype_forEach_Addr        = Address()
    val Array_prototype_indexOf_Addr        = Address()
    val Array_prototype_join_Addr           = Address()
    val Array_prototype_lastIndexOf_Addr    = Address()
    val Array_prototype_map_Addr            = Address()
    val Array_prototype_pop_Addr            = Address()
    val Array_prototype_push_Addr           = Address()
    val Array_prototype_reduce_Addr         = Address()
    val Array_prototype_reduceRight_Addr    = Address()
    val Array_prototype_reverse_Addr        = Address()
    val Array_prototype_shift_Addr          = Address()
    val Array_prototype_slice_Addr          = Address()
    val Array_prototype_some_Addr           = Address()
    val Array_prototype_sort_Addr           = Address()
    val Array_prototype_splice_Addr         = Address()
    val Array_prototype_toLocaleString_Addr = Address()
    val Array_prototype_toString_Addr       = Address()
    val Array_prototype_unshift_Addr        = Address()


    // Math addresses
    val Math_abs_Addr           = Address()
    val Math_acos_Addr          = Address()
    val Math_asin_Addr          = Address()
    val Math_atan_Addr          = Address()
    val Math_atan2_Addr         = Address()
    val Math_ceil_Addr          = Address()
    val Math_cos_Addr           = Address()
    val Math_exp_Addr           = Address()
    val Math_floor_Addr         = Address()
    val Math_log_Addr           = Address()
    val Math_max_Addr           = Address()
    val Math_min_Addr           = Address()
    val Math_pow_Addr           = Address()
    val Math_random_Addr        = Address()
    val Math_round_Addr         = Address()
    val Math_sin_Addr           = Address()
    val Math_sqrt_Addr          = Address()
    val Math_tan_Addr           = Address()

    // Function addresses
    val Function_prototype_Addr = Address()
    
    // Function prototype addresses
    val Function_prototype_apply_Addr = Address()
    val Function_prototype_call_Addr = Address()
    val Function_prototype_toString_Addr = Address()

    // Number addresses
    val Number_prototype_Addr = Address()

    // Number prototype addresses
    val Number_prototype_toString_Addr        = Address()
    val Number_prototype_toLocaleString_Addr  = Address()
    val Number_prototype_valueOf_Addr         = Address()
    val Number_prototype_toFixed_Addr         = Address()
    val Number_prototype_toExponential_Addr   = Address()
    val Number_prototype_toPrecision_Addr     = Address()

    // String addresses
    val String_prototype_Addr    = Address()
    val String_fromCharCode_Addr = Address()

    // String.prototype addresses
    val String_prototype_charAt_Addr              = Address()
    val String_prototype_charCodeAt_Addr          = Address()
    val String_prototype_concat_Addr              = Address()
    val String_prototype_indexOf_Addr             = Address()
    val String_prototype_lastIndexOf_Addr         = Address()
    val String_prototype_localeCompare_Addr       = Address()
    val String_prototype_match_Addr               = Address()
    val String_prototype_replace_Addr             = Address()
    val String_prototype_search_Addr              = Address()
    val String_prototype_slice_Addr               = Address()
    val String_prototype_split_Addr               = Address()
    val String_prototype_substr_Addr              = Address()
    val String_prototype_substring_Addr           = Address()
    val String_prototype_toLocaleLowerCase_Addr   = Address()
    val String_prototype_toLocaleUpperCase_Addr   = Address()
    val String_prototype_toLowerCase_Addr         = Address()
    val String_prototype_toString_Addr            = Address()
    val String_prototype_toUpperCase_Addr         = Address()
    val String_prototype_trim_Addr                = Address()
    val String_prototype_valueOf_Addr             = Address()

    // Boolean addresses
    val Boolean_prototype_Addr = Address()

    // Boolean.prototype addresses
    val Boolean_prototype_toString_Addr = Address()
    val Boolean_prototype_valueOf_Addr  = Address()

    // Error addresses
    val Error_prototype_Addr = Address()

    // Error.prototype addresses
    val Error_prototype_toString_Addr = Address()

    // JSON addresses
    val JSON_parse_Addr = Address()
    val JSON_stringify_Addr = Address()

    // Date Addresses
    val Date_now_Addr = Address()
    val Date_parse_Addr = Address()
    val Date_prototype_Addr = Address()

    // RegExp Addresses
    val RegExp_prototype_Addr = Address()

    // Arguments Address
    val Arguments_Addr = Address()

    // Dummy Address
    // This address is used by the translator in place where arguments object is constructed
    val Dummy_Addr = Address()

    def initState( s:Stmt ): State = {

    val ρ = Env(Map(window_Variable → window_binding_Addr))
  
    val σ =   Store(Map(
      window_binding_Addr → window_Addr), Map(
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
      Date_Addr → Date_Obj,
      Error_Addr → Error_Obj,
      //EvalError_Addr → EvalError_Obj, // TODO: this
      //RangeError_Addr → RangeError_Obj,
      //ReferenceError_Addr → ReferenceError_Obj,
      //TypeError_Addr → TypeError_Obj,
      //URIError_Addr → URIError_Obj,
      Function_Addr → Function_Obj,
      Function_prototype_Addr → Function_prototype_Obj,
      Function_prototype_apply_Addr → Function_prototype_apply_Obj,
      Function_prototype_call_Addr → Function_prototype_call_Obj,
      Function_prototype_toString_Addr → Function_prototype_toString_Obj,
      JSON_Addr → JSON_Obj,
      Math_Addr → Math_Obj,
      Number_Addr → Number_Obj,
      RegExp_Addr → RegExp_Obj,
      String_Addr → String_Obj,
      Object_Addr → Object_Obj,
      Object_create_Addr → Object_create_Obj,
      Object_defineProperties_Addr → Object_defineProperties_Obj,
      Object_defineProperty_Addr → Object_defineProperty_Obj,
      Object_freeze_Addr → Object_freeze_Obj,
      Object_getOwnPropertyDescriptor_Addr → Object_getOwnPropertyDescriptor_Obj,
      Object_getOwnPropertyNames_Addr → Object_getOwnPropertyNames_Obj,
      Object_getPrototypeOf_Addr → Object_getPrototypeOf_Obj,
      Object_isExtensible_Addr → Object_isExtensible_Obj,
      Object_isFrozen_Addr → Object_isFrozen_Obj,
      Object_isSealed_Addr → Object_isSealed_Obj,
      Object_keys_Addr → Object_keys_Obj,
      Object_preventExtensions_Addr → Object_preventExtensions_Obj,
      Object_seal_Addr → Object_seal_Obj,
      Object_prototype_Addr → Object_prototype_Obj,
      Object_prototype_valueOf_Addr → Object_prototype_valueOf_Obj,
      Object_prototype_toString_Addr → Object_prototype_toString_Obj,
      Object_prototype_isPrototypeOf_Addr → Object_prototype_isPrototypeOf_Obj,
      Object_prototype_propertyIsEnumerable_Addr → Object_prototype_propertyIsEnumerable_Obj,
      Object_prototype_hasOwnProperty_Addr → Object_prototype_hasOwnProperty_Obj,
      Object_prototype_toLocaleString_Addr → Object_prototype_toLocaleString_Obj,
      Array_prototype_Addr → Array_prototype_Obj,
      Array_isArray_Addr → Array_isArray_Obj,
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
      Number_prototype_Addr → Number_prototype_Obj,
      Number_prototype_toString_Addr → Number_prototype_toString_Obj,
      Number_prototype_toLocaleString_Addr → Number_prototype_toLocaleString_Obj,
      Number_prototype_valueOf_Addr → Number_prototype_valueOf_Obj,
      Number_prototype_toFixed_Addr → Number_prototype_toFixed_Obj,
      Number_prototype_toExponential_Addr → Number_prototype_toExponential_Obj,
      Number_prototype_toPrecision_Addr → Number_prototype_toPrecision_Obj,
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
      Error_prototype_Addr → Error_prototype_Obj,
      Error_prototype_toString_Addr → Error_prototype_toString_Obj,
      JSON_parse_Addr → JSON_parse_Obj,
      JSON_stringify_Addr → JSON_stringify_Obj,
      Date_now_Addr → Date_now_Obj,
      Date_parse_Addr → Date_parse_Obj,
      Date_prototype_Addr → Date_prototype_Obj,
      RegExp_prototype_Addr → RegExp_prototype_Obj,
      Arguments_Addr → Arguments_Obj,
      Dummy_Addr → createObj(Map())
      ))
      
      State(StmtT(s), ρ, σ, Scratchpad(0), KStack(List(HaltK)))
    }

    // TODO: fill in special classes  
    // map each class to its set of non-enumerable fields
    val noenum = Map[JSClass, Set[Str]](
        CFunction → Set(Str("length")), // in ES3, prototype is in fact enumerable: see 15.3.5.2
        CArray → Set(Str("length")),
        CString → Set(Str("length")),
        CArguments → Set(Str("length")),
        CRegexp → Set(Str("source"), Str("global"), Str("ignoreCase"), Str("multiline"), Str("lastIndex")),
        CObject_Obj → Set(
          Str("prototype"),
          Str("create"),
          Str("defineProperties"),
          Str("defineProperty"),
          Str("freeze"),
          Str("getOwnPropertyDescriptor"),
          Str("getOwnPropertyNames"),
          Str("getPrototypeOf"),
          Str("isExtensible"),
          Str("isFrozen"),
          Str("isSealed"),
          Str("keys"),
          Str("length"),
          Str("preventExtensions"),
          Str("seal")
        ),
        CObject_prototype_Obj → Set(
          Str("constructor"),
          Str("valueOf"),
          Str("toString"),
          Str("isPrototypeOf"),
          Str("propertyIsEnumerable"),
          Str("hasOwnProperty"),
          Str("toLocaleString")
        ),
        CArray_Obj → Set(
          Str("prototype"),
          Str("isArray"),
          Str("length")
        ),
        CArray_prototype_Obj → Set(
          Str("constructor"),
          Str("concat"),
          Str("every"),
          Str("filter"),
          Str("forEach"),
          Str("indexOf"),
          Str("join"),
          Str("lastIndexOf"),
          Str("map"),
          Str("pop"),
          Str("push"),
          Str("reduce"),
          Str("reduceRight"),
          Str("reverse"),
          Str("shift"),
          Str("slice"),
          Str("some"),
          Str("sort"),
          Str("splice"),
          Str("toLocaleString"),
          Str("toString"),
          Str("unshift")
        ),
        CFunction_Obj → Set(
          Str("prototype"),
          Str("length")
        ),
        CFunction_prototype_Obj → Set(
          Str("constructor"),
          Str("apply"),
          Str("call"),
          Str("toString"),
          Str("length")
        ),
        CMath_Obj → Set(
          Str("E"),
          Str("LN10"),
          Str("LN2"),
          Str("LOG2E"),
          Str("LOG10E"),
          Str("PI"),
          Str("SQRT1_2"),
          Str("SQRT2"),
          Str("abs"),
          Str("acos"),
          Str("asin"),
          Str("atan"),
          Str("atan2"),
          Str("ceil"),
          Str("cos"),
          Str("exp"),
          Str("floor"),
          Str("log"),
          Str("max"),
          Str("min"),
          Str("pow"),
          Str("random"),
          Str("round"),
          Str("sin"),
          Str("sqrt"),
          Str("tan")
        ),
        CNumber_Obj → Set(
          Str("prototype"),
          Str("length"),
          Str("MAX_VALUE"),
          Str("MIN_VALUE"),
          Str("NaN"),
          Str("NEGATIVE_INFINITY"),
          Str("POSITIVE_INFINITY")
        ),
        CNumber_prototype_Obj → Set(
          Str("constructor"),
          Str("toString"),
          Str("toLocaleString"),
          Str("valueOf"),
          Str("toFixed"),
          Str("toExponential"),
          Str("toPrecision")
        ),
        CString_Obj → Set(
          Str("prototype"),
          Str("length"),
          Str("fromCharCode")
        ),
        CString_prototype_Obj → Set(
          Str("constructor"),
          Str("charAt"),
          Str("charCodeAt"),
          Str("concat"),
          Str("indexOf"),
          Str("lastIndexOf"),
          Str("localeCompare"),
          Str("match"),
          Str("replace"),
          Str("search"),
          Str("slice"),
          Str("split"),
          Str("substr"),
          Str("substring"),
          Str("toLocaleLowerCase"),
          Str("toLocaleUpperCase"),
          Str("toLowerCase"),
          Str("toString"),
          Str("toUpperCase"),
          Str("trim"),
          Str("valueOf")
        )
      ).withDefaultValue(Set[Str]())
  
    // TODO: fill in special classes  
    // map each class to its set of non-deleteable fields
    val nodelete = Map[JSClass, Set[Str]](
        CFunction → Set(Str("length"), Str("prototype")),
        CArray → Set(Str("length")),
        CString → Set(Str("length")),
        CRegexp → Set(Str("source"), Str("global"), Str("ignoreCase"), Str("multiline"), Str("lastIndex")),
        // Note that the prototypes do not typically have _any_ non-modifiable properties.
        CObject_Obj → Set(
          Str("prototype"),
          Str("length")
        ),
        CArray_Obj → Set(
          Str("prototype"),
          Str("length")
        ),
        CFunction_Obj → Set(
          Str("prototype"),
          Str("length")
        ),
        CMath_Obj → Set(
          Str("E"),
          Str("LN10"),
          Str("LN2"),
          Str("LOG2E"),
          Str("LOG10E"),
          Str("PI"),
          Str("SQRT1_2"),
          Str("SQRT2")
        ),
        CNumber_Obj → Set(
          Str("prototype"),
          Str("length")
        ),
        CString_Obj → Set(
          Str("prototype"),
          Str("length")
        )
      ).withDefaultValue(Set[Str]())
  
  
    // TODO: fill in special classes
    // map each class to its set of non-updateable fields
    val noupdate = Map[JSClass, Set[Str]](
        CFunction → Set(Str("length")),
        CString → Set(Str("length")),
        CRegexp → Set(Str("source"), Str("global"), Str("ignoreCase"), Str("multiline")),
       // Note that the prototypes do not typically have _any_ non-modifiable properties.
        CObject_Obj → Set(
          Str("prototype"),
          Str("length")
        ),
        CArray_Obj → Set(
          Str("prototype"),
          Str("length")
        ),
        CFunction_Obj → Set(
          Str("prototype"),
          Str("length")
        ),
        CMath_Obj → Set(
          Str("E"),
          Str("LN10"),
          Str("LN2"),
          Str("LOG2E"),
          Str("LOG10E"),
          Str("PI"),
          Str("SQRT1_2"),
          Str("SQRT2")
        ),
        CNumber_Obj → Set(
          Str("prototype"),
          Str("length")
        ),
        CString_Obj → Set(
          Str("prototype"),
          Str("length")
        )
      ).withDefaultValue(Set[Str]())
  
    // map the addresses assigned to the special objects by initState to
    // the classes they represent; used by allocObj to determine an
    // object's class based on its prototype
    val classFromAddress = Map[Address, JSClass](
          Function_Addr → CFunction,
          Array_Addr → CArray,
          String_Addr → CString,
          Boolean_Addr → CBoolean,
          Number_Addr → CNumber, 
          Date_Addr → CDate,
          Error_Addr → CError,
          RegExp_Addr → CRegexp,
          Arguments_Addr → CArguments
        ).withDefaultValue(CObject)  
}
