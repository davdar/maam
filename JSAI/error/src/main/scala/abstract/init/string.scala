// initial notJS state: String

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.traces.Trace
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.helpers.Errors._
import notjs.abstracted.init.Init._
import notjs.abstracted.init.InitHelpers._
import notjs.abstracted.init.StringHelpers._


object InitString {

  // string methods convert self to a string
  def strSig(argHints: List[ConversionHint], length: Int) =
    Sig(StringHint, argHints, length)
    
  def ezStrSig(argHints: ConversionHint*) =
    ezSig(StringHint, argHints.toList)

  // String
  val Internal_String_constructor_afterToString = valueObjConstructor("String") {
    arg_value ⇒ assert(arg_value.defStr,
      "String constructor: type conversion ensures argument is a string")
  }

  val Internal_String_normal_afterToString =
    (bvs: List[BValue], x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ: Trace) ⇒ {
      assert(bvs.length == 1, "String function: should have 1 argument by this point")
      val arg_value = bvs(0)
      assert(arg_value.defStr, "String function: type conversion ensures argument is a string")

      // if called as a function, merely convert argument to a string and return it
      makeState(arg_value, x, ρ, σ, ß, κ, τ)
    }

  val String_Obj = createInitFunctionObj(
    Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ: Trace) ⇒ {
        /* TODO: I suggest factoring these asserts and head extraction into a helper,
           or even the behavior of Native, if possible. */
        assert(argArrayAddr.defAddr, "String: argument array must be an address set")
        assert(argArrayAddr.as.size == 1, "String: argument array address set size must be 1")
        val argsArray = σ.getObj(argArrayAddr.as.head, Str.α("0"))

        // NB: use empty string if argument not given
        val arg_preconv = (argsArray(Str.α("0")) getOrElse Str.inject(Str.α("")), StringHint)

        // true iff invoking as a constructor:
        val calledAsConstr = argsArray.intern.getOrElse(Fields.constructor, false).asInstanceOf[Boolean]
        val (argList, postconvF) =
          if (calledAsConstr)
            (List((selfAddr, NoConversion), arg_preconv),
             Internal_String_constructor_afterToString)
          else
            (List(arg_preconv), Internal_String_normal_afterToString)

        Convert(argList, postconvF, x, ρ, σ, ß, κ, τ)
      }
    ),
    Map(
      "length" → Num.inject(Num.α(1)),
      "prototype" → Address.inject(String_prototype_Addr),
      "fromCharCode" → Address.inject(String_fromCharCode_Addr)
    ), cls = CString_Obj
  )

  val String_fromCharCode_Obj =
    constFunctionObj(VarSig(NoConversion, NumberHint, 1), Str.inject(STop))

  // String proto
  val String_prototype_Obj = createInitObj(
    Map(
      "charAt" → Address.inject(String_prototype_charAt_Addr), // TODO
      "charCodeAt" → Address.inject(String_prototype_charCodeAt_Addr), // TODO
      "concat" → Address.inject(String_prototype_concat_Addr), // TODO
      "indexOf" → Address.inject(String_prototype_indexOf_Addr), // TODO
      "lastIndexOf" → Address.inject(String_prototype_lastIndexOf_Addr), // TODO
      "localeCompare" → Address.inject(String_prototype_localeCompare_Addr), // TODO
      "match" → Address.inject(String_prototype_match_Addr),
      "replace" → Address.inject(String_prototype_replace_Addr), // TODO
      "search" → Address.inject(String_prototype_search_Addr), // TODO
      "slice" → Address.inject(String_prototype_slice_Addr), // TODO
      "split" → Address.inject(String_prototype_split_Addr), // TODO
      "substr" → Address.inject(String_prototype_substr_Addr), // TODO
      "substring" → Address.inject(String_prototype_substring_Addr), // TODO
      "toLocaleLowerCase" → Address.inject(String_prototype_toLocaleLowerCase_Addr), // TODO
      "toLocaleUpperCase" → Address.inject(String_prototype_toLocaleUpperCase_Addr), // TODO
      "toLowerCase" → Address.inject(String_prototype_toLowerCase_Addr), // TODO
      "toString" → Address.inject(String_prototype_toString_Addr),
      "toUpperCase" → Address.inject(String_prototype_toUpperCase_Addr), // TODO
      "trim" → Address.inject(String_prototype_trim_Addr), // TODO
      "valueOf" → Address.inject(String_prototype_valueOf_Addr)
    ),
    Map(
      Fields.classname → CString_prototype_Obj,
      Fields.value → Str.inject(Str.α(""))
    )
  )

  val String_prototype_toString_Obj =
    usualToPrim(isStringClass, _.str, Str.⊥, Str.inject)(_ ⊔ _)
  
  val String_prototype_valueOf_Obj = String_prototype_toString_Obj

  val String_prototype_charAt_Obj =
    constFunctionObj(ezStrSig(NumberHint), Str.inject(Str.SingleChar ⊔ Str.Empty))
  
  val String_prototype_charCodeAt_Obj =
    constFunctionObj(ezStrSig(NumberHint), Num.inject(NTop))
  
  val String_prototype_concat_Obj =
    constFunctionObj(VarSig(StringHint, StringHint, 1), Str.inject(STop))
  
  val String_prototype_indexOf_Obj =
    constFunctionObj(strSig(List(StringHint, NumberHint), 1), Num.inject(NReal))
  
  val String_prototype_lastIndexOf_Obj =
    constFunctionObj(strSig(List(StringHint, NumberHint), 1), Num.inject(NReal))
  
  val String_prototype_localeCompare_Obj =
    constFunctionObj(ezStrSig(StringHint), Num.inject(NReal))
  /* If the parameter to `match` is a RegExp object with the `global` property
     set, then match will mutate its `lastIndex` property; otherwise, it calls
     new RegExp on its parameter.  Assumption: for all objects passed in,
     it is sound to join their `lastIndex` properties with NReal, and
     convert all parameters to strings with ToString.  ToString is a step in
     new RegExp; we assume it is the only one which can have side-effects,
     and calling to ToString on a RegExp will not have any side-effects.
     `match` returns an array of matches, or null in the case of no matches.
     TODO: converting the RegExp parameter to a string makes it so we cannot
     properly mutate its lastIndex; this should be fixed. */
  val String_prototype_match_Obj =
    usualFunctionObj(ezStrSig(StringHint)) {
      case (List(_, regexp), σ, τ) ⇒ InitRegExp.matchBody(regexp.as, σ, τ)
      case _ ⇒ sys.error("String.prototype.match: signature conformance error")
    }
  /* `replace` handles RegExp conversions a bit differently: if the separator
      is a RegExp it does not convert it, and if not it calls ToString on it.
      This should hopefully have the same effects as before.
      In the RegExp case though, `replace` handles `global` and `lastIndex`
      like `match` does. */
  val String_prototype_replace_Obj =
    usualFunctionObj(ezStrSig(StringHint, StringHint)) {
      case (List(_, searchValue, _), σ, _) ⇒ {
        Set((Str.inject(STop), InitRegExp.mutateLastIndex(searchValue.as, σ)))
      }
      case _ ⇒ sys.error("string replace: arguments nonconformant to signature; usualFunctionObj must be broken")
    }
  /* `search` ignores `global` and does not touch `lastIndex`,
     but the RegExp conversion of `match` applies */
  val String_prototype_search_Obj =
    constFunctionObj(ezStrSig(StringHint), Num.inject(NReal))
  
  val String_prototype_slice_Obj =
    constFunctionObj(ezStrSig(NumberHint, NumberHint), Str.inject(STop))
  /* `split` handles RegExp conversions like `replace`.
     It seems like `split` does not modify `lastIndex` though.
     `split` returns an array of segments, even when its arguments are bad. */
  val String_prototype_split_Obj =
    usualFunctionObj(ezStrSig(StringHint, NumberHint)) {
      case (_, σ, τ) ⇒ {
        val (arr_a_bv, σ_, err) = InitRegExp.allocUnknownStringArray(σ, τ)
        Set((arr_a_bv, σ_)) ++ (err match {
          case Some(bv) ⇒ Set((bv, σ_))
          case None ⇒ Set()
        })
      }
    }
  val String_prototype_substring_Obj =
    constFunctionObj(ezStrSig(NumberHint, NumberHint), Str.inject(STop))
  
  val String_prototype_substr_Obj = String_prototype_substring_Obj
  
  val String_prototype_toLowerCase_Obj =
    constFunctionObj(ezStrSig(), Str.inject(STop))
  
  val String_prototype_toLocaleLowerCase_Obj =
    constFunctionObj(ezStrSig(), Str.inject(STop))
  
  val String_prototype_toUpperCase_Obj =
    constFunctionObj(ezStrSig(), Str.inject(STop))
  
  val String_prototype_toLocaleUpperCase_Obj =
    constFunctionObj(ezStrSig(), Str.inject(STop))
  
  val String_prototype_trim_Obj =
    constFunctionObj(ezStrSig(), Str.inject(STop))
}
