// initial notJS state: Date

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.traces.Trace
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.init.Init._
import notjs.abstracted.init.InitHelpers._
import notjs.abstracted.init.StringHelpers._


object InitDate {

  val Internal_Date_constructor_afterToNumber = genValueObjConstructor("Date") {
    _ ⇒ Num.inject(NTop) // approximation of current date value
  }
  val Date_Obj = createInitFunctionObj(
    Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(argArrayAddr.defAddr, "Date: Arguments array should refer to addresses")
        assert(argArrayAddr.as.size == 1, "Date: Arguments array should refer to a single address")
        val argsArray = σ getObj argArrayAddr.as.head

        val argList: List[(BValue, ConversionHint)] = List.range(0, 7) map {
          i ⇒ (argsArray(Str.α(i.toString)) getOrElse Undef.BV, NumberHint)
        }

        // true iff invoking as a constructor:
        val calledAsConstr = argsArray.intern.getOrElse(Fields.constructor, false).asInstanceOf[Boolean]

        if (calledAsConstr) // if a constructor, construct Date object
          Convert((selfAddr, NoConversion) :: argList, Internal_Date_constructor_afterToNumber, x, ρ, σ, ß, κ, τ)
        else // if not a constructor, ignore arguments and return a string
          makeState(Str.inject(Str.DateStr), x, ρ, σ, ß, κ, τ)
      }
    ),
    Map(
      "length" → Num.inject(Num.α(7)),
      "prototype" → Address.inject(Date_prototype_Addr),
      "now" → Address.inject(Date_now_Addr),
      "parse" → Address.inject(Date_parse_Addr)
    )
  )

  val Date_now_Obj = constFunctionObj(ezSig(NoConversion, List()),
    Num.inject(NTop))
  val Date_parse_Obj = constFunctionObj(ezSig(NoConversion, List(StringHint)),
    Num.inject(NTop))

  val Date_prototype_Obj = createInitObj(
    Map(
      "toString" → Address.inject(Date_prototype_toString_Addr),
      "valueOf" → Address.inject(Date_prototype_valueOf_Addr),
      "toLocaleString" → Address.inject(Date_prototype_toLocaleString_Addr)
    ),
    Map(
      Fields.value → Num.inject(Num.NaN),
      Fields.classname → CDate
    )
  )

  val Date_prototype_toString_Obj = constFunctionObj(ezSig(NoConversion, List()),
    Str.inject(Str.DateStr))
  val Date_prototype_valueOf_Obj = constFunctionObj(ezSig(NoConversion, List()),
    Num.inject(NTop))
  val Date_prototype_toLocaleString_Obj = constFunctionObj(ezSig(NoConversion, List()),
    Str.inject(Str.DateStr))

}
