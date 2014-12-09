// notJS initial state: Arguments

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.traces.Trace
import notjs.abstracted.helpers.Fields
import notjs.abstracted.init.Init._
import notjs.abstracted.init.InitHelpers._
import notjs.abstracted.init.StringHelpers._


object InitArguments {

  // dummy arguments object used in several places:
  val Dummy_Arguments_Obj = createInitObj(
    Map("length" → Num.inject(Num.α(0))),
    Map(Fields.classname → CArguments)
  )


  val Dummy_Obj = createObj()

  val Arguments_Obj = createInitFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      lazy val argsObj = σ.getObj(argArrayAddr.as.head, Str.⊥)
      lazy val calledAsConstr = argsObj.intern.getOrElse(
        Fields.constructor, false).asInstanceOf[Boolean]
      assert(calledAsConstr, "Arguments should never be called as a function")
      makeState(selfAddr, x, ρ, σ, ß, κ, τ)
    }),
    fields = Map(
        "prototype" → Address.inject(Object_prototype_Addr),
        "length" → Num.inject(Num.α(0))))

}
