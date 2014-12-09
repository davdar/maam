// notJS initial state: Arguments

package notjs.concrete.init

import notjs.syntax._
import notjs.concrete.domains._
import notjs.concrete.interpreter.State
import notjs.concrete.helpers.Fields
import notjs.concrete.helpers.Errors._
import notjs.concrete.helpers.Helpers._

import notjs.concrete.init.Init._
import notjs.concrete.init.InitHelpers._


object InitArguments {

    val Arguments_Obj = createFunctionObj(Native(
      (selfAddr: Address, argArrayAddr: Address, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack) ⇒ {
        makeState(selfAddr, x, ρ, σ, ß, κ)
      }
    ), external = Map(Str("prototype") → Object_prototype_Addr, Str("length") → Num(0)))

}
