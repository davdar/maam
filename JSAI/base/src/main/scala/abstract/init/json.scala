// initial notJS state: JSON

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.traces.Trace
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.helpers.Errors._
import notjs.abstracted.init.Init._
import notjs.abstracted.init.InitHelpers._
import notjs.abstracted.init.StringHelpers._

object InitJSON {

  val JSON_Obj =  createInitObj(Map(
    "parse" → Address.inject(JSON_parse_Addr),
    "stringify" → Address.inject(JSON_stringify_Addr)
  )) // TODO: JSON class

  /* TODO: some arguments to JSON methods can be arbitrary callable user code
     and the stringification walk can call user code methods within the objects
     it traverses. */

  /* the result of parsing JSON is one of:
     * a SyntaxError
     * an unknown object or array (make weak so we can have self-reference for subfields which are objects)
     * an unknown string, number, boolean, or null */
  val Internal_JSON_parse =
    (_ : List[BValue], x: Var, ρ: Env, σ: Store, ß: Scratchpad, κ: KStack, τ: Trace) ⇒ {
      val errς = makeState(syntaxError, x, ρ, σ, ß, κ, τ)

      val (σ1, unkObj_addr_bv) = allocObj(Addresses.inject(Set(Object_Addr, Array_Addr)), τ.toAddr, σ, τ)
      assert(unkObj_addr_bv.as.size == 1, "JSON.parse: Freshly-allocated address set should be singleton")
      val unkObj_addr = unkObj_addr_bv.as.head

      val res_bv = unkObj_addr_bv ⊔ Str.inject(STop) ⊔ Num.inject(NTop) ⊔ Bool.inject(BTop) ⊔ Null.BV

      val oldObj = σ1 getObj unkObj_addr
      val unkObj = oldObj copy (
        extern = oldObj.extern copy (top = Some(res_bv))
      )

      val σ2 = σ1.putObj(unkObj_addr, unkObj) copy (weak = σ1.weak + unkObj_addr)
      val resς = makeState(res_bv, x, ρ, σ2, ß, κ, τ)

      errς ++ resς
    }
  val JSON_parse_Obj = createInitFunctionObj(
    Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        assert(argArrayAddr.defAddr, "JSON.parse: Arguments array refers to non-addresses")
        assert(argArrayAddr.as.size == 1, "JSON.parse: Arguments array refers to multiple addresses")
        val argsArray = σ.getObj(argArrayAddr.as.head)

        val text = argsArray(Str.α("0")) getOrElse Undef.BV

        /* TODO: not currently handling second `reviver` argument
           as it can be a user function */
        if (argsArray(Str.α("1")).nonEmpty)
          sys.error("JSON.parse: `reviver` argument not supported")

        ToString(List(text), Internal_JSON_parse, x, ρ, σ, ß, κ, τ)
      }
    ),
    Map("length" → Num.inject(Num.α(2)))
  )

  /* NB: implicit conversion behavior of the third `space` argument is more complex than
     a simple string conversion, but when only converting for side-effects, as we are,
     this should not matter. */
  val JSON_stringify_Obj =
    constFunctionObj(ezSig(NoConversion, List(NoConversion, NoConversion, StringHint)),
      Str.inject(STop))

}
