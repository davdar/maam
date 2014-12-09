// notJS init state: Typed Arrays

package notjs.abstracted.init

import notjs.syntax._
import notjs.abstracted.domains._
import notjs.abstracted.init.InitHelpers._
import notjs.abstracted.init.StringHelpers._
import notjs.abstracted.traces.Trace
import notjs.abstracted.domains.AddressSpace._
import notjs.abstracted.init.Init._
import notjs.abstracted.helpers.Fields
import notjs.abstracted.helpers.Helpers._
import notjs.abstracted.init.StringHelpers._

object InitTypedArrays {

  val ArrayBuffer_Obj = createInitFunctionObj(Native(
      (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
        // TODO: if not called as a constructor, throw a TypeError
        assert(selfAddr.defAddr && selfAddr.as.size == 1, "We don't currently support mixing of ArrayBuffers with other objects")
        assert(argArrayAddr.defAddr && argArrayAddr.as.size == 1, "Arguments array refers to non-addresses or multiple addresses")
        val argsObj = σ.getObj(argArrayAddr.as.head, Str.α("0"))

        val input = argsObj(Str.α("0")).getOrElse(Num.inject(Num.Zero))
        // we should not throw an exception because selfAddr.defAddr
        val oldObj = σ getObj (selfAddr.as.head, Str.⊥)
        // we join Num.Zero with Undef, because we don't know if the access will be within limits
        val updatedObj = newArrayBuffer(input, oldObj)
        makeState(selfAddr, x, ρ, σ.putObj(selfAddr.as.head, updatedObj), ß, κ, τ)
      }
    ), Map(
      "prototype" → Address.inject(ArrayBuffer_prototype_Addr),
      "length" → Num.inject(Num.α(1))))

  def createTypedArrayObj(proto: Address, name: String) = 
    createInitFunctionObj(Native(
        (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
          assert(selfAddr.defAddr && selfAddr.as.size == 1, 
            "We don't currently support mixing of %s with other objects".format(name))
          val oldObj = σ getObj(selfAddr.as.head, Str.⊥)
          val updatedObj = newArray(NReal, List(), Some(Num.inject(NReal)), oldObj, true)
          makeState(selfAddr, x, ρ, σ.putObj(selfAddr.as.head, updatedObj), ß, κ, τ)
        }
      ), Map(
        "prototype" → Address.inject(proto),
        "length" → Num.inject(Num.U32)))


  val Int8Array_Obj = createTypedArrayObj(Int8Array_prototype_Addr, "Int8Array")

  val Uint8Array_Obj = createTypedArrayObj(Uint8Array_prototype_Addr, "Uint8Array")

  val Int16Array_Obj = createTypedArrayObj(Int16Array_prototype_Addr, "Int16Array")

  val Uint16Array_Obj = createTypedArrayObj(Uint16Array_prototype_Addr, "Uint16Array")

  val Int32Array_Obj = createTypedArrayObj(Int32Array_prototype_Addr, "Int32Array")

  val Uint32Array_Obj = createTypedArrayObj(Uint32Array_prototype_Addr, "Uint32Array")

  val Float32Array_Obj = createTypedArrayObj(Float32Array_prototype_Addr, "Float32Array")

  val Float64Array_Obj = createTypedArrayObj(Float64Array_prototype_Addr, "Float64Array")

  val ArrayBuffer_prototype_Obj = createObj()

  val Int8Array_prototype_Obj = createInitObj( Map(
    "set" → Address.inject(Int8Array_prototype_set_Addr),
    "subarray" → Address.inject(Int8Array_prototype_subarray_Addr)))

  val Uint8Array_prototype_Obj = createInitObj( Map(
    "set" → Address.inject(Uint8Array_prototype_set_Addr),
    "subarray" → Address.inject(Uint8Array_prototype_subarray_Addr)))

  val Int16Array_prototype_Obj = createInitObj( Map(
    "set" → Address.inject(Int16Array_prototype_set_Addr),
    "subarray" → Address.inject(Int16Array_prototype_subarray_Addr)))

  val Uint16Array_prototype_Obj = createInitObj( Map(
    "set" → Address.inject(Uint16Array_prototype_set_Addr),
    "subarray" → Address.inject(Uint16Array_prototype_subarray_Addr)))

  val Int32Array_prototype_Obj = createInitObj( Map(
    "set" → Address.inject(Int32Array_prototype_set_Addr),
    "subarray" → Address.inject(Int32Array_prototype_subarray_Addr)))

  val Uint32Array_prototype_Obj = createInitObj( Map(
    "set" → Address.inject(Uint32Array_prototype_set_Addr),
    "subarray" → Address.inject(Uint32Array_prototype_subarray_Addr)))

  val Float32Array_prototype_Obj = createInitObj( Map(
    "set" → Address.inject(Float32Array_prototype_set_Addr),
    "subarray" → Address.inject(Float32Array_prototype_subarray_Addr)))

  val Float64Array_prototype_Obj = createInitObj( Map(
    "set" → Address.inject(Float64Array_prototype_set_Addr),
    "subarray" → Address.inject(Float64Array_prototype_subarray_Addr)))

  def createTypedArraySetFunction = createInitFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      makeState(Undef.BV, x, ρ, σ, ß, κ, τ)
    }), Map(
      "length" → Num.inject(Num.U32)))

  def createTypedArraySubarrayFunction(prototype: Address) = createInitFunctionObj(Native(
    (selfAddr: BValue, argArrayAddr: BValue, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack, τ:Trace) ⇒ {
      assert(selfAddr.defAddr && selfAddr.as.size == 1, "We don't currently support mixing of Int8Array with other objects")
      val (σ1, subarrBV) = allocObj(Address.inject(Object_Addr), τ.toAddr, σ, τ)
      val oldObj = σ1 getObj (subarrBV.as.head, Str.⊥)
      val updatedObj = newArray(NReal, List(), Some(Num.inject(NReal)), oldObj, true)
      makeState(subarrBV, x, ρ, σ1.putObj(subarrBV.as.head, updatedObj), ß, κ, τ)
    }
  ), Map(
    "prototype" → Address.inject(prototype),
    "length" → Num.inject(Num.U32)))

  val Int8Array_prototype_set_Obj = createTypedArraySetFunction
  val Int8Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Int8Array_prototype_Addr)
  
  val Uint8Array_prototype_set_Obj = createTypedArraySetFunction
  val Uint8Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Uint8Array_prototype_Addr)

  val Int16Array_prototype_set_Obj = createTypedArraySetFunction
  val Int16Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Int16Array_prototype_Addr)

  val Uint16Array_prototype_set_Obj = createTypedArraySetFunction
  val Uint16Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Uint16Array_prototype_Addr)

  val Int32Array_prototype_set_Obj = createTypedArraySetFunction
  val Int32Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Int32Array_prototype_Addr)

  val Uint32Array_prototype_set_Obj = createTypedArraySetFunction
  val Uint32Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Uint32Array_prototype_Addr)

  val Float32Array_prototype_set_Obj = createTypedArraySetFunction
  val Float32Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Float32Array_prototype_Addr)

  val Float64Array_prototype_set_Obj = createTypedArraySetFunction
  val Float64Array_prototype_subarray_Obj = createTypedArraySubarrayFunction(Float64Array_prototype_Addr)
}