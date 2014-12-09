// notJS initial state: Object

package notjs.concrete.init

import notjs.syntax._
import notjs.concrete.domains._
import notjs.concrete.interpreter.State
import notjs.concrete.helpers.Fields
import notjs.concrete.helpers.Errors._
import notjs.concrete.helpers.Helpers._

import notjs.concrete.init.Init._
import notjs.concrete.init.InitHelpers._


object InitObject {


  val Object_Obj = makeNativeValueStore(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val args = σ.getObj(argArrayAddr)
        val input = args(Str("0")).getOrElse(Undef)
        
        input match {
          case Null | Undef ⇒ {
            val newAddr = Address()
            val newObj = createObj(Map())
            val newσ = σ.putObj(newAddr, newObj)
            (newAddr, newσ)
          }
          case _ ⇒ ToObject(input, σ)  // The spec allows implementation-defined different behavior for 'host' objects. We don't do that.
        }
      },
    Map(
      Str("prototype") → Object_prototype_Addr,
      Str("create") → Object_create_Addr,
      Str("defineProperties") → Object_defineProperties_Addr,
      Str("defineProperty") → Object_defineProperty_Addr,
      Str("freeze") → Object_freeze_Addr,
      Str("getOwnPropertyDescriptor") → Object_getOwnPropertyDescriptor_Addr,
      Str("getOwnPropertyNames") → Object_getOwnPropertyNames_Addr,
      Str("getPrototypeOf") → Object_getPrototypeOf_Addr,
      Str("isExtensible") → Object_isExtensible_Addr,
      Str("isFrozen") → Object_isFrozen_Addr,
      Str("isSealed") → Object_isSealed_Addr,
      Str("keys") → Object_keys_Addr,
      Str("length") → Num(1),
      Str("preventExtensions") → Object_preventExtensions_Addr,
      Str("seal") → Object_seal_Addr
    ), myclass = CObject_Obj
    )

  val Object_prototype_Obj = Object(Map(
    Str("constructor") → Object_Addr,
    Str("valueOf") → Object_prototype_valueOf_Addr,
    Str("toString") → Object_prototype_toString_Addr,
    Str("isPrototypeOf") → Object_prototype_isPrototypeOf_Addr,
    Str("propertyIsEnumerable") → Object_prototype_propertyIsEnumerable_Addr,
    Str("hasOwnProperty") → Object_prototype_hasOwnProperty_Addr,
    Str("toLocaleString") → Object_prototype_toLocaleString_Addr
  ), Map(Fields.proto → Null, Fields.classname → CObject_prototype_Obj))

  val Object_create_Obj = unimplemented

  val Object_defineProperties_Obj = unimplemented

  val Object_defineProperty_Obj = unimplemented

  val Object_freeze_Obj = unimplemented

  val Object_getOwnPropertyDescriptor_Obj = unimplemented

  val Object_getOwnPropertyNames_Obj = unimplemented

  val Object_getPrototypeOf_Obj = unimplemented

  val Object_isExtensible_Obj = unimplemented

  val Object_isFrozen_Obj = unimplemented

  val Object_isSealed_Obj = unimplemented

  val Object_keys_Obj = unimplemented

  val Object_preventExtensions_Obj = unimplemented

  val Object_seal_Obj = unimplemented

  val Object_prototype_toString_Obj = makeNativeValue(
    (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
      val selfObj = σ.getObj(selfAddr)
      Object_toString_helper(selfObj)
    }, Map(Str("length") → Num(0))
  )

  val Object_prototype_valueOf_Obj = makeNativeValue(
    (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
      selfAddr // Allowed to differ (implementation defined) for host objects.
    }, Map(Str("length") → Num(0))
  )

  val Object_prototype_isPrototypeOf_Obj = unimplemented

  val Object_prototype_propertyIsEnumerable_Obj = unimplemented

  val Object_prototype_hasOwnProperty_Obj = makeNativeValue(
   (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
      val args = σ.getObj(argArrayAddr)
      val input = args(Str("0")).getOrElse(Undef)
      val istr = ToString(input, σ)        
      val selfObj = σ.getObj(selfAddr)
      if (selfObj.extern.keySet(istr)) Bool.True else Bool.False
    }, Map(Str("length") → Num(0)) 
  )

  val Object_prototype_toLocaleString_Obj = unimplemented


}
