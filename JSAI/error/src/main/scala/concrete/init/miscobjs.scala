// notJS initial state: Misc Objects

package notjs.concrete.init

import notjs.syntax._
import notjs.concrete.domains._
import notjs.concrete.interpreter.State
import notjs.concrete.helpers.Fields
import notjs.concrete.helpers.Errors._
import notjs.concrete.helpers.Helpers._

import notjs.concrete.init.Init._
import notjs.concrete.init.InitHelpers._


object InitMisc {

  val Boolean_Obj = makeNativeValueStore(
    (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
      val argsObj = σ.getObj(argArrayAddr)
      val calledAsConstr = argsObj.intern.getOrElse(Fields.constructor, false).asInstanceOf[Boolean]
      val boolValue: BValue = argsObj(Str("0")) match {
        case Some(v) ⇒ v.tobool
        case None ⇒ Bool(false)
      }

      if (calledAsConstr) {
        val newAddr = Address()
        val newObj = createObj(Map(), Map(
          Fields.proto → Boolean_prototype_Addr,
          Fields.classname → CBoolean,
          Fields.value → boolValue
        ))

        val newσ = σ.putObj(newAddr, newObj)
        (newAddr, newσ)
      }
      else {
        (boolValue, σ)
      }
    },
    Map(
      Str("prototype") → Boolean_prototype_Addr,
      Str("length") → Num(1)
    )
  )

  val Boolean_prototype_Obj = createObj(Map(
    Str("toString") → Boolean_prototype_toString_Addr,
    Str("valueOf") → Boolean_prototype_valueOf_Addr
  ))

  val Boolean_prototype_toString_Obj = makeNativeValue(
    (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
      val selfObj = σ.getObj(selfAddr)

      selfObj.getJSClass match {
        case CBoolean ⇒ { // since the class is boolean, it must have an internal value field
          selfObj.getValue match {
            case Some(Bool(true)) ⇒ Str("true")
            case Some(Bool(false)) ⇒ Str("false")
            case _ ⇒ sys.error("We should not have a non-boolean as a Boolean's internal value")
          }
        }
        case _ ⇒ typeError
      }
    }, 
    Map(Str("length") → Num(0)))

  val Boolean_prototype_valueOf_Obj = makeNativeValue(
    (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
      val selfObj = σ.getObj(selfAddr)

      selfObj.getJSClass match {
        case CBoolean ⇒ { // since the class is boolean, it must have an internal value field
          selfObj.getValue match {
            case Some(Bool(x)) ⇒ Bool(x)
            case _ ⇒ sys.error("We should not have a non-boolean as a Boolean's internal value")
          }
        }
        case _ ⇒ typeError
      }
    }, 
    Map(Str("length") → Num(0)))

  val Error_Obj = createFunctionObj(Native(
      (selfAddr: Address, argArrayAddr: Address, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack) ⇒ {
        sys.error("!! Not Implemented")
      }
    ),
    Map(
      Str("prototype") → Error_prototype_Addr,
      Str("length") → Num(1)
    )
  )

  val Error_prototype_Obj = createObj(Map(
    Str("constructor") → Error_Addr,
    Str("name") → Str("Error"),
    Str("message") → Str(""),
    Str("toString") → Error_prototype_toString_Addr
  ))

  val Error_prototype_toString_Obj = unimplemented


  val JSON_Obj = createObj(Map(
    Str("parse") → JSON_parse_Addr,
    Str("stringify") → JSON_stringify_Addr
  ))

  val JSON_parse_Obj = unimplemented

  val JSON_stringify_Obj = unimplemented

  val Date_Obj = createFunctionObj(Native(
      (selfAddr: Address, argArrayAddr: Address, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack) ⇒ {
        sys.error("!! Not Implemented")
      }
    ), Map(
      Str("now") → Date_now_Addr,
      Str("parse") → Date_parse_Addr,
      Str("prototype") → Date_prototype_Addr,
      Str("length") → Num(7)
    )
  )

  val Date_now_Obj = unimplemented

  val Date_parse_Obj = unimplemented

  val Date_prototype_Obj = createObj(Map( // TODO: the rest of this.
    Str("constructor") → Date_Addr
  ))

  val RegExp_Obj = createFunctionObj(Native(
      (selfAddr: Address, argArrayAddr: Address, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack) ⇒ {
        sys.error("!! Not Implemented")
      }
    ), Map(
      Str("prototype") → RegExp_prototype_Addr,
      Str("length") → Num(0)
    )
  )

  val RegExp_prototype_Obj = createObj(Map())




}
