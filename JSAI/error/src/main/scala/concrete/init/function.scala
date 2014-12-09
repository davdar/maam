// notJS initial state: Function

package notjs.concrete.init

import notjs.syntax._
import notjs.concrete.domains._
import notjs.concrete.interpreter.State
import notjs.concrete.helpers.Fields
import notjs.concrete.helpers.Errors._
import notjs.concrete.helpers.Helpers._

import notjs.concrete.init.Init._
import notjs.concrete.init.InitHelpers._


object InitFunction {

  val Function_Obj = createFunctionObj(Native(
      (selfAddr: Address, argArrayAddr: Address, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack) ⇒ {
        sys.error("!! Won't implement: Function() is eval()")
      }
    ),
    Map(
      Str("prototype") → Function_prototype_Addr,
      Str("length") → Num(1)
    ), myclass = CFunction_Obj
  )

  val Function_prototype_Obj = Object(Map(
      Str("constructor") → Function_Addr,
      Str("apply") → Function_prototype_apply_Addr,
      Str("call") → Function_prototype_call_Addr,
      Str("toString") → Function_prototype_toString_Addr,
      Str("length") → Num(0)
    ), Map(Fields.proto → Object_prototype_Addr, Fields.classname → CFunction_prototype_Obj, Fields.code → Native( 
      (selfAddr: Address, argArrayAddr: Address, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack) ⇒ {
        makeState(Undef, x, ρ, σ, ß, κ)
      }
    ))
  )

  val Function_prototype_apply_Obj = createFunctionObj(Native(
      (selfAddr: Address, argArrayAddr: Address, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack) ⇒ {
            
        val argsObj = σ.getObj(argArrayAddr)

        // Build the new Arguments object
        val external: Option[Map[Str, BValue]] = argsObj(Str("1")) match { // Option because typeerrors.
          case None | Some(Undef) | Some(Null) ⇒ Some(Map(Str("length") → Num(0)))
          case Some(a:Address) ⇒ {
            val passedArgsObj = σ.getObj(a)
            passedArgsObj.getJSClass match {
              case CArray | CArguments ⇒ { // TODO: make this isArrayClass
                val arglen = passedArgsObj(Str("length")) match {
                  case Some(Num(n)) ⇒ n
                  case _ ⇒ sys.error("inconceivable: array or arguments object with non-numeric length")
                }
                Some(
                  (0 until arglen.toInt).foldLeft(Map[Str, BValue](Str("length") → Num(arglen)))(
                    (m:Map[Str, BValue],i:Int) ⇒ (m + (Str(i.toString) → (passedArgsObj(Str(i.toString)).get)))
                  )
                )
              }
              case _ ⇒ None
            }
          }
          case _ ⇒ None
        }
        external match {
          case None ⇒ makeState(typeError, x, ρ, σ, ß, κ)
          case Some(extm) ⇒ {

            val newArgsAddr = Address()
            val newObj = createObj(extm, Map( 
              Fields.proto → Object_prototype_Addr,
              Fields.classname → CArguments
            ))

            val (newThisAddr, σ1) = argsObj(Str("0")) match {
              case None | Some(Undef) | Some(Null) ⇒ (window_Addr, σ)
              // we can be sure that type error is not by ToObject below, because 
              // ToObject returns type error on Undef and Null handled above
              // just to be sure we assert it below
              case Some(v) ⇒ ToObject(v, σ)
            }
            assert(newThisAddr.isInstanceOf[Address], "this passed cannot be converted to address, should have been an infeasible program path")

            val σ2 = σ1.putObj(newArgsAddr, newObj)
            applyClo(selfAddr, newThisAddr.asInstanceOf[Address], newArgsAddr, x, ρ, σ2, ß, κ)
          }
        }
      }
    ),
    Map(
      Str("length") → Num(2)
    )
  )

  val Function_prototype_call_Obj = createFunctionObj(Native(
    (selfAddr: Address, argArrayAddr: Address, x: Var, ρ: Env, σ: Store, ß:Scratchpad, κ: KStack) ⇒ {

      val argsObj = σ.getObj(argArrayAddr)

      val arglen = argsObj(Str("length")) match {
        case Some(Num(n)) ⇒ n
        case _ ⇒ sys.error("inconceivable: arguments object with non-numeric length")
      }
      
      val (newThisAddr, σ1) = argsObj(Str("0")) match {
        case None | Some(Undef) | Some(Null) ⇒ (window_Addr, σ)
        // we can be sure that type error is not by ToObject below, because 
        // ToObject returns type error on Undef and Null handled above
        // just to be sure we assert it below
        case Some(v) ⇒ ToObject(v, σ) 
      }
      assert(newThisAddr.isInstanceOf[Address], "this passed cannot be converted to address, should have been an infeasible program path")

      // Build the new Arguments object
      val external: Map[Str, BValue] =
        (1 until arglen.toInt).foldLeft(Map[Str, BValue](Str("length") → Num(arglen-1)))(
          (m:Map[Str, BValue], i:Int) ⇒ (m + (Str((i-1).toString) → (argsObj(Str(i.toString)).get)))
        )
      val newArgsAddr = Address()
      val newObj = createObj(external, Map( 
        Fields.proto → Object_prototype_Addr,
        Fields.classname → CArguments
      ))

      val σ2 = σ1.putObj(newArgsAddr, newObj)
      applyClo(selfAddr, newThisAddr.asInstanceOf[Address], newArgsAddr, x, ρ, σ2, ß, κ)
    }),
    Map(
      Str("length") → Num(1)
    )
  )

  val Function_prototype_toString_Obj = unimplemented


}
