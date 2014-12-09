// notJS initial state: Number

package notjs.concrete.init

import notjs.syntax._
import notjs.concrete.domains._
import notjs.concrete.interpreter.State
import notjs.concrete.helpers.Fields
import notjs.concrete.helpers.Errors._
import notjs.concrete.helpers.Helpers._

import notjs.concrete.init.Init._
import notjs.concrete.init.InitHelpers._


object InitNumber {


  val Number_Obj = makeNativeValueStore(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val argsObj = σ.getObj(argArrayAddr)
        val arglen = argsObj(Str("length")) match { // Here and elsewhere I'm trusting that arguments.length does not require prototype lookup
          case Some(Num(n)) ⇒ n
          case _ ⇒ sys.error("inconceivable: args without length")
        }
        val calledAsConstr = argsObj.intern.getOrElse(Fields.constructor, false).asInstanceOf[Boolean] // true iff invoking as a constructor

        val pvalue: Num = if (arglen == 0) Num(0) else ToNumber(argsObj(Str("0")).get, σ)
        
        if(calledAsConstr) {
          val newAddr = Address()
          val newObj = createObj(Map(), Map(
            Fields.proto → Number_prototype_Addr,
            Fields.classname → CNumber,
            Fields.value → pvalue
          ))
          
          val newσ = σ.putObj(newAddr, newObj)
          (newAddr, newσ)
        }
        else {
          (pvalue, σ)
        }
      },
    Map(
      Str("prototype") → Number_prototype_Addr,
      Str("length") → Num(1),
      Str("MAX_VALUE") → Num(Double.MaxValue),
      Str("MIN_VALUE") → Num(Double.MinValue),
      Str("NaN") → Num(Double.NaN),
      Str("NEGATIVE_INFINITY") → Num(Double.PositiveInfinity),
      Str("POSITIVE_INFINITY") → Num(Double.NegativeInfinity)
    ),
    myclass = CNumber_Obj
  )

  val Number_prototype_Obj = createObj(Map(
    Str("constructor") → Number_Addr,
    Str("toString") → Number_prototype_toString_Addr,
    Str("toLocaleString") → Number_prototype_toLocaleString_Addr,
    Str("valueOf") → Number_prototype_valueOf_Addr,
    Str("toFixed") → Number_prototype_toFixed_Addr,
    Str("toExponential") → Number_prototype_toExponential_Addr,
    Str("toPrecision") → Number_prototype_toPrecision_Addr
  ), internal = Map(Fields.classname → CNumber_prototype_Obj)
  )

  val Number_prototype_toString_Obj = makeNativeValue(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val self = σ.getObj(selfAddr)
        
        self.getJSClass match { // TypeError if this is not a Number object
          case CNumber ⇒ {
            val args = σ.getObj(argArrayAddr)
            
            val arglen = args(Str("length")) match { // Here and elsewhere I'm trusting that arguments.length does not require prototype lookup
              case Some(Num(n)) ⇒ n
              case _ ⇒ sys.error("inconceivable")
            } 
            val radix = if (arglen == 0) 10 else (args(Str("0")).get match {
              case Num(n) if n==10 ⇒ 10
              case Undef ⇒ 10
              case Num(n) if n>=2 && n<=36 ⇒ sys.error("!! Not Implemented")
              case _ ⇒ -1
            })
            if(radix == -1) rangeError // TODO: probably a cleaner way of doing this
            else {
              self.getValue match {
                case Some(n:Num) ⇒ n.tostr
                case _ ⇒ sys.error("inconceivable: Number without a number value")
              }
            }
          }
          case _ ⇒ typeError
        }
      }, Map(Str("length") → Num(1))
    )

  val Number_prototype_toLocaleString_Obj = unimplemented

  val Number_prototype_valueOf_Obj = makeNativeValue(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val self = σ.getObj(selfAddr)
        self.getJSClass match { // TypeError if this is not a Number object
          case CNumber ⇒ self.getValue.get
          case _ ⇒ typeError
        }
      }, Map(Str("length") → Num(0))
    )

  val Number_prototype_toFixed_Obj = unimplemented

  val Number_prototype_toExponential_Obj = unimplemented

  val Number_prototype_toPrecision_Obj = unimplemented


}
