// notJS initial state: String

package notjs.concrete.init

import notjs.syntax._
import notjs.concrete.domains._
import notjs.concrete.interpreter.State
import notjs.concrete.helpers.Fields
import notjs.concrete.helpers.Errors._
import notjs.concrete.helpers.Helpers._

import notjs.concrete.init.Init._
import notjs.concrete.init.InitHelpers._


object InitString {


  val String_Obj = makeNativeValueStore(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val argsObj = σ.getObj(argArrayAddr)
        val arglen = argsObj(Str("length")) match { // Here and elsewhere I'm trusting that arguments.length does not require prototype lookup
          case Some(Num(n)) ⇒ n
          case _ ⇒ sys.error("inconceivable: args without length")
        }
        val calledAsConstr = argsObj.intern.getOrElse(Fields.constructor, false).asInstanceOf[Boolean] // true iff invoking as a constructor

        val pvalue: Str = if (arglen == 0) Str("") else ToString(argsObj(Str("0")).getOrElse(Undef), σ)
        
        if(calledAsConstr) {
          val strmap = List.range(0, pvalue.str.length).foldLeft(Map[Str, BValue](Fields.length → Num(pvalue.str.length)))(
                        (acc, e) ⇒ acc + (Str(e.toString) → Str(pvalue.str(e).toString)))

          val newObj = createObj(strmap, Map(
            Fields.proto → String_prototype_Addr,
            Fields.classname → CString,
            Fields.value → pvalue
          ))
          
          val newσ = σ.putObj(selfAddr, newObj)
          (selfAddr, newσ)
        }
        else {
          (pvalue, σ)
        }
      },
    Map(
      Str("prototype") → String_prototype_Addr,
      Str("length") → Num(1),
      Str("fromCharCode") → String_fromCharCode_Addr
    ), myclass = CString_Obj
  )

  val String_fromCharCode_Obj = makeNativeValue(
    (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
      val args = σ.getObj(argArrayAddr)

      val arglen = args(Str("length")) match {
        case Some(Num(n)) ⇒ n.toInt
        case _ ⇒ sys.error("inconceivable: arguments without numeric length")
      }
      // TODO: There needs to be a ToUInt16, in principle
      val result = (0 until arglen).foldLeft("")((acc, k) ⇒ {
        acc + ToNumber(args(Str(k.toString)).getOrElse(Undef), σ).n.toChar
      })

      Str(result)

    }, Map(Str("length") → Num(1))
  )

  val String_prototype_Obj = createObj(Map(
    Str("constructor") → String_Addr,
    Str("charAt") → String_prototype_charAt_Addr,
    Str("charCodeAt") → String_prototype_charCodeAt_Addr,
    Str("concat") → String_prototype_concat_Addr,
    Str("indexOf") → String_prototype_indexOf_Addr,
    Str("lastIndexOf") → String_prototype_lastIndexOf_Addr,
    Str("localeCompare") → String_prototype_localeCompare_Addr,
    Str("match") → String_prototype_match_Addr,
    Str("replace") → String_prototype_replace_Addr,
    Str("search") → String_prototype_search_Addr,
    Str("slice") → String_prototype_slice_Addr,
    Str("split") → String_prototype_split_Addr,
    Str("substr") → String_prototype_substr_Addr,
    Str("substring") → String_prototype_substring_Addr,
    Str("toLocaleLowerCase") → String_prototype_toLocaleLowerCase_Addr,
    Str("toLocaleUpperCase") → String_prototype_toLocaleUpperCase_Addr,
    Str("toLowerCase") → String_prototype_toLowerCase_Addr,
    Str("toString") → String_prototype_toString_Addr,
    Str("toUpperCase") → String_prototype_toUpperCase_Addr,
    Str("trim") → String_prototype_trim_Addr,
    Str("valueOf") → String_prototype_valueOf_Addr
  ), internal = Map(Fields.classname → CString_Obj))


  val String_prototype_charAt_Obj = makeNativeValue(
    (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val args = σ.getObj(argArrayAddr)

        val selfStr = ToString(selfAddr, σ).str
        val pos = args(Str("0")) match {
          case Some(x) => ToNumber(x, σ).n.toInt
          case None ⇒ 0
        }

        val charAt = if (pos >= 0 && pos < selfStr.length) selfStr(pos).toString
                     else ""
        Str(charAt)             
      }, Map(Str("length") → Num(1))
  )

  val String_prototype_charCodeAt_Obj = makeNativeValue(
    (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val args = σ.getObj(argArrayAddr)

        val selfStr = ToString(selfAddr, σ).str
        val pos = args(Str("0")) match {
          case Some(x) => ToNumber(x, σ).n.toInt
          case None ⇒ 0
        }

        val charCodeAt = if (pos >= 0 && pos < selfStr.length) Num(selfStr(pos).toInt)
                     else Num(Double.NaN) 

        charCodeAt
      }, Map(Str("length") → Num(1))
  )

  val String_prototype_concat_Obj = makeNativeValue(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val args = σ.getObj(argArrayAddr)

        val arglen = args(Str("length")) match { // Here and elsewhere I'm trusting that arguments.length does not require prototype lookup
          case Some(Num(n)) ⇒ n
          case _ ⇒ sys.error("inconceivable: arguments without numeric length")
        }
        
        (0 until arglen.toInt).foldLeft(ToString(selfAddr, σ))( (s:Str, i:Int) ⇒ s ++ ToString(args(Str(i.toString)).getOrElse(Undef), σ) )

      }, Map(Str("length") → Num(1))
  )

  val String_prototype_indexOf_Obj = approx_num

  val String_prototype_lastIndexOf_Obj = approx_num
  
  val String_prototype_localeCompare_Obj = unimplemented

  val String_prototype_match_Obj = approx_array

  val String_prototype_replace_Obj = approx_str

  val String_prototype_search_Obj = approx_num

  val String_prototype_slice_Obj = approx_str

  val String_prototype_split_Obj = approx_array

  val String_prototype_substr_Obj = approx_str

  val String_prototype_substring_Obj = approx_str

  val String_prototype_toLocaleLowerCase_Obj = unimplemented

  val String_prototype_toLocaleUpperCase_Obj = unimplemented

  val String_prototype_toLowerCase_Obj = unimplemented

  val String_prototype_toString_Obj = makeNativeValue(
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val self = σ.getObj(selfAddr)
        self.getJSClass match { // TypeError if this is not a String object
          case CString | CString_prototype_Obj ⇒ {
            self.getValue match {
              case Some(s:Str) ⇒ s
              case _ ⇒ sys.error("inconceivable: String without a string value")
            }
          }
          case _ ⇒ typeError
        }
      }, Map(Str("length") → Num(0))
    )

  val String_prototype_toUpperCase_Obj = unimplemented

  val String_prototype_trim_Obj = unimplemented

  val String_prototype_valueOf_Obj = makeNativeValue( // TODO: same as toString
      (selfAddr: Address, argArrayAddr: Address, σ: Store) ⇒ {
        val self = σ.getObj(selfAddr)
        self.getJSClass match { // TypeError if this is not a String object
          case CString | CString_prototype_Obj ⇒ {
            self.getValue match {
              case Some(s:Str) ⇒ s
              case _ ⇒ sys.error("inconceivable: String without a string value")
            }
          }
          case _ ⇒ typeError
        }
      }, Map(Str("length") → Num(0))
    )


}
