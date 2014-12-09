package notjs.tester.abstracted
import notjs.abstracted.{domains ⇒ adomains}
import notjs.concrete.{domains ⇒ cdomains}

object TestHelpers {
  def isDouble(x: String) = {
    try {
      x.toDouble
      true
    } catch {
      case e: java.lang.NumberFormatException ⇒ false 
    }
  }

  def overapproximates(abstracted: adomains.BValue, concrete: cdomains.BValue): Boolean = {
    concrete match {
      case cdomains.Num(n) ⇒ abstracted.n match {
        case adomains.NBot ⇒ false
        case adomains.NConst(n1) ⇒ (n == n1) || (n.isNaN && n1.isNaN)
        case adomains.NReal ⇒ !n.isNaN && !n.isInfinity
        case adomains.NTop ⇒ true
      }
      case cdomains.Bool(b) ⇒ abstracted.b match {
        case adomains.BBot ⇒ false
        case adomains.BTrue ⇒ b == true
        case adomains.BFalse ⇒ b == false
        case adomains.BTop ⇒ true
      }
      case cdomains.Str(str) ⇒ abstracted.str match {
        case adomains.SBot ⇒ false
        case adomains.STop ⇒ true
        case adomains.SNotSpl ⇒ !adomains.Str.SplStrings(str)
        case adomains.SNotNum ⇒ !isDouble(str)
        case adomains.SNum ⇒ isDouble(str)
        case adomains.SNotSplNorNum ⇒ !adomains.Str.SplStrings(str) && !isDouble(str)
        case adomains.SSpl ⇒ adomains.Str.SplStrings(str)
        case adomains.SConstNum(str1) ⇒ str == str1
        case adomains.SConstNotSplNorNum(str1) ⇒ str == str1
        case adomains.SConstSpl(str1) ⇒ str == str1
      }
      case cdomains.Address(a) ⇒ abstracted.as.size > 0 
      case cdomains.Null ⇒ abstracted.nil == adomains.Null.⊤
      case cdomains.Undef ⇒ abstracted.undef == adomains.Undef.⊤
    }
  }

}