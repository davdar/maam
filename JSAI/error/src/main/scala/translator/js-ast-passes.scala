package notjs.translator.jsast

import notjs.translator._
import notjs.translator.PVarMapper.{selfName, windowName,
                                    WINDOW_NAME, ARGUMENTS_NAME}

object TransformationHelpers {
  def toToplevelDecl(j: JSAST): JSToplevelDecl =
    j match {
      case t: JSToplevelDecl => t
      case _ => throw BadTransformation("Expected a toplevel decl but got: " + j)
    }
  
  def toStmt(j: JSAST): JSStmt =
    j match {
      case s: JSStmt => s
      case _ => throw BadTransformation("Expected a statement but got: " + j)
    }

  def updateGlobally(str: String, e: JSExp): JSSimpleUpdate =
    JSSimpleUpdate(JSAccess(JSPVar(windowName), JSStr(str)), e)
}
import TransformationHelpers._

trait JSTransformHelpers[D, U] extends TransformBase[JSAST, D, U] {
  def transformExp(j: JSAST, t1: D): (JSExp, U) =
    transform(j, t1) match {
      case (e: JSExp, t2) => (e, t2)
      case (a, _) => throw BadTransformation("Expected an expression but got: " + a)
    }

  def transformLHS(j: JSAST, t1: D): (JSLHS, U) =
    transform(j, t1) match {
      case (lhs: JSLHS, t2) => (lhs, t2)
      case (a, _) => throw BadTransformation("Expected an LHS but got: " + a)
    }

  def transformStmt(j: JSAST, t1: D): (JSStmt, U) = {
    val (s, t2) = transform(j, t1)
    (toStmt(s), t2)
  }

  def transformVar(j: JSAST, t1: D): (JSVar, U) =
    transform(j, t1) match {
      case (v: JSVar, t2) => (v, t2)
      case (a, _) => throw BadTransformation("Expected any variable but got: " + a)
    }

  def transformPVar(j: JSAST, t1: D): (JSPVar, U) =
    transform(j, t1) match {
      case (v: JSPVar, t2) => (v, t2)
      case (a, _) => throw BadTransformation("Expected a program variable but got: " + a)
    }

  def transformScratch(j: JSAST, t1: D): (JSScratch, U) =
    transform(j, t1) match {
      case (v: JSScratch, t2) => (v, t2)
      case (a, _) => throw BadTransformation("Expected a scratch variable but got: " + a)
    }

  def transformAccess(j: JSAST, t1: D): (JSAccess, U) =
    transform(j, t1) match {
      case (a: JSAccess, t2) => (a, t2)
      case (a, _) => throw BadTransformation("Expected an access but got: " + a)
    }

  def transformString(j: JSAST, t1: D): (JSStr, U) =
    transform(j, t1) match {
      case (s: JSStr, t2) => (s, t2)
      case (a, _) => throw BadTransformation("Expected a string but got: " + a)
    }

  def transformLabel(j: JSAST, t1: D): (JSLabel, U) =
    transform(j, t1) match {
      case (l: JSLabel, t2) => (l, t2)
      case (a, _) => throw BadTransformation("Expected a label but got: " + a)
    }
}
  
// -D is the type of information that is passed down
// -U is the type of information that is passed up
trait JSTransformPass[D, U] extends TransformPass[JSAST, D, U] with JSTransformHelpers[D, U] {
  def defaultTransform(j: JSAST, t: D): (JSAST, U) =
    j match {
      case JSToplevelDecl(vars, rest) =>
        for {
          varsAsts <- toMonad(vars.map(v => transformPVar(v, t)))
          stmtAst <- transformStmt(rest, t)
        } yield JSToplevelDecl(varsAsts, stmtAst)
      case JSRegexp(s, flags) => 
        for {
          ast <- transformString(s, t)
        } yield JSRegexp(ast, flags)
      case JSSimpleAssign(x, rhs) => 
        for {
          xAst <- transformVar(x, t)
          rhsAst <- transformExp(rhs, t)
        } yield JSSimpleAssign(xAst, rhsAst)
      case JSCompoundAssign(x, op, rhs) => 
        for {
          xAst <- transformVar(x, t)
          rhsAst <- transformExp(rhs, t)
        } yield JSCompoundAssign(xAst, op, rhsAst)
      case JSSimpleUpdate(lhs, rhs) => 
        for {
          lhsAst <- transformAccess(lhs, t)
          rhsAst <- transformExp(rhs, t)
        } yield JSSimpleUpdate(lhsAst, rhsAst)
      case JSCompoundUpdate(lhs, op, rhs) => 
        for {
          lhsAst <- transformAccess(lhs, t)
          rhsAst <- transformExp(rhs, t)
        } yield JSCompoundUpdate(lhsAst, op, rhsAst)
      case JSTernary(e1, e2, e3) => 
        for {
          e1Ast <- transformExp(e1, t)
          e2Ast <- transformExp(e2, t)
          e3Ast <- transformExp(e3, t)
        } yield JSTernary(e1Ast, e2Ast, e3Ast)
      case JSAccess(e1, e2) => 
        for {
          e1Ast <- transformExp(e1, t)
          e2Ast <- transformExp(e2, t)
        } yield JSAccess(e1Ast, e2Ast)
      case JSNew(e1, e2s) => 
        for {
          e1Ast <- transformExp(e1, t)
          e2Asts <- toMonad(e2s.map(e => transformExp(e, t)))
        } yield JSNew(e1Ast, e2Asts)
      case JSDebug(e) =>
        for {
          ast <- transformExp(e, t)
        } yield JSDebug(ast)
      case JSCall(e, es) => 
        for {
          eAst <- transformExp(e, t)
          esAsts <- toMonad(es.map(e => transformExp(e, t)))
        } yield JSCall(eAst, esAsts)
      case JSFunctionExp(name, xs, s) => 
        for {
          newName <- toMonad(name.map(n => transformPVar(n, t)))
          xsAsts <- toMonad(xs.map(x => transformPVar(x, t)))
          sAst <- transformStmt(s, t)
        } yield JSFunctionExp(newName, xsAsts, sAst)
      case JSFunctionDecl(name, xs, s) => 
        for {
          nameAst <- transformPVar(name, t)
          xsAsts <- toMonad(xs.map(x => transformPVar(x, t)))
          sAst <- transformStmt(s, t)
        } yield JSFunctionDecl(nameAst, xsAsts, sAst)
      case JSBinop(e1, op, e2) => 
        for {
          e1Ast <- transformExp(e1, t)
          e2Ast <- transformExp(e2, t)
        } yield JSBinop(e1Ast, op, e2Ast)
      case JSUnop(op, e) =>
        for {
          eAst <- transformExp(e, t)
        } yield JSUnop(op, eAst)
      case JSObject(fields) => 
        for {
          fieldAsts <- toMonad(fields.map(p => transformString(p._1, t)))
          valueAsts <- toMonad(fields.map(p => transformExp(p._2, t)))
        } yield JSObject(fieldAsts.zip(valueAsts))
      case JSArray(es) => 
        for {
          asts <- toMonad(es.map(e => transformExp(e, t)))
        } yield JSArray(asts)
      case JSDelete(e) =>
        for {
          eAst <- transformExp(e, t)
        } yield JSDelete(eAst)
      case JSPrefixInc(lhs) =>
        for {
          lhsAst <- transformLHS(lhs, t)
        } yield JSPrefixInc(lhsAst)
      case JSPostfixInc(lhs) =>
        for {
          lhsAst <- transformLHS(lhs, t)
        } yield JSPostfixInc(lhsAst)
      case JSPrefixDec(lhs) =>
        for {
          lhsAst <- transformLHS(lhs, t)
        } yield JSPrefixDec(lhsAst)
      case JSPostfixDec(lhs) =>
        for {
          lhsAst <- transformLHS(lhs, t)
        } yield JSPostfixDec(lhsAst)
      case JSWhile(e, s) =>
        for {
          eAst <- transformExp(e, t)
          sAst <- transformStmt(s, t)
        } yield JSWhile(eAst, sAst)
      case JSDoWhile(s, e) =>
        for {
          sAst <- transformStmt(s, t)
          eAst <- transformExp(e, t)
        } yield JSDoWhile(sAst, eAst)
      case JSForIn(lhs, e, s) =>
        for {
          lhsAst <- transformLHS(lhs, t)
          eAst <- transformExp(e, t)
          sAst <- transformStmt(s, t)
        } yield JSForIn(lhsAst, eAst, sAst)
      case JSFor(s1, e, s2, s3) =>
        for {
          s1Ast <- transformStmt(s1, t)
          eAst <- transformExp(e, t)
          s2Ast <- transformStmt(s2, t)
          s3Ast <- transformStmt(s3, t)
        } yield JSFor(s1Ast, eAst, s2Ast, s3Ast)
      case JSOrigSeq(ss) => 
        for {
          asts <- toMonad(ss.map(s => transformStmt(s, t)))
        } yield JSOrigSeq(asts)
      case JSInsertedSeq(ss) => 
        for {
          asts <- toMonad(ss.map(s => transformStmt(s, t)))
        } yield JSInsertedSeq(asts)
      case JSDecl(bindings) => 
        for {
          varAsts <- toMonad(bindings.map(p => transformPVar(p._1, t)))
          valuesAsts <- optionPairsToMonad(bindings.map(_._2.map(e => transformExp(e, t))))
        } yield JSDecl(varAsts.zip(valuesAsts))
      case JSIf(e, s1, s2) => 
        for {
          eAst <- transformExp(e, t)
          s1Ast <- transformStmt(s1, t)
          s2Ast <- toMonad(s2.map(s2p => transformStmt(s2p, t)))
        } yield JSIf(eAst, s1Ast, s2Ast)
      case JSTry(s1, c, f) => 
        for {
          s1Ast <- transformStmt(s1, t)
          xAst <- toMonad(c.map(cp => transformPVar(cp._1, t)))
          catchAst <- toMonad(c.map(cp => transformStmt(cp._2, t)))
          finallyAst <- toMonad(f.map(fp => transformStmt(fp, t)))
        } yield JSTry(s1Ast,
                      for {
                        xRes <- xAst
                        catchRes <- catchAst
                      } yield (xRes, catchRes),
                      finallyAst)
      case JSThrow(e) => 
        for {
          eAst <- transformExp(e, t)
        } yield JSThrow(eAst)
      case JSLabeledStmt(lbls, s) => 
        for {
          lblAsts <- toMonad(lbls.map(l => transformLabel(l, t)))
          stmtAst <- transformStmt(s, t)
        } yield JSLabeledStmt(lblAsts, stmtAst)
      case JSBreak(l) => 
        for {
          ast <- toMonad(l.map(lp => transformLabel(lp, t)))
        } yield JSBreak(ast)
      case JSContinue(l) => 
        for {
          ast <- toMonad(l.map(lp => transformLabel(lp, t)))
        } yield JSContinue(ast)
      case JSWith(e, s) => 
        for {
          eAst <- transformExp(e, t)
          sAst <- transformStmt(s, t)
        } yield JSWith(eAst, sAst)
      case JSReturn(e) =>
        for {
          ast <- toMonad(e.map(ep => transformExp(ep, t)))
        } yield JSReturn(ast)
      case JSSwitch(e, cases, default) =>
        for {
          eAst <- transformExp(e, t)
          caseAsts <- toMonad(cases.map(p => transformExp(p._1, t)))
          valueAsts <- toMonad(cases.map(p => transformStmt(p._2, t)))
          default <- toMonad(default.map(dp => transformStmt(dp, t)))
        } yield JSSwitch(eAst, caseAsts.zip(valueAsts), default)
      case TransformDecl(bindings, retval) =>
        for {
          scratchAsts <- toMonad(bindings.map(p => transformScratch(p._1, t)))
          exprAsts <- toMonad(bindings.map(p => transformExp(p._2, t)))
          retvalAst <- transformExp(retval, t)
        } yield TransformDecl(scratchAsts.zip(exprAsts), retvalAst)

      case JSNum(n) => (JSNum(n), upwardBase)
      case JSBool(b) => (JSBool(b), upwardBase)
      case JSStr(s) => (JSStr(s), upwardBase)
      case JSUndef() => (JSUndef(), upwardBase)
      case JSNull() => (JSNull(), upwardBase)
      case JSEmpty() => (JSEmpty(), upwardBase)
      case JSPVar(x) => (JSPVar(x), upwardBase)
      case JSScratch(n) => (JSScratch(n), upwardBase)
      case JSLabel(l) => (JSLabel(l), upwardBase)
      case JSThis() => (JSThis(), upwardBase)
    }
}

trait JSOnlyDownwardPass[D] extends JSTransformPass[D, Unit] with OnlyDownwardPass[JSAST, D]

trait JSOnlyUpwardPass[U] extends JSTransformPass[Unit, U] with OnlyUpwardPass[JSAST, U]

// For passes that don't thread anything up or down the call stack
trait JSStatelessTransformPass extends JSOnlyDownwardPass[Unit] with JSOnlyUpwardPass[Unit] {
  def statelessTransformer: PartialFunction[JSAST, JSAST]
  val transformer: PartialFunction[(JSAST, Unit), (JSAST, Unit)] =
    { case (j: JSAST, t) if statelessTransformer.isDefinedAt(j) =>
        (statelessTransformer(j), t) }

  def transformExp(j: JSAST): JSExp =
    transformExp(j, downwardBase)._1

  def transformLHS(j: JSAST): JSLHS =
    transformLHS(j, downwardBase)._1

  def transformStmt(j: JSAST): JSStmt =
    transformStmt(j, downwardBase)._1

  def transformAccess(j: JSAST): JSAccess =
    transformAccess(j, downwardBase)._1
  
  def transformString(j: JSAST): JSStr = 
    transformString(j, downwardBase)._1

  def transformLabel(j: JSAST): JSLabel =
    transformLabel(j, downwardBase)._1
}

trait JSThreadedTransformPass[T] extends ThreadedTransformPass[JSAST, T] with JSTransformHelpers[T, T] {
  def transformExp(j: JSAST): TransformMonad[JSExp] =
    new TransformMonad[JSExp](
      (thread: T) =>
        transformExp(j, thread))

  def transformLHS(j: JSAST): TransformMonad[JSLHS] =
    new TransformMonad[JSLHS](
      (thread: T) =>
        transformLHS(j, thread))

  def transformStmt(j: JSAST): TransformMonad[JSStmt] =
    new TransformMonad[JSStmt](
      (thread: T) =>
        transformStmt(j, thread))

  def transformVar(j: JSAST): TransformMonad[JSVar] =
    new TransformMonad[JSVar](
      (thread: T) =>
        transformVar(j, thread))

  def transformPVar(j: JSAST): TransformMonad[JSPVar] =
    new TransformMonad[JSPVar](
      (thread: T) =>
        transformPVar(j, thread))

  def transformScratch(j: JSAST): TransformMonad[JSScratch] =
    new TransformMonad[JSScratch](
      (thread: T) =>
        transformScratch(j, thread))

  def transformAccess(j: JSAST): TransformMonad[JSAccess] =
    new TransformMonad[JSAccess](
      (thread: T) =>
        transformAccess(j, thread))

  def transformString(j: JSAST): TransformMonad[JSStr] =
    new TransformMonad[JSStr](
      (thread: T) =>
        transformString(j, thread))

  def transformLabel(j: JSAST): TransformMonad[JSLabel] =
    new TransformMonad[JSLabel](
      (thread: T) =>
        transformLabel(j, thread))

  def defaultTransform(j: JSAST, t: T): (JSAST, T) = {
    implicit def monadToAST[X <: JSAST](monad: TransformMonad[X]): (X, T) =
      monad.needsThread(t)

    j match {
      case JSToplevelDecl(vars, rest) =>
        for {
          varsAsts <- toMonad(vars.toList.map(v => transformPVar(v)))
          stmtAst <- transformStmt(rest)
        } yield JSToplevelDecl(varsAsts.toSet, stmtAst)
      case JSRegexp(s, flags) => 
        for {
          ast <- transformString(s)
        } yield JSRegexp(ast, flags)
      case JSSimpleAssign(x, rhs) => 
        for {
          xAst <- transformVar(x)
          rhsAst <- transformExp(rhs)
        } yield JSSimpleAssign(xAst, rhsAst)
      case JSCompoundAssign(x, op, rhs) => 
        for {
          xAst <- transformVar(x)
          rhsAst <- transformExp(rhs)
        } yield JSCompoundAssign(xAst, op, rhsAst)
      case JSSimpleUpdate(lhs, rhs) => 
        for {
          lhsAst <- transformAccess(lhs)
          rhsAst <- transformExp(rhs)
        } yield JSSimpleUpdate(lhsAst, rhsAst)
      case JSCompoundUpdate(lhs, op, rhs) => 
        for {
          lhsAst <- transformAccess(lhs)
          rhsAst <- transformExp(rhs)
        } yield JSCompoundUpdate(lhsAst, op, rhsAst)
      case JSTernary(e1, e2, e3) => 
        for {
          e1Ast <- transformExp(e1)
          e2Ast <- transformExp(e2)
          e3Ast <- transformExp(e3)
        } yield JSTernary(e1Ast, e2Ast, e3Ast)
      case JSAccess(e1, e2) => 
        for {
          e1Ast <- transformExp(e1)
          e2Ast <- transformExp(e2)
        } yield JSAccess(e1Ast, e2Ast)
      case JSNew(e1, e2s) => 
        for {
          e1Ast <- transformExp(e1)
          e2Asts <- toMonad(e2s.toList.map(e => transformExp(e)))
        } yield JSNew(e1Ast, e2Asts)
      case JSDebug(e) =>
        for {
          ast <- transformExp(e)
        } yield JSDebug(ast)
      case JSCall(e, es) => 
        for {
          eAst <- transformExp(e)
          esAsts <- toMonad(es.toList.map(e => transformExp(e)))
        } yield JSCall(eAst, esAsts)
      case JSFunctionExp(name, xs, s) => 
        for {
          newName <- toMonad(name.map(n => transformPVar(n)))
          xsAsts <- toMonad(xs.toList.map(x => transformPVar(x)))
          sAst <- transformStmt(s)
        } yield JSFunctionExp(newName, xsAsts, sAst)
      case JSFunctionDecl(name, xs, s) => 
        for {
          nameAst <- transformPVar(name)
          xsAsts <- toMonad(xs.toList.map(x => transformPVar(x)))
          sAst <- transformStmt(s)
        } yield JSFunctionDecl(nameAst, xsAsts, sAst)
      case JSBinop(e1, op, e2) => 
        for {
          e1Ast <- transformExp(e1)
          e2Ast <- transformExp(e2)
        } yield JSBinop(e1Ast, op, e2Ast)
      case JSUnop(op, e) =>
        for {
          eAst <- transformExp(e)
        } yield JSUnop(op, eAst)
      case JSObject(fields) => 
        for {
          fieldAsts <- toMonad(fields.toList.map(p => transformString(p._1)))
          valueAsts <- toMonad(fields.toList.map(p => transformExp(p._2)))
        } yield JSObject(fieldAsts.zip(valueAsts))
      case JSArray(es) => 
        for {
          asts <- toMonad(es.toList.map(e => transformExp(e)))
        } yield JSArray(asts)
      case JSDelete(e) =>
        for {
          eAst <- transformExp(e)
        } yield JSDelete(eAst)
      case JSPrefixInc(lhs) =>
        for {
          lhsAst <- transformLHS(lhs)
        } yield JSPrefixInc(lhsAst)
      case JSPostfixInc(lhs) =>
        for {
          lhsAst <- transformLHS(lhs)
        } yield JSPostfixInc(lhsAst)
      case JSPrefixDec(lhs) =>
        for {
          lhsAst <- transformLHS(lhs)
        } yield JSPrefixDec(lhsAst)
      case JSPostfixDec(lhs) =>
        for {
          lhsAst <- transformLHS(lhs)
        } yield JSPostfixDec(lhsAst)
      case JSWhile(e, s) =>
        for {
          eAst <- transformExp(e)
          sAst <- transformStmt(s)
        } yield JSWhile(eAst, sAst)
      case JSDoWhile(s, e) =>
        for {
          sAst <- transformStmt(s)
          eAst <- transformExp(e)
        } yield JSDoWhile(sAst, eAst)
      case JSForIn(lhs, e, s) =>
        for {
          lhsAst <- transformLHS(lhs)
          eAst <- transformExp(e)
          sAst <- transformStmt(s)
        } yield JSForIn(lhsAst, eAst, sAst)
      case JSFor(s1, e, s2, s3) =>
        for {
          s1Ast <- transformStmt(s1)
          eAst <- transformExp(e)
          s2Ast <- transformStmt(s2)
          s3Ast <- transformStmt(s3)
        } yield JSFor(s1Ast, eAst, s2Ast, s3Ast)
      case JSOrigSeq(ss) => 
        for {
          asts <- toMonad(ss.map(s => transformStmt(s)))
        } yield JSOrigSeq(asts)
      case JSInsertedSeq(ss) => 
        for {
          asts <- toMonad(ss.map(s => transformStmt(s)))
        } yield JSInsertedSeq(asts)
      case JSDecl(bindings) => 
        for {
          varAsts <- toMonad(bindings.map(p => transformPVar(p._1)))
          valuesAsts <- listOptionToMonad(bindings.map(_._2.map(e => transformExp(e))))
        } yield JSDecl(varAsts.zip(valuesAsts))
      case JSIf(e, s1, s2) => 
        for {
          eAst <- transformExp(e)
          s1Ast <- transformStmt(s1)
          s2Ast <- toMonad(s2.map(s2p => transformStmt(s2p)))
        } yield JSIf(eAst, s1Ast, s2Ast)
      case JSTry(s1, c, f) => 
        for {
          s1Ast <- transformStmt(s1)
          xAst <- toMonad(c.map(cp => transformPVar(cp._1)))
          catchAst <- toMonad(c.map(cp => transformStmt(cp._2)))
          finallyAst <- toMonad(f.map(fp => transformStmt(fp)))
        } yield JSTry(s1Ast,
                      for {
                        xRes <- xAst
                        catchRes <- catchAst
                      } yield (xRes, catchRes),
                      finallyAst)
      case JSThrow(e) => 
        for {
          eAst <- transformExp(e)
        } yield JSThrow(eAst)
      case JSLabeledStmt(lbls, s) => 
        for {
          lblAsts <- toMonad(lbls.toList.map(l => transformLabel(l)))
          stmtAst <- transformStmt(s)
        } yield JSLabeledStmt(lblAsts, stmtAst)
      case JSBreak(l) => 
        for {
          ast <- toMonad(l.map(lp => transformLabel(lp)))
        } yield JSBreak(ast)
      case JSContinue(l) => 
        for {
          ast <- toMonad(l.map(lp => transformLabel(lp)))
        } yield JSContinue(ast)
      case JSWith(e, s) => 
        for {
          eAst <- transformExp(e)
          sAst <- transformStmt(s)
        } yield JSWith(eAst, sAst)
      case JSReturn(e) =>
        for {
          ast <- toMonad(e.map(ep => transformExp(ep)))
        } yield JSReturn(ast)
      case JSSwitch(e, cases, default) =>
        for {
          eAst <- transformExp(e)
          caseAsts <- toMonad(cases.toList.map(p => transformExp(p._1)))
          valueAsts <- toMonad(cases.toList.map(p => transformStmt(p._2)))
          default <- toMonad(default.map(dp => transformStmt(dp)))
        } yield JSSwitch(eAst, caseAsts.zip(valueAsts), default)
      case TransformDecl(bindings, retval) =>
        for {
          scratchAsts <- toMonad(bindings.toList.map(p => transformScratch(p._1)))
          exprAsts <- toMonad(bindings.toList.map(p => transformExp(p._2)))
          retvalAst <- transformExp(retval)
        } yield TransformDecl(scratchAsts.zip(exprAsts), retvalAst)

      case JSNum(n) => (JSNum(n), t)
      case JSBool(b) => (JSBool(b), t)
      case JSStr(s) => (JSStr(s), t)
      case JSUndef() => (JSUndef(), t)
      case JSNull() => (JSNull(), t)
      case JSEmpty() => (JSEmpty(), t)
      case JSPVar(x) => (JSPVar(x), t)
      case JSScratch(n) => (JSScratch(n), t)
      case JSLabel(l) => (JSLabel(l), t)
      case JSThis() => (JSThis(), t)
    }
  }
}

// Used to get the maximal scratch id used in a given JSAST.
// Doesn't actually change anything in the AST.
object MaxScratchId extends JSOnlyUpwardPass[Option[Int]] {
  def upwardBase(): Option[Int] = None
  def combiner(t1: Option[Int], t2: Option[Int]): Option[Int] =
    (t1, t2) match {
      case (Some(i1), Some(i2)) => Some(math.max(i1, i2))
      case (s@Some(_), None) => s
      case (None, s@Some(_)) => s
      case (None, None) => None
    }

  val transformer: PartialFunction[(JSAST, Unit), (JSAST, Option[Int])] =
    { case (s@JSScratch(n), _) => (s, Some(n)) }

  // returns the maximum scratch variable used in the given ast, or
  // None if no scratch variables were used
  def maxId(ast: JSAST): Option[Int] =
    apply(ast, downwardBase)._2

  def main(args: Array[String]) {
    println(apply(JSBinop(JSBinop(JSScratch(2), JSMul, JSScratch(10)),
                          JSMul,
                          JSBinop(JSScratch(21), JSMul, JSScratch(5))),
                  downwardBase))
  }
}

// Simply counts the number of JSUndef() nodes in a given AST.
// Only for testing purposes.
object CountUndef extends JSTransformPass[Int, Int] {
  def downwardBase(): Int = 0
  def upwardBase(): Int = 0
  def combiner(t1: Int, t2: Int): Int = t1 + t2
  val transformer: PartialFunction[(JSAST, Int), (JSAST, Int)] =
    { case (JSUndef(), t) => assert(t == 0); (JSUndef(), 1) }

  def main(args: Array[String]) {
    println(apply(JSBinop(JSBinop(JSUndef(), JSMul, JSUndef()),
                          JSMul,
                          JSBinop(JSUndef(), JSMul, JSUndef()))))
  }
}

// Replaces JSEmpty with JSUndef
object ReplaceEmptyWithUndef extends JSStatelessTransformPass {
  val statelessTransformer: PartialFunction[JSAST, JSAST] = 
    { case JSEmpty() => JSUndef() }

  def main(args: Array[String]) {
    val ast = JSSeq(List(JSNum(5.0),
			JSSimpleAssign(JSPVar("x"),
				       JSBinop(JSNum(2.0), JSAdd, JSEmpty())),
			JSPVar("x")))
    println("BEFORE:\n" + ast)
    println("AFTER:\n" + apply(ast))
  }
				   
}

// Replaces any JSDecl nodes that don't have any bindings with JSUndef
object RemoveEmptyDecl extends JSStatelessTransformPass {
  val statelessTransformer: PartialFunction[JSAST, JSAST] = 
    { case JSDecl(bindings) if bindings.isEmpty => JSUndef() }
}

object VariableAllocator {
  val tempPrefix = "t`"
  private var nextPVarID = 0
  private var nextScratchID = 0

  def freshPVar(): JSPVar = {
    val retval = JSPVar(tempPrefix + nextPVarID)
    nextPVarID += 1
    retval
  }

  def freshScratch(): JSScratch = {
    val retval = JSScratch(nextScratchID)
    nextScratchID += 1
    retval
  }

  def isTempVar(x: JSPVar): Boolean =
    x.name.startsWith(tempPrefix)
}
import VariableAllocator._

// Hoists function definitions to the top of their enclosing scope.
// For example, with the following JavaScript:
//
// var x = 2;
// function foo() {
//   var y = 7;
//   function bar() {
//     return 42;
//   }
// }
//
// ...becomes...
//
// function foo() {
//   function bar() {
//     return 42;
//   }
//   var y = 7;
// }
// var x = 2;
//
// -Information passed down: Nothing.
// -Information passed up: Functions that should be hoisted to their enclosing scope, in
//  reverse order.
//
object HoistFunctions extends JSOnlyUpwardPass[List[JSFunctionDecl]] {
  type Transformer = PartialFunction[(JSAST, Unit), (JSAST, List[JSFunctionDecl])]
  def upwardBase(): List[JSFunctionDecl] = List()
  def combiner(l1: List[JSFunctionDecl], l2: List[JSFunctionDecl]): List[JSFunctionDecl] =
    l1 ++ l2

  def newBody(oldBody: JSStmt): JSStmt = {
    val (ast, toHoist) = transformStmt(oldBody, downwardBase)
    JSSeq((ast :: toHoist).reverse)
  }

  // for getting a handle on the function scope for function declarations
  val functionDeclTransform: Transformer =
    { case (JSFunctionDecl(name, params, body), _) =>
        (JSUndef(),
         List(JSFunctionDecl(name, params, newBody(body))))
   }

  // for getting a handle on the function scope for function expressions
  val functionExpTransform: Transformer =
    { case (JSFunctionExp(name, params, body), _) =>
        (JSFunctionExp(name, params, newBody(body)), upwardBase) }

  val transformer: Transformer =
    functionDeclTransform orElse functionExpTransform

  // for getting a handle on the global scope
  override def atTransformEnd(j: JSAST, decls: List[JSFunctionDecl]): (JSAST, List[JSFunctionDecl]) =
    (JSSeq((toStmt(j) :: decls).reverse), upwardBase)

  def main(args: Array[String]) {
    val ast = JSFunctionDecl(JSPVar("f1"),
			     Seq(),
			     JSSeq(List(
			       JSNum(12.0),
			       JSSimpleAssign(JSPVar("a"),
					      JSFunctionExp(Some(JSPVar("f2")), Seq(),
							    JSSeq(List(
							      JSNum(3.0),
							      JSFunctionDecl(JSPVar("f3"),
									     Seq(),
									     JSPVar("undefined")))))),
			       JSFunctionDecl(JSPVar("f4"), Seq(), JSPVar("undefined")))))
    println("BEFORE:\n" + ast)
    println("AFTER:\n" + apply(ast))
  }
}

// For the following code:
// function foo() {
//   var x = 12;
//   x++;
//   var y = x + 5;
// }
// ...it will hoist vars so that we get:
// function foo() {
//   var x = undefined;
//   var y = undefined;
//   x = 12;
//   x++;
//   y = x + 5;
// }
//
// Each function will start with a JSDecl after this pass if it
// declared any variables within.  Also handles hoisting function names.
// Also handles stripping out TransformDecls.
//
// -Information passed down: Nothing.
// -Information passed up: The variables that need to be hoisted.
//
object HoistFunctionVars extends JSOnlyUpwardPass[Set[JSPVar]] {
  type Transformer = PartialFunction[(JSAST, Unit), (JSAST, Set[JSPVar])]

  def upwardBase(): Set[JSPVar] = Set()
  def combiner(s1: Set[JSPVar], s2: Set[JSPVar]): Set[JSPVar] =
    s1 ++ s2

  // find the variables to hoist
  val jsDeclTransform: Transformer =
    { case (JSDecl(bindings), _) => {
        for {
          exps <- optionPairsToMonad(
            bindings.map(
              _._2.map(e => transformExp(e, downwardBase))))
          _ <- addToState(bindings.map(_._1).toSet)
        } yield JSSeq(bindings.map(_._1).zip(exps).flatMap(
            { case (x, e) => e.map(ep => JSSimpleAssign(x, ep))}))
    }
   }

  // strip out transform decls, and hoist the temporary variables introduced by them
  val transformDeclTransform: Transformer =
    { case (TransformDecl(bindings, retval), _) =>
        for {
          exps <- toMonad(bindings.map(p => transformExp(p._2, downwardBase)))
          vars = bindings.map(_._1).toSet
          retvalAst <- transformExp(retval, downwardBase)
        } yield vars.zip(exps).foldRight(retvalAst)(
            (cur, res) =>
              JSBinop(JSSimpleAssign(cur._1, cur._2), JSComma, res))
   }

  // To get a handle on the function scope.
  // Also performs this transformation:
  // 
  // var foo = function bar() {
  //    var a = 7;
  // };
  //
  // ...to...
  //
  // var t`0;
  // var foo = t`0 = function bar() {
  //    var bar = t`0;
  //    var a = undefined;
  //    var a = 7;
  // }
  //
  val functionExpTransform: Transformer =
    { case (JSFunctionExp(name, params, body), _) => {
        val (bodyAst, nestedToHoist) = transformStmt(body, downwardBase)
        
        def makeFunction(add: List[(JSPVar, Option[JSExp])]): JSFunctionExp = {
          JSFunctionExp(name, params, JSSeq(List(
            JSDecl(
              add ++ nestedToHoist.toList.map(x => (x, Some(JSUndef())))),
            bodyAst)))
        }

        name match {
          case Some(n) => {
            // this can't be a scratch var, since it is captured in a closure
            // (i.e. it is used within the function returned by makeFunction)
            val newVar = freshPVar()
            (JSSimpleAssign(newVar,
                            makeFunction(List((n, Some(newVar))))),
             Set(newVar))
          }
          case None =>
            (makeFunction(List()), upwardBase)
        }
    } 
   }
  
  // to get a handle on the function scope
  val functionDeclTransform: Transformer =
    { case (JSFunctionDecl(name, params, body), _) => {
        val (bodyAst, nestedToHoist) = transformStmt(body, downwardBase)
        (JSFunctionDecl(name,
                        params,
                        JSSeq(List(
                          JSDecl(nestedToHoist.toList.map((_, Some(JSUndef())))),
                          bodyAst))), Set(name))
    }
   }

  // to get a handle on the global scope
  override def atTransformEnd(j: JSAST, vars: Set[JSPVar]): (JSAST, Set[JSPVar]) = {
    val (temp, normal) = vars.partition(isTempVar)
    (JSToplevelDecl(
      temp,
      JSSeq(
        normal.toList.map(x => updateGlobally(x.name, JSUndef())) ++ List(toStmt(j)))),
     upwardBase)
  }

  val transformer: Transformer =
    jsDeclTransform orElse transformDeclTransform orElse functionExpTransform orElse functionDeclTransform

  def main(args: Array[String]) {
    val ast = JSSeq(List(JSFunctionDecl(JSPVar("foo"), Seq(),
					JSSeq(List(
					  JSDecl(List(
					    (JSPVar("x"), Some(JSNum(12.0))))),
					  JSPostfixInc(JSPVar("x")),
					  JSDecl(List(
					    (JSPVar("y"), Some(JSBinop(JSPVar("x"),
								      JSAdd,
								      JSNum(5.0)))))),
					  JSFunctionDecl(JSPVar("bar"), Seq(),
							 JSDecl(List((JSPVar("z"),
								     Some(JSNum(30.0)))))),
					  JSSimpleAssign(JSPVar("x"),
							 JSFunctionExp(Some(JSPVar("moo")),
								       Seq(),
								       JSPVar("undefined"))))))))
					  
    println("BEFORE:\n" + ast)
    println("AFTER:\n" + apply(ast))
  }
}

// -To be called after HoistFunctionVars and MakeAllAssignmentsSimple.
// -For any variable that isn't in a function scope, it sets it to be an access
//  from window
// -Exploits the assumption that there are no reference errors in the code
//
// -Information passed down: Stack of sets of variables that are in scope
// -Information passed up: Nothing
//
object HoistGlobalVars extends JSOnlyDownwardPass[List[Set[JSPVar]]] {
  type Transformer = PartialFunction[(JSAST, List[Set[JSPVar]]), (JSAST, Unit)]

  def downwardBase(): List[Set[JSPVar]] =
    List(Set(JSPVar(WINDOW_NAME), JSPVar(windowName)))

  def isInScope(x: JSPVar, scope: List[Set[JSPVar]]): Boolean =
    (x.name == ARGUMENTS_NAME && scope.size > 2) || scope.exists(_.contains(x))

  // to put the toplevel variables in scope
  val toplevelDeclTransform: Transformer =
    { case (JSToplevelDecl(vars, rest), scope) =>
        for {
          ast <- transformStmt(rest, vars :: scope)
        } yield JSToplevelDecl(vars, ast)
   }

  // to put the function parameters and function local variables in scope
  val functionTransform: Transformer =
    { case (f: JSFunction, scope) =>
        // the previous pass guarantees that we see Decls as the first statement in
	// a function body
        f.body match {
          case JSSeq((d@JSDecl(bindings)) :: rest) => {
            val newScope = (bindings.map(_._1).toSet ++ f.params.toSet) :: scope
            val (restAsts, _) = rest.map(s => transformStmt(s, newScope)).unzip
            val newRest = JSSeq(d :: restAsts)
            val function =
              f match {
                case JSFunctionExp(name, params, _) =>
                  JSFunctionExp(name, params, newRest)
                case JSFunctionDecl(name, params, _) =>
                  JSFunctionDecl(name, params, newRest)
              }
            (function, upwardBase)
          }
	  case a => throw BadTransformation(
            "Expected a Decl after the function but received: " + a)
        }
   }

  // Should never be called.  This is just to assert the assumption that
  // Decls are only at the start of functions now.
  val declTransform: Transformer =
    { case (_: JSDecl, _) => throw BadTransformation("Found a Decl outside of a function") }

    // scope.size > 2 is seeing whether or not we are in a function
    // scope's size is initially one, and the toplevel decl adds another
    // level, so scope is only > 2 if we hit a function
  // If we see the following JavaScript:
  //
  // x = 7
  //
  // ...if x is not in scope, this will transform this into:
  //
  // window.x = 7
  //
  // even if x is on the rhs, we don't need to make temporaries for window and
  // the field.  This is because window.str is guarenteed pure.
  val simpleAssignTransform: Transformer =
    { case (JSSimpleAssign(x@JSPVar(name), rhs), scope) if !isInScope(x, scope) =>
        for {
          rhsAst <- transformExp(rhs, scope)
        } yield updateGlobally(name, rhsAst)
   }

  // Should never be called.  This is just to assert the assumption that there
  // exist only simple assignments at this point.
  val compoundAssignTransform: Transformer =
    { case (_: JSCompoundAssign, _) => throw BadTransformation("Found a compound assign") }

  val assignTransform: Transformer =
    simpleAssignTransform orElse compoundAssignTransform

  // needed in order to put the catch variable in scope
  val tryTransform: Transformer =
    { case (JSTry(body, catchPart, finallyPart), scope) =>
        (JSTry(transformStmt(body, scope)._1,
               catchPart.map(
                 { case (x, s) => (x, transformStmt(s, Set(x) :: scope)._1) }),
               finallyPart.map(s => transformStmt(s, scope)._1)), upwardBase) }

  // will make `x` `window.x`, as long as `x` is not in scope
  val varTransform: Transformer =
    { case (x@JSPVar(name), scope) if !isInScope(x, scope) =>
        (JSAccess(JSPVar(windowName), JSStr(name)), upwardBase) }

  val transformer: Transformer =
    toplevelDeclTransform orElse varTransform orElse functionTransform orElse assignTransform orElse declTransform orElse tryTransform

  def main(args: Array[String]) {
    val ast = JSSeq(List(JSFunctionDecl(JSPVar("foo"),
					Seq(JSPVar("x")),
					JSSeq(List(
					  JSDecl(List((JSPVar("y"),
						      Some(JSPVar("undefined"))))),
					  JSSimpleAssign(JSPVar("y"), JSNum(5.0)),
					  JSSimpleAssign(JSPVar("z"),
							 JSBinop(JSPVar("a"), JSAdd,
								 JSBinop(JSPVar("x"),
									 JSAdd,
									 JSPVar("y")))))))))
    println("BEFORE:\n" + ast)
    println("AFTER:\n" + apply(ast))
  }
}

// JavaScript allows for users to define labels on loops to which one can
// jump via break and continue.  This label is placed at the outside of
// the loop, like so:
//
// label:
//   while (x < 5) {
//     if (x == 2) continue label;
//     alert(x);
//   }
//
// The problem is that since `label` is outside of the loop, a naive continue
// will end up acting exactly as a break would, since it escapes the loop.  We solve
// this problem via this transformation:
//
// label:
//   while (x < 5) {
//     continue_label:
//     if (x == 2) continue continue_label;
//     alert(x);
//   }
//
object FixContinueLabels extends JSStatelessTransformPass {
  type Transformer = PartialFunction[JSAST, JSAST]

  def contLbl(lbl: String): JSLabel =
    JSLabel("continue_" + lbl)

  val continueTransformer: Transformer =
    { case JSContinue(Some(JSLabel(label))) => 
        JSContinue(Some(contLbl(label))) }

  val loopLabelTransformer: Transformer =
    { case JSLabeledStmt(labels, loop: JSLoop) if labels.size >= 1 => {
        if (labels.size != 1) {
          throw BadTransformation("Found a loop head with multiple labels")
        }
        val loopBody = JSLabeledStmt(Seq(contLbl(labels.head.name)),
                                     transformStmt(loop.body))
        val newLoop =
          loop match {
            case JSWhile(guard, _) =>
              JSWhile(transformExp(guard), loopBody)
            case JSDoWhile(_, guard) =>
              JSDoWhile(loopBody, transformExp(guard))
            case JSForIn(itervar, iterable, _) =>
              JSForIn(transformLHS(itervar), transformExp(iterable), loopBody)
            case JSFor(initializer, guard, increment, _) =>
              JSFor(transformStmt(initializer),
                    transformExp(guard),
                    transformStmt(increment),
                    loopBody)
          }
      JSLabeledStmt(labels, newLoop)
    }
   }

  val statelessTransformer: Transformer =
    continueTransformer orElse loopLabelTransformer
}

// Converts compound assignments like so:
//
// x += y
//
// ...into equivalent simple assignments:
//
// x = x + y
//
// This is not always straightforward, as with `x.y += 7`, since we
// only want to evaluate `x` and `y` once.
//
// Must run before the Hoist* passes.
object MakeAllAssignmentsSimple extends JSStatelessTransformPass {
  type Transformer = PartialFunction[JSAST, JSAST]

  val assignTransform: Transformer =
    { case JSCompoundAssign(x, op, rhs) => 
	JSSimpleAssign(x, JSBinop(x, op, transformExp(rhs))) }

  val updateTransform: Transformer =
    { case JSCompoundUpdate(JSAccess(target, field), op, rhs) => {
	val y1 = freshScratch
	val y2 = freshScratch
	val access = JSAccess(y1, y2)
	TransformDecl(
	  Seq((y1, JSUnop(JSToObj, transformExp(target))),
	      (y2, transformExp(field))),
	  JSSimpleUpdate(access, JSBinop(access, op, transformExp(rhs))))
    }
   }

  val statelessTransformer: Transformer =
    assignTransform orElse updateTransform
}

// a sort of subroutine used by FunctionDeclToExp.  Should not be called
// directly, outside of the call in FunctionDeclToExp.
object FunctionDeclToExpInFunction extends JSStatelessTransformPass {
  type Transformer = PartialFunction[JSAST, JSAST]

  val statelessTransformer: Transformer =
    { case JSFunctionDecl(name, params, body) => {
	val newFunc = JSFunctionExp(Some(name),
				    params,
				    transformStmt(body))
	JSSimpleAssign(name, newFunc)
    }
   }
}

// converts function Decls to Exps.  For example:
// function foo() { ... }
// ...becomes...
// var foo = function () { ... }
// This must come after HoistFunctionVars and HoistFunctions
object FunctionDeclToExp extends JSStatelessTransformPass {
  type Transformer = PartialFunction[JSAST, JSAST]

  val functionDeclTransformer: Transformer =
    { case JSFunctionDecl(name, params, body) =>
	updateGlobally(name.name,
		       JSFunctionExp(Some(name),
				     params,
				     FunctionDeclToExpInFunction.transformStmt(body))) }

  val functionExpTransformer: Transformer =
    { case JSFunctionExp(name, params, body) => 
        JSFunctionExp(name, params,
                      FunctionDeclToExpInFunction.transformStmt(body)) }

  val statelessTransformer: Transformer =
    functionDeclTransformer orElse functionExpTransformer
}

// A sort of subroutine used in RemoveThis.  Should only be called by RemoveThis.
object RemoveThisInFunction extends JSStatelessTransformPass {
  type Transformer = PartialFunction[JSAST, JSAST]

  val statelessTransformer: Transformer =
    { case JSThis() => JSPVar(selfName) }
}

// replaces uses of 'this' with variable access
// must be run after FunctionDeclToExp
object RemoveThis extends JSStatelessTransformPass {
  type Transformer = PartialFunction[JSAST, JSAST]

  val thisTransformer: Transformer =
    { case JSThis() => JSPVar(windowName) }

  val functionExpTransformer: Transformer =
    { case JSFunctionExp(name, params, body) =>
	JSFunctionExp(name,
		      params,
		      RemoveThisInFunction.transformStmt(body)) }

  val statelessTransformer: Transformer =
    thisTransformer orElse functionExpTransformer

  def main(args: Array[String]) {
    val ast = JSSeq(List(
      JSThis(),
      JSFunctionExp(None, Seq(),
		    JSSeq(List(
		      JSDecl(List()),
		      JSThis())))))
    println("BEFORE:\n" + ast)
    println("AFTER:\n" + apply(ast))
  }
}
  
// Handles scoping for the catch variable.  This performs the following transformation:
// function foo() {
//   var local1 = undefined, local2 = undefined, ..., localN = undefined;
//   try {
//     ...
//   } catch (x) {
//     ...
//   } finally {
//     ...
//   }
// }
// ...to...
// function foo() {
//   var local1 = undefined, local2 = undefined, ..., localN = undefined, t`n = undefined;
//   try {
//     ...
//   } catch (t'n) {
//     ...
//   } finally {
//     ...
//   }
// }
//
// -Information passed down: mapping of catch variable names to what they should be renamed
//  as.
// -Information passed up: catch variable names that should be hoisted.
//
object HandleCatchScoping extends JSTransformPass[Map[JSPVar, JSPVar], Set[JSPVar]] {
  type Transformer = PartialFunction[(JSAST, Map[JSPVar, JSPVar]), (JSAST, Set[JSPVar])]
  def downwardBase(): Map[JSPVar, JSPVar] = Map()
  def upwardBase(): Set[JSPVar] = Set()
  def combiner(vars1: Set[JSPVar], vars2: Set[JSPVar]): Set[JSPVar] = vars1 ++ vars2

  // for substituting variable names
  val varTransformer: Transformer =
    { case (x: JSPVar, varMap) if varMap.contains(x) => (varMap(x), upwardBase) }

  // gets a handle on the catch, and sets up everything for renaming
  val tryTransformer: Transformer =
    { case (JSTry(body, catchPart, finallyPart), varMap) => {
        val (bodyAst, bodyHoist) = transformStmt(body, varMap)
        val newCatchPart =
          catchPart.map(
            { case (x, catchBody) => {
                // this must be a pvar, since the AST is defined that way
                val newVar = freshPVar
                val (catchAst, catchHoist) = transformStmt(catchBody,
                                                           varMap + (x -> newVar))
                (newVar, catchAst, catchHoist + newVar)
            } } )
        val newFinallyPart =
          finallyPart.map(f => transformStmt(f, varMap))
        (JSTry(bodyAst,
               newCatchPart.map(tup => (tup._1, tup._2)),
               newFinallyPart.map(_._1)),
         combine(Seq(bodyHoist,
                     newCatchPart.map(_._3).getOrElse(Set()),
                     newFinallyPart.map(_._2).getOrElse(Set()))))
    }
   }

  // to get a handle on the function scope
  val realFunctionExpTransformer: Transformer =
    { case (JSFunctionExp(name, params, JSSeq(JSDecl(bindings) :: rest)), varMap) => {
        val localSet = params.toSet ++ bindings.map(_._1).toSet
        val withoutLocals = varMap.filterNot(p => localSet(p._1))
        val (restAsts, hoistThese) = rest.map(s => transformStmt(s, withoutLocals)).unzip
        val newBindings = bindings ++ hoistThese.flatten.toSeq.map(x => (x, Some(JSUndef())))
        (JSFunctionExp(name, params, JSSeq(JSDecl(newBindings) :: restAsts)), upwardBase)
    }
   }

  // Matches arbitrary functions.  Makes sure that there aren't any functions
  // sitting around without Decls starting their bodies.  Should never be called.
  val fakeFunctionExpTransformer: Transformer =
    { case (_: JSFunctionExp, _) => throw BadTransformation(
      "Found a JSFunctionExp that didn't start with a JSDecl") }

  val functionExpTransformer: Transformer =
    realFunctionExpTransformer orElse fakeFunctionExpTransformer

  val transformer: Transformer =
    tryTransformer orElse functionExpTransformer orElse varTransformer

  override def atTransformEnd(j: JSAST, hoistThese: Set[JSPVar]): (JSAST, Set[JSPVar]) = {
    val JSToplevelDecl(vars, rest) = toToplevelDecl(j)
    (JSToplevelDecl(vars ++ hoistThese, rest), upwardBase)
  }

  def main(args: Array[String]) {
    val ast = JSToplevelDecl(
      Set(),
      JSFunctionExp(None,
		    Seq(),
		    JSSeq(List(
		      JSDecl(List()),
		      JSTry(JSPVar("undefined"),
			    Some((JSPVar("x"),
				  JSBinop(JSPVar("x"), JSAdd, JSNum(1.0)))),
			    None),
		      JSTry(JSPVar("undefined"),
			    Some((JSPVar("x"),
				  JSBinop(JSPVar("x"), JSAdd, JSNum(2.0)))),
			    None)))))
    println("BEFORE:\n" + ast)
    println("AFTER:\n" + apply(ast))
  }
}

// Applies all the AST transformations for JSASTs in the proper order.
object TransformJSAST {
  def apply(j: JSAST): JSAST = 
    HandleCatchScoping(
      RemoveThis(
        FunctionDeclToExp(
          HoistGlobalVars(
            HoistFunctionVars(
              HoistFunctions(
                MakeAllAssignmentsSimple(
                  FixContinueLabels(
                    ReplaceEmptyWithUndef(j)))))))))

  def main(args: Array[String]) {
    if (args.length != 1) {
      println("Takes one parameter: JavaScript file to translate.")
    } else {
      val ast = apply(
        RhinoToJSAST(
          notjs.translator.RunTranslator.parseJavaScript(
            new java.io.File(args(0)))))
      println(ast)
    }    
  }
}
