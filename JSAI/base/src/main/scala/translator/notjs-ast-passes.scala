package notjs.translator.notjspass

import notjs.syntax.{Seq => SyntaxSeq, _}
import notjs.translator._

trait NotJSTransformHelpers[D, U] extends TransformBase[AST, D, U] {
  def transformStmt(a: AST, d: D): (Stmt, U) =
    transform(a, d) match {
      case (s: Stmt, u) => (s, u)
      case (wrong, _) => throw BadTransformation("Expected a statement but got: " + wrong)
    }

  def transformPVar(a: AST, d: D): (PVar, U) =
    transform(a, d) match {
      case (s: PVar, u) => (s, u)
      case (wrong, _) => throw BadTransformation("Expected a program variable but got: " + wrong)
    }

  def transformExp(a: AST, d: D): (Exp, U) =
    transform(a, d) match {
      case (s: Exp, u) => (s, u)
      case (wrong, _) => throw BadTransformation("Expected an expression but got: " + wrong)
    }

  def transformVar(a: AST, d: D): (Var, U) =
    transform(a, d) match {
      case (s: Var, u) => (s, u)
      case (wrong, _) => throw BadTransformation("Expected a variable but got: " + wrong)
    }

  def transformScratch(a: AST, d: D): (Scratch, U) =
    transform(a, d) match {
      case (s: Scratch, u) => (s, u)
      case (wrong, _) => throw BadTransformation("Expected a scratch variable but got: " + wrong)
    }

  def transformMethod(a: AST, d: D): (Method, U) =
    transform(a, d) match {
      case (s: Method, u) => (s, u)
      case (wrong, _) => throw BadTransformation("Expected a method but got: " + wrong)
    }

  def transformNum(a: AST, d: D): (NumAST, U) =
    transform(a, d) match {
      case (s: NumAST, u) => (s, u)
      case (wrong, _) => throw BadTransformation("Expected a number literal but got: " + wrong)
    }
}

// -D is the type of information that is passed down
// -U is the type of information that is passed up
trait NotJSTransformPass[D, U] extends TransformPass[AST, D, U] with NotJSTransformHelpers[D, U] {

  def defaultTransform(a: AST, d: D): (AST, U) =
    a match {
      case Decl(bindings, rest) =>
        for {
          varsAsts <- toMonad(bindings.map(b => transformPVar(b._1, d)))
          expAsts <- toMonad(bindings.map(b => transformExp(b._2, d)))
          restAst <- transformStmt(rest, d)
        } yield Decl(varsAsts.zip(expAsts), restAst)

      case SDecl(num, rest) =>
        for {
          restAst <- transformStmt(rest, d)
        } yield SDecl(num, restAst)

      case SyntaxSeq(ss) =>
        for {
          asts <- toMonad(ss.map(s => transformStmt(s, d)))
        } yield SyntaxSeq(asts)

      case If(e, s1, s2) =>
        for {
          eAst <- transformExp(e, d)
          s1Ast <- transformStmt(s1, d)
          s2Ast <- transformStmt(s2, d)
        } yield If(eAst, s1Ast, s2Ast)

      case While(e, s) =>
        for {
          eAst <- transformExp(e, d)
          sAst <- transformStmt(s, d)
        } yield While(eAst, sAst)

      case Assign(x, e) =>
        for {
          xAst <- transformVar(x, d)
          eAst <- transformExp(e, d)
        } yield Assign(xAst, eAst)

      case Call(x, e1, e2, e3) =>
        for {
          xAst <- transformVar(x, d)
          e1Ast <- transformExp(e1, d)
          e2Ast <- transformExp(e2, d)
          e3Ast <- transformExp(e3, d)
        } yield Call(xAst, e1Ast, e2Ast, e3Ast)

      case New(x, e1, e2) =>
        for {
          xAst <- transformVar(x, d)
          e1Ast <- transformExp(e1, d)
          e2Ast <- transformExp(e2, d)
        } yield New(xAst, e1Ast, e2Ast)

      case Newfun(x, m, n) =>
        for {
          xAst <- transformVar(x, d)
          mAst <- transformMethod(m, d)
          nAst <- transformNum(n, d)
        } yield Newfun(xAst, mAst, nAst)

      case ToObj(x, e) =>
        for {
          xAst <- transformVar(x, d)
          eAst <- transformExp(e, d)
        } yield ToObj(xAst, eAst)

      case Del(x, e1, e2) =>
        for {
          xAst <- transformScratch(x, d)
          e1Ast <- transformExp(e1, d)
          e2Ast <- transformExp(e2, d)
        } yield Del(xAst, e1Ast, e2Ast)

      case Update(e1, e2, e3) =>
        for {
          e1Ast <- transformExp(e1, d)
          e2Ast <- transformExp(e2, d)
          e3Ast <- transformExp(e3, d)
        } yield Update(e1Ast, e2Ast, e3Ast)

      case Throw(e) =>
        for {
          eAst <- transformExp(e, d)
        } yield Throw(eAst)

      case Try(s1, x, s2, s3) =>
        for {
          s1Ast <- transformStmt(s1, d)
          xAst <- transformPVar(x, d)
          s2Ast <- transformStmt(s2, d)
          s3Ast <- transformStmt(s3, d)
        } yield Try(s1Ast, xAst, s2Ast, s3Ast)

      case Lbl(lbl, s) =>
        for {
          sAst <- transformStmt(s, d)
        } yield Lbl(lbl, sAst)

      case Jump(lbl, e) =>
        for {
          eAst <- transformExp(e, d)
        } yield Jump(lbl, eAst)

      case For(x, e, s) =>
        for {
          xAst <- transformVar(x, d)
          eAst <- transformExp(e, d)
          sAst <- transformStmt(s, d)
        } yield For(xAst, eAst, sAst)

      case Merge() => (Merge(), upwardBase)

      case Print(e) =>
        for {
          eAst <- transformExp(e, d)
        } yield Print(eAst)

      case NumAST(v) => (NumAST(v), upwardBase)

      case BoolAST(v) => (BoolAST(v), upwardBase)

      case StrAST(v) => (StrAST(v), upwardBase)

      case UndefAST() => (UndefAST(), upwardBase)

      case NullAST() => (NullAST(), upwardBase)

      case PVar(n) => (PVar(n), upwardBase)

      case Scratch(n) => (Scratch(n), upwardBase)

      case Binop(op, e1, e2) =>
        for {
          e1Ast <- transformExp(e1, d)
          e2Ast <- transformExp(e2, d)
        } yield Binop(op, e1Ast, e2Ast)

      case Unop(op, e) =>
        for {
          eAst <- transformExp(e, d)
        } yield Unop(op, eAst)

      case Method(self, args, s) =>
        for {
          selfAst <- transformPVar(self, d)
          argsAst <- transformPVar(args, d)
          sAst <- transformStmt(s, d)
        } yield Method(selfAst, argsAst, sAst)
    } // a match
} // NotJSTransformPass

trait NotJSOnlyDownwardPass[D] extends NotJSTransformPass[D, Unit] with OnlyDownwardPass[AST, D]

trait NotJSOnlyUpwardPass[U] extends NotJSTransformPass[Unit, U] with OnlyUpwardPass[AST, U]

trait NotJSStatelessTransformPass extends NotJSOnlyDownwardPass[Unit] with NotJSOnlyUpwardPass[Unit] {
  def statelessTransformer: PartialFunction[AST, AST]
  val transformer: PartialFunction[(AST, Unit), (AST, Unit)] =
    { case (a: AST, t) if statelessTransformer.isDefinedAt(a) =>
        (statelessTransformer(a), t) }

  def transformStmt(a: AST): Stmt =
    transformStmt(a, downwardBase)._1

  def transformPVar(a: AST): PVar =
    transformPVar(a, downwardBase)._1

  def transformExp(a: AST): Exp =
    transformExp(a, downwardBase)._1

  def transformVar(a: AST): Var =
    transformVar(a, downwardBase)._1

  def transformScratch(a: AST): Scratch =
    transformScratch(a, downwardBase)._1

  def transformMethod(a: AST): Method =
    transformMethod(a, downwardBase)._1

  def transformNum(a: AST): NumAST =
    transformNum(a, downwardBase)._1
}

trait NotJSThreadedTransformPass[T] extends ThreadedTransformPass[AST, T] with NotJSTransformHelpers[T, T] {
  def transformStmt(a: AST): TransformMonad[Stmt] =
    new TransformMonad[Stmt](
      (thread: T) =>
        transformStmt(a, thread))

  def transformPVar(a: AST): TransformMonad[PVar] =
    new TransformMonad[PVar](
      (thread: T) =>
        transformPVar(a, thread))

  def transformExp(a: AST): TransformMonad[Exp] =
    new TransformMonad[Exp](
      (thread: T) =>
        transformExp(a, thread))

  def transformVar(a: AST): TransformMonad[Var] =
    new TransformMonad[Var](
      (thread: T) =>
        transformVar(a, thread))
    
  def transformScratch(a: AST): TransformMonad[Scratch] =
    new TransformMonad[Scratch](
      (thread: T) =>
        transformScratch(a, thread))

  def transformMethod(a: AST): TransformMonad[Method] =
    new TransformMonad[Method](
      (thread: T) =>
        transformMethod(a, thread))

  def transformNum(a: AST): TransformMonad[NumAST] =
    new TransformMonad[NumAST](
      (thread: T) =>
        transformNum(a, thread))

  def defaultTransform(a: AST, thread: T): (AST, T) = {
    implicit def monadToAst[X <: AST](monad: TransformMonad[X]): (X, T) =
      monad.needsThread(thread)

    a match {
      case Decl(bindings, rest) =>
        for {
          varsAsts <- toMonad(bindings.map(b => transformPVar(b._1)))
          expAsts <- toMonad(bindings.map(b => transformExp(b._2)))
          restAst <- transformStmt(rest)
        } yield Decl(varsAsts.zip(expAsts), restAst)

      case SDecl(num, rest) =>
        for {
          restAst <- transformStmt(rest)
        } yield SDecl(num, restAst)

      case SyntaxSeq(ss) =>
        for {
          asts <- toMonad(ss.map(s => transformStmt(s)))
        } yield SyntaxSeq(asts)

      case If(e, s1, s2) =>
        for {
          eAst <- transformExp(e)
          s1Ast <- transformStmt(s1)
          s2Ast <- transformStmt(s2)
        } yield If(eAst, s1Ast, s2Ast)

      case While(e, s) =>
        for {
          eAst <- transformExp(e)
          sAst <- transformStmt(s)
        } yield While(eAst, sAst)

      case Assign(x, e) =>
        for {
          xAst <- transformVar(x)
          eAst <- transformExp(e)
        } yield Assign(xAst, eAst)

      case Call(x, e1, e2, e3) =>
        for {
          xAst <- transformVar(x)
          e1Ast <- transformExp(e1)
          e2Ast <- transformExp(e2)
          e3Ast <- transformExp(e3)
        } yield Call(xAst, e1Ast, e2Ast, e3Ast)

      case New(x, e1, e2) =>
        for {
          xAst <- transformVar(x)
          e1Ast <- transformExp(e1)
          e2Ast <- transformExp(e2)
        } yield New(xAst, e1Ast, e2Ast)

      case Newfun(x, m, n) =>
        for {
          xAst <- transformVar(x)
          mAst <- transformMethod(m)
          nAst <- transformNum(n)
        } yield Newfun(xAst, mAst, nAst)

      case ToObj(x, e) =>
        for {
          xAst <- transformVar(x)
          eAst <- transformExp(e)
        } yield ToObj(xAst, eAst)

      case Del(x, e1, e2) =>
        for {
          xAst <- transformScratch(x)
          e1Ast <- transformExp(e1)
          e2Ast <- transformExp(e2)
        } yield Del(xAst, e1Ast, e2Ast)

      case Update(e1, e2, e3) =>
        for {
          e1Ast <- transformExp(e1)
          e2Ast <- transformExp(e2)
          e3Ast <- transformExp(e3)
        } yield Update(e1Ast, e2Ast, e3Ast)

      case Throw(e) =>
        for {
          eAst <- transformExp(e)
        } yield Throw(eAst)

      case Try(s1, x, s2, s3) =>
        for {
          s1Ast <- transformStmt(s1)
          xAst <- transformPVar(x)
          s2Ast <- transformStmt(s2)
          s3Ast <- transformStmt(s3)
        } yield Try(s1Ast, xAst, s2Ast, s3Ast)

      case Lbl(lbl, s) =>
        for {
          sAst <- transformStmt(s)
        } yield Lbl(lbl, sAst)

      case Jump(lbl, e) =>
        for {
          eAst <- transformExp(e)
        } yield Jump(lbl, eAst)

      case For(x, e, s) =>
        for {
          xAst <- transformVar(x)
          eAst <- transformExp(e)
          sAst <- transformStmt(s)
        } yield For(xAst, eAst, sAst)

      case Merge() => (Merge(), thread)

      case Print(e) =>
        for {
          eAst <- transformExp(e)
        } yield Print(eAst)

      case NumAST(v) => (NumAST(v), thread)

      case BoolAST(v) => (BoolAST(v), thread)

      case StrAST(v) => (StrAST(v), thread)

      case UndefAST() => (UndefAST(), thread)

      case NullAST() => (NullAST(), thread)

      case PVar(n) => (PVar(n), thread)

      case Scratch(n) => (Scratch(n), thread)

      case Binop(op, e1, e2) =>
        for {
          e1Ast <- transformExp(e1)
          e2Ast <- transformExp(e2)
        } yield Binop(op, e1Ast, e2Ast)

      case Unop(op, e) =>
        for {
          eAst <- transformExp(e)
        } yield Unop(op, eAst)

      case Method(self, args, s) =>
        for {
          selfAst <- transformPVar(self)
          argsAst <- transformPVar(args)
          sAst <- transformStmt(s)
        } yield Method(selfAst, argsAst, sAst)
    } // a match
  }
}

// Clones some given input AST.  This is needed in order to ensure that
// ASTs generated are truly trees instead of DAGs.  DAGs can result from
// using the same AST node twice, which is very common within the translator
// and permitted by AST passes.
object CloneAst extends NotJSStatelessTransformPass {
  // doesn't match anything.  Relies on the base class for copying over everything
  val statelessTransformer: PartialFunction[AST, AST] =
    { case a: AST if false => a}
}

// simple pass that counts the number of times UndefAST() is in the AST.
// used only for testing
object ThreadCountUndef extends NotJSThreadedTransformPass[Int] {
  val transformer: PartialFunction[(AST, Int), (AST, Int)] =
    { case (UndefAST(), x) => (UndefAST(), x + 1) }

  def downwardBase(): Int = 0

  def main(args: Array[String]) {
    println(apply(Binop(In,
                        Binop(In, UndefAST(), UndefAST()),
                        Binop(In, UndefAST(), UndefAST())),
                  downwardBase))
  }

}

// MUST BE THE FIRST PASS AFTER TRANSLATION!
//
// The JS -> notJS pass inserts scratch variables, but it doesn't deal with SDecls.
// Additionally, scratch variable ids are assigned globally, instead of based
// on a particular scope.  This pass inserts SDecls, and gives Scratch variables
// proper IDs.
//
// -Going down: when I hit a scoping boundary, the scratch variable counter resets to zero.
//  When a Scratch variable is encountered, see if we've already mapped it.  If so, use
//  the value from the map.  Else, increment the counter, use the previous counter
//  for the id, and add this old id -> new id mapping to our map.
//
// -Going up: when I hit a scoping boundary, introduce an SDecl after the Decl, but
//  only if we actually mapped to anything.  Use the value passed up for this.
//
// -Information passed down: (counter, maxScratchMade, mapping)
// -Information passed up: (counter, maxScratchMade, mapping)
object InsertSDecls extends NotJSThreadedTransformPass[(Int, Int, Map[Int, Int])] {
  type Thread = (Int, Int, Map[Int, Int])
  type Transformer = PartialFunction[(AST, Thread), (AST, Thread)]

  def downwardBase(): Thread =
    (0, 0, Map())

  override def atTransformEnd(ast: AST, thread: Thread): (AST, Thread) =
    ast match {
      case Decl(bindings, rest) =>
        (Decl(bindings, SDecl(thread._2, rest)), thread)
      case _ =>
        throw BadTransformation(
          "The notJS program didn't start with a Decl")
    }

  val scratchTransformer: Transformer =
    { case (Scratch(oldId), pass@(counter, maxScratchMade, mapping)) =>
        if (mapping.contains(oldId)) {
          (Scratch(mapping(oldId)), pass)
        } else {
          val newCounter = counter + 1
          (Scratch(counter),
           (newCounter, 
            math.max(newCounter, maxScratchMade),
            mapping + (oldId -> counter)))
        }
   }

  val realMethodTransformer: Transformer =
    { case (Method(self, args, Decl(params, body)), passAlong) => {
        val (bodyAst, (_, numScratch, _)) = transformStmt(body, downwardBase)
        val newBody = Decl(params, SDecl(numScratch, bodyAst))
        (Method(self, args, newBody), passAlong)
    }
   }

  // only to make sure that methods have a Decl
  val fakeMethodTransformer: Transformer =
    { case (Method(_, _, _), _) =>
        throw BadTransformation(
          "Encountered a method that doesn't begin with a Decl") }

  val statementTransformer: Transformer =
    { case (Decl(params, s), (counter, numScratch, mapping)) if params == PVarMapper.INDICATE_JS_SEQUENCE => {
        val stmts = 
          s match {
            case SyntaxSeq(ss) => ss
            case _ => List(s)
          }
        val (finalNumScratch, finalMapping, finalStmts) = 
          stmts.foldLeft((numScratch, mapping, List[Stmt]()))((res, cur) => {
            val (curNumScratch, curMapping, curStmts) = res
            val (finalStmt, (_, newNumScratch, newMapping)) = 
              transformStmt(cur, (0, curNumScratch, curMapping))
            (newNumScratch, newMapping, finalStmt :: curStmts)
          })
        (SyntaxSeq(finalStmts.reverse), (0, finalNumScratch, finalMapping))
    }
   }

  val methodTransformer: Transformer =
    realMethodTransformer orElse fakeMethodTransformer

  val transformer: Transformer =
    scratchTransformer orElse methodTransformer orElse statementTransformer
}

// Replaces Decls that have no bindings with their bodies.
object RemoveEmptyDecls extends NotJSStatelessTransformPass {
  val statelessTransformer: PartialFunction[AST, AST] =
    { case Decl(bindings, s) if bindings.isEmpty => transformStmt(s) }
}

// Replaces SDecls without any scratch variables declared with their bodies.
object RemoveEmptySDecls extends NotJSStatelessTransformPass {
  val statelessTransformer: PartialFunction[AST, AST] =
    { case SDecl(numScratch, s) if numScratch == 0 => transformStmt(s) }
}

// Will attempt to flatten out nested Seq statements into a single Seq.
// For example, given this:
//
// Seq(List(Seq(List(PVar("x")))))
//
// ...we will convert to...
//
// Seq(List(PVar("x")))
//
object FlattenSequences extends NotJSStatelessTransformPass {
  val statelessTransformer: PartialFunction[AST, AST] =
    { case SyntaxSeq(stmts) => {
        val newStmts = stmts.flatMap(s =>
          transformStmt(s) match {
            case SyntaxSeq(inner) => inner
            case s => List(s)
          })
        newStmts match {
          case Nil => PVarMapper.noOpStatement
          case one :: Nil => one
          case _ => SyntaxSeq(newStmts)
        }
    }
   }
}

object RemoveNoOps extends NotJSStatelessTransformPass {
  val statelessTransformer: PartialFunction[AST, AST] =
    { case SyntaxSeq(stmts) =>
        stmts.map(transformStmt).filter(_ != PVarMapper.noOpStatement) match {
          case Nil => PVarMapper.noOpStatement
          case one :: Nil => one
          case many => SyntaxSeq(many)
        }
   }
}

// Must be called after FlattenSequences and before WrapInSequence.
//
// Removes merge nodes that are next to each other in sequence, replacing the
// block of merge nodes found with a single merge node.
// For example, given this"
//
// Seq(Call(bar), Merge, Merge, Call(baz), Merge, Call(moo), Merge)
//
// ...it will convert to...
//
// Seq(Call(bar, Merge, Call(baz), Merge, Call(moo), Merge)
//
// -Information passed down: Nothing
// -Information passed up: Nothing
//
object RemoveRedundantMerge extends NotJSStatelessTransformPass {
  def compress(stmts: List[Stmt]): List[Stmt] =
    stmts.foldRight(List[Stmt]())((cur, res) =>
      (cur, res) match {
        case (Merge(), Merge() :: _) => res
        case _ => cur :: res
      })

  val statelessTransformer: PartialFunction[AST, AST] =
    { case SyntaxSeq(stmts) if stmts.nonEmpty =>
        SyntaxSeq(compress(stmts.map(transformStmt))) }
}

// Wraps all non-(Sequence, Decl, SDecl, return label) statements in a sequence node.
// For example, given this:
//
// If(PVar("foo"), Call(bar), Seq(Call(baz), Call(moo)))
//
// ...it will convert to...
//
// Seq(If(PVar("foo"), Seq(Call(bar)), Seq(Call(baz), Call(moo))))
//
// -Information passed down: whether or not the preceeding statement was a sequence
// -Information passed up: Nothing
//
object WrapInSequence extends NotJSOnlyDownwardPass[Boolean] {
  type Transformer = PartialFunction[(AST, Boolean), (AST, Unit)]

  val retLabel = Translator.RETURN_LABEL

  // ends up being ignored
  def downwardBase(): Boolean = false

  val sequenceTransform: Transformer =
    { case (SyntaxSeq(ss), _) =>
        (SyntaxSeq(ss.map(s => transformStmt(s, true)._1)), upwardBase) }

  def shouldIgnoreStatement(s: Stmt): Boolean =
    s match {
      case _: Decl | _: SDecl | Lbl(`retLabel`, _) => true
      case _: SyntaxSeq => 
        throw BadTransformation("Unexpectantly encountered a sequence")
      case _ => false
    }

  val stmtTransform: Transformer =
    { case (s: Stmt, prevSeq) if !shouldIgnoreStatement(s) =>
        if (prevSeq) defaultTransform(s, false)
        else (SyntaxSeq(List(transformStmt(s, true)._1)), upwardBase) }

  val transformer: Transformer =
    sequenceTransform orElse stmtTransform

  def main(args: Array[String]) {
    println(apply(If(PVar(0),
                     Call(PVar(0), UndefAST(), UndefAST(), UndefAST()),
                     SyntaxSeq(List(
                       Call(PVar(0), UndefAST(), UndefAST(), UndefAST()),
                       Call(PVar(0), UndefAST(), UndefAST(), UndefAST())))),
                  downwardBase))
  }
}

// Applies all the AST transformations for NotJS' AST in the proper order.
object TransformNotJSAST {
  def apply(a: AST): AST =
    CloneAst(
      WrapInSequence(
        RemoveRedundantMerge(
          RemoveNoOps(
            RemoveEmptySDecls(
              RemoveEmptyDecls(
                FlattenSequences(
                  InsertSDecls(a))))))))
}

