package ca.uwaterloo.flix.language.phase

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.Ast.Modifiers
import ca.uwaterloo.flix.language.ast.SimplifiedAst._
import ca.uwaterloo.flix.language.ast.{SourceLocation, Symbol, Type}
import ca.uwaterloo.flix.language.{CompilationError, GenSym}
import ca.uwaterloo.flix.util.Validation._
import ca.uwaterloo.flix.util.{InternalCompilerException, Validation}

object Continuations extends Phase[Root, Root] {

  /**
    * Transforms all expressions in the given AST `root` into continuation passing style (CPS).
    *
    * The transformation is currently very naive and could be optimized to yield better performance.
    */
  def run(root: Root)(implicit flix: Flix): Validation[Root, CompilationError] = {

    // Put gen sym into implicit scope.
    implicit val _ = flix.genSym

    // TODO
    root.defs map {
      case (sym, defn) => visitDefn(defn)
    }

    root.toSuccess
  }


  def visitDefn(defn: Def)(implicit genSym: GenSym): Def = {
    // TODO: Figure out what type to pass here...
    val tpe = defn.exp.tpe
    val kont = mkIdentity(tpe)

    visitExp(defn.exp, kont)

    null // TODO
  }

  /**
    * Transforms the given expression `exp0` into continuation passing style with the given continuation `kont0`.
    */
  def visitExp(exp0: Expression, kont0: Expression)(implicit genSym: GenSym): Expression = exp0 match {
    //
    // Unit. A value, apply the continuation.
    //
    case Expression.Unit => mkApplyCont(kont0, exp0)

    //
    // True. A value, apply the continuation.
    //
    case Expression.True => mkApplyCont(kont0, exp0)

    case Expression.False => exp0 // TODO

    case Expression.Char(lit) => exp0 // TODO

    case Expression.Float32(lit) => exp0 // TODO

    case Expression.Float64(lit) => exp0 // TODO

    case Expression.Int8(lit) => exp0 // TODO

    case Expression.Int16(lit) => exp0 // TODO

    case Expression.Int32(lit) => exp0 // TODO

    case Expression.Int64(lit) => exp0 // TODO

    case Expression.BigInt(lit) => exp0 // TODO

    case Expression.Str(lit) => exp0 // TODO

    case Expression.Var(sym, tpe, loc) => exp0 // TODO

    case Expression.Def(sym, tpe, loc) => exp0 // TODO

    case Expression.Eff(sym, tpe, loc) => exp0 // TODO

    case Expression.Lambda(fparams, body, tpe, loc) => exp0 // TODO

    case Expression.Apply(exp, args, tpe, loc) => exp0 // TODO

    case Expression.LambdaClosure(lambda, freeVars, tpe, loc) => exp0 // TODO

    case Expression.ApplyClo(exp, args, tpe, loc) => exp0 // TODO

    case Expression.ApplyDef(sym, args, tpe, loc) => exp0 // TODO

    case Expression.ApplyEff(sym, args, tpe, loc) => exp0 // TODO

    case Expression.Unary(sop, op, exp, tpe, loc) => exp0 // TODO

    case Expression.Binary(sop, op, exp1, exp2, tpe, loc) => exp0 // TODO

    case Expression.IfThenElse(exp1, exp2, exp3, tpe, loc) =>
      //
      // Evaluate the conditional expression `exp1` passing a lambda that
      // selects the appropriate branch where to continue execution.
      //

      // Retrieve the argument and return type of the continuation `kont0`.
      val kontArgumentType = getArgumentType(kont0.tpe)
      val kontReturnType = getReturnType(kont0.tpe)

      // Introduce a fresh variable symbol for the value of the conditional.
      val freshCondSym = Symbol.freshVarSym("c")
      val freshCondVar = Expression.Var(freshCondSym, Type.Bool, loc)

      // Construct an expression that branches on the variable symbol and
      // continues execution in the CPS converted version of the two branches.
      val e2 = visitExp(exp2, kont0)
      val e3 = visitExp(exp3, kont0)
      val e = Expression.IfThenElse(freshCondVar, e2, e3, kontReturnType, loc)

      // Constructs the lambda to pass as the continuation to the evaluation of the conditional.
      val lambda = mkLambda(freshCondSym, Type.Bool, e)

      // Recurse on the conditional.
      visitExp(exp1, lambda)

    case Expression.Branch(exp, branches, tpe, loc) => exp0 // TODO

    case Expression.JumpTo(sym, tpe, loc) => exp0 // TODO

    case Expression.Let(sym, exp1, exp2, tpe, loc) => exp0 // TODO

    case Expression.LetRec(sym, exp1, exp2, tpe, loc) => exp0 // TODO

    case Expression.Is(sym, tag, exp, loc) => exp0 // TODO

    case Expression.Tag(enum, tag, exp, tpe, loc) => exp0 // TODO

    case Expression.Untag(sym, tag, exp, tpe, loc) => exp0 // TODO

    case Expression.Index(exp, offset, tpe, loc) => exp0 // TODO

    case Expression.Tuple(elms, tpe, loc) => exp0 // TODO

    case Expression.ArrayNew(elm, len, tpe, loc) => exp0 // TODO

    case Expression.ArrayLit(elms, tpe, loc) => exp0 // TODO

    case Expression.ArrayLoad(base, index, tpe, loc) => exp0 // TODO

    case Expression.ArrayStore(base, index, value, tpe, loc) => exp0 // TODO

    case Expression.Ref(exp, tpe, loc) => exp0 // TODO

    case Expression.Deref(exp, tpe, loc) => exp0 // TODO

    case Expression.Assign(exp1, exp2, tpe, loc) => exp0 // TODO

    case Expression.HandleWith(exp, bindings, tpe, loc) => exp0 // TODO

    case Expression.Existential(params, exp, loc) => exp0 // TODO

    case Expression.Universal(params, exp, loc) => exp0 // TODO

    case Expression.TryCatch(exp, rules, tpe, eff, loc) => exp0 // TODO

    case Expression.NativeConstructor(constructor, args, tpe, loc) => exp0 // TODO

    case Expression.NativeField(field, tpe, loc) => exp0 // TODO

    case Expression.NativeMethod(method, args, tpe, loc) => exp0 // TODO

    case Expression.UserError(tpe, loc) => exp0 // TODO

    case Expression.HoleError(sym, tpe, eff, loc) => exp0 // TODO

    case Expression.MatchError(tpe, loc) => exp0 // TODO

    case Expression.SwitchError(tpe, loc) => exp0 // TODO

    case _ => throw InternalCompilerException(s"Unexpected expression: '${exp0.getClass}'.")
  }

  /**
    * Returns the identity lambda for the given type `tpe`.
    */
  def mkIdentity(tpe: Type)(implicit genSym: GenSym): Expression = {
    val loc = SourceLocation.Generated

    val freshSym = Symbol.freshVarSym()
    val freshVar = Expression.Var(freshSym, tpe, loc)
    val fparam = FormalParam(freshSym, Modifiers.Empty, tpe, loc)
    Expression.Lambda(List(fparam), freshVar, Type.mkArrow(tpe, tpe), loc)
  }

  /**
    * Returns a lambda expression with the given symbol `sym` as a formal parameter,
    * the given type `argType` as its argument type and the given body `exp`.
    */
  def mkLambda(sym: Symbol.VarSym, argType: Type, exp: Expression): Expression = {
    val loc = exp.loc
    val fparam = FormalParam(sym, Modifiers.Empty, argType, loc)
    Expression.Lambda(List(fparam), exp, Type.mkArrow(argType, exp.tpe), loc)
  }

  /**
    * Returns an apply expression that applies the given continuation `kont0` to the value or variable expression `exp0`.
    */
  private def mkApplyCont(kont0: Expression, exp0: Expression) = {
    val kontReturnType = getReturnType(kont0.tpe)
    Expression.Apply(kont0, List(exp0), kont0.tpe, SourceLocation.Generated)
  }

  /**
    * Returns the argument type of the given type `tpe` which must be an arrow type.
    */
  private def getArgumentType(tpe: Type): Type = {
    assert(tpe.isArrow)
    tpe.typeArguments.head
  }

  /**
    * Returns the return type of the given type `tpe` which must be an arrow type.
    */
  private def getReturnType(tpe: Type): Type = {
    assert(tpe.isArrow)
    tpe.typeArguments.last
  }

}
