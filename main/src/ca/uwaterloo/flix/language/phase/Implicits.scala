/*
 * Copyright 2017 Magnus Madsen
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package ca.uwaterloo.flix.language.phase

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.CompilationError
import ca.uwaterloo.flix.language.ast.Ast.AttributeMode
import ca.uwaterloo.flix.language.ast.{Symbol, Type, TypedAst}
import ca.uwaterloo.flix.util.Validation
import ca.uwaterloo.flix.util.Validation._
import ca.uwaterloo.flix.util.collection.MultiMap

/**
  * Computes equivalences of implicit parameters in constraints.
  */
object Implicits extends Phase[TypedAst.Root, TypedAst.Root] {

  // TODO: Do we want to allow explicit implicit parameters, e.g.:
  //
  // LocalVar(r, sum(?ctx, ?stm, v1, v2)) :- AddStm(r, x, y), LocalVar(x, v1), LocalVar(y, v2).
  //

  // TODO: We have to be careful with implicit variables not bound in the body. For example, this rule is unsafe:
  //
  // R(x, ?y) :- A(x) // where A does not define an implicit y.


  /**
    * Performs implicit resolution on the constraints in the given program.
    */
  def run(root: TypedAst.Root)(implicit flix: Flix): Validation[TypedAst.Root, CompilationError] = {
    val strata = root.strata.map(implicify)
    root.copy(strata = strata).toSuccess
  }

  /**
    * Performs implicit resolution on the given stratum `s`.
    */
  def implicify(s: TypedAst.Stratum): TypedAst.Stratum = TypedAst.Stratum(s.constraints.map(implicify))

  /**
    * Performs implicit resolution on the given constraint `c`.
    */
  def implicify(c: TypedAst.Constraint): TypedAst.Constraint = {
    // An equivalence relation on implicit variable symbols that share the same type.
    val m = new MultiMap[Type, Symbol.VarSym]

    // Iterate through every constraint parameter to compute equivalences for each implicit parameter.
    for (cparam <- c.cparams) {
      cparam match {
        case TypedAst.ConstraintParam.HeadParam(sym, tpe, loc) =>
        // case 1: A head parameter is never implicit.
        case TypedAst.ConstraintParam.RuleParam(sym, tpe, loc) =>
          // case 2: A rule parameter may be implicit.
          if (sym.mode == AttributeMode.Implicit) {
            m.put(tpe, sym)
          }
      }
    }

    // Retrieve the equivalence classes.
    val equivalences = m.values

    // Pick a representative of each equivalence class and obtain a substitution map.
    val substitutions = equivalences.map(getSubstitution)

    // Since the equivalence classes form a partition we can merge the substitution map into one.
    val substitution = substitutions.foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym]) {
      case (macc, subst) => macc ++ subst
    }

    // Apply the substitution to the constraint.
    replace(c, substitution)
  }

  /**
    * Picks a representative from the the set `s` and returns a substitution map
    * replacing every other symbols with the picked representative.
    */
  def getSubstitution(ec: Set[Symbol.VarSym]): Map[Symbol.VarSym, Symbol.VarSym] = {
    // Check if the equivalence class is a singleton. If so, simply return the empty map.
    if (ec.size == 1)
      return Map.empty

    // Randomly pick the first element of the equivalence class.
    val representative = ec.head

    // Map every other symbol to the representative.
    ec.foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym]) {
      case (macc, sym) =>
        if (sym == representative)
          macc
        else
          macc + (sym -> representative)
    }
  }

  /**
    * Applies the given substitution map `subst` to every variable in the given constraint `c`.
    */
  def replace(c: TypedAst.Constraint, subst: Map[Symbol.VarSym, Symbol.VarSym]): TypedAst.Constraint = c match {
    case TypedAst.Constraint(cparams0, head0, body0, loc) =>
      val cparams = cparams0.filter {
        case TypedAst.ConstraintParam.HeadParam(sym, _, _) => true
        case TypedAst.ConstraintParam.RuleParam(sym, _, _) => !subst.contains(sym)
      }
      val head = replace(head0, subst)
      val body = body0.map(b => replace(b, subst))
      TypedAst.Constraint(cparams, head, body, c.loc)
  }

  /**
    * Applies the given substitution map `subst` to every variable in the given head predicate `h`.
    */
  def replace(h: TypedAst.Predicate.Head, subst: Map[Symbol.VarSym, Symbol.VarSym]): TypedAst.Predicate.Head = h match {
    case TypedAst.Predicate.Head.True(loc) => TypedAst.Predicate.Head.True(loc)
    case TypedAst.Predicate.Head.False(loc) => TypedAst.Predicate.Head.False(loc)
    case TypedAst.Predicate.Head.Positive(sym, terms, loc) =>
      val ts = terms.map(t => replace(t, subst))
      TypedAst.Predicate.Head.Positive(sym, ts, loc)
    case TypedAst.Predicate.Head.Negative(sym, terms, loc) =>
      val ts = terms.map(t => replace(t, subst))
      TypedAst.Predicate.Head.Negative(sym, ts, loc)
  }

  /**
    * Applies the given substitution map `subst` to every variable in the given body predicate `h`.
    */
  def replace(b: TypedAst.Predicate.Body, subst: Map[Symbol.VarSym, Symbol.VarSym]): TypedAst.Predicate.Body = b match {
    case TypedAst.Predicate.Body.Positive(sym, terms, loc) =>
      val ts = terms.map(t => replace(t, subst))
      TypedAst.Predicate.Body.Positive(sym, ts, loc)
    case TypedAst.Predicate.Body.Negative(sym, terms, loc) =>
      val ts = terms.map(t => replace(t, subst))
      TypedAst.Predicate.Body.Negative(sym, ts, loc)
    // TODO: How do implicits interact with filter and loop predicates?
    case TypedAst.Predicate.Body.Filter(sym, terms, loc) => b
    case TypedAst.Predicate.Body.Loop(sym, term, loc) => b
  }

  /**
    * Applies given substitution map `subst` to every variable in the given expression `e`.
    *
    * NB: Implicit parameters always occur at the top-level and so this is the only place renaming has to occur.
    */
  def replace(e: TypedAst.Expression, subst: Map[Symbol.VarSym, Symbol.VarSym]): TypedAst.Expression = e match {
    case TypedAst.Expression.Var(sym, tpe, loc) => subst.get(sym) match {
      case None => TypedAst.Expression.Var(sym, tpe, loc)
      case Some(newSym) => TypedAst.Expression.Var(newSym, tpe, loc)
    }
    case _ => e
  }

  /**
    * Applies given substitution map `subst` to every variable in the given pattern `p`.
    *
    * NB: Implicit parameters always occur at the top-level and so this is the only place renaming has to occur.
    */
  def replace(p: TypedAst.Pattern, subst: Map[Symbol.VarSym, Symbol.VarSym]): TypedAst.Pattern = p match {
    case TypedAst.Pattern.Var(sym, tpe, loc) => subst.get(sym) match {
      case None => TypedAst.Pattern.Var(sym, tpe, loc)
      case Some(newSym) => TypedAst.Pattern.Var(newSym, tpe, loc)
    }
    case _ => p
  }

}
