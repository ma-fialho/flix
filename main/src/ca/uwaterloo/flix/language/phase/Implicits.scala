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
import ca.uwaterloo.flix.language.ast.Ast.VariableMode
import ca.uwaterloo.flix.language.ast.{Symbol, Type, TypedAst}
import ca.uwaterloo.flix.util.{InternalCompilerException, Validation}
import ca.uwaterloo.flix.util.Validation._
import ca.uwaterloo.flix.util.collection.MultiMap

//
// Open Questions:
//
// 1. Do we want to allow explicit implicit parameters, e.g. ?width, ?ctx, ?stm, etc. I think we do.
//
// 2. We have to ensure safety, i.e. no unbound variables in head predicates, e.g.:
//    We have to disallow: P(implicit$1). and P(implicit$1) :- A(x). etc.
//
// 3. Introduce syntax for putting an explicit parameter into implicit scope (i.e. allowing an explicit parameter to unify with an implicit).
//
// 4. What does it mean for an implicit to be ambiguous here (and in Scala)?
//
// 5. Is it okay to have an implicit parameter alone?


// Properties:
//
// We want to prove these properties for our implicits:
//
//    1. Type safety.
//    2. Rule safety (no unbound head variables).
//    3. Two distinct explicit variables should never be equivalent.
//    4. Unique translation.

// TODO: Rename Ambiguous table to Overloaded? or something or other?

/**
  * Computes equivalences of implicit parameters in constraints.
  */
object Implicits extends Phase[TypedAst.Root, TypedAst.Root] {

  /**
    * Performs implicit resolution on the constraints in the given program.
    */
  def run(root: TypedAst.Root)(implicit flix: Flix): Validation[TypedAst.Root, CompilationError] = {
    val strata = root.strata.map(implicify)
    val result = root.copy(strata = strata)
    result.toSuccess
  }

  /**
    * Performs implicit resolution on the given stratum `s`.
    */
  def implicify(s: TypedAst.Stratum): TypedAst.Stratum = TypedAst.Stratum(s.constraints.map(implicify))

  /**
    * Performs implicit resolution on the given constraint `s`.
    */
  def implicify(c: TypedAst.Constraint): TypedAst.Constraint = {
    // An equivalence relation on a single explicit parameters in implicit scope and a set implicit parameters.
    val m1 = new MultiMap[Symbol.VarSym, Symbol.VarSym]

    /*
     * Phase 1: Compute equivalences between explicit and implicit parameters.
     */

    // Compute equivalences between an explicit parameter in implicit scope and implicit parameter.
    for ((explicitSym, explicitType) <- explicitParamsInImplicitScope(c)) {
      // Ensure reflexivity.
      m1.put(explicitSym, explicitSym)

      // Check if the explicit parameter occurs in the head predicate.
      if (occurs(explicitSym, c.head)) {
        // Attempt to unify the explicit parameter with the implicit parameters.
        for ((implicitSym, implicitType) <- implicitParamsOf(c.head)) {
          // Check that the types are compatible.
          if (explicitType == implicitType) {
            m1.put(explicitSym, implicitSym)
          }
        }
      }

      // Iterate through each body predicate.
      for (b <- c.body) {
        // Check if the explicit parameter occurs in the body predicate.
        if (occurs(explicitSym, b)) {
          // Attempt to unify the explicit parameter with the implicit parameters.
          for ((implicitSym, implicitType) <- implicitParamsOf(b)) {
            // Check that the types are compatible.
            if (explicitType == implicitType) {
              m1.put(explicitSym, implicitSym)
            }
          }
        }
      }
    }

    /*
     * Check for conflicts: It is possible that two implicit parameters belong to different equivalence classes.
     */
    for (ec1 <- m1.values) {
      for (sym1 <- ec1) {
        for (ec2 <- m1.values) {
          for (sym2 <- ec2) {
            if (sym1 == sym2 && ec1 != ec2) {
              throw InternalCompilerException(s"Symbol '$sym1' contained in two different ECs: '$ec1' and '$ec2'.")
            }
          }
        }
      }
    }

    /*
     * Phase 2: Compute equivalences between the remaining implicit parameters.
     */

    // Compute equivalences of implicit parameters not unified with an explicit parameter.
    val m2 = new MultiMap[Type, Symbol.VarSym]

    // Iterate through all implicits parameter and unify those that do not yet belong to any equivalence class.
    for ((implicitSym, implicitType) <- implicitParamsOf(c)) {
      // Check if the implicit parameter already belongs to an equivalence class.
      if (!m1.values.exists(_.contains(implicitSym))) {
        // The implicit parameter does not belong to any equivalence class.
        m2.put(implicitType, implicitSym)
      }
    }

    // Assert that the two sets of equivalence classes are disjoint.
    assert((m1.values.flatten intersect m2.values.flatten).isEmpty)

    // Compute the union of the two sets of equivalence classes.
    val equivalences = m1.values ++ m2.values

    // Compute a substitution map for each equivalence class.
    val substitutions = equivalences.map(getSubstitution)

    // Merge each substitution map into a single substitution map.
    val substitution = substitutions.foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym]) {
      case (macc, subst) => macc ++ subst
    }

    // Apply the substitution to the constraint.
    replace(c, substitution)
  }

  /**
    * Returns `true` iff the given head predicate `h0` is ambiguous and contains the given `explicitSym`.
    */
  def occurs(explicitSym: Symbol.VarSym, h0: TypedAst.Predicate.Head): Boolean = {
    assert(explicitSym.mode.isExplicit)

    h0 match {
      case TypedAst.Predicate.Head.Ambiguous(_, explicits, implicits, loc) => explicits.exists {
        case (sym, tpe) => sym == explicitSym
      }
      case _ => false
    }
  }

  /**
    * Returns `true` iff the given body predicate `b0` is ambiguous and contains the given `explicitSym`.
    */
  def occurs(explicitSym: Symbol.VarSym, b0: TypedAst.Predicate.Body): Boolean = b0 match {
    case TypedAst.Predicate.Body.Ambiguous(_, polarity, explicits, implicits, loc) => explicits.exists {
      case (sym, tpe) => sym == explicitSym
    }
    case _ => false
  }

  /**
    * Returns the unifiable explicit parameters along with their types of the given constraint `c`.
    */
  def explicitParamsInImplicitScope(c: TypedAst.Constraint): List[(Symbol.VarSym, Type)] = c.cparams.collect {
    case TypedAst.ConstraintParam.RuleParam(sym, tpe, loc) if sym.mode.isExplicit => (sym, tpe)
  }

  /**
    * Returns the implicit parameters along with their types of the given constraint `c`.
    */
  def implicitParamsOf(c: TypedAst.Constraint): List[(Symbol.VarSym, Type)] = c.cparams.collect {
    case TypedAst.ConstraintParam.RuleParam(sym, tpe, loc) if sym.mode == VariableMode.Implicit => (sym, tpe)
  }

  /**
    * Returns the implicit parameters of the given head predicate `h0`.
    */
  def implicitParamsOf(h0: TypedAst.Predicate.Head): Set[(Symbol.VarSym, Type)] = h0 match {
    case TypedAst.Predicate.Head.True(loc) => Set.empty
    case TypedAst.Predicate.Head.False(loc) => Set.empty
    case TypedAst.Predicate.Head.Table(_, terms, loc) =>
      terms.foldLeft(Set.empty[(Symbol.VarSym, Type)]) {
        case (sacc, TypedAst.Expression.Var(sym, tpe, _)) => sym.mode match {
          case VariableMode.Implicit => sacc + ((sym, tpe))
          case VariableMode.Explicit(implicitScope) => sacc
        }
        case (sacc, _) => sacc // NB: *If* we allow user-written implicit parameters ?x then we must traverse the expression.
      }
    case TypedAst.Predicate.Head.Ambiguous(sym, terms, implicits, loc) => implicits.toSet
  }

  /**
    * Returns the implicit parameters of the given body predicate `b0`.
    */
  def implicitParamsOf(b0: TypedAst.Predicate.Body): Set[(Symbol.VarSym, Type)] = b0 match {
    case TypedAst.Predicate.Body.Table(_, _, terms, _) =>
      terms.foldLeft(Set.empty[(Symbol.VarSym, Type)]) {
        case (sacc, TypedAst.Pattern.Var(sym, tpe, loc)) => sym.mode match {
          case VariableMode.Implicit => sacc + ((sym, tpe))
          case VariableMode.Explicit(implicitScope) => sacc
        }
        case (sacc, _) => sacc // NB: *If* we allow user-written implicit parameters ?x then we must traverse the pattern.
      }
    case TypedAst.Predicate.Body.Ambiguous(_, _, _, implicits, _) => implicits.toSet
    case TypedAst.Predicate.Body.Filter(sym, terms, loc) => Set.empty // As above.
    case TypedAst.Predicate.Body.Loop(sym, term, loc) => Set.empty // As above.
  }

  /**
    * Picks a representative from the the set `s` and returns a substitution map
    * replacing every other symbols with the picked representative.
    */
  def getSubstitution(ec: Set[Symbol.VarSym]): Map[Symbol.VarSym, Symbol.VarSym] = {
    // Check if the equivalence class is a singleton. If so, simply return the empty map.
    if (ec.size == 1)
      return Map.empty

    // Try to select the explicit parameter (if any other).
    // Otherwise randomly select the first parameter.
    val representative = ec.find(_.mode == VariableMode.Explicit).getOrElse(ec.head)

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
    * Applies the given substitution map `subst` to every parameter in the given constraint `c`.
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
    * Applies the given substitution map `subst` to every parameter in the given head predicate `h`.
    */
  def replace(h: TypedAst.Predicate.Head, subst: Map[Symbol.VarSym, Symbol.VarSym]): TypedAst.Predicate.Head = h match {
    case TypedAst.Predicate.Head.True(loc) => TypedAst.Predicate.Head.True(loc)
    case TypedAst.Predicate.Head.False(loc) => TypedAst.Predicate.Head.False(loc)
    case TypedAst.Predicate.Head.Table(sym, terms, loc) =>
      val ts = terms.map(t => replace(t, subst))
      TypedAst.Predicate.Head.Table(sym, ts, loc)
    case TypedAst.Predicate.Head.Ambiguous(sym, terms, implicits, loc) =>
      val ts = implicits2exps(implicits, subst)
      TypedAst.Predicate.Head.Table(sym, ts, loc)
  }

  /**
    * Applies the given substitution map `subst` to every parameter in the given body predicate `h`.
    */
  def replace(b: TypedAst.Predicate.Body, subst: Map[Symbol.VarSym, Symbol.VarSym]): TypedAst.Predicate.Body = b match {
    case TypedAst.Predicate.Body.Table(sym, polarity, terms, loc) =>
      val ts = terms.map(t => replace(t, subst))
      TypedAst.Predicate.Body.Table(sym, polarity, ts, loc)

    case TypedAst.Predicate.Body.Ambiguous(sym, polarity, terms, implicits, loc) =>
      val ts = implicits2pats(implicits, subst)
      TypedAst.Predicate.Body.Table(sym, polarity, ts, loc)

    case TypedAst.Predicate.Body.Filter(sym, terms, loc) => b // NB: *If* we allow user-written implicit parameters ?x then we must traverse the pattern.

    case TypedAst.Predicate.Body.Loop(sym, term, loc) => b // NB: *If* we allow user-written implicit parameters ?x then we must traverse the pattern.
  }

  /**
    * Applies the given substitution map `subst` to every parameter in the given expression `e`.
    */
  def replace(e: TypedAst.Expression, subst: Map[Symbol.VarSym, Symbol.VarSym]): TypedAst.Expression = e match {
    case TypedAst.Expression.Var(sym, tpe, loc) => subst.get(sym) match {
      case None => TypedAst.Expression.Var(sym, tpe, loc)
      case Some(newSym) => TypedAst.Expression.Var(newSym, tpe, loc)
    }
    case _ => e // NB: *If* we allow user-written implicit parameters then this must traverse the expression.
  }

  /**
    * Applies given substitution map `subst` to every parameter in the given pattern `p`.
    */
  def replace(p: TypedAst.Pattern, subst: Map[Symbol.VarSym, Symbol.VarSym]): TypedAst.Pattern = p match {
    case TypedAst.Pattern.Var(sym, tpe, loc) => subst.get(sym) match {
      case None => TypedAst.Pattern.Var(sym, tpe, loc)
      case Some(newSym) => TypedAst.Pattern.Var(newSym, tpe, loc)
    }
    case _ => p // NB: *If* we allow user-written implicit parameters then this must traverse the pattern.
  }

  /**
    * Returns the given list of implicits parameters as a list of expressions after applying the given substitution `subst`.
    */
  def implicits2exps(implicits: List[(Symbol.VarSym, Type)], subst: Map[Symbol.VarSym, Symbol.VarSym]): List[TypedAst.Expression] = implicits.map {
    case (varSym, tpe) => subst.get(varSym) match {
      case None => TypedAst.Expression.Var(varSym, tpe, varSym.loc)
      case Some(newSym) => TypedAst.Expression.Var(newSym, tpe, varSym.loc)
    }
  }

  /**
    * Returns the given list of implicits parameters as a list of patterns after applying the given substitution `subst`.
    */
  def implicits2pats(implicits: List[(Symbol.VarSym, Type)], subst: Map[Symbol.VarSym, Symbol.VarSym]): List[TypedAst.Pattern] = implicits.map {
    case (varSym, tpe) => subst.get(varSym) match {
      case None => TypedAst.Pattern.Var(varSym, tpe, varSym.loc)
      case Some(newSym) => TypedAst.Pattern.Var(newSym, tpe, varSym.loc)
    }
  }

}
