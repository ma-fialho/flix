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

// TODO: Do we want to allow explicit implicit parameters, e.g.:
//
// LocalVar(r, sum(?ctx, ?stm, v1, v2)) :- AddStm(r, x, y), LocalVar(x, v1), LocalVar(y, v2).
//
// We can, but that is an extension.
//

// TODO: We have to be careful with implicit variables not bound in the body. For example, this rule is unsafe:
//
// R(x, ?y) :- A(x) // where A does not define an implicit y.
//
// This goes back to the notion of safe rules.
//
// Essentially we want implicits to have 2-3 properties:
//
// 1. Preserves type safety.
// 2. preservers rule safety. (no unbound head variables).
// 3. Unambigious / deterministic.
// 4. (Optional) disallow a single occurence of an implicit parameter? (Perhaps not, after all we can use relevance types for that).
//
// In Scala an implicit can be ambiguios, what does it mean here?
//

// TODO: Introduce an equivalance abstraction which allows *n* implicits to be equivalent with at most one explicitCanUnify.

/**
  * TODO: Important idea: Allow explicit parameters to be annoted with ! to
  * indicate that hthey may be unified with implicit variables. E.g.
  *
  * VarPointsToIn(!s2) :−
  * CFG(!s1, !s2),
  * VarPointsToOut(!s1).
  */

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
    // A map from types to symbols.
    val type2sym = getType2Symbols(c)

    // An equivalence relation on implicit variable symbols that share the same type.
    val m = new MultiMap[Symbol.VarSym, Symbol.VarSym]

    // TODO: Here we should iterate through the explicit CAN UNIF parameters...
    // Iterate through all *explicit* parameters and unify each explicit parameter with the implicit parameters from where it occurs.
    for ((explicitSym, explicitType) <- explicitUnifiableParamsOf(c)) {

      m.put(explicitSym, explicitSym)

      if (occurs(explicitSym, c.head)) {
        val implicitsParams = implicitParamsOf(c.head)
        for ((implicitSym, implicitType) <- implicitsParams) {
          if (explicitType == implicitType) {
            m.put(explicitSym, implicitSym)
          }
        }
      }

      for (b <- c.body) {
        // The explicit variable `sym` appears explicitly in `b`.
        // Make it equivalent to the appropriate implicit variable in `b`.
        if (occurs(explicitSym, b)) {
          val implicitsParams = implicitParamsOf(b)
          for ((implicitSym, implicitType) <- implicitsParams) {
            if (explicitType == implicitType) {
              m.put(explicitSym, implicitSym)
            }
          }
        }
      }

    }

    // TODO: Handle conflicts.
    // TODO: Iterate through all symbols that do not belong to a class and unify them by type.


    // Retrieve the equivalence classes.
    val equivalences = m.values

    // Pick a representative of each equivalence class and obtain a substitution map.
    val substitutions = equivalences.map(getSubstitution)

    // Since the equivalence classes form a partition we can merge the substitution map into one.
    val substitution = substitutions.foldLeft(Map.empty[Symbol.VarSym, Symbol.VarSym]) {
      case (macc, subst) => macc ++ subst
    }

    println(substitution)

    // Apply the substitution to the constraint.
    replace(c, substitution)
  }

  /**
    * Returns `true` iff the given `explicitSym` occurs in the given head predicate `h0`.
    */
  def occurs(explicitSym: Symbol.VarSym, h0: TypedAst.Predicate.Head): Boolean = h0 match {
    case TypedAst.Predicate.Head.True(loc) => false
    case TypedAst.Predicate.Head.False(loc) => false
    case TypedAst.Predicate.Head.Positive(sym, terms, loc) => false // TODO: Is it right to return false here?
    case TypedAst.Predicate.Head.PositiveOverloaded(_, terms, implicits, loc) => terms.exists {
      // TODO: Recurse?
      case TypedAst.Expression.Var(sym, tpe, _) => sym == explicitSym
      case _ => false
    }
    case TypedAst.Predicate.Head.Negative(sym, terms, loc) => false // TODO: Remove
  }

  /**
    * Returns `true` iff the given `explicitSym` occurs in the given body predicate `b0`.
    */
  def occurs(explicitSym: Symbol.VarSym, b0: TypedAst.Predicate.Body): Boolean = b0 match {
    case TypedAst.Predicate.Body.Positive(sym, terms ,loc) => false // TODO: Is it right to return false here?
    case TypedAst.Predicate.Body.PositiveOverloaded(_, terms, implicits, loc) => terms.exists {
      // TODO: Recurse?
      case TypedAst.Pattern.Var(sym, tpe, _) => sym == explicitSym
      case _ => false
    }
    case TypedAst.Predicate.Body.Negative(sym, terms ,loc) => false // TODO: Is it right to return false here?
    case TypedAst.Predicate.Body.NegativeOverloaded(_, implicits, loc) => ??? // TODO
  }

  /**
    * Returns a map from types to variable symbols for the given constraint `c`.
    */
  def getType2Symbols(c: TypedAst.Constraint): MultiMap[Type, Symbol.VarSym] = {
    val m = new MultiMap[Type, Symbol.VarSym]
    for (cparam <- c.cparams) {
      m.put(cparam.tpe, cparam.sym)
    }
    m
  }

  /**
    * Returns the unifiable explicit parameters along with their types of the given constraint `c`.
    */
  def explicitUnifiableParamsOf(c: TypedAst.Constraint): List[(Symbol.VarSym, Type)] = c.cparams.collect {
    case TypedAst.ConstraintParam.RuleParam(sym, tpe, loc) if sym.mode == AttributeMode.Explicit => (sym, tpe)
  }

  /**
    * Returns the implicit parameters of the given head predicate `h0`.
    */
  def implicitParamsOf(h0: TypedAst.Predicate.Head): Set[(Symbol.VarSym, Type)] = h0 match {
    case TypedAst.Predicate.Head.True(loc) => Set.empty
    case TypedAst.Predicate.Head.False(loc) => Set.empty
    case TypedAst.Predicate.Head.Positive(_, terms, loc) =>
      terms.foldLeft(Set.empty[(Symbol.VarSym, Type)]) {
        case (sacc, TypedAst.Expression.Var(sym, tpe, _)) => sym.mode match {
          case AttributeMode.Implicit => sacc + ((sym, tpe))
          case AttributeMode.Explicit => sacc
        }
        case (sacc, _) => sacc // TODO: Decide if this needs to be recursive?
      }
    case TypedAst.Predicate.Head.PositiveOverloaded(sym, terms, implicits, loc) => implicits.toSet
    case _ => ??? // TODO: remove negative head predicates.
  }

  /**
    * Returns the implicit parameters of the given body predicate `b0`.
    */
  def implicitParamsOf(b0: TypedAst.Predicate.Body): Set[(Symbol.VarSym, Type)] = b0 match {
    case TypedAst.Predicate.Body.Positive(_, terms, _) =>
      terms.foldLeft(Set.empty[(Symbol.VarSym, Type)]) {
        case (sacc, TypedAst.Pattern.Var(sym, tpe, loc)) => sym.mode match {
          case AttributeMode.Implicit => sacc + ((sym, tpe))
          case AttributeMode.Explicit => sacc
        }
        case (sacc, _) => sacc // TODO: Decide if this needs to be recursive?
      }
    case TypedAst.Predicate.Body.PositiveOverloaded(_, _, implicits, _) => implicits.toSet
    case TypedAst.Predicate.Body.Negative(_, terms, _) => ???
    case TypedAst.Predicate.Body.NegativeOverloaded(_, _, _) => ???
    case TypedAst.Predicate.Body.Filter(sym, terms, loc) => Set.empty // TODO: Correct?
    case TypedAst.Predicate.Body.Loop(sym, term, loc) => Set.empty // TODO: Correct?
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
    case TypedAst.Predicate.Head.PositiveOverloaded(sym, terms, implicits, loc) =>
      val ts = implicits2exps(implicits, subst)
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

    case TypedAst.Predicate.Body.PositiveOverloaded(sym, terms, implicits, loc) =>
      val ts = implicits2pats(implicits, subst)
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

  /**
    * Returns the given list of implicits variables as a list of expressions after applying the substitution `subst`.
    */
  def implicits2exps(implicits: List[(Symbol.VarSym, Type)], subst: Map[Symbol.VarSym, Symbol.VarSym]): List[TypedAst.Expression] = implicits.map {
    case (varSym, tpe) => subst.get(varSym) match {
      case None => TypedAst.Expression.Var(varSym, tpe, varSym.loc)
      case Some(newSym) => TypedAst.Expression.Var(newSym, tpe, varSym.loc)
    }
  }

  /**
    * Returns the given list of implicits variables as a list of patterns after applying the substitution `subst`.
    */
  def implicits2pats(implicits: List[(Symbol.VarSym, Type)], subst: Map[Symbol.VarSym, Symbol.VarSym]): List[TypedAst.Pattern] = implicits.map {
    case (varSym, tpe) => subst.get(varSym) match {
      case None => TypedAst.Pattern.Var(varSym, tpe, varSym.loc)
      case Some(newSym) => TypedAst.Pattern.Var(newSym, tpe, varSym.loc)
    }
  }

}
