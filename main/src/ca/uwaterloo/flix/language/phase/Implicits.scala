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
    val substitution = substitutions.reduce(_ ++ _)

    // Apply the substitution to the constraint.
    replace(c, substitution)
  }

  /**
    * Picks a representative from the the set `s` and returns a substitution map
    * replacing every other symbols with the picked representative.
    */
  def getSubstitution(xs: Set[Symbol.VarSym]): Map[Symbol.VarSym, Symbol.VarSym] = ???

  // TODO
  def replace(c: TypedAst.Constraint, subst: Map[Symbol.VarSym, Symbol.VarSym]): TypedAst.Constraint = ???

  def replace(p: TypedAst.Predicate.Head, subst: Map[Symbol.VarSym, Symbol.VarSym]): TypedAst.Constraint = ???

  def replace(p: TypedAst.Predicate.Body, subst: Map[Symbol.VarSym, Symbol.VarSym]): TypedAst.Constraint = ???

  // TODO: Replace in patterns/expressions?


}
