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

object Implicits extends Phase[TypedAst.Root, TypedAst.Root] {

  def run(root: TypedAst.Root)(implicit flix: Flix): Validation[TypedAst.Root, CompilationError] = {

    for (stratum <- root.strata) {
      for (constraint <- stratum.constraints) {
        implicify(constraint)
      }
    }

    root.toSuccess
  }


  def implicify(c: TypedAst.Stratum): TypedAst.Stratum = ???

  def implicify(c: TypedAst.Constraint): TypedAst.Constraint = {

    // An equivalence relation on implicit variable symbols that share the same type.
    val m = new MultiMap[Type, Symbol.VarSym]

    for (cparam <- c.cparams) {
      cparam match {
        case TypedAst.ConstraintParam.HeadParam(sym, tpe, loc) =>
        // Nop - no equivalences for head parameters.
        case TypedAst.ConstraintParam.RuleParam(sym, tpe, loc) =>
          // Check if the symbol is implicit.
          if (sym.mode == AttributeMode.Implicit) {

          }
      }

    }

    // TODO: Perform substitution.

    c
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
