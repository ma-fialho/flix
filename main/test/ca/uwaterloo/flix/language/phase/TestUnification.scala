/*
 *  Copyright 2016 Magnus Madsen
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *  http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package ca.uwaterloo.flix.language.phase

import ca.uwaterloo.flix.api.Flix
import ca.uwaterloo.flix.language.ast.{Eff, Kind, SourceLocation, Symbol, Type, TypeConstructor}
import ca.uwaterloo.flix.language.phase.Unification._
import ca.uwaterloo.flix.util.Result
import org.scalatest.FunSuite

class TestUnification extends FunSuite {

  val SL: SourceLocation = SourceLocation.Unknown

  implicit val flix: Flix = new Flix()

  /////////////////////////////////////////////////////////////////////////////
  // Substitutions                                                           //
  /////////////////////////////////////////////////////////////////////////////

  test("Substitution.Empty.01") {
    val tpe = Type.Cst(TypeConstructor.Unit)
    val subst = Unification.Substitution.empty
    assertResult(Type.Cst(TypeConstructor.Unit))(subst(tpe))
  }

  test("Substitution.Empty.02") {
    val tpe = Type.Cst(TypeConstructor.Bool)
    val subst = Unification.Substitution.empty
    assertResult(Type.Cst(TypeConstructor.Bool))(subst(tpe))
  }

  test("Substitution.Empty.03") {
    val tpe = Type.Var(1, Kind.Star)
    val subst = Unification.Substitution.empty
    assertResult(Type.Var(1, Kind.Star))(subst(tpe))
  }

  test("Substitution.Empty.04") {
    val tpe = Type.mkArrow(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Unit))
    val subst = Unification.Substitution.empty
    assertResult(Type.mkArrow(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Unit)))(subst(tpe))
  }

  test("Substitution.Singleton.01") {
    val tpe = Type.Var(1, Kind.Star)
    val subst = Unification.Substitution.singleton(Type.Var(2, Kind.Star), Type.Cst(TypeConstructor.Bool))
    assertResult(Type.Var(1, Kind.Star))(subst(tpe))
  }

  test("Substitution.Singleton.02") {
    val tpe = Type.Var(1, Kind.Star)
    val subst = Unification.Substitution.singleton(Type.Var(1, Kind.Star), Type.Cst(TypeConstructor.Bool))
    assertResult(Type.Cst(TypeConstructor.Bool))(subst(tpe))
  }

  test("Substitution.Singleton.05") {
    val tpe = Type.Var(1, Kind.Star)
    val subst = Unification.Substitution.singleton(Type.Var(1, Kind.Star), Type.Var(2, Kind.Star))
    assertResult(Type.Var(2, Kind.Star))(subst(tpe))
  }

  test("Substitution.++.01") {
    val subst1 = Unification.Substitution.singleton(Type.Var(1, Kind.Star), Type.Cst(TypeConstructor.Bool))
    val subst2 = Unification.Substitution.singleton(Type.Var(2, Kind.Star), Type.Cst(TypeConstructor.Char))

    val tpe = Type.Var(1, Kind.Star)
    assertResult(Type.Cst(TypeConstructor.Bool))((subst1 ++ subst2) (tpe))
  }

  test("Substitution.++.02") {
    val subst1 = Unification.Substitution.singleton(Type.Var(1, Kind.Star), Type.Cst(TypeConstructor.Bool))
    val subst2 = Unification.Substitution.singleton(Type.Var(2, Kind.Star), Type.Cst(TypeConstructor.Char))

    val tpe = Type.Var(2, Kind.Star)
    assertResult(Type.Cst(TypeConstructor.Char))((subst1 ++ subst2) (tpe))
  }

  test("Substitution.++.03") {
    val subst1 = Unification.Substitution.singleton(Type.Var(1, Kind.Star), Type.Cst(TypeConstructor.Bool))
    val subst2 = Unification.Substitution.singleton(Type.Var(1, Kind.Star), Type.Cst(TypeConstructor.Char))

    val tpe = Type.Var(1, Kind.Star)
    assertResult(Type.Cst(TypeConstructor.Bool))((subst1 ++ subst2) (tpe))
  }

  test("Substitution.++.04") {
    val subst1 = Unification.Substitution.singleton(Type.Var(1, Kind.Star), Type.Cst(TypeConstructor.Bool))
    val subst2 = Unification.Substitution.singleton(Type.Var(2, Kind.Star), Type.Cst(TypeConstructor.Char))

    val tpe = Type.mkArrow(Type.Var(1, Kind.Star), Type.Var(2, Kind.Star))
    assertResult(Type.mkArrow(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Char)))((subst1 ++ subst2) (tpe))
  }

  test("Substitution.@@.01") {
    val subst1 = Unification.Substitution.singleton(Type.Var(1, Kind.Star), Type.Cst(TypeConstructor.Bool))
    val subst2 = Unification.Substitution.singleton(Type.Var(2, Kind.Star), Type.Cst(TypeConstructor.Char))

    val tpe = Type.mkArrow(Type.Var(1, Kind.Star), Type.Var(2, Kind.Star))
    assertResult(Type.mkArrow(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Char)))((subst2 @@ subst1) (tpe))
  }

  test("Substitution.@@.02") {
    val subst1 = Unification.Substitution.singleton(Type.Var(1, Kind.Star), Type.Cst(TypeConstructor.Bool))
    val subst2 = Unification.Substitution.singleton(Type.Var(1, Kind.Star), Type.Cst(TypeConstructor.Char))

    val tpe = Type.Var(1, Kind.Star)
    assertResult(Type.Cst(TypeConstructor.Bool))((subst2 @@ subst1) (tpe))
  }

  test("Substitution.@@.03") {
    val subst1 = Unification.Substitution.singleton(Type.Var(1, Kind.Star), Type.Var(2, Kind.Star))
    val subst2 = Unification.Substitution.singleton(Type.Var(2, Kind.Star), Type.Cst(TypeConstructor.Bool))

    val tpe = Type.Var(1, Kind.Star)
    assertResult(Type.Cst(TypeConstructor.Bool))((subst2 @@ subst1) (tpe))
  }

  test("Substitution.@@.04") {
    val subst1 = Unification.Substitution.singleton(Type.Var(1, Kind.Star), Type.Var(2, Kind.Star))
    val subst2 = Unification.Substitution.singleton(Type.Var(2, Kind.Star), Type.Var(3, Kind.Star))
    val subst3 = Unification.Substitution.singleton(Type.Var(3, Kind.Star), Type.Cst(TypeConstructor.Bool))

    val tpe = Type.Var(1, Kind.Star)
    assertResult(Type.Cst(TypeConstructor.Bool))((subst3 @@ (subst2 @@ subst1)) (tpe))
  }

  test("Unify.Var.01") {
    val result = Unification.unifyTypes(Type.Var(1, Kind.Star), Type.Cst(TypeConstructor.Unit))
    assert(isOk(result))
  }

  test("Unify.Var.02") {
    val result = Unification.unifyTypes(Type.Cst(TypeConstructor.Unit), Type.Var(1, Kind.Star))
    assert(isOk(result))
  }

  test("Unify.Var.03") {
    val result = Unification.unifyTypes(Type.Var(1, Kind.Star), Type.Var(1, Kind.Star))
    assert(isOk(result))
  }

  test("Unify.Var.04") {
    val result = Unification.unifyTypes(Type.Var(1, Kind.Star), Type.Var(2, Kind.Star))
    assert(isOk(result))
  }

  test("Unify.Unit") {
    val result = Unification.unifyTypes(Type.Cst(TypeConstructor.Unit), Type.Cst(TypeConstructor.Unit))
    assert(isOk(result))
  }

  test("Unify.Bool") {
    val result = Unification.unifyTypes(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Bool))
    assert(isOk(result))
  }

  test("Unify.Char") {
    val result = Unification.unifyTypes(Type.Cst(TypeConstructor.Char), Type.Cst(TypeConstructor.Char))
    assert(isOk(result))
  }

  test("Unify.Float32") {
    val result = Unification.unifyTypes(Type.Cst(TypeConstructor.Float32), Type.Cst(TypeConstructor.Float32))
    assert(isOk(result))
  }

  test("Unify.Float64") {
    val result = Unification.unifyTypes(Type.Cst(TypeConstructor.Float64), Type.Cst(TypeConstructor.Float64))
    assert(isOk(result))
  }

  test("Unify.Int8") {
    val result = Unification.unifyTypes(Type.Cst(TypeConstructor.Int8), Type.Cst(TypeConstructor.Int8))
    assert(isOk(result))
  }

  test("Unify.Int16") {
    val result = Unification.unifyTypes(Type.Cst(TypeConstructor.Int16), Type.Cst(TypeConstructor.Int16))
    assert(isOk(result))
  }

  test("Unify.Int32") {
    val result = Unification.unifyTypes(Type.Cst(TypeConstructor.Int32), Type.Cst(TypeConstructor.Int32))
    assert(isOk(result))
  }

  test("Unify.Int64") {
    val result = Unification.unifyTypes(Type.Cst(TypeConstructor.Int64), Type.Cst(TypeConstructor.Int64))
    assert(isOk(result))
  }

  test("Unify.BigInt") {
    val result = Unification.unifyTypes(Type.Cst(TypeConstructor.BigInt), Type.Cst(TypeConstructor.BigInt))
    assert(isOk(result))
  }

  test("Unify.Str") {
    val result = Unification.unifyTypes(Type.Cst(TypeConstructor.Str), Type.Cst(TypeConstructor.Str))
    assert(isOk(result))
  }

  test("Unify.Arrow") {
    val result = Unification.unifyTypes(Type.Arrow(Eff.Pure, 3), Type.Arrow(Eff.Pure, 3))
    assert(isOk(result))
  }

  test("Unify.Zero") {
    val result = Unification.unifyTypes(Type.Zero, Type.Zero)
    assert(isOk(result))
  }

  test("Unify.ZeroSucc.01") {
    val result = Unification.unifyTypes(Type.Zero, Type.Succ(0, Type.Zero))
    assert(isOk(result))
  }

  test("Unify.ZeroSucc.02") {
    val result = Unification.unifyTypes(Type.Succ(0, Type.Zero), Type.Zero)
    assert(isOk(result))
  }

  test("Unify.Succ.01") {
    val freshVar = Type.Var(1, Kind.Star)
    val result = Unification.unifyTypes(Type.Succ(1, freshVar), Type.Succ(1, freshVar))
    assert(isOk(result))
  }

  test("Unify.Succ.02") {
    val freshVar = Type.Var(1, Kind.Star)
    val result = Unification.unifyTypes(Type.Succ(1, freshVar), Type.Succ(2, freshVar))
    assert(isOk(result))
  }

  test("Unify.Succ.03") {
    val freshVar = Type.Var(1, Kind.Star)
    val freshVar2 = Type.Var(1, Kind.Star)
    val result = Unification.unifyTypes(Type.Succ(1, freshVar), Type.Succ(2, freshVar2))
    assert(isOk(result))
  }

  test("Unify.Succ.04") {
    val freshVar = Type.Var(1, Kind.Star)
    val result = Unification.unifyTypes(Type.Succ(1, freshVar), Type.Succ(2, Type.Zero))
    assert(isOk(result))
  }

  test("Unify.Succ.05") {
    val freshVar = Type.Var(1, Kind.Star)
    val tpe1 = Type.mkApply(Type.Cst(TypeConstructor.Vector), Type.Cst(TypeConstructor.Bool) :: Type.Succ(7, Type.Zero) :: Nil)
    val tpe2 = Type.mkApply(Type.Cst(TypeConstructor.Vector), Type.Cst(TypeConstructor.Bool) :: Type.Succ(5, freshVar) :: Nil)
    val result = Unification.unifyTypes(tpe1, tpe2)
    assert(isOk(result))
  }

  test("Unify.Succ.06") {
    val freshVar = Type.Var(1, Kind.Star)
    val freshVar2 = Type.Var(1, Kind.Star)
    val result = Unification.unifyTypes(Type.Succ(1, freshVar), Type.Succ(2, Type.Zero))
    assert(isOk(result))
  }

  test("Unify.Enum.01") {
    val sym = Symbol.mkEnumSym("Color")
    val result = Unification.unifyTypes(Type.Cst(TypeConstructor.Enum(sym, Kind.Star)), Type.Cst(TypeConstructor.Enum(sym, Kind.Star)))
    assert(isOk(result))
  }

  test("Unify.01") {
    val tpe1 = Type.Var(1, Kind.Star)
    val tpe2 = Type.Cst(TypeConstructor.Bool)
    val result = Unification.unifyTypes(tpe1, tpe2).get
    assertResult(Type.Cst(TypeConstructor.Bool))(result(tpe1))
  }

  test("Unify.02") {
    val tpe1 = Type.Cst(TypeConstructor.Bool)
    val tpe2 = Type.Var(1, Kind.Star)
    val result = Unification.unifyTypes(tpe1, tpe2).get
    assertResult(Type.Cst(TypeConstructor.Bool))(result(tpe2))
  }

  test("Unify.03") {
    val A = Type.Var(1, Kind.Star)
    val tpe1 = Type.mkArrow(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Char))
    val tpe2 = Type.mkArrow(Type.Cst(TypeConstructor.Bool), A)
    val result = Unification.unifyTypes(tpe1, tpe2).get
    assertResult(Type.Cst(TypeConstructor.Char))(result(A))
  }

  test("Unify.04") {
    val A = Type.Var(1, Kind.Star)
    val tpe1 = Type.mkArrow(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Char))
    val tpe2 = Type.mkArrow(Type.Cst(TypeConstructor.Bool), A)
    val result = Unification.unifyTypes(tpe1, tpe2).get
    assertResult(Type.Cst(TypeConstructor.Char))(result(A))
  }

  test("Unify.05") {
    val A = Type.Var(1, Kind.Star)
    val tpe1 = Type.mkArrow(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Char))
    val tpe2 = A
    val result = Unification.unifyTypes(tpe1, tpe2).get
    assertResult(tpe1)(result(A))
  }

  test("Unify.06") {
    val A = Type.Var(1, Kind.Star)
    val tpe1 = A
    val tpe2 = Type.mkArrow(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Char))
    val result = Unification.unifyTypes(tpe1, tpe2).get
    assertResult(tpe2)(result(A))
  }

  test("Unify.07") {
    val A = Type.Var(1, Kind.Star)
    val tpe1 = Type.mkArrow(A, Type.Cst(TypeConstructor.Bool))
    val tpe2 = Type.mkArrow(Type.Cst(TypeConstructor.Bool), A)
    val result = Unification.unifyTypes(tpe1, tpe2).get
    assertResult(Type.Cst(TypeConstructor.Bool))(result(A))
  }

  test("Unify.08") {
    val A = Type.Var(1, Kind.Star)
    val B = Type.Var(2, Kind.Star)
    val tpe1 = Type.mkArrow(A, B)
    val tpe2 = Type.mkArrow(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Char))
    val result = Unification.unifyTypes(tpe1, tpe2).get
    assertResult(Type.Cst(TypeConstructor.Bool))(result(A))
    assertResult(Type.Cst(TypeConstructor.Char))(result(B))
  }

  test("Unify.09") {
    val A = Type.Var(1, Kind.Star)
    val B = Type.Var(2, Kind.Star)
    val tpe1 = Type.mkArrow(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Char))
    val tpe2 = Type.mkArrow(A, B)
    val result = Unification.unifyTypes(tpe1, tpe2).get
    assertResult(Type.Cst(TypeConstructor.Bool))(result(A))
    assertResult(Type.Cst(TypeConstructor.Char))(result(B))
  }

  test("Unify.10") {
    val A = Type.Var(1, Kind.Star)
    val B = Type.Var(2, Kind.Star)
    val tpe1 = Type.mkArrow(A, Type.Cst(TypeConstructor.Char))
    val tpe2 = Type.mkArrow(Type.Cst(TypeConstructor.Bool), B)
    val result = Unification.unifyTypes(tpe1, tpe2).get
    assertResult(Type.Cst(TypeConstructor.Bool))(result(A))
    assertResult(Type.Cst(TypeConstructor.Char))(result(B))
  }

  test("Unify.11") {
    val A = Type.Var(1, Kind.Star)
    val B = Type.Var(2, Kind.Star)
    val C = Type.Var(3, Kind.Star)
    val tpe1 = Type.mkArrow(A, B)
    val tpe2 = Type.mkArrow(C, Type.Cst(TypeConstructor.Bool))
    val result = Unification.unifyTypes(tpe1, tpe2).get
    assertResult(Type.Cst(TypeConstructor.Bool))(result(B))
    assertResult(C)(result(A))
  }

  test("liftM.01") {
    val subst0 = Substitution.empty
    val result = Unification.liftM(Type.Cst(TypeConstructor.Bool), subst0).run(subst0)
    val (_, tpe) = result.get
    assertResult(Type.Cst(TypeConstructor.Bool))(tpe)
  }

  test("liftM.02") {
    val tpe1 = Type.Var(1, Kind.Star)
    val tpe2 = Type.Cst(TypeConstructor.Bool)
    val subst0 = Substitution.singleton(tpe1, tpe2)
    val result = Unification.liftM(tpe1, subst0).run(subst0)
    val (subst, _) = result.get
    assertResult(Type.Cst(TypeConstructor.Bool))(subst.typeMap(tpe1))
  }

  test("unifyM.01") {
    val subst0 = Substitution.empty
    val result = Unification.unifyTypM(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Bool), SL).run(subst0)
    assert(isOk(result))
  }

  test("unifyM.02") {
    val subst0 = Substitution.empty
    val result = Unification.unifyTypM(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Char), SL).run(subst0)
    assert(!isOk(result))
  }

  test("unifyM.03") {
    val tpe1 = Type.Var(1, Kind.Star)
    val tpe2 = Type.Cst(TypeConstructor.Bool)
    val subst0 = Substitution.empty
    val result = Unification.unifyTypM(tpe1, tpe2, SL).run(subst0)
    val (subst, tpe) = result.get
    assertResult(Type.Cst(TypeConstructor.Bool))(subst(tpe1))
    assertResult(Type.Cst(TypeConstructor.Bool))(subst(tpe2))
    assertResult(Type.Cst(TypeConstructor.Bool))(tpe)
  }

  test("seqM.01") {
    val subst0 = Substitution.empty
    val res1 = Unification.unifyTypM(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Bool), SL)
    val res2 = Unification.unifyTypM(Type.Cst(TypeConstructor.Char), Type.Cst(TypeConstructor.Char), SL)
    val result = seqM(List(res1, res2)).run(subst0)
    assert(isOk(result))
  }

  test("seqM.02") {
    val subst0 = Substitution.empty
    val res1 = Unification.unifyTypM(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Char), SL)
    val res2 = Unification.unifyTypM(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Char), SL)
    val result = seqM(List(res1, res2)).run(subst0)
    assert(!isOk(result))
  }

  test("seqM.03") {
    val subst0 = Substitution.empty
    val res1 = Unification.unifyTypM(Type.Var(1, Kind.Star), Type.Cst(TypeConstructor.Bool), SL)
    val res2 = Unification.unifyTypM(Type.Var(2, Kind.Star), Type.Cst(TypeConstructor.Char), SL)
    val res3 = Unification.unifyTypM(Type.Var(3, Kind.Star), Type.mkTuple(List(Type.Var(1, Kind.Star), Type.Var(2, Kind.Star))), SL)
    val result = seqM(List(res1, res2, res3)).run(subst0)
    val (subst, tpe) = result.get
    assertResult(Type.Cst(TypeConstructor.Bool))(subst.typeMap(Type.Var(1, Kind.Star)))
    assertResult(Type.Cst(TypeConstructor.Char))(subst.typeMap(Type.Var(2, Kind.Star)))
    assertResult(Type.mkTuple(List(Type.Cst(TypeConstructor.Bool), Type.Cst(TypeConstructor.Char))))(subst.typeMap(Type.Var(3, Kind.Star)))
  }

  private def isOk[T, E](r: Result[T, E]) = r match {
    case Result.Ok(_) => true
    case Result.Err(_) => false
  }

}
