package ca.uwaterloo.flix.language.library

import ca.uwaterloo.flix.language.ast.Name
import ca.uwaterloo.flix.language.ast.TypedAst.Type

import scala.collection.immutable

object FBool {

  /**
    * A common super-type for all boolean operations.
    */
  sealed trait BoolOperator extends LibraryOperator

  /**
    * All bool operations.
    */
  val Ops: immutable.Map[Name.Resolved, BoolOperator] = List(
    "Bool/&&" -> and,
    "Bool/||" -> or
  ).map {
    case (name, op) => Name.Resolved.mk(name) -> op
  }.toMap

  /////////////////////////////////////////////////////////////////////////////
  // Logical Operations                                                      //
  /////////////////////////////////////////////////////////////////////////////
  object and extends BoolOperator {
    val tpe = (Type.Bool, Type.Bool) ~> Type.Bool
  }

  object or extends BoolOperator {
    val tpe = (Type.Bool, Type.Bool) ~> Type.Bool
  }

}