package ca.uwaterloo.flix.language.phase

import ca.uwaterloo.flix.language.ast.{SimplifiedAst, TypedAst}

/**
  * A phase that simplifies a Typed AST by:
  *
  * - Compiles literals to expressions.
  * - Eliminates match expressions.
  * - Numbers every variable.
  */
object Simplifier {

  def simplify(tast: TypedAst.Root)(implicit genSym: GenSym): SimplifiedAst.Root = {
    val constants = tast.constants.mapValues(Definition.simplify)
    val directives = Directives.simplify(tast.directives)
    val lattices = tast.lattices.mapValues(Definition.simplify)
    val collections = tast.collections.mapValues(Collection.simplify)
    val indexes = tast.indexes.mapValues(Definition.simplify)
    val facts = tast.facts.map(Constraint.simplify)
    val rules = tast.rules.map(Constraint.simplify)
    val time = tast.time

    SimplifiedAst.Root(constants, directives, lattices, collections, indexes, facts, rules, time)
  }

  object Collection {
    def simplify(tast: TypedAst.Collection)(implicit genSym: GenSym): SimplifiedAst.Collection = tast match {
      case TypedAst.Collection.Relation(name, attributes, loc) =>
        SimplifiedAst.Collection.Relation(name, attributes.map(Simplifier.simplify), loc)
      case TypedAst.Collection.Lattice(name, keys, values, loc) =>
        SimplifiedAst.Collection.Lattice(name, keys.map(Simplifier.simplify), values.map(Simplifier.simplify), loc)
    }
  }

  object Constraint {
    def simplify(tast: TypedAst.Constraint.Fact)(implicit genSym: GenSym): SimplifiedAst.Constraint.Fact =
      SimplifiedAst.Constraint.Fact(Predicate.Head.simplify(tast.head))

    def simplify(tast: TypedAst.Constraint.Rule)(implicit genSym: GenSym): SimplifiedAst.Constraint.Rule = {
      implicit val genSym = new GenSym
      val head = Predicate.Head.simplify(tast.head)
      val body = tast.body.map(Predicate.Body.simplify)
      SimplifiedAst.Constraint.Rule(head, body)
    }
  }

  object Definition {
    def simplify(tast: TypedAst.Definition.BoundedLattice)(implicit genSym: GenSym): SimplifiedAst.Definition.Lattice = tast match {
      case TypedAst.Definition.BoundedLattice(tpe, bot, top, leq, lub, glb, loc) =>
        import Expression.{simplify => s}
        SimplifiedAst.Definition.Lattice(tpe, s(bot), s(top), s(leq), s(lub), s(glb), loc)
    }

    def simplify(tast: TypedAst.Definition.Constant)(implicit genSym: GenSym): SimplifiedAst.Definition.Constant =
      SimplifiedAst.Definition.Constant(tast.name, Expression.simplify(tast.exp), tast.tpe, tast.loc)

    def simplify(tast: TypedAst.Definition.Index)(implicit genSym: GenSym): SimplifiedAst.Definition.Index =
      SimplifiedAst.Definition.Index(tast.name, tast.indexes, tast.loc)
  }

  object Directives {
    def simplify(tast: TypedAst.Directives)(implicit genSym: GenSym): SimplifiedAst.Directives =
      SimplifiedAst.Directives(tast.directives map simplify)

    def simplify(tast: TypedAst.Directive)(implicit genSym: GenSym): SimplifiedAst.Directive = tast match {
      case TypedAst.Directive.AssertFact(fact, loc) => throw new UnsupportedOperationException // TODO: To be removed?
      case TypedAst.Directive.AssertRule(fact, loc) => throw new UnsupportedOperationException // TODO: To be removed?
      case TypedAst.Directive.Print(fact, loc) => throw new UnsupportedOperationException // TODO: To be removed?
    }
  }

  object Expression {
    def simplify(tast: TypedAst.Expression)(implicit genSym: GenSym): SimplifiedAst.Expression = tast match {
      case TypedAst.Expression.Lit(lit, tpe, loc) => Literal.simplify(lit)
      case TypedAst.Expression.Var(ident, tpe, loc) => SimplifiedAst.Expression.Var(ident, tpe, loc)
      case TypedAst.Expression.Ref(name, tpe, loc) => SimplifiedAst.Expression.Ref(name, tpe, loc)
      case TypedAst.Expression.Lambda(annotations, args, body, tpe, loc) =>
        SimplifiedAst.Expression.Lambda(annotations, args map Simplifier.simplify, simplify(body), tpe, loc)
      case TypedAst.Expression.Apply(e, args, tpe, loc) =>
        SimplifiedAst.Expression.Apply(simplify(e), args map simplify, tpe, loc)
      case TypedAst.Expression.Unary(op, e, tpe, loc) =>
        SimplifiedAst.Expression.Unary(op, simplify(e), tpe, loc)
      case TypedAst.Expression.Binary(op, e1, e2, tpe, loc) =>
        SimplifiedAst.Expression.Binary(op, simplify(e1), simplify(e2), tpe, loc)
      case TypedAst.Expression.IfThenElse(e1, e2, e3, tpe, loc) =>
        SimplifiedAst.Expression.IfThenElse(simplify(e1), simplify(e2), simplify(e3), tpe, loc)
      case TypedAst.Expression.Let(ident, e1, e2, tpe, loc) =>
        SimplifiedAst.Expression.Let(ident, simplify(e1), simplify(e2), tpe, loc)

      case TypedAst.Expression.Match(exp, rules, tpe, loc) =>
        val name = genSym.fresh()
        // TODO: This should probably be in a let binding
        val valueExp = simplify(exp)
        val zero = SimplifiedAst.Expression.MatchError(tpe, loc)
        rules.foldRight(zero: SimplifiedAst.Expression) {
          case (rule, acc) => Pattern.simplify(valueExp, rule, acc)
        }
      case TypedAst.Expression.Tag(enum, tag, e, tpe, loc) =>
        SimplifiedAst.Expression.Tag(enum, tag, simplify(e), tpe, loc)
      case TypedAst.Expression.Tuple(elms, tpe, loc) =>
        SimplifiedAst.Expression.Tuple(elms map simplify, tpe, loc)
      case TypedAst.Expression.Set(elms, tpe, loc) =>
        SimplifiedAst.Expression.Set(elms map simplify, tpe, loc)
      case TypedAst.Expression.Error(tpe, loc) =>
        SimplifiedAst.Expression.Error(tpe, loc)
      case TypedAst.Expression.NativeField(field, tpe, loc) => throw new UnsupportedOperationException // TODO: To be removed?
      case TypedAst.Expression.NativeMethod(method, tpe, loc) => throw new UnsupportedOperationException // TODO: To be removed?
    }
  }

  object Pattern {
    def simplify(valueExp: SimplifiedAst.Expression, rule: (TypedAst.Pattern, TypedAst.Expression), elseExp: SimplifiedAst.Expression)(implicit genSym: GenSym): SimplifiedAst.Expression = {
      val (pat, matchExp) = rule

      pat match {
        case TypedAst.Pattern.Var(ident, tpe, loc) => ???
      }

      ???
    }
  }

  object Literal {
    def simplify(tast: TypedAst.Literal)(implicit genSym: GenSym): SimplifiedAst.Expression = tast match {
      case TypedAst.Literal.Unit(loc) => SimplifiedAst.Expression.Unit
      case TypedAst.Literal.Bool(b, loc) =>
        if (b) SimplifiedAst.Expression.True else SimplifiedAst.Expression.False
      case TypedAst.Literal.Int(i, loc) => SimplifiedAst.Expression.Int(i)
      case TypedAst.Literal.Str(s, loc) => SimplifiedAst.Expression.Str(s, loc)
      case TypedAst.Literal.Tag(enum, tag, lit, tpe, loc) => SimplifiedAst.Expression.Tag(enum, tag, simplify(lit), tpe, loc)
      case TypedAst.Literal.Tuple(elms, tpe, loc) => SimplifiedAst.Expression.Tuple(elms map simplify, tpe, loc)
      case TypedAst.Literal.Set(elms, tpe, loc) => SimplifiedAst.Expression.Set(elms map simplify, tpe, loc)
    }
  }

  object Predicate {

    object Head {
      def simplify(tast: TypedAst.Predicate.Head)(implicit genSym: GenSym): SimplifiedAst.Predicate.Head = tast match {
        case TypedAst.Predicate.Head.Relation(name, terms, tpe, loc) =>
          SimplifiedAst.Predicate.Head.Relation(name, terms map Term.simplify, tpe, loc)
        case TypedAst.Predicate.Head.Error(terms, tpe, loc) => throw new UnsupportedOperationException // TODO: To be removed?
        case TypedAst.Predicate.Head.Trace(terms, tpe, loc) => throw new UnsupportedOperationException // TODO: To be removed?
        case TypedAst.Predicate.Head.Write(terms, path, tpe, loc) => throw new UnsupportedOperationException // TODO: To be removed?
      }
    }

    object Body {
      def simplify(tast: TypedAst.Predicate.Body)(implicit genSym: GenSym): SimplifiedAst.Predicate.Body = tast match {
        case TypedAst.Predicate.Body.Collection(name, terms, tpe, loc) =>
          SimplifiedAst.Predicate.Body.Collection(name, terms map Term.simplify, tpe, loc)
        case TypedAst.Predicate.Body.Function(name, terms, tpe, loc) =>
          SimplifiedAst.Predicate.Body.Function(name, terms map Term.simplify, tpe, loc)
        case TypedAst.Predicate.Body.NotEqual(ident1, ident2, tpe, loc) =>
          SimplifiedAst.Predicate.Body.NotEqual(ident1, ident2, tpe, loc)
        case TypedAst.Predicate.Body.Loop(ident, term, tpe, loc) =>
          SimplifiedAst.Predicate.Body.Loop(ident, Term.simplify(term), tpe, loc)
        case TypedAst.Predicate.Body.Read(terms, path, tpe, loc) => throw new UnsupportedOperationException // TODO: to be removed?
      }
    }

  }

  object Term {
    def simplify(tast: TypedAst.Term.Head)(implicit genSym: GenSym): SimplifiedAst.Term.Head = tast match {
      case TypedAst.Term.Head.Var(ident, tpe, loc) => SimplifiedAst.Term.Head.Var(ident, tpe, loc)
      case TypedAst.Term.Head.Lit(lit, tpe, loc) => SimplifiedAst.Term.Head.Exp(Literal.simplify(lit), tpe, loc)
      case TypedAst.Term.Head.Apply(name, args, tpe, loc) => SimplifiedAst.Term.Head.Apply(name, args map simplify, tpe, loc)
      case TypedAst.Term.Head.NativeField(field, tpe, loc) => throw new UnsupportedOperationException // TODO: to be removed?
    }

    def simplify(tast: TypedAst.Term.Body)(implicit genSym: GenSym): SimplifiedAst.Term.Body = tast match {
      case TypedAst.Term.Body.Wildcard(tpe, loc) => SimplifiedAst.Term.Body.Wildcard(tpe, loc)
      case TypedAst.Term.Body.Var(ident, tpe, loc) => SimplifiedAst.Term.Body.Var(genSym.of(ident), tpe, loc)
      case TypedAst.Term.Body.Lit(lit, tpe, loc) => SimplifiedAst.Term.Body.Exp(Literal.simplify(lit), tpe, loc)
    }
  }

  def simplify(tast: TypedAst.Attribute): SimplifiedAst.Attribute =
    SimplifiedAst.Attribute(tast.ident, tast.tpe)

  def simplify(tast: TypedAst.FormalArg): SimplifiedAst.FormalArg =
    SimplifiedAst.FormalArg(tast.ident, tast.tpe)
}