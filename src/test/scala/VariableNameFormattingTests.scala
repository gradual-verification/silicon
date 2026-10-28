// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.tests

import org.scalatest.Outcome
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.{Config, Map}
import viper.silicon.logger.{LogConfig, MemberSymbExLog, SymbExLog, SymbExLogger}
import viper.silicon.state.{Heap, Identifier, State, Store}
import viper.silicon.state.terms.{Forall, IntLiteral, Quantification, Term, True, Var, sorts}
import viper.silicon.verifier.Verifier
import viper.silver.ast

class VariableNameFormattingTests extends AnyFunSuite {
  override protected def withFixture(test: NoArgTest): Outcome = SymbExLogger.synchronized {
    val previousConfig = Verifier.config
    val previousFinder = SymbExLogger.sourceNameFinder
    val previousLoggers = SymbExLogger.loggers.keySet.toSet
    Verifier.config = new Config(Seq())
    SymbExLogger.sourceNameFinder = Some {
      case node: ast.Infoed => node.info.comment.headOption
      case _ => None
    }
    try super.withFixture(test)
    finally {
      SymbExLogger.sourceNameFinder = previousFinder
      SymbExLogger.loggers.keys.filterNot(previousLoggers.contains).toList.foreach { logger =>
        SymbExLogger.loggers.remove(logger)
      }
      Verifier.config = previousConfig
    }
  }

  private def declaration(encodedName: String, sourceName: String): ast.LocalVarDecl =
    ast.LocalVarDecl(encodedName, ast.Int)(info = ast.SimpleInfo(Seq(sourceName)))

  private def reference(encodedName: String, sourceName: String): ast.LocalVar =
    ast.LocalVar(encodedName, ast.Int)(info = ast.SimpleInfo(Seq(sourceName)))

  private def symbol(encodedName: String): Var =
    Var(Identifier(encodedName, "@", "0"), sorts.Int, false)

  private def newLogger(member: ast.Method = ast.Method("test", Nil, Nil, Nil, Nil, None)()): MemberSymbExLog = {
    val config = LogConfig.default()
    // Formatting and member registration do not require a path-condition stack.
    new MemberSymbExLog(SymbExLog(config), config, member, null)
  }

  private def state(bindings: (ast.AbstractLocalVar, Term)*): State =
    State(
      g = Store(bindings.map { case (variable, term) => variable -> (term, None) }),
      program = ast.Program(Nil, Nil, Nil, Nil, Nil, Nil)(),
      currentMember = None,
      currentBlock = None,
      predicateData = Map.empty,
      functionData = Map.empty)

  test("opening a member registers parameter, local declaration, and reference aliases") {
    val parameter = declaration("input_0", "input")
    val local = declaration("total_1", "total")
    val alias = reference("temporary_2", "total")
    val body = ast.Seqn(Seq(ast.LocalVarAssign(alias, parameter.localVar)()), Seq(local))()
    val member = ast.Method("test", Seq(parameter), Nil, Nil, Nil, Some(body))()
    val logger = newLogger(member)
    logger.openMemberScope()

    val inputTerm = symbol(parameter.name)
    val localTerm = symbol(local.name)
    val aliasTerm = symbol(alias.name)
    val current = state(parameter.localVar -> inputTerm, local.localVar -> localTerm, alias -> aliasTerm)
    logger.freshTerms.update(localTerm, IntLiteral(3))

    assert(logger.formatTerm(inputTerm, current) == "input")
    assert(logger.formatTerm(localTerm, current) == "total")
    assert(logger.formatTerm(aliasTerm, current) == "total")
  }

  test("variable registration accepts ordinary and versioned local references") {
    val logger = newLogger()
    val local = reference("value_4", "value")
    val versioned = ast.LocalVarWithVersion("previous_5", ast.Int)(info = ast.SimpleInfo(Seq("previous")))
    logger.registerVariable(local)
    logger.registerVariable(versioned)

    assert(logger.variableName(local.name) == "value")
    assert(logger.variableName(versioned.name) == "previous")
  }

  test("missing source metadata preserves the encoded variable name") {
    val logger = newLogger()
    val local = ast.LocalVar("unmapped_12", ast.Int)()
    val term = symbol(local.name)
    logger.registerVariable(local)

    assert(logger.variableName(local.name) == local.name)
    assert(logger.formatTerm(term, state(local -> term)) == "unmapped_12")
  }

  test("versioned debugger variables retain names under their full verifier identifier") {
    val logger = newLogger()
    val versioned = ast.LocalVarWithVersion("value_4", ast.Int)(info = ast.SimpleInfo(Seq("value")))
    val term = Var(Identifier(versioned.name + "@worker"), sorts.Int, false)
    logger.registerVariable(versioned, term.id.name)

    assert(logger.formatTerm(term, state()) == "value")
  }

  test("missing source-name callback preserves the encoded variable name") {
    SymbExLogger.sourceNameFinder = None
    val logger = newLogger()
    val local = reference("value_12", "value")
    val term = symbol(local.name)
    logger.registerVariable(local)

    assert(logger.variableName(local.name) == local.name)
    assert(logger.formatTerm(term, state(local -> term)) == "value_12")
  }

  test("source names containing underscores and numeric suffixes are preserved exactly") {
    val logger = newLogger()
    val local = reference("source_name_42_3", "source_name_42")
    val term = symbol(local.name)
    logger.registerVariable(local)

    assert(logger.formatTerm(term, state(local -> term)) == "source_name_42")
  }

  test("old and loop-entry values use the source variable name") {
    val logger = newLogger()
    val local = reference("count_6", "count")
    val term = symbol(local.name)
    logger.registerVariable(local)
    val current = state()

    assert(logger.formatTerm(term, current) == "old(count)")
    assert(logger.formatTerm(term, current.copy(invariantContexts = Seq(Heap()))) == "in(count)")
  }

  test("quantifier declarations use source names for suffixed and plain identifiers") {
    val logger = newLogger()
    val variable = declaration("index_6", "index")
    logger.registerVariable(variable)
    val suffixed = symbol(variable.name)
    val plain = Var(Identifier(variable.name), sorts.Int, false)
    val quantified = Quantification(Forall, Seq(suffixed), True, Nil)

    assert(logger.formatQVar(suffixed) == "index Int")
    assert(logger.formatQVar(plain) == "index Int")
    assert(logger.formatTerm(plain, state()) == "index")
    assert(logger.formatTerm(quantified, state()) == "forall index Int :: (true)")
  }

  test("store bindings sharing a symbolic term retain distinct source names") {
    val logger = newLogger()
    val left = reference("left_1", "left")
    val right = reference("right_2", "right")
    logger.registerVariables(ast.LocalVarAssign(right, left)())
    val shared = symbol(left.name)
    val current = state(left -> shared, right -> shared)
    val displayedNames = current.g.values.keys.map(variable => logger.variableName(variable.name)).toSet

    assert(displayedNames == Set("left", "right"))
    assert(logger.formatTerm(shared, current) == "left")
  }

  test("variable names are isolated per member and cleared when its maps reset") {
    val first = newLogger()
    val second = newLogger()
    first.registerVariable(reference("value_0", "first"))
    assert(second.variableName("value_0") == "value_0")
    second.registerVariable(reference("value_0", "second"))

    assert(first.variableName("value_0") == "first")
    assert(second.variableName("value_0") == "second")
    first.resetMaps()
    assert(first.variableName("value_0") == "value_0")
    assert(second.variableName("value_0") == "second")
  }

  test("resetting logger maps retains names declared by its member") {
    val parameter = declaration("input_0", "input")
    val member = ast.Method("test", Seq(parameter), Nil, Nil, Nil, None)()
    val logger = newLogger(member)
    logger.openMemberScope()
    logger.registerVariable(reference("temporary_1", "temporary"))
    logger.resetMaps()

    assert(logger.variableName(parameter.name) == "input")
    assert(logger.variableName("temporary_1") == "temporary_1")
  }
}
