// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.tests

import java.nio.file.Paths
import org.scalatest.Outcome
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.{Config, Map}
import viper.silicon.logger.{LogConfig, MemberSymbExLog, SymbExLog, SymbExLogger}
import viper.silicon.resources.PredicateID
import viper.silicon.state.{BasicChunk, BasicChunkIdentifier, Identifier, State, Store}
import viper.silicon.state.terms.{App, FullPerm, HeapDepFun, IntLiteral, Term, Unit => SnapshotUnit, sorts}
import viper.silicon.verifier.Verifier
import viper.silver.ast

class MemberNameFormattingTests extends AnyFunSuite {
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

  private def info(sourceName: Option[String]): ast.Info =
    sourceName.fold[ast.Info](ast.NoInfo)(name => ast.SimpleInfo(Seq(name)))

  private def newLogger(): MemberSymbExLog = {
    val config = LogConfig.default()
    val member = ast.Method("test", Nil, Nil, Nil, Nil, None)()
    // Formatting does not inspect the member's path-condition stack.
    new MemberSymbExLog(SymbExLog(config), config, member, null)
  }

  private def state(functions: Seq[ast.Function] = Nil, predicates: Seq[ast.Predicate] = Nil): State =
    State(
      g = Store(),
      program = ast.Program(Nil, Nil, functions, predicates, Nil, Nil)(),
      currentMember = None,
      currentBlock = None,
      predicateData = Map.empty,
      functionData = Map.empty)

  private def function(encodedName: String, sourceName: Option[String]): ast.Function =
    ast.Function(encodedName, Seq(ast.LocalVarDecl("left", ast.Int)(), ast.LocalVarDecl("right", ast.Int)()),
      ast.Int, Nil, Nil, None)(info = info(sourceName))

  private def application(encodedName: String,
                          sourceName: Option[String],
                          position: ast.Position = ast.NoPosition): ast.FuncApp =
    ast.FuncApp(encodedName, Seq(ast.IntLit(7)(), ast.IntLit(9)()))(
      position, info(sourceName), ast.Int, ast.NoTrafos)

  private def functionTerm(encodedName: String): Term =
    App(HeapDepFun(Identifier(encodedName), Seq(sorts.Snap, sorts.Int, sorts.Int), sorts.Int),
      Seq(SnapshotUnit, IntLiteral(7), IntLiteral(9)))

  private def predicate(encodedName: String, sourceName: Option[String]): ast.Predicate =
    ast.Predicate(encodedName, Seq(ast.LocalVarDecl("arg", ast.Int)()), None)(info = info(sourceName))

  private def access(encodedName: String, sourceName: Option[String], argument: Int = 1): ast.PredicateAccess =
    ast.PredicateAccess(Seq(ast.IntLit(argument)()), encodedName)(info = info(sourceName))

  private def chunk(encodedName: String, argument: Int = 1): BasicChunk =
    BasicChunk(PredicateID, BasicChunkIdentifier(encodedName), Seq(IntLiteral(argument)), None,
      SnapshotUnit, None, FullPerm, None)

  test("pure function applications use original source names with opaque symbolic identifiers") {
    val logger = newLogger()
    val encodedName = "source_name_42_F_deadbeef_F"
    val term = functionTerm(encodedName + "%opaque")
    val position = ast.TranslatedPosition(ast.SourcePosition(Paths.get("members.gobra"), 12, 8))
    logger.functionApps.update(term, application(encodedName, Some("source_name_42_F"), position))

    assert(logger.formatTerm(term, state()) == "source_name_42_F(7, 9) at 12.8")
  }

  test("pure function call metadata takes precedence over declaration metadata") {
    val logger = newLogger()
    val encodedName = "apply_deadbeef_F"
    val term = functionTerm(encodedName)
    logger.functionApps.update(term, application(encodedName, Some("atCall")))

    assert(logger.formatTerm(term, state(functions = Seq(function(encodedName, Some("atDeclaration"))))) ==
      "atCall(7, 9)")
  }

  test("pure functions without recorded applications use declaration metadata") {
    val logger = newLogger()
    val encodedName = "size_deadbeef_PMTree"

    assert(logger.formatTerm(functionTerm(encodedName), state(functions = Seq(function(encodedName, Some("size"))))) ==
      "size(7, 9)")
  }

  test("opaque pure function terms locate declarations through the recorded original application") {
    val logger = newLogger()
    val encodedName = "size_deadbeef_F"
    val term = functionTerm(encodedName + "%opaque")
    logger.functionApps.update(term, application(encodedName, None))

    assert(logger.formatTerm(term, state(functions = Seq(function(encodedName, Some("size"))))) ==
      "size(7, 9)")
  }

  test("pure function terms without an application or declaration preserve their encoded identifiers") {
    val logger = newLogger()
    val encodedName = "generated_function_42"

    assert(logger.formatTerm(functionTerm(encodedName), state()) == "generated_function_42(7, 9)")
  }

  test("pure function fallback preserves recorded source positions without source-name metadata") {
    val logger = newLogger()
    val encodedName = "read_deadbeef_F"
    val term = functionTerm(encodedName)
    val position = ast.TranslatedPosition(ast.SourcePosition(Paths.get("members.gobra"), 4, 3))
    logger.functionApps.update(term, application(encodedName, None, position))

    assert(logger.formatTerm(term, state(functions = Seq(function(encodedName, None)))) ==
      "read_deadbeef_F(7, 9) at 4.3")
  }

  test("pure functions preserve encoded identifiers when the source-name callback is absent") {
    SymbExLogger.sourceNameFinder = None
    val logger = newLogger()
    val encodedName = "read_deadbeef_F"
    val term = functionTerm(encodedName)
    logger.functionApps.update(term, application(encodedName, Some("read")))

    assert(logger.formatTerm(term, state(functions = Seq(function(encodedName, Some("read"))))) ==
      "read_deadbeef_F(7, 9)")
  }

  test("ordinary predicate chunks use source names from their declarations") {
    val logger = newLogger()
    val encodedName = "valid_state_42_deadbeef_PMTree"
    val current = state(predicates = Seq(predicate(encodedName, Some("valid_state_42"))))

    assert(logger.formatBasicChunk(chunk(encodedName), current) == "valid_state_42(1) == UNIT")
  }

  test("predicate access metadata takes precedence over declaration metadata") {
    val logger = newLogger()
    val encodedName = "valid_deadbeef_F"
    logger.registerPredicateAccess(access(encodedName, Some("atCall")), Seq(IntLiteral(1)))
    val current = state(predicates = Seq(predicate(encodedName, Some("atDeclaration"))))

    assert(logger.formatBasicChunk(chunk(encodedName), current) == "atCall(1) == UNIT")
  }

  test("dynamic predicate names are associated with their evaluated arguments") {
    val logger = newLogger()
    val encodedName = "dynamic_pred_0"
    // The same source argument can evaluate to different terms in different states.
    logger.registerPredicateAccess(access(encodedName, Some("first")), Seq(IntLiteral(1)))
    logger.registerPredicateAccess(access(encodedName, Some("second")), Seq(IntLiteral(2)))

    assert(logger.formatBasicChunk(chunk(encodedName, 1), state()) == "first(1) == UNIT")
    assert(logger.formatBasicChunk(chunk(encodedName, 2), state()) == "second(2) == UNIT")
    assert(logger.formatBasicChunk(chunk(encodedName, 3), state()) == "dynamic_pred_0(3) == UNIT")
  }

  test("repeated predicate registrations with the same source name remain unambiguous") {
    val logger = newLogger()
    val encodedName = "dynamic_pred_0"
    logger.registerPredicateAccess(access(encodedName, Some("valid")), Seq(IntLiteral(1)))
    logger.registerPredicateAccess(access(encodedName, Some("valid")), Seq(IntLiteral(1)))

    assert(logger.formatBasicChunk(chunk(encodedName), state()) == "valid(1) == UNIT")
  }

  test("ambiguous dynamic predicate accesses retain the encoded name for those arguments") {
    val logger = newLogger()
    val encodedName = "dynamic_pred_0"
    logger.registerPredicateAccess(access(encodedName, Some("first")), Seq(IntLiteral(1)))
    logger.registerPredicateAccess(access(encodedName, Some("second")), Seq(IntLiteral(1)))
    logger.registerPredicateAccess(access(encodedName, Some("first")), Seq(IntLiteral(1)))
    logger.registerPredicateAccess(access(encodedName, Some("third")), Seq(IntLiteral(2)))

    assert(logger.formatBasicChunk(chunk(encodedName, 1), state()) == "dynamic_pred_0(1) == UNIT")
    assert(logger.formatBasicChunk(chunk(encodedName, 2), state()) == "third(2) == UNIT")
  }

  test("predicate chunks without source metadata preserve their encoded names") {
    val logger = newLogger()
    val encodedName = "generated_predicate_42"
    logger.registerPredicateAccess(access(encodedName, None), Seq(IntLiteral(1)))

    assert(logger.formatBasicChunk(chunk(encodedName), state()) == "generated_predicate_42(1) == UNIT")
    assert(logger.formatBasicChunk(chunk(encodedName), state(predicates = Seq(predicate(encodedName, None)))) ==
      "generated_predicate_42(1) == UNIT")
  }

  test("predicate chunks preserve encoded names when the source-name callback is absent") {
    SymbExLogger.sourceNameFinder = None
    val logger = newLogger()
    val encodedName = "valid_deadbeef_F"
    logger.registerPredicateAccess(access(encodedName, Some("valid")), Seq(IntLiteral(1)))

    assert(logger.formatBasicChunk(chunk(encodedName), state(predicates = Seq(predicate(encodedName, Some("valid"))))) ==
      "valid_deadbeef_F(1) == UNIT")
  }

  test("predicate access names are isolated per member and cleared by reset") {
    val first = newLogger()
    val second = newLogger()
    val encodedName = "dynamic_pred_0"
    first.registerPredicateAccess(access(encodedName, Some("first")), Seq(IntLiteral(1)))
    assert(second.formatBasicChunk(chunk(encodedName), state()) == "dynamic_pred_0(1) == UNIT")
    second.registerPredicateAccess(access(encodedName, Some("second")), Seq(IntLiteral(1)))

    assert(first.formatBasicChunk(chunk(encodedName), state()) == "first(1) == UNIT")
    assert(second.formatBasicChunk(chunk(encodedName), state()) == "second(1) == UNIT")
    first.resetMaps()
    assert(first.formatBasicChunk(chunk(encodedName), state()) == "dynamic_pred_0(1) == UNIT")
    assert(second.formatBasicChunk(chunk(encodedName), state()) == "second(1) == UNIT")
    first.registerPredicateAccess(access(encodedName, Some("afterReset")), Seq(IntLiteral(1)))
    assert(first.formatBasicChunk(chunk(encodedName), state()) == "afterReset(1) == UNIT")
  }
}
