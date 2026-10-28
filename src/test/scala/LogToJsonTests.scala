// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.tests

import java.nio.file.Paths
import org.scalatest.Outcome
import org.scalatest.funsuite.AnyFunSuite
import spray.json._
import viper.silicon.{Config, Map}
import viper.silicon.logger.{LogConfig, MemberSymbExLog, MemberSymbExLogger, NoopMemberSymbExLog, SymbExLog, SymbExLogger}
import viper.silicon.logger.records.data.{CommentRecord, EndRecord, ErrorRecord, ExecuteRecord, LoopInRecord, LoopOutRecord}
import viper.silicon.logger.records.scoping.{CloseScopeRecord, OpenScopeRecord}
import viper.silicon.logger.records.structural.BranchingRecord
import viper.silicon.resources.PredicateID
import viper.silicon.state.{BasicChunk, BasicChunkIdentifier, Heap, State}
import viper.silicon.state.terms.{FullPerm, IntLiteral, Unit => SnapshotUnit}
import viper.silicon.verifier.Verifier
import viper.silver.ast
import viper.silver.verifier.{errors, reasons}

class LogToJsonTests extends AnyFunSuite {
  override protected def withFixture(test: NoArgTest): Outcome = SymbExLogger.synchronized {
    val previousConfig = Verifier.config
    val previousFinder = SymbExLogger.sourceNameFinder
    val previousLoggers = SymbExLogger.loggers.keySet.toSet
    Verifier.config = new Config(Seq())
    SymbExLogger.sourceNameFinder = None
    try super.withFixture(test)
    finally {
      SymbExLogger.sourceNameFinder = previousFinder
      SymbExLogger.loggers.keys.filterNot(previousLoggers.contains).toList.foreach { logger =>
        SymbExLogger.loggers.remove(logger)
      }
      Verifier.config = previousConfig
    }
  }

  private def newLogger(): MemberSymbExLog = {
    val config = LogConfig.default()
    new MemberSymbExLog(SymbExLog(config), config, ast.Method("test", Nil, Nil, Nil, Nil, None)(), null)
  }

  private def state(heap: Heap = Heap(), predicates: Seq[ast.Predicate] = Nil): State =
    State(
      h = heap,
      program = ast.Program(Nil, Nil, Nil, predicates, Nil, Nil)(),
      currentMember = None,
      currentBlock = None,
      predicateData = Map.empty,
      functionData = Map.empty)

  private def executeRecord(position: ast.Position, current: State = state()): ExecuteRecord =
    new ExecuteRecord(ast.Assert(ast.TrueLit()())(pos = position), current, null)

  private def translatedPosition(line: Int, column: Int): ast.TranslatedPosition =
    ast.TranslatedPosition(ast.SourcePosition(Paths.get("program.gobra"), line, column))

  private def entry(line: JsValue, column: JsValue, heap: JsArray = JsArray()): JsObject =
    JsObject("line" -> line, "column" -> column, "heap" -> heap)

  test("empty and disabled member logs export an empty array through the base API") {
    val logger: MemberSymbExLogger = newLogger()
    assert(logger.logToJson == JsArray())
    assert(NoopMemberSymbExLog.logToJson == JsArray())
  }

  test("only statements with translated positions are exported") {
    val logger = newLogger()
    logger.log = Vector(
      executeRecord(translatedPosition(12, 8)),
      executeRecord(ast.SourcePosition(Paths.get("program.vpr"), 3, 4)),
      executeRecord(ast.LineColumnPosition(5, 6)),
      executeRecord(ast.NoPosition),
      executeRecord(ast.VirtualPosition("generated")))

    assert(logger.logToJson == JsArray(entry(JsNumber(12), JsNumber(8))))
  }

  test("nested branches are traversed in recorded order without exporting scope or comment records") {
    val logger = newLogger()
    val first = executeRecord(translatedPosition(1, 1))
    val outer = new BranchingRecord(2, None, None)
    val inner = new BranchingRecord(2, None, None)
    inner.appendLog(executeRecord(translatedPosition(3, 1)))
    inner.appendLog(executeRecord(ast.SourcePosition(Paths.get("program.vpr"), 20, 1)))
    inner.switchToNextBranch()
    inner.appendLog(executeRecord(translatedPosition(4, 1)))
    outer.markReachable()
    outer.appendLog(executeRecord(translatedPosition(2, 1)))
    outer.appendLog(inner)
    outer.appendLog(new CommentRecord("inside branch", state(), null))
    outer.appendLog(executeRecord(translatedPosition(5, 1)))
    outer.switchToNextBranch()
    // Records in branches not marked reachable are still part of the log.
    outer.appendLog(executeRecord(translatedPosition(6, 1)))
    logger.log = Vector(first, new OpenScopeRecord(first), outer, new CloseScopeRecord(first.id),
      new CommentRecord("after branch", state(), null), executeRecord(translatedPosition(7, 1)))

    assert(logger.logToJson == JsArray((1 to 7).map { line =>
      entry(JsNumber(line), JsNumber(1))
    }.toVector))
  }

  test("loop records export invariant positions in log order, including nested branches") {
    val logger = newLogger()
    val branch = new BranchingRecord(1, None, None)
    branch.appendLog(new LoopInRecord(ast.TrueLit()(pos = translatedPosition(12, 8)), state(), null))
    branch.appendLog(new LoopOutRecord(ast.TrueLit()(pos = translatedPosition(13, 9)), state(), null))
    branch.appendLog(new LoopInRecord(ast.TrueLit()(), state(), null))
    branch.appendLog(new LoopOutRecord(
      ast.TrueLit()(pos = ast.SourcePosition(Paths.get("program.vpr"), 20, 1)), state(), null))
    logger.log = Vector(executeRecord(translatedPosition(1, 2)), branch,
      executeRecord(translatedPosition(14, 3)))

    assert(logger.logToJson == JsArray(
      entry(JsNumber(1), JsNumber(2)),
      entry(JsNumber(12), JsNumber(8)),
      entry(JsNumber(13), JsNumber(9)),
      entry(JsNumber(14), JsNumber(3))))
  }

  test("each execution retains its own formatted heap even at the same source position") {
    val logger = newLogger()
    SymbExLogger.sourceNameFinder = Some {
      case node: ast.Infoed => node.info.comment.headOption
      case _ => None
    }
    val predicate = ast.Predicate("encoded_resource", Seq(ast.LocalVarDecl("arg", ast.Int)()), None)(
      info = ast.SimpleInfo(Seq("resource")))
    def chunk(argument: Int): BasicChunk =
      BasicChunk(PredicateID, BasicChunkIdentifier(predicate.name), Seq(IntLiteral(argument)), None,
        SnapshotUnit, None, FullPerm, None)
    val firstState = state(Heap(Seq(chunk(7), chunk(9))), Seq(predicate))
    val secondState = state(Heap(Seq(chunk(11))), Seq(predicate))
    val position = translatedPosition(10, 2)
    logger.log = Vector(executeRecord(position, firstState), executeRecord(position, secondState))

    assert(logger.logToJson == JsArray(
      entry(JsNumber(10), JsNumber(2), JsArray(JsString("resource(7) == UNIT; "), JsString("resource(9) == UNIT; "))),
      entry(JsNumber(10), JsNumber(2), JsArray(JsString("resource(11) == UNIT; ")))))
  }

  test("end and error records export their heaps in order, including inside branches") {
    val logger = newLogger()
    val predicate = ast.Predicate("resource", Seq(ast.LocalVarDecl("arg", ast.Int)()), None)()
    val chunk = BasicChunk(PredicateID, BasicChunkIdentifier(predicate.name), Seq(IntLiteral(7)), None,
      SnapshotUnit, None, FullPerm, None)
    val current = state(Heap(Seq(chunk)), Seq(predicate))
    val assertion = ast.Assert(ast.FalseLit()())()
    val error = errors.AssertFailed(assertion, reasons.AssertionFalse(assertion.exp))
    val branch = new BranchingRecord(1, None, None)
    branch.appendLog(new ErrorRecord(error, current, null))
    branch.appendLog(new EndRecord(current, null))
    logger.log = Vector(executeRecord(translatedPosition(1, 2)), branch, new EndRecord(state(), null))

    val heap = JsArray(JsString("resource(7) == UNIT; "))
    def terminal(kind: String, contents: JsArray): JsObject =
      JsObject(entry(JsNull, JsNull, contents).fields + ("kind" -> JsString(kind)))
    assert(logger.logToJson == JsArray(
      entry(JsNumber(1), JsNumber(2)),
      JsObject(terminal("error", heap).fields + ("error" -> JsString(error.readableMessage))),
      terminal("end", heap),
      terminal("end", JsArray())))
  }
}
