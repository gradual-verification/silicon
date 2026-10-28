// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2026 ETH Zurich.

package viper.silicon.tests

import org.scalatest.Outcome
import org.scalatest.funsuite.AnyFunSuite
import viper.silicon.logger.SymbExLogger
import viper.silicon.logger.records.data.{FunctionRecord, MemberRecord, MethodCallRecord, MethodRecord, PredicateRecord}
import viper.silver.ast

class MemberRecordNameFormattingTests extends AnyFunSuite {
  override protected def withFixture(test: NoArgTest): Outcome = SymbExLogger.synchronized {
    val previousFinder = SymbExLogger.sourceNameFinder
    SymbExLogger.sourceNameFinder = Some {
      case node: ast.Infoed => node.info.comment.headOption
      case _ => None
    }
    try super.withFixture(test)
    finally SymbExLogger.sourceNameFinder = previousFinder
  }

  private def memberRecords(info: ast.Info): Seq[(MemberRecord, String)] = Seq(
    new MethodRecord(ast.Method("encoded_method", Nil, Nil, Nil, Nil, None)(info = info), null) -> "encoded_method",
    new FunctionRecord(ast.Function("encoded_function", Nil, ast.Int, Nil, Nil, None)(info = info), null) -> "encoded_function",
    new PredicateRecord(ast.Predicate("encoded_predicate", Nil, None)(info = info), null) -> "encoded_predicate")

  test("method, pure function, and predicate headings preserve the source name exactly") {
    memberRecords(ast.SimpleInfo(Seq("source_name_42"))).foreach { case (record, encodedName) =>
      assert(record.toSimpleString == "source_name_42")
      assert(record.value.asInstanceOf[ast.Member].name == encodedName)
    }
  }

  test("member headings retain encoded names when source metadata is absent") {
    memberRecords(ast.NoInfo).foreach { case (record, encodedName) =>
      assert(record.toSimpleString == encodedName)
    }
  }

  test("member headings retain encoded names when the callback is absent") {
    SymbExLogger.sourceNameFinder = None
    memberRecords(ast.SimpleInfo(Seq("source_name"))).foreach { case (record, encodedName) =>
      assert(record.toSimpleString == encodedName)
    }
  }

  test("method calls rename only the member while preserving targets, arguments, and the original AST") {
    val encodedName = "encoded_method"
    val sameNamedLocal = ast.LocalVar(encodedName, ast.Int)()
    val otherTarget = ast.LocalVar("other_1", ast.Int)()
    val args = Seq(sameNamedLocal, ast.IntLit(2)())
    val targets = Seq(sameNamedLocal, otherTarget)
    val call = ast.MethodCall(encodedName, args, targets)(ast.NoPosition, ast.NoInfo, ast.NoTrafos)
    val original = call.toString()
    SymbExLogger.sourceNameFinder = Some(node => if (node eq call) Some("source_name_42") else None)
    val record = new MethodCallRecord(call, null, null)

    assert(record.toSimpleString == "encoded_method, other_1 := source_name_42(encoded_method, 2)")
    assert(record.value eq call)
    assert(call.methodName == encodedName)
    assert(call.args eq args)
    assert(call.targets eq targets)
    assert(call.toString() == original)
  }

  test("method calls without targets keep their call syntax") {
    val call = ast.MethodCall("encoded_method", Nil, Nil)(ast.NoPosition, ast.NoInfo, ast.NoTrafos)
    SymbExLogger.sourceNameFinder = Some(node => if (node eq call) Some("sourceMethod") else None)

    assert(new MethodCallRecord(call, null, null).toSimpleString == "sourceMethod()")
  }

  test("method calls preserve their original rendering when metadata or the callback is absent") {
    val target = ast.LocalVar("result_0", ast.Int)()
    val call = ast.MethodCall("encoded_method", Seq(ast.IntLit(2)()), Seq(target))(
      ast.NoPosition, ast.NoInfo, ast.NoTrafos)

    assert(new MethodCallRecord(call, null, null).toSimpleString == call.toString())
    SymbExLogger.sourceNameFinder = None
    assert(new MethodCallRecord(call, null, null).toSimpleString == call.toString())
  }

  test("null records retain their existing display") {
    assert(new MethodRecord(null, null).toSimpleString == "null")
    assert(new FunctionRecord(null, null).toSimpleString == "null")
    assert(new PredicateRecord(null, null).toSimpleString == "null")
    assert(new MethodCallRecord(null, null, null).toSimpleString == "null")
  }
}
