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
import viper.silicon.resources.FieldID
import viper.silicon.state.{BasicChunk, BasicChunkIdentifier, Identifier, State, Store}
import viper.silicon.state.terms.{App, DomainFun, FullPerm, IntLiteral, Term, Var, sorts}
import viper.silicon.verifier.Verifier
import viper.silver.ast

class StructFieldFormattingTests extends AnyFunSuite {
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

  private class Fixture {
    val local = ast.LocalVar("value", ast.Ref)()
    val receiver = Var(Identifier("value", "@", "0"), sorts.Ref, false)
    val state = State(
      g = Store(local -> (receiver, None)),
      program = ast.Program(Nil, Nil, Nil, Nil, Nil, Nil)(),
      currentMember = None,
      currentBlock = None,
      predicateData = Map.empty,
      functionData = Map.empty)
    private val config = LogConfig.default()
    private val member = ast.Method("test", Nil, Nil, Nil, Nil, None)()
    // Formatting does not inspect the member's path-condition stack.
    val logger = new MemberSymbExLog(SymbExLog(config), config, member, null)

    def getter(name: String, base: Term = receiver): Term =
      App(DomainFun(Identifier(name), Seq(sorts.Ref), sorts.Ref), Seq(base))

    def source(name: String, base: ast.Exp = local): ast.DomainFuncApp =
      ast.DomainFuncApp(name, Seq(base), scala.collection.immutable.Map.empty)(
        ast.NoPosition, ast.NoInfo, ast.Ref, "ShStruct", ast.NoTrafos)

    def chunk(receiver: Term): BasicChunk =
      BasicChunk(FieldID, BasicChunkIdentifier("valueField"), Seq(receiver), None,
        IntLiteral(0), None, FullPerm, None)
  }

  test("shared struct getters use field names from the recorded source node") {
    val f = new Fixture
    val getter = f.getter("ShStructget0of3")
    val source = f.source("ShStructget0of3")
    f.logger.functionApps.update(getter, source)
    SymbExLogger.sourceNameFinder = Some(node => if (node eq source) Some("first") else None)

    assert(f.logger.formatTerm(getter, f.state) == "value.first")
    assert(f.logger.formatBasicChunk(f.chunk(getter), f.state) == "value.first")
  }

  test("nested shared struct getters resolve each field from its own source node") {
    val f = new Fixture
    val outer = f.getter("ShStructget0of3[Ref]")
    val inner = f.getter("ShStructget1of2[Ref]", outer)
    val outerSource = f.source("ShStructget0of3")
    val innerSource = f.source("ShStructget1of2", outerSource)
    f.logger.functionApps.update(outer, outerSource)
    f.logger.functionApps.update(inner, innerSource)
    val names = Map[ast.Node, String](outerSource -> "nested", innerSource -> "leaf")
    SymbExLogger.sourceNameFinder = Some(names.get)

    assert(f.logger.formatTerm(inner, f.state) == "value.nested.leaf")
    assert(f.logger.formatBasicChunk(f.chunk(inner), f.state) == "value.nested.leaf")
  }

  test("shared struct getters fall back to the index without a field-name callback") {
    val f = new Fixture
    val getter = f.getter("ShStructget1of3")
    f.logger.functionApps.update(getter, f.source("ShStructget1of3"))

    assert(f.logger.formatTerm(getter, f.state) == "value.#1")
    assert(f.logger.formatBasicChunk(f.chunk(getter), f.state) == "value.#1")
  }

  test("shared struct getters fall back to the index without a recorded source node") {
    val f = new Fixture
    val getter = f.getter("ShStructget2of3")
    SymbExLogger.sourceNameFinder = Some(_ => Some("unavailable"))

    assert(f.logger.formatTerm(getter, f.state) == "value.#2")
    assert(f.logger.formatBasicChunk(f.chunk(getter), f.state) == "value.#2")
  }

  test("shared struct getters fall back to the index when the source has no field name") {
    val f = new Fixture
    val getter = f.getter("ShStructget0of3")
    f.logger.functionApps.update(getter, f.source("ShStructget0of3"))
    SymbExLogger.sourceNameFinder = Some(_ => None)

    assert(f.logger.formatTerm(getter, f.state) == "value.#0")
    assert(f.logger.formatBasicChunk(f.chunk(getter), f.state) == "value.#0")
  }

  test("unrelated domain functions retain their ordinary term and chunk formatting") {
    val f = new Fixture
    val term = f.getter("OtherDomainFunction")
    f.logger.functionApps.update(term, f.source("OtherDomainFunction"))
    SymbExLogger.sourceNameFinder = Some(_ => Some("notAField"))

    assert(f.logger.formatTerm(term, f.state) == "OtherDomainFunction(value)")
    assert(f.logger.formatBasicChunk(f.chunk(term), f.state) == s"{$term}#valueField")
  }
}
