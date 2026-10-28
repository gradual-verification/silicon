// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silicon.logger.records.data

import viper.silicon.common.collections.immutable.InsertionOrderedSet
import viper.silicon.decider.PathConditionStack
import viper.silicon.logger.SymbExLogger
import viper.silicon.state.State
import viper.silicon.state.terms.Term
import viper.silver.ast

class MethodCallRecord(v: ast.MethodCall, s: State, p: PathConditionStack) extends DataRecord {
  val value: ast.MethodCall = v
  val state: State = s
  val pcs: InsertionOrderedSet[Term] = if (p != null) p.assumptions else null

  override val toTypeString: String = "method call"

  override lazy val toSimpleString: String = {
    if (value != null) {
      val name = SymbExLogger.displayName(value, value.methodName)
      value.copy(methodName = name)(value.pos, value.info, value.errT).toString()
    } else "null"
  }
}
