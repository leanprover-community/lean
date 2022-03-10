/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.core init.logic init.control init.data.basic init.version
import init.propext init.cc_lemmas init.funext init.control.combinators init.function init.classical
import init.util init.coe init.wf init.meta init.meta.well_founded_tactics init.algebra init.data
import init.meta.float
import init.meta.widget
import init.meta.feature_search

@[user_attribute]
meta def debugger.attr : user_attribute :=
{ name  := `breakpoint,
  descr := "breakpoint for debugger" }
