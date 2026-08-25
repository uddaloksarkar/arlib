/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# KR additions

Aggregate entry point for the reusable lattice, convexity, and topology modules
merged from `kr-25-ssm`. Continuous-state Markov-chain additions have their own
entry point, `Arlib.MarkovChains.Continuous`, because the upstream finite-chain
and KR continuous-chain libraries currently contain a few declarations with the
same fully qualified names.
-/

import Arlib.Lattice
import Arlib.Probability.KR
import Arlib.Convexity
import Arlib.Topology.HamSandwich
