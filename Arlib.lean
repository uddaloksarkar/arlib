/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib

A curated, mathlib-style library of reusable Lean 4 + Mathlib lemmas, distilled
from the meelgroup formalization projects.

Importing `Arlib` pulls in every reusable module the library exposes. Import a
sub-namespace (e.g. `import Arlib.Probability`) to pull in just one area.

This root re-exports every public area of the library. Keep it as a pure
aggregation of area roots — put content in the area modules, not here.

## Areas

* `Arlib.Prelude` — small shared notation (e.g. the relative-error interval).
* `Arlib.Probability` — finite/discrete probability: finite probability spaces,
  product/coin spaces, independence, conditional expectation, Markov and
  median-of-means tail bounds.
* `Arlib.Combinatorics` — generic `Finset` / `List` / `BigOperators` helpers
  (union-folds, powerset-of-union, disjoint-union projection, a concatenation
  counting bound, `List.foldr min` bounds).
-/

import Arlib.Prelude
import Arlib.Probability
import Arlib.Combinatorics
import Arlib.GameTheory
import Arlib.InformationTheory
