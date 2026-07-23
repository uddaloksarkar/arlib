/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib.Combinatorics

Reusable, fully generic `Finset` / `List` / `BigOperators` helper lemmas that
recur across combinatorial developments but are not in Mathlib under an obvious
name — union-folds, powerset-of-union, disjoint-union projection, interval
tiling, a concatenation counting bound, sum/product algebra (double-sum splits,
idempotent products, a surjection–product inequality), and `List.foldr min`
bounds, and `Finset.fold max` as a maximum with a floor.

This is the area root; it re-exports the modules below.  Import it to get the
whole set, or import a single module for just one piece.
-/

import Arlib.Combinatorics.Atoms
import Arlib.Combinatorics.Finset
import Arlib.Combinatorics.BigOperators
import Arlib.Combinatorics.ListFold
import Arlib.Combinatorics.FoldMax
