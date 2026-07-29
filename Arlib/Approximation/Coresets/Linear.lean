/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Linear reparametrisation of features: a free operation

A layer that replaces each feature vector `v` by `L v` for a fixed matrix `L`
costs a domain reduction *nothing*: the reduced set for the old features is
already a reduced set for the new ones, with the same window and without
enlarging the domain.  The reason is one line — `⟨y, L v⟩ = ⟨Lᵀ y, v⟩`, so a
linear test on the new features *is* a linear test on the old ones, and the
embedding property is quantified over all queries.

This is the "sum gate" step of a bottom-up construction over a circuit: a layer
of sum gates applies a fixed linear map to the vector of gate values at a region,
and therefore introduces no error and requires no resampling.  Only the *product*
steps, which genuinely enlarge the domain, need sparsifying — which is why the
error exponent counts product regions and nothing else.

* `WPS.linMap L C` — the reparametrised weighted point set (same index, same
  weights).
* `adjQuery L y` — the transposed query `Lᵀ y`.
* `WPS.E_linMap` — `E(L C, y) = E(C, Lᵀ y)`.
* `Embeds.linMap` — reductions survive reparametrisation, with the same window.

No `sorry`.
-/
import Arlib.Approximation.Coresets.Embedding

namespace Arlib.Approximation

open scoped BigOperators
open Finset

variable {ι κ d d' : Type*} [Fintype ι] [Fintype κ] [Fintype d] [Fintype d']

/-- The **transposed query** `Lᵀ y`, the query on the old features that a query
`y` on the new features amounts to. -/
def adjQuery (L : d' → d → ℝ) (y : d' → ℝ) : d → ℝ := fun a => ∑ a', y a' * L a' a

/-- A linear test on reparametrised features is a linear test on the originals:
`⟨y, L v⟩ = ⟨Lᵀ y, v⟩`. -/
theorem dot_linear (L : d' → d → ℝ) (y : d' → ℝ) (v : d → ℝ) :
    dot y (fun a' => ∑ a, L a' a * v a) = dot (adjQuery L y) v := by
  simp only [dot, adjQuery, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => by ring

namespace WPS

/-- **Reparametrising the features by a fixed linear map.**  The index set and the
weights are untouched; only the feature vectors change. -/
def linMap (L : d' → d → ℝ) (C : WPS ι d) : WPS ι d' where
  wt := C.wt
  wt_nonneg := C.wt_nonneg
  feat := fun i a' => ∑ a, L a' a * C.feat i a

omit [Fintype ι] [Fintype d'] in
@[simp] theorem linMap_wt (L : d' → d → ℝ) (C : WPS ι d) (i : ι) :
    (linMap L C).wt i = C.wt i := rfl

omit [Fintype ι] [Fintype d'] in
@[simp] theorem linMap_feat (L : d' → d → ℝ) (C : WPS ι d) (i : ι) (a' : d') :
    (linMap L C).feat i a' = ∑ a, L a' a * C.feat i a := rfl

/-- **The functional after reparametrisation** is the old functional at the
transposed query. -/
theorem E_linMap (L : d' → d → ℝ) (C : WPS ι d) (y : d' → ℝ) :
    (linMap L C).E y = C.E (adjQuery L y) := by
  simp only [E_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [linMap_wt]
  congr 1
  congr 1
  exact dot_linear L y (C.feat i)

end WPS

/-- **A sum layer is free.**  If `C` reduces `U` then `L C` reduces `L U`, with the
*same* window and the same number of points.  No sparsification is needed and no
error is incurred. -/
theorem Embeds.linMap {lo hi : ℝ} {U : WPS κ d} {C : WPS ι d} (L : d' → d → ℝ)
    (h : Embeds lo hi U C) : Embeds lo hi (WPS.linMap L U) (WPS.linMap L C) := by
  intro y
  rw [WPS.E_linMap, WPS.E_linMap]
  exact h (adjQuery L y)

end Arlib.Approximation
