/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# ℓ¹ subspace embeddings of weighted point sets

The approximation relation a domain reduction has to satisfy: `C` is a reduction
of `U` when the evaluation functional agrees on **every** query simultaneously,
to within a multiplicative window.  Uniformity over queries is the whole point —
it is what lets the reduced set be used inside a later, unforeseen linear test,
and it is exactly what Lewis-weight row sampling delivers.

* `Embeds lo hi U C` — `∀ y, C.E y ∈ [lo · U.E y, hi · U.E y]`.
* `Embeds.trans` — reductions compose, the windows multiplying.  This is the
  step that turns a per-stage `(1 ± δ)` into an end-to-end `(1 ± δ)^L`.
* `Embeds.sum_queries` — a *fixed* reduction applied to a whole family of
  queries at once, summed.  This is how a reduction of one factor of a product
  is used: the other factor's assignments index the family.
* `Embeds.congr_left` / `congr_right` — replacing either side by a set with the
  same functional.

The window is kept asymmetric (`lo`, `hi` rather than a single `δ`) throughout,
because composition does not preserve symmetry; `Embeds.relErr` converts back at
the end.

No `sorry`.
-/
import Arlib.Approximation.Coresets.Basic

namespace Arlib.Approximation

open scoped BigOperators
open Finset

variable {ι κ ν d : Type*} [Fintype ι] [Fintype κ] [Fintype ν] [Fintype d]

/-- **`C` is an ℓ¹ subspace embedding of `U` with window `[lo, hi]`**: every
linear test is preserved up to the multiplicative window, *simultaneously* for
all queries.

Read `Embeds lo hi U C` as "`C` reduces `U`": `U` is the large candidate set,
`C` the small surviving one. -/
def Embeds (lo hi : ℝ) (U : WPS κ d) (C : WPS ι d) : Prop :=
  ∀ y : d → ℝ, Between lo hi (C.E y) (U.E y)

namespace Embeds

variable {lo hi lo' hi' : ℝ} {U : WPS κ d} {V : WPS ν d} {C : WPS ι d}

theorem apply (h : Embeds lo hi U C) (y : d → ℝ) : Between lo hi (C.E y) (U.E y) := h y

/-- A weighted point set reduces itself, with the trivial window. -/
theorem refl (U : WPS κ d) : Embeds 1 1 U U := fun y => Between.refl (U.E y)

/-- Two weighted point sets with the same functional reduce each other. -/
theorem of_E_eq (h : ∀ y : d → ℝ, C.E y = U.E y) : Embeds 1 1 U C :=
  fun y => Between.of_eq (h y)

/-- **Reductions compose.**  If `V` reduces `U` with window `[lo, hi]` and `C`
reduces `V` with window `[lo', hi']`, then `C` reduces `U` with the product
window.  Nonnegativity of the outer window is what lets the inequalities
chain. -/
theorem trans (hlo' : 0 ≤ lo') (hhi' : 0 ≤ hi')
    (h₁ : Embeds lo hi U V) (h₂ : Embeds lo' hi' V C) :
    Embeds (lo' * lo) (hi' * hi) U C :=
  fun y => Between.trans hlo' hhi' (h₂ y) (h₁ y)

/-- Widening the window. -/
theorem mono (hl : lo' ≤ lo) (hh : hi ≤ hi') (h : Embeds lo hi U C) :
    Embeds lo' hi' U C :=
  fun y => Between.mono (U.E_nonneg y) hl hh (h y)

/-- Replacing the reduced set by one with the same functional. -/
theorem congr_right {ι' : Type*} [Fintype ι'] {C' : WPS ι' d} (h : Embeds lo hi U C)
    (hC : ∀ y : d → ℝ, C'.E y = C.E y) : Embeds lo hi U C' := by
  intro y; rw [hC y]; exact h y

/-- Replacing the reduced *source* by one with the same functional. -/
theorem congr_left {κ' : Type*} [Fintype κ'] {U' : WPS κ' d} (h : Embeds lo hi U C)
    (hU : ∀ y : d → ℝ, U'.E y = U.E y) : Embeds lo hi U' C := by
  intro y; rw [hU y]; exact h y

/-- **One reduction, a whole family of queries.**  The window survives summing
the functional over any finite family of queries.

This is the form in which a child's reduction is consumed at a product region:
the queries are indexed by the *other* child's surviving assignments, and the
weighted sum over them is exactly what has to be preserved. -/
theorem sum_queries {ι : Type*} (h : Embeds lo hi U C) (s : Finset ι)
    (y : ι → d → ℝ) (c : ι → ℝ) (hc : ∀ j, 0 ≤ c j) :
    Between lo hi (∑ j ∈ s, c j * C.E (y j)) (∑ j ∈ s, c j * U.E (y j)) :=
  Between.sum s _ _ fun j _ => Between.const_mul (hc j) (h (y j))

/-- The symmetric case: a `(1 ± δ)` reduction, in `Arlib.relErr` form. -/
theorem relErr {δ : ℝ} (h : Embeds (1 - δ) (1 + δ) U C) (y : d → ℝ) :
    C.E y ∈ relErr δ (U.E y) := h y

end Embeds

end Arlib.Approximation
