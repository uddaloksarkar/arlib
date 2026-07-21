/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Probability.FinProb
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Laws of random variables on a finite probability space

This is the foundation of `Arlib.InformationTheory`. Everything in the area —
entropy, conditional entropy, mutual information, Kullback–Leibler divergence —
is a function of the *law* (distribution) of one or more random variables on a
common `Arlib.FinProb`, and this file sets up that law and its marginals.

## Design

We work with random variables `X : P.Ω → α` on a shared finite probability space
`P : FinProb`, rather than with abstract distributions. This is what makes the
conditional statements usable: the arguments downstream condition on a growing
prefix of a transcript, and expressing those as marginals of one joint law on a
common space is far cheaper than juggling a tower of conditional distributions.

The two workhorses are `pair` (bundle two random variables into one valued in a
product) and `dist_pair_marginal` (summing a joint law over one coordinate gives
the marginal law). Nearly every identity downstream — the chain rules in
particular — is those two facts plus algebra.

## Main definitions

* `Arlib.InformationTheory.dist P X` — the law of `X`, a function `α → ℝ`.
* `Arlib.InformationTheory.pair X Y` — the joint random variable `ω ↦ (X ω, Y ω)`.
* `Arlib.InformationTheory.tuple Y` — a family `Fin n → P.Ω → β` bundled into a
  single random variable valued in `Fin n → β`.
* `Arlib.InformationTheory.IsProbDist p` — `p` is a probability distribution.
-/

open scoped BigOperators
open Finset

namespace Arlib
namespace InformationTheory

variable {P : FinProb} {α β γ : Type}

/-! ### Probability distributions -/

/-- A nonnegative function summing to `1`. The laws produced by `dist` satisfy
this, and it is the hypothesis form used by results (such as Gibbs' inequality)
that do not need an ambient probability space. -/
structure IsProbDist [Fintype α] (p : α → ℝ) : Prop where
  nonneg : ∀ a, 0 ≤ p a
  sum_eq_one : ∑ a, p a = 1

namespace IsProbDist

variable [Fintype α] {p : α → ℝ}

theorem le_one (hp : IsProbDist p) (a : α) : p a ≤ 1 := by
  have h : p a ≤ ∑ b, p b :=
    Finset.single_le_sum (f := p) (fun b _ => hp.nonneg b) (Finset.mem_univ a)
  simpa [hp.sum_eq_one] using h

/-- A probability distribution lives on a nonempty type: an empty sum cannot
be `1`. -/
theorem nonempty (hp : IsProbDist p) : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hz : (∑ a : α, p a) = 0 := by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
  rw [hp.sum_eq_one] at hz
  exact one_ne_zero hz

end IsProbDist

/-! ### The law of a random variable -/

/-- The law of the random variable `X`: `dist P X a` is the probability that
`X` takes the value `a`. -/
noncomputable def dist (P : FinProb) [DecidableEq α] (X : P.Ω → α) : α → ℝ :=
  fun a => ∑ ω, if X ω = a then P.mass ω else 0

section

variable [DecidableEq α]

theorem dist_nonneg (X : P.Ω → α) (a : α) : 0 ≤ dist P X a := by
  refine Finset.sum_nonneg fun ω _ => ?_
  by_cases h : X ω = a <;> simp [h, P.mass_nonneg ω]

variable [Fintype α]

@[simp] theorem dist_sum (X : P.Ω → α) : ∑ a, dist P X a = 1 := by
  simp only [dist]
  rw [Finset.sum_comm]
  calc ∑ ω, ∑ a, (if X ω = a then P.mass ω else 0)
      = ∑ ω, P.mass ω := Finset.sum_congr rfl fun ω _ => by simp
    _ = 1 := P.mass_sum

theorem isProbDist_dist (X : P.Ω → α) : IsProbDist (dist P X) :=
  ⟨dist_nonneg X, dist_sum X⟩

theorem dist_le_one (X : P.Ω → α) (a : α) : dist P X a ≤ 1 :=
  (isProbDist_dist X).le_one a

end

/-! ### Pairing and tupling -/

/-- Two random variables bundled into one valued in the product. -/
def pair (X : P.Ω → α) (Y : P.Ω → β) : P.Ω → α × β := fun ω => (X ω, Y ω)

@[simp] theorem pair_apply (X : P.Ω → α) (Y : P.Ω → β) (ω : P.Ω) :
    pair X Y ω = (X ω, Y ω) := rfl

section

variable [DecidableEq α] [DecidableEq β]

/-- **Marginalisation.** Summing the joint law over the second coordinate
recovers the law of the first. -/
theorem dist_pair_marginal [Fintype β] (X : P.Ω → α) (Y : P.Ω → β) (a : α) :
    ∑ b, dist P (pair X Y) (a, b) = dist P X a := by
  simp only [dist, pair]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : X ω = a
  · simp [h]
  · simp [h, Prod.ext_iff]

/-- **Marginalisation**, second coordinate. -/
theorem dist_pair_marginal' [Fintype α] (X : P.Ω → α) (Y : P.Ω → β) (b : β) :
    ∑ a, dist P (pair X Y) (a, b) = dist P Y b := by
  simp only [dist, pair]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : Y ω = b
  · simp [h]
  · simp [h, Prod.ext_iff]

/-- The law of a pair, summed over all pairs, is `1` — restated in the curried
form that double sums produce. -/
theorem dist_pair_sum [Fintype α] [Fintype β] (X : P.Ω → α) (Y : P.Ω → β) :
    ∑ a, ∑ b, dist P (pair X Y) (a, b) = 1 := by
  simp [dist_pair_marginal]

end

/-! ### Conditional laws -/

/-- The conditional law of `Z` given `X = a`. On the null event `dist P X a = 0`
this is the zero function; every result about it therefore carries the hypothesis
`dist P X a ≠ 0`, which is the honest scope. -/
noncomputable def condDist (P : FinProb) [DecidableEq α] [DecidableEq β]
    (Z : P.Ω → β) (X : P.Ω → α) (a : α) : β → ℝ :=
  fun b => if dist P X a = 0 then 0 else dist P (pair X Z) (a, b) / dist P X a

section

variable [DecidableEq α] [DecidableEq β]

theorem condDist_nonneg (Z : P.Ω → β) (X : P.Ω → α) (a : α) (b : β) :
    0 ≤ condDist P Z X a b := by
  unfold condDist
  split
  · exact le_refl 0
  · exact div_nonneg (dist_nonneg _ _) (dist_nonneg _ _)

/-- The defining property: joint law = marginal × conditional. -/
theorem dist_pair_eq_mul_condDist (Z : P.Ω → β) (X : P.Ω → α) (a : α) (b : β) :
    dist P (pair X Z) (a, b) = dist P X a * condDist P Z X a b := by
  unfold condDist
  split
  · rename_i h
    -- `dist P X a = 0` forces the joint law to vanish, since it is dominated by it.
    have hle : dist P (pair X Z) (a, b) ≤ dist P X a := by
      calc dist P (pair X Z) (a, b)
          = ∑ ω, if (X ω, Z ω) = (a, b) then P.mass ω else 0 := rfl
        _ ≤ ∑ ω, if X ω = a then P.mass ω else 0 := by
            refine Finset.sum_le_sum fun ω _ => ?_
            by_cases hx : X ω = a
            · by_cases hz : Z ω = b <;> simp [hx, hz, P.mass_nonneg ω]
            · simp [hx, Prod.ext_iff]
        _ = dist P X a := rfl
    have := le_antisymm (h ▸ hle) (dist_nonneg (pair X Z) (a, b))
    simp [h, this]
  · rename_i h
    field_simp

theorem condDist_sum [Fintype β] (Z : P.Ω → β) (X : P.Ω → α) (a : α)
    (ha : dist P X a ≠ 0) : ∑ b, condDist P Z X a b = 1 := by
  have : ∑ b, dist P X a * condDist P Z X a b = dist P X a := by
    simp only [← dist_pair_eq_mul_condDist]
    exact dist_pair_marginal X Z a
  rw [← Finset.mul_sum] at this
  exact mul_left_cancel₀ ha (by simpa using this)

theorem isProbDist_condDist [Fintype β] (Z : P.Ω → β) (X : P.Ω → α) (a : α)
    (ha : dist P X a ≠ 0) : IsProbDist (condDist P Z X a) :=
  ⟨condDist_nonneg Z X a, condDist_sum Z X a ha⟩

end

/-- A family of random variables bundled into a single random variable valued in
the function type. This is how a length-`n` transcript is represented. -/
def tuple {n : ℕ} (Y : Fin n → P.Ω → β) : P.Ω → (Fin n → β) := fun ω i => Y i ω

@[simp] theorem tuple_apply {n : ℕ} (Y : Fin n → P.Ω → β) (ω : P.Ω) (i : Fin n) :
    tuple Y ω i = Y i ω := rfl

/-- The prefix of a transcript: the first `i` entries of `Y`. Together with the
`i`-th entry this reconstitutes the length-`(i+1)` prefix, which is the induction
step behind the `q`-fold chain rules. -/
def prefixTuple {n : ℕ} (Y : Fin n → P.Ω → β) (i : Fin n) :
    P.Ω → (Fin i.val → β) :=
  fun ω j => Y ⟨j.val, lt_trans j.isLt i.isLt⟩ ω

@[simp] theorem prefixTuple_apply {n : ℕ} (Y : Fin n → P.Ω → β) (i : Fin n)
    (ω : P.Ω) (j : Fin i.val) :
    prefixTuple Y i ω j = Y ⟨j.val, lt_trans j.isLt i.isLt⟩ ω := rfl

/-- Bundling a length-`n` tuple with one more entry is the same as a length-`(n+1)`
tuple, up to the evident relabelling `Fin.snoc`. -/
def snocEquiv (β : Type) {n : ℕ} : ((Fin n → β) × β) ≃ (Fin (n + 1) → β) where
  toFun p := Fin.snoc p.1 p.2
  invFun f := (Fin.init f, f (Fin.last n))
  left_inv p := by
    ext j
    · simp [Fin.init_snoc]
    · simp [Fin.snoc_last]
  right_inv f := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Fin.snoc_last]
    · simp [Fin.snoc_castSucc, Fin.init]

end InformationTheory
end Arlib
