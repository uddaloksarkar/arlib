/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.Estimator
import Arlib.Probability.TV
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Accumulated dependence: `lem:delta-ind` and the truncation device

Cousins–Vempala's `O*(n³)` volume algorithm estimates a telescoping product
`R_1 ⋯ R_m` by a product of phase means `W̄_1 ⋯ W̄_m`, each phase mean being an
average of `k` sample scores. Chebyshev's inequality on the product needs the
factors to be independent, and they are not: every sample comes from the same
Markov chain trajectory. §5.2 of the paper (`:1479-1500`) repairs this in two
steps, both formalised here.

1. **`lem:delta-ind`** (`:1481-1488`) — successive samples are *`ν`-independent*
   rather than independent, where `ν` is the per-sample total-variation error,
   and the defect accumulates only linearly along the chain.
2. **The truncation device** (`:1489-1503`) — `lem:cov-bd` needs *bounded*
   variables and `W̄_i` is unbounded, so the paper replaces `W̄_i` by
   `V_i = min {W̄_i, α E(W̄_i)}` and pays for it with `lem:exp-bd`.

`ν` is carried as a **hypothesis** throughout. Nothing here claims that any
sampler achieves it; that is §4 of the paper and is not in scope for this file.
Everything below is a conditional statement: *given* per-sample error `ν`, the
accumulated dependence is controlled.

## What this file does not re-prove

The dependence measure itself and the two `LV2` lemmas the argument runs on
already exist in this repository, in
`Arlib/Convexity/GaussianCooling/Estimator.lean`:

* `NuIndep μ X Y ν` — `|P(X ∈ A, Y ∈ B) − P(X ∈ A) P(Y ∈ B)| ≤ ν`, the paper's
  `μ(X, Y) ≤ ν` (`:1390-1394`), stated as a universally quantified bound.
* `NuIndep.comp` — `lem:fn-indep` (`:1398`): measurable functions cannot
  decrease independence.
* `expect_min_ge` — `lem:exp-bd` (`:1412`): `E(min(X, a)) ≥ E(X) − E(X²)/(4a)`.

This file therefore introduces **no new definition**; it imports the existing
one and extends its API. That is also why it lives in the `Arlib.GaussianCooling`
namespace despite its path: the cross-area import
(`Arlib/Probability/` importing `Arlib/Convexity/GaussianCooling/`) is
deliberate and is the price of not duplicating `NuIndep`. `Estimator.lean`
imports only Mathlib, so there is no cycle.

## Contents

### Basic API for `NuIndep`

* `NuIndep.mono`, `NuIndep.symm` — weakening and symmetry.
* `nuIndep_zero_iff_indepFun` — the grounding lemma: `0`-independence is exactly
  Mathlib's `IndepFun`. This is what makes `NuIndep` a quantitative
  interpolation of a standard notion rather than an unanchored definition.

### The mechanism: an approximate product structure

* `nuIndep_of_approx_product` — **the workhorse.** If there is a *fixed*
  set function `q` with `|P(X ∈ A, Y ∈ B) − P(X ∈ A) q B| ≤ ν` for all
  measurable `A, B`, then `X` and `Y` are `ν`-independent. Note the constant:
  `ν`, not `2ν`. The naive route (compare `P(Y ∈ B)` to `q B` separately) loses
  a factor of two; the identity
  `P(A ∩ B) − P(A)P(B) = (1 − P(A)) h(A,B) − P(A) h(Aᶜ,B)` does not.
* `nuIndep_compProd_of_tvLe` — **where that hypothesis comes from.** For a joint
  law `ρ ⊗ₘ κ` built from a Markov kernel, a pure *mixing* bound
  `TVLe (κ a) τ ν` — from every starting configuration the chain is within total
  variation `ν` of its target `τ` — yields `ν`-independence of past and next
  sample, with no loss of constant. This is what keeps `lem:delta-ind` (a) and
  (b) from being restatements of their own hypotheses.

### Transfer along a coupling

* `NuIndep.of_coupling` — `ν`-independence survives replacing `X, Y` by variables
  that agree with them off an event of small probability, at cost
  `ν + 2 δ₁ + 2 δ₂`. This is the step that carries the bound from the sampled
  variables `Z_i` to the exactly-distributed `Z̄_i` of `:1426-1431`.

### `lem:delta-ind`

* `delta_ind_a`, `delta_ind_a_bar` — part (a), unbarred and barred.
* `delta_ind_b` — part (b), stated for an abstract history variable;
  `delta_ind_b_tuple` is the paper's literal `(Z_0, …, Z_i)`.
* `delta_ind_c` — part (c), the statement the variance argument consumes;
  `delta_ind_c_paper` is the same in the paper's parameters `k`, `m`, `ν`.

### The truncation device

* `expect_trunc_le` — `E(V_i) ≤ E(W̄_i)`.
* `expect_trunc_ge` — `E(V_i) ≥ (1 − c/(4α)) E(W̄_i)` given `E(W̄_i²) ≤ c E(W̄_i)²`.
* `expect_trunc_ge_half` — the paper's form `E(V_i) ≥ (1 − 1/(2α)) E(W̄_i)`,
  which needs `c ≤ 2`, i.e. `k ≥ 7` in the paper's `c = 1 + 7/k`;
  `expect_trunc_ge_half_of_seven_le` is that instance.

### Towards `lem:cov-bd`

* `abs_integral_indicator_mul_sub_le` — `lem:cov-bd` (`:1405`) in the case where
  the first factor is an indicator: `|E(1_{X ∈ A₀} g(Y)) − P(X ∈ A₀) E(g(Y))| ≤ ν`
  for `g` with values in `[0,1]`. A single layer cake over `g`, whose level sets
  the indicator turns into exactly the rectangles `NuIndep` controls.
* `abs_integral_indicator_mul_sub_le'` — the same for `g` with values in `[0,b]`,
  at cost `b ν`; this is the paper's bound at `a = 1`.

## What is *not* here

**`lem:cov-bd` in full** — `|E(XY) − E(X)E(Y)| ≤ ab μ(X,Y)` for general bounded
`X`, `Y` — is not proved. Its proof is a *double* layer-cake identity
`E(XY) = ∫₀^a ∫₀^b P(X > s, Y > t) dt ds`; the inner cake is the indicator case
above, but the outer one needs Tonelli on `Ω × (0,1]` and is left open. The `U_i`
recursion of `:1505-1560` that consumes `lem:cov-bd`, and `lem:accuracy` itself,
are likewise out of scope.

The truncation device above is precisely the preparation `lem:cov-bd` needs
(`:1489`: "the variables `W̄_i` are not bounded, but we will introduce a new set
of random variables based on `W̄_i` that are bounded so we can later apply Lemma
`cov-bd`"), so this file ends exactly where that argument begins.

## Deviation from the paper's constants

Parts (a) and (b) come out at the paper's constant. The *barred* statements do
not: the paper asserts `3ν` for `Z̄_i, Z̄_{i+1}` and `3kmν` for part (c), citing
`LV2` without proof, whereas the coupling transfer proved here costs
`ν + 2(δ₁ + δ₂)`, giving `5ν` and `O(kmν)` respectively. The discrepancy is a
constant factor in a bound the downstream argument uses only symbolically
(`μ = 3kmν` enters `:1512-1520` as an opaque parameter), so the paper-shaped
corollaries below are stated with the constants that are actually proved, and
the symbolic forms are given as well so a caller can supply its own budget.

## References

Cousins–Vempala, *Bypassing KLS: Gaussian Cooling and an `O*(n³)` Volume
Algorithm*, §5.2. Line references are to
`1409.6011/vol3_journal.tex` in this repository.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Set Real ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## Basic API for `NuIndep` -/

/-- **Weakening.** A `ν`-independence bound is also a `ν'`-independence bound for
any larger `ν'`. -/
theorem NuIndep.mono {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {X : Ω → α} {Y : Ω → β} {ν ν' : ℝ} (h : NuIndep μ X Y ν) (hν : ν ≤ ν') :
    NuIndep μ X Y ν' := fun A B hA hB => (h A B hA hB).trans hν

/-- **Symmetry.** The dependence measure does not distinguish the two arguments. -/
theorem NuIndep.symm {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {X : Ω → α} {Y : Ω → β} {ν : ℝ} (h : NuIndep μ X Y ν) :
    NuIndep μ Y X ν := by
  intro B A hB hA
  have := h A B hA hB
  rwa [Set.inter_comm, mul_comm]

/-- **The grounding lemma.** `0`-independence is exactly Mathlib's `IndepFun`.

This is what licenses reading `NuIndep μ X Y ν` as "independent up to `ν`": at
`ν = 0` the notion collapses onto the standard one, with no residue. The proof
is `indepFun_iff_measure_inter_preimage_eq_mul` plus the passage between `μ S`
and `μ.real S`, which is lossless because a probability measure is finite. -/
theorem nuIndep_zero_iff_indepFun {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β} :
    NuIndep μ X Y 0 ↔ IndepFun X Y μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  constructor
  · intro h A B hA hB
    have hzero := h A B hA hB
    rw [abs_nonpos_iff, sub_eq_zero] at hzero
    have hfin : μ (X ⁻¹' A) * μ (Y ⁻¹' B) ≠ ⊤ :=
      ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _)
    refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) hfin).mp ?_
    rw [ENNReal.toReal_mul]
    exact hzero
  · intro h A B hA hB
    have := h A B hA hB
    simp only [Measure.real, this, ENNReal.toReal_mul, sub_self, abs_zero, le_refl]

/-! ## The mechanism: an approximate product structure

Where does `ν`-independence come from? Never from a direct estimate of
`|P(A ∩ B) − P(A) P(B)|`. It comes from the chain: conditionally on anything
that has happened so far, the law of the next sample is within total variation
`ν` of a *fixed* target `q`, because the chain has been run past its mixing
time. That hypothesis is a statement about `P(X ∈ A, Y ∈ B)` versus
`P(X ∈ A) · q B` — a comparison against a fixed reference, with no reference to
`Y`'s own marginal.

`nuIndep_of_approx_product` closes the gap, and closes it without loss: the
constant it returns is `ν`, not `2ν`. The naive argument first bounds
`|P(Y ∈ B) − q B| ≤ ν` (take `A = univ`) and then adds two errors. The identity

  `P(A ∩ B) − P(A) P(B) = (1 − P(A)) · h(A,B) − P(A) · h(Aᶜ,B)`,

where `h(A,B) = P(A ∩ B) − P(A) q B`, is a convex combination of two `h`-values
and so costs only one `ν`. -/

/-- Splitting a measurable set along another: `μ(S ∩ T) + μ(Sᶜ ∩ T) = μ(T)`, in
real-valued form. -/
theorem measureReal_inter_add_compl_inter [IsFiniteMeasure μ] {S T : Set Ω}
    (hS : MeasurableSet S) (hT : MeasurableSet T) :
    μ.real (S ∩ T) + μ.real (Sᶜ ∩ T) = μ.real T := by
  have hdisj : Disjoint (S ∩ T) (Sᶜ ∩ T) := by
    rw [Set.disjoint_left]
    rintro ω ⟨hωS, -⟩ ⟨hωSc, -⟩
    exact hωSc hωS
  have hunion : (S ∩ T) ∪ (Sᶜ ∩ T) = T := by
    ext ω; by_cases h : ω ∈ S <;> simp [h]
  rw [← measureReal_union hdisj (hS.compl.inter hT), hunion]

/-- **The workhorse.** Suppose there is a fixed set function `q` on the range of
`Y` — think of it as the target law the chain is mixing to — such that

  `|P(X ∈ A, Y ∈ B) − P(X ∈ A) · q B| ≤ ν`

for all measurable `A`, `B`. Then `X` and `Y` are `ν`-independent.

No property of `q` is used: it need not be a measure, let alone a probability
measure. What does the work is that `q` does not depend on `A`, so the estimate
applied at `A` and at `Aᶜ` can be combined convexly, and the `q B` terms cancel:

  `P(A ∩ B) − P(A) P(B) = (1 − P(A)) · h(A,B) − P(A) · h(Aᶜ,B)`

with `h(A,B) = P(A ∩ B) − P(A) q B`. Since `0 ≤ P(A) ≤ 1`, the right-hand side
is bounded by `(1 − P(A)) ν + P(A) ν = ν`. -/
theorem nuIndep_of_approx_product {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β} {ν : ℝ} {q : Set β → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ A : Set α, ∀ B : Set β, MeasurableSet A → MeasurableSet B →
      |μ.real (X ⁻¹' A ∩ Y ⁻¹' B) - μ.real (X ⁻¹' A) * q B| ≤ ν) :
    NuIndep μ X Y ν := by
  intro A B hA hB
  have hXA : MeasurableSet (X ⁻¹' A) := hX hA
  have hYB : MeasurableSet (Y ⁻¹' B) := hY hB
  -- the two instances of the hypothesis, at `A` and at `Aᶜ`
  have h1 := h A B hA hB
  have h2 := h Aᶜ B hA.compl hB
  -- rewrite the `Aᶜ` instance in terms of the `A` quantities
  have hpre : X ⁻¹' Aᶜ = (X ⁻¹' A)ᶜ := rfl
  have hcompl : μ.real ((X ⁻¹' A)ᶜ) = 1 - μ.real (X ⁻¹' A) := by
    rw [measureReal_compl hXA, probReal_univ]
  have hsplit : μ.real (X ⁻¹' A ∩ Y ⁻¹' B) + μ.real ((X ⁻¹' A)ᶜ ∩ Y ⁻¹' B)
      = μ.real (Y ⁻¹' B) := measureReal_inter_add_compl_inter hXA hYB
  rw [hpre, hcompl] at h2
  -- `0 ≤ P(X ∈ A) ≤ 1`
  have hp0 : 0 ≤ μ.real (X ⁻¹' A) := measureReal_nonneg
  have hp1 : μ.real (X ⁻¹' A) ≤ 1 := by
    rw [← probReal_univ (μ := μ)]
    exact measureReal_mono (subset_univ _) (measure_ne_top μ _)
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, hp0, hp1, hsplit]

/-! ## Where the hypothesis comes from: mixing

`nuIndep_of_approx_product` takes the approximate-product bound as given. That
bound is not an assumption in disguise: it is what a **mixing** statement
delivers. The next lemma is the derivation, in the one setting where "the
conditional law of the next sample" has an unambiguous meaning — a joint law
built as `ρ ⊗ₘ κ` from a law `ρ` for the past and a Markov kernel `κ` giving the
next sample's conditional law.

The hypothesis is exactly a mixing bound: `TVLe (κ a) π ν` for every `a`, i.e.
from *every* starting configuration the chain has come within total variation
`ν` of its target `π`. The conclusion is `ν`-independence of past and future,
with no loss of constant. -/

/-- **Mixing gives `ν`-independence.** Let the joint law of (past, next sample) be
`ρ ⊗ₘ κ`. If the conditional law `κ a` of the next sample is within total
variation `ν` of a fixed target `τ` for *every* past `a`, then the past and the
next sample are `ν.toReal`-independent.

This is the statement that makes `lem:delta-ind` (a) and (b) non-circular: their
hypothesis is a bound against a fixed reference `q`, and here `q = τ.real`
arrives from a pure mixing bound with nothing about the marginal of the next
sample assumed.

Both directions of the estimate stay in `ℝ≥0∞`, where `TVLe` is stated, so no
truncated subtraction appears: the upper bound integrates `κ a B ≤ τ B + ν` and
the lower bound integrates `τ B ≤ κ a B + ν`. -/
theorem nuIndep_compProd_of_tvLe {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ρ : Measure α} [IsProbabilityMeasure ρ] {κ : Kernel α β} [IsMarkovKernel κ]
    {τ : Measure β} [IsProbabilityMeasure τ] {ν : ℝ≥0∞} (hν : ν ≠ ⊤)
    (hmix : ∀ a, TVLe (κ a) τ ν) :
    NuIndep (ρ ⊗ₘ κ) (Prod.fst : α × β → α) (Prod.snd : α × β → β) ν.toReal := by
  refine nuIndep_of_approx_product (q := fun B => τ.real B)
    measurable_fst measurable_snd ?_
  intro A B hA hB
  have hrect : (Prod.fst ⁻¹' A ∩ Prod.snd ⁻¹' B : Set (α × β)) = A ×ˢ B := rfl
  have hfst : (Prod.fst ⁻¹' A : Set (α × β)) = A ×ˢ (univ : Set β) := by
    ext p; simp
  have hκmeas : Measurable fun a => κ a B := Kernel.measurable_coe κ hB
  -- the joint probability, as an integral of the conditional law
  have hjoint : (ρ ⊗ₘ κ) (A ×ˢ B) = ∫⁻ a in A, κ a B ∂ρ :=
    Measure.compProd_apply_prod hA hB
  have hmarg : (ρ ⊗ₘ κ) (A ×ˢ (univ : Set β)) = ρ A := by
    rw [Measure.compProd_apply_prod hA MeasurableSet.univ]
    simp
  set I : ℝ≥0∞ := ∫⁻ a in A, κ a B ∂ρ with hIdef
  have hρA : ρ A ≤ 1 := by
    rw [← measure_univ (μ := ρ)]; exact measure_mono (subset_univ _)
  have hτB : τ B ≤ 1 := by
    rw [← measure_univ (μ := τ)]; exact measure_mono (subset_univ _)
  -- the two one-sided bounds, in `ℝ≥0∞`
  have hub : I ≤ τ B * ρ A + ν := by
    have h1 : I ≤ ∫⁻ _a in A, (τ B + ν) ∂ρ :=
      lintegral_mono fun a => (hmix a B hB).1
    have h2 : ∫⁻ _a in A, (τ B + ν) ∂ρ = (τ B + ν) * ρ A := by
      rw [setLIntegral_const]
    have hνρ : ν * ρ A ≤ ν := by
      calc ν * ρ A ≤ ν * 1 := by gcongr
        _ = ν := mul_one ν
    refine h1.trans (h2.le.trans ?_)
    rw [add_mul]
    gcongr
  have hlb : τ B * ρ A ≤ I + ν := by
    have h1 : τ B * ρ A = ∫⁻ _a in A, τ B ∂ρ := by rw [setLIntegral_const]
    have h2 : ∫⁻ _a in A, τ B ∂ρ ≤ ∫⁻ a in A, (κ a B + ν) ∂ρ :=
      lintegral_mono fun a => (hmix a B hB).2
    have h3 : ∫⁻ a in A, (κ a B + ν) ∂ρ = I + ν * ρ A := by
      rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    have hνρ : ν * ρ A ≤ ν := by
      calc ν * ρ A ≤ ν * 1 := by gcongr
        _ = ν := mul_one ν
    rw [h1]
    refine (h2.trans_eq h3).trans ?_
    gcongr
  -- transfer to `ℝ`
  have hmulfin : τ B * ρ A ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top τ B) (measure_ne_top ρ A)
  have hIfin : I ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ hub
    exact ENNReal.add_ne_top.2 ⟨hmulfin, hν⟩
  have hubR : I.toReal ≤ (τ B).toReal * (ρ A).toReal + ν.toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hmulfin, hν⟩) hub
    rwa [ENNReal.toReal_add hmulfin hν, ENNReal.toReal_mul] at this
  have hlbR : (τ B).toReal * (ρ A).toReal ≤ I.toReal + ν.toReal := by
    have := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hIfin, hν⟩) hlb
    rwa [ENNReal.toReal_add hIfin hν, ENNReal.toReal_mul] at this
  rw [hrect, hfst]
  simp only [Measure.real, hjoint, hmarg]
  rw [abs_le]
  constructor <;> [linarith; linarith]

/-- **Non-vacuity of the mixing hypothesis.** A constant kernel — the next sample
drawn from the target `τ` regardless of the past — satisfies the hypothesis of
`nuIndep_compProd_of_tvLe` with `ν = 0`, and the conclusion is then genuine
independence of past and future by `nuIndep_zero_iff_indepFun`.

So the hypotheses of the mixing lemma, and hence of `lem:delta-ind` (a) and (b)
below, are satisfiable, and the `ν = 0` corner of the theory reproduces the
classical statement rather than something weaker. -/
theorem indepFun_compProd_const {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (ρ : Measure α) [IsProbabilityMeasure ρ] (τ : Measure β) [IsProbabilityMeasure τ] :
    IndepFun (Prod.fst : α × β → α) (Prod.snd : α × β → β) (ρ ⊗ₘ Kernel.const α τ) := by
  have hmix : ∀ a : α, TVLe (Kernel.const α τ a) τ 0 := by
    intro a
    rw [Kernel.const_apply]
    exact tvLe_zero_iff.mpr rfl
  have h : NuIndep (ρ ⊗ₘ Kernel.const α τ)
      (Prod.fst : α × β → α) (Prod.snd : α × β → β) (0 : ℝ≥0∞).toReal :=
    nuIndep_compProd_of_tvLe (ρ := ρ) (κ := Kernel.const α τ) (τ := τ) (ν := 0)
      (by simp) hmix
  rw [ENNReal.toReal_zero] at h
  exact nuIndep_zero_iff_indepFun.mp h

/-! ## Transfer along a coupling

Cousins–Vempala do not pay for the sampler in bias; they pay for it in failure
probability. `:1426-1431` couples the algorithm's samples `X_j^i` to
exactly-distributed samples `X̄_j^i` with

  `P(X_j^i = X̄_j^i for all i, j) ≥ 1 − tν`,

and every subsequent statement is made about the *barred* variables. So the
dependence bound has to survive the substitution. It does, at an additive cost
of twice the coupling failure probability on each side. -/

/-- If two measurable sets agree on an event `E`, their measures differ by at most
`μ(Eᶜ)`. -/
theorem abs_measureReal_sub_le_of_inter_eq [IsFiniteMeasure μ] {S S' E : Set Ω}
    (hS : MeasurableSet S) (hS' : MeasurableSet S') (hE : MeasurableSet E)
    (hagree : E ∩ S = E ∩ S') :
    |μ.real S - μ.real S'| ≤ μ.real Eᶜ := by
  have h1 : μ.real (E ∩ S) + μ.real (Eᶜ ∩ S) = μ.real S :=
    measureReal_inter_add_compl_inter hE hS
  have h2 : μ.real (E ∩ S') + μ.real (Eᶜ ∩ S') = μ.real S' :=
    measureReal_inter_add_compl_inter hE hS'
  have hb1 : μ.real (Eᶜ ∩ S) ≤ μ.real Eᶜ :=
    measureReal_mono inter_subset_left (measure_ne_top μ _)
  have hb2 : μ.real (Eᶜ ∩ S') ≤ μ.real Eᶜ :=
    measureReal_mono inter_subset_left (measure_ne_top μ _)
  have hn1 : 0 ≤ μ.real (Eᶜ ∩ S) := measureReal_nonneg
  have hn2 : 0 ≤ μ.real (Eᶜ ∩ S') := measureReal_nonneg
  rw [hagree] at h1
  rw [abs_le]
  constructor <;> linarith

/-- **`ν`-independence survives a coupling.** If `X` agrees with `X'` off an event of
probability at most `δ₁`, and `Y` agrees with `Y'` off an event of probability at
most `δ₂`, then `ν`-independence of `(X, Y)` gives `(ν + 2 δ₁ + 2 δ₂)`-independence
of `(X', Y')`.

The factor of two is unavoidable in this argument and is where the paper's
constants come from: the joint probability moves by at most `δ₁ + δ₂`, and the
product of the marginals moves by at most `δ₁ + δ₂` again (each marginal moves by
its own `δ` and the other factor is at most `1`).

The agreement events are taken as explicit measurable sets rather than as
`{ω | X ω = X' ω}`, which need not be measurable without separability
assumptions on the target space. -/
theorem NuIndep.of_coupling {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [IsProbabilityMeasure μ] {X X' : Ω → α} {Y Y' : Ω → β} {ν δ₁ δ₂ : ℝ}
    (h : NuIndep μ X Y ν)
    (hX : Measurable X) (hX' : Measurable X') (hY : Measurable Y) (hY' : Measurable Y')
    {E₁ E₂ : Set Ω} (hE₁ : MeasurableSet E₁) (hE₂ : MeasurableSet E₂)
    (hδ₁ : μ.real E₁ᶜ ≤ δ₁) (hδ₂ : μ.real E₂ᶜ ≤ δ₂)
    (hagree₁ : ∀ ω ∈ E₁, X ω = X' ω) (hagree₂ : ∀ ω ∈ E₂, Y ω = Y' ω) :
    NuIndep μ X' Y' (ν + 2 * δ₁ + 2 * δ₂) := by
  intro A B hA hB
  have hbase := h A B hA hB
  -- the joint probabilities
  have hjoint : |μ.real (X ⁻¹' A ∩ Y ⁻¹' B) - μ.real (X' ⁻¹' A ∩ Y' ⁻¹' B)|
      ≤ μ.real (E₁ ∩ E₂)ᶜ := by
    refine abs_measureReal_sub_le_of_inter_eq ((hX hA).inter (hY hB))
      ((hX' hA).inter (hY' hB)) (hE₁.inter hE₂) ?_
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨⟨hω₁, hω₂⟩, hωA, hωB⟩
      refine ⟨⟨hω₁, hω₂⟩, ?_, ?_⟩
      · rwa [← hagree₁ ω hω₁]
      · rwa [← hagree₂ ω hω₂]
    · rintro ⟨⟨hω₁, hω₂⟩, hωA, hωB⟩
      refine ⟨⟨hω₁, hω₂⟩, ?_, ?_⟩
      · rwa [hagree₁ ω hω₁]
      · rwa [hagree₂ ω hω₂]
  have hEc : μ.real (E₁ ∩ E₂)ᶜ ≤ δ₁ + δ₂ := by
    have : (E₁ ∩ E₂)ᶜ = E₁ᶜ ∪ E₂ᶜ := by rw [Set.compl_inter]
    rw [this]
    exact (measureReal_union_le _ _).trans (by linarith)
  -- the marginals
  have hmargX : |μ.real (X ⁻¹' A) - μ.real (X' ⁻¹' A)| ≤ δ₁ := by
    refine le_trans (abs_measureReal_sub_le_of_inter_eq (hX hA) (hX' hA) hE₁ ?_) hδ₁
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hω, hωA⟩; exact ⟨hω, by rwa [← hagree₁ ω hω]⟩
    · rintro ⟨hω, hωA⟩; exact ⟨hω, by rwa [hagree₁ ω hω]⟩
  have hmargY : |μ.real (Y ⁻¹' B) - μ.real (Y' ⁻¹' B)| ≤ δ₂ := by
    refine le_trans (abs_measureReal_sub_le_of_inter_eq (hY hB) (hY' hB) hE₂ ?_) hδ₂
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨hω, hωB⟩; exact ⟨hω, by rwa [← hagree₂ ω hω]⟩
    · rintro ⟨hω, hωB⟩; exact ⟨hω, by rwa [hagree₂ ω hω]⟩
  -- everything in sight is a probability, hence in `[0, 1]`
  have hle1 : ∀ S : Set Ω, μ.real S ≤ 1 := fun S => by
    rw [← probReal_univ (μ := μ)]
    exact measureReal_mono (subset_univ _) (measure_ne_top μ _)
  have hn : ∀ S : Set Ω, 0 ≤ μ.real S := fun _ => measureReal_nonneg
  rw [abs_le] at hbase hjoint hmargX hmargY ⊢
  constructor <;>
    nlinarith [hbase.1, hbase.2, hjoint.1, hjoint.2, hmargX.1, hmargX.2,
      hmargY.1, hmargY.2, hEc, hn (X ⁻¹' A), hle1 (X ⁻¹' A), hn (Y ⁻¹' B),
      hle1 (Y ⁻¹' B), hn (X' ⁻¹' A), hle1 (X' ⁻¹' A), hn (Y' ⁻¹' B), hle1 (Y' ⁻¹' B)]

/-! ## `lem:delta-ind`

The paper's Lemma at `:1481-1488`. Writing `(Z_0, …, Z_{t-1})` for the whole
sequence of sample points used by the algorithm and `Z̄_i` for their coupled,
exactly-distributed versions:

> (a) For `0 ≤ i < t`, `Z_i` and `Z_{i+1}` are `ν`-independent, and `Z̄_i`,
>     `Z̄_{i+1}` are `(3ν)`-independent.
> (b) For `0 ≤ i < t`, `(Z_0, …, Z_i)` and `Z_{i+1}` are `(3ν)`-independent.
> (c) For `0 ≤ i < m`, `W̄_1 ⋯ W̄_i` and `W̄_{i+1}` are `(3kmν)`-independent.

The hypothesis carried throughout is the **mixing** input: conditionally on
whatever has already happened, the next sample's law is within `ν` of a fixed
target `q`. That is a statement comparing against a fixed reference and is
strictly weaker than the conclusion, which compares against `Z_{i+1}`'s own
marginal; `nuIndep_of_approx_product` is what converts one into the other.

Note that (a) and (b) have the *same* proof. The paper's `(Z_0, …, Z_i)` plays no
role beyond being some measurable function of the past, so the statements below
take an abstract history variable `H`; the literal tuple is recovered in
`delta_ind_b_tuple`. -/

section DeltaInd

variable {α : Type*} [MeasurableSpace α] [IsProbabilityMeasure μ]

/-- **`lem:delta-ind` (a), unbarred half.** If the chain has mixed — the law of
`Z_{i+1}` given `Z_i ∈ A` is within `ν` of a fixed `q`, uniformly in `A` — then
`Z_i` and `Z_{i+1}` are `ν`-independent. The paper's constant, exactly. -/
theorem delta_ind_a {Z : ℕ → Ω → α} {ν : ℝ} {q : Set α → ℝ}
    (hZ : ∀ j, Measurable (Z j)) (i : ℕ)
    (hmix : ∀ A B : Set α, MeasurableSet A → MeasurableSet B →
      |μ.real (Z i ⁻¹' A ∩ Z (i + 1) ⁻¹' B) - μ.real (Z i ⁻¹' A) * q B| ≤ ν) :
    NuIndep μ (Z i) (Z (i + 1)) ν :=
  nuIndep_of_approx_product (hZ i) (hZ (i + 1)) hmix

/-- **`lem:delta-ind` (a), barred half.** Transferring (a) along the coupling of
`:1426-1431`, in which `Z_j` and `Z̄_j` agree off an event of probability at most
`ν`, gives `ν`-independence of `Z̄_i, Z̄_{i+1}` with constant `5ν`.

The paper asserts `3ν`, citing `LV2`; the constant proved here is what
`NuIndep.of_coupling` yields (`ν + 2ν + 2ν`), and the difference is immaterial
downstream, where the parameter is consumed symbolically. -/
theorem delta_ind_a_bar {Z Z' : ℕ → Ω → α} {ν : ℝ} (i : ℕ)
    (h : NuIndep μ (Z i) (Z (i + 1)) ν)
    (hZ : ∀ j, Measurable (Z j)) (hZ' : ∀ j, Measurable (Z' j))
    {E : ℕ → Set Ω} (hE : ∀ j, MeasurableSet (E j)) (hEν : ∀ j, μ.real (E j)ᶜ ≤ ν)
    (hagree : ∀ j, ∀ ω ∈ E j, Z j ω = Z' j ω) :
    NuIndep μ (Z' i) (Z' (i + 1)) (5 * ν) := by
  have := h.of_coupling (hZ i) (hZ' i) (hZ (i + 1)) (hZ' (i + 1))
    (hE i) (hE (i + 1)) (hEν i) (hEν (i + 1)) (hagree i) (hagree (i + 1))
  exact this.mono (by ring_nf; rfl)

/-- **`lem:delta-ind` (b).** The whole past, packaged as any measurable variable
`H`, is `ν`-independent of the next sample, under the same mixing hypothesis as
(a) — now required to hold uniformly over events of the *history* rather than
just of `Z_i`. This is exactly where the Markov property is used in the paper:
the conditional law of `Z_{i+1}` given the past depends on the past only through
`Z_i`, so the same `ν` serves. -/
theorem delta_ind_b {γ : Type*} [MeasurableSpace γ] {H : Ω → γ} {Y : Ω → α}
    {ν : ℝ} {q : Set α → ℝ} (hH : Measurable H) (hY : Measurable Y)
    (hmix : ∀ A : Set γ, ∀ B : Set α, MeasurableSet A → MeasurableSet B →
      |μ.real (H ⁻¹' A ∩ Y ⁻¹' B) - μ.real (H ⁻¹' A) * q B| ≤ ν) :
    NuIndep μ H Y ν :=
  nuIndep_of_approx_product hH hY hmix

/-- **`lem:delta-ind` (b), the paper's literal statement**: the tuple
`(Z_0, …, Z_i)` and `Z_{i+1}` are `ν`-independent. An instance of `delta_ind_b`
with `H` the tuple map; the only work is that a tuple of measurable maps is
measurable. -/
theorem delta_ind_b_tuple {Z : ℕ → Ω → α} {ν : ℝ} {q : Set α → ℝ}
    (hZ : ∀ j, Measurable (Z j)) (i : ℕ)
    (hmix : ∀ A : Set (Fin (i + 1) → α), ∀ B : Set α, MeasurableSet A → MeasurableSet B →
      |μ.real ((fun ω (j : Fin (i + 1)) => Z (j : ℕ) ω) ⁻¹' A ∩ Z (i + 1) ⁻¹' B)
        - μ.real ((fun ω (j : Fin (i + 1)) => Z (j : ℕ) ω) ⁻¹' A) * q B| ≤ ν) :
    NuIndep μ (fun ω (j : Fin (i + 1)) => Z (j : ℕ) ω) (Z (i + 1)) ν :=
  delta_ind_b (measurable_pi_lambda _ fun j => hZ (j : ℕ)) (hZ (i + 1)) hmix

/-- **`lem:delta-ind` (c), general form** — the statement the variance argument of
`:1512-1520` consumes.

`S` and `T` are the algorithm's sample blocks: `S` carries the first `i` phases
(from which `W̄_1 ⋯ W̄_i` is computed by the measurable map `f`) and `T` carries
phase `i + 1` (from which `W̄_{i+1}` is computed by `g`). `S'`, `T'` are their
coupled exact counterparts. Three ingredients, and no more:

* a block-level mixing bound `νb` between the *unbarred* blocks
  (`nuIndep_of_approx_product`);
* the coupling transfer at cost `2 δ₁ + 2 δ₂` (`NuIndep.of_coupling`);
* `lem:fn-indep` to push the bound through `f` and `g` (`NuIndep.comp`, already
  in `Estimator.lean`).

Note the order: the transfer has to happen *before* `f` and `g` are applied,
because the coupling is between sample blocks, not between phase means. -/
theorem delta_ind_c {α₁ α₂ β₁ β₂ : Type*} [MeasurableSpace α₁] [MeasurableSpace α₂]
    [MeasurableSpace β₁] [MeasurableSpace β₂]
    {S S' : Ω → α₁} {T T' : Ω → α₂} {f : α₁ → β₁} {g : α₂ → β₂}
    {νb δ₁ δ₂ : ℝ} {q : Set α₂ → ℝ}
    (hS : Measurable S) (hS' : Measurable S') (hT : Measurable T) (hT' : Measurable T')
    (hf : Measurable f) (hg : Measurable g)
    (hmix : ∀ A : Set α₁, ∀ B : Set α₂, MeasurableSet A → MeasurableSet B →
      |μ.real (S ⁻¹' A ∩ T ⁻¹' B) - μ.real (S ⁻¹' A) * q B| ≤ νb)
    {E₁ E₂ : Set Ω} (hE₁ : MeasurableSet E₁) (hE₂ : MeasurableSet E₂)
    (hδ₁ : μ.real E₁ᶜ ≤ δ₁) (hδ₂ : μ.real E₂ᶜ ≤ δ₂)
    (hagree₁ : ∀ ω ∈ E₁, S ω = S' ω) (hagree₂ : ∀ ω ∈ E₂, T ω = T' ω) :
    NuIndep μ (fun ω => f (S' ω)) (fun ω => g (T' ω)) (νb + 2 * δ₁ + 2 * δ₂) :=
  ((nuIndep_of_approx_product hS hT hmix).of_coupling hS hS' hT hT'
    hE₁ hE₂ hδ₁ hδ₂ hagree₁ hagree₂).comp hf hg

/-- **`lem:delta-ind` (c), in the paper's parameters.** With `k` samples per phase,
`m` phases and per-sample total-variation error `ν`, the coupling failure over
the first `i ≤ m` phases costs at most `k m ν` and over phase `i + 1` at most
`k ν`; with a block-level mixing bound of `k ν` the result is

  `W̄_1 ⋯ W̄_i` and `W̄_{i+1}` are `(5 k m ν)`-independent.

The paper claims `3 k m ν` (`:1487`), inherited from `LV2` without proof. Both
are `O(k m ν)`, and `:1512-1520` uses only that. -/
theorem delta_ind_c_paper {α₁ α₂ β₁ β₂ : Type*} [MeasurableSpace α₁] [MeasurableSpace α₂]
    [MeasurableSpace β₁] [MeasurableSpace β₂]
    {S S' : Ω → α₁} {T T' : Ω → α₂} {f : α₁ → β₁} {g : α₂ → β₂}
    {k m ν : ℝ} {q : Set α₂ → ℝ} (hν : 0 ≤ ν) (hk : 0 ≤ k) (hm : 1 ≤ m)
    (hS : Measurable S) (hS' : Measurable S') (hT : Measurable T) (hT' : Measurable T')
    (hf : Measurable f) (hg : Measurable g)
    (hmix : ∀ A : Set α₁, ∀ B : Set α₂, MeasurableSet A → MeasurableSet B →
      |μ.real (S ⁻¹' A ∩ T ⁻¹' B) - μ.real (S ⁻¹' A) * q B| ≤ k * ν)
    {E₁ E₂ : Set Ω} (hE₁ : MeasurableSet E₁) (hE₂ : MeasurableSet E₂)
    (hδ₁ : μ.real E₁ᶜ ≤ k * m * ν) (hδ₂ : μ.real E₂ᶜ ≤ k * ν)
    (hagree₁ : ∀ ω ∈ E₁, S ω = S' ω) (hagree₂ : ∀ ω ∈ E₂, T ω = T' ω) :
    NuIndep μ (fun ω => f (S' ω)) (fun ω => g (T' ω)) (5 * k * m * ν) := by
  refine (delta_ind_c hS hS' hT hT' hf hg hmix hE₁ hE₂ hδ₁ hδ₂ hagree₁ hagree₂).mono ?_
  nlinarith [mul_nonneg hk hν]

end DeltaInd

/-! ## The truncation device

The paper's `V_i = min {W̄_i, α E(W̄_i)}` (`:1495-1500`). The upper bound
`E(V_i) ≤ E(W̄_i)` is monotonicity of the integral; the lower bound is
`lem:exp-bd` (`expect_min_ge`) with the truncation level `a = α E(W̄_i)`, fed a
per-phase second-moment ratio `E(W̄_i²) ≤ c E(W̄_i)²`.

Nothing here is specific to the phase means: `X` is any nonnegative integrable
random variable with a finite second moment and a strictly positive mean. -/

/-- The truncation `min X a` of a nonnegative integrable `X` at a nonnegative level is
itself integrable, being sandwiched between `0` and `X`. -/
theorem integrable_min_const {X : Ω → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hX0 : ∀ ω, 0 ≤ X ω) (hXm : Measurable X) (hX : Integrable X μ) :
    Integrable (fun ω => min (X ω) a) μ := by
  refine Integrable.mono' hX ((hXm.min measurable_const).aestronglyMeasurable) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hX0 ω) ha)]
  exact min_le_left _ _

/-- **`E(V_i) ≤ E(W̄_i)`** (`:1498`, "it is clear that"). Truncation cannot increase
the mean, because `min X a ≤ X` pointwise. -/
theorem expect_trunc_le {X : Ω → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hX0 : ∀ ω, 0 ≤ X ω) (hXm : Measurable X) (hX : Integrable X μ) :
    (∫ ω, min (X ω) a ∂μ) ≤ ∫ ω, X ω ∂μ :=
  integral_mono (integrable_min_const ha hX0 hXm hX) hX fun _ => min_le_left _ _

/-- **The truncation lower bound, general form.** If `X ≥ 0` has a strictly positive
mean and a second moment obeying `E(X²) ≤ c E(X)²`, then truncating at
`a = α E(X)` costs a factor of at most `c / (4α)`:

  `E(min(X, α E(X))) ≥ (1 − c/(4α)) E(X)`.

This is `lem:exp-bd` (`expect_min_ge`) with the paper's choice of truncation
level; the only extra step is `E(X²)/(4 α E(X)) ≤ c E(X)/(4α)`. -/
theorem expect_trunc_ge {X : Ω → ℝ} {c α : ℝ} (hα : 0 < α)
    (hX0 : ∀ ω, 0 ≤ X ω) (hXm : Measurable X) (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => (X ω) ^ 2) μ)
    (hEpos : 0 < ∫ ω, X ω ∂μ)
    (hc : (∫ ω, (X ω) ^ 2 ∂μ) ≤ c * (∫ ω, X ω ∂μ) ^ 2) :
    (1 - c / (4 * α)) * (∫ ω, X ω ∂μ) ≤ ∫ ω, min (X ω) (α * ∫ ω, X ω ∂μ) ∂μ := by
  set E := ∫ ω, X ω ∂μ with hE
  have ha : 0 < α * E := mul_pos hα hEpos
  have key := expect_min_ge (μ := μ) (X := X) (a := α * E) ha hX0 hXm hX hX2
  have hden : (0 : ℝ) < 4 * (α * E) := by positivity
  have hstep : (∫ ω, (X ω) ^ 2 ∂μ) / (4 * (α * E)) ≤ c * E / (4 * α) := by
    have h1 : (∫ ω, (X ω) ^ 2 ∂μ) / (4 * (α * E)) ≤ (c * E ^ 2) / (4 * (α * E)) := by
      gcongr
    refine h1.trans_eq ?_
    field_simp
  have : (1 - c / (4 * α)) * E = E - c * E / (4 * α) := by ring
  rw [this]
  linarith

/-- **The truncation lower bound, the paper's form** (`:1499-1500`):

  `E(V_i) ≥ (1 − 1/(2α)) E(W̄_i)`.

The paper's per-phase second-moment ratio is `c = 1 + 7/k`, and the step from
`1 − c/(4α)` to `1 − 1/(2α)` is exactly `c ≤ 2`. -/
theorem expect_trunc_ge_half {X : Ω → ℝ} {c α : ℝ} (hα : 0 < α)
    (hX0 : ∀ ω, 0 ≤ X ω) (hXm : Measurable X) (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => (X ω) ^ 2) μ)
    (hEpos : 0 < ∫ ω, X ω ∂μ)
    (hc : (∫ ω, (X ω) ^ 2 ∂μ) ≤ c * (∫ ω, X ω ∂μ) ^ 2) (hc2 : c ≤ 2) :
    (1 - 1 / (2 * α)) * (∫ ω, X ω ∂μ) ≤ ∫ ω, min (X ω) (α * ∫ ω, X ω ∂μ) ∂μ := by
  refine le_trans ?_ (expect_trunc_ge hα hX0 hXm hX hX2 hEpos hc)
  have hstep : c / (4 * α) ≤ 1 / (2 * α) := by
    have hrw : 1 / (2 * α) = 2 / (4 * α) := by
      field_simp
      ring
    rw [hrw]
    gcongr
  nlinarith [hEpos.le]

/-- **The paper's instance** (`:1498-1500`): with the per-phase ratio
`E(W̄_i²) ≤ (1 + 7/k) E(W̄_i)²` and `k ≥ 7` samples per phase,

  `E(V_i) ≥ (1 − 1/(2α)) E(W̄_i)`.

`k ≥ 7` is precisely what turns `1 + 7/k ≤ 2` into a true statement; the paper
imposes a much larger lower bound on `k` elsewhere. -/
theorem expect_trunc_ge_half_of_seven_le {X : Ω → ℝ} {k α : ℝ} (hα : 0 < α) (hk : 7 ≤ k)
    (hX0 : ∀ ω, 0 ≤ X ω) (hXm : Measurable X) (hX : Integrable X μ)
    (hX2 : Integrable (fun ω => (X ω) ^ 2) μ)
    (hEpos : 0 < ∫ ω, X ω ∂μ)
    (hc : (∫ ω, (X ω) ^ 2 ∂μ) ≤ (1 + 7 / k) * (∫ ω, X ω ∂μ) ^ 2) :
    (1 - 1 / (2 * α)) * (∫ ω, X ω ∂μ) ≤ ∫ ω, min (X ω) (α * ∫ ω, X ω ∂μ) ∂μ := by
  have hkpos : (0 : ℝ) < k := by linarith
  have : (7 : ℝ) / k ≤ 1 := by
    rw [div_le_one hkpos]; linarith
  exact expect_trunc_ge_half hα hX0 hXm hX hX2 hEpos hc (by linarith)

/-! ## Towards `lem:cov-bd`

`lem:cov-bd` (`:1405`) says that for `0 ≤ X ≤ a` and `0 ≤ Y ≤ b`,

  `|E(XY) − E(X) E(Y)| ≤ a b μ(X, Y)`,

and its proof is the double layer-cake identity
`E(XY) = ∫₀^a ∫₀^b P(X > s, Y > t) dt ds`. The *outer* layer cake — the one over
`X` — needs Tonelli on `Ω × (0,1]` and is not done here. The *inner* one is, in
the case that costs nothing: when the first factor is an indicator, the layer
cake over it is trivial, and what remains is a single layer cake over the second
factor. That case is proved below, and it is already a covariance bound. -/

/-- **`lem:cov-bd` with one factor an indicator.** For `ν`-independent `X`, `Y`
and a measurable `g` with values in `[0,1]`,

  `|E(1_{X ∈ A₀} · g(Y)) − P(X ∈ A₀) E(g(Y))| ≤ ν`.

The single layer cake `∫ f = ∫_{(0,1]} P(f ≥ t) dt` applies to both terms, and
the point is the set identity, valid for every `t > 0`:

  `{ω | t ≤ 1_{X ∈ A₀}(ω) · g(Y ω)} = X⁻¹(A₀) ∩ Y⁻¹{y | t ≤ g y}`

— the indicator annihilates everything off `A₀`, where the product is `0 < t`.
So the integrand gap at level `t` is *exactly* the quantity `NuIndep` bounds,
and `(0,1]` has Lebesgue measure `1`, so integrating loses nothing. The constant
is `ν`, matching `lem:cov-bd` at `a = b = 1`. -/
theorem abs_integral_indicator_mul_sub_le {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β} {ν : ℝ}
    (h : NuIndep μ X Y ν) (hX : Measurable X) (hY : Measurable Y)
    {A₀ : Set α} (hA₀ : MeasurableSet A₀) {g : β → ℝ} (hg : Measurable g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    |(∫ ω, (X ⁻¹' A₀).indicator (fun _ => (1 : ℝ)) ω * g (Y ω) ∂μ)
      - μ.real (X ⁻¹' A₀) * ∫ ω, g (Y ω) ∂μ| ≤ ν := by
  set c : ℝ := μ.real (X ⁻¹' A₀) with hc
  set f : Ω → ℝ := fun ω => (X ⁻¹' A₀).indicator (fun _ => (1 : ℝ)) ω * g (Y ω) with hf
  have hXA : MeasurableSet (X ⁻¹' A₀) := hX hA₀
  have hfmeas : Measurable f := (measurable_const.indicator hXA).mul (hg.comp hY)
  have hgYmeas : Measurable fun ω => g (Y ω) := hg.comp hY
  have hf0 : ∀ ω, 0 ≤ f ω := by
    intro ω
    by_cases hω : ω ∈ X ⁻¹' A₀ <;> simp [hf, Set.indicator_of_mem, Set.indicator_of_notMem, hω,
      hg0 (Y ω)]
  have hf1 : ∀ ω, f ω ≤ 1 := by
    intro ω
    by_cases hω : ω ∈ X ⁻¹' A₀ <;>
      simp [hf, Set.indicator_of_mem, Set.indicator_of_notMem, hω, hg1 (Y ω)]
  -- the level sets of `f`, for every positive level
  have hset : ∀ t : ℝ, 0 < t →
      {ω | t ≤ f ω} = X ⁻¹' A₀ ∩ Y ⁻¹' {y | t ≤ g y} := by
    intro t ht
    ext ω
    by_cases hω : ω ∈ X ⁻¹' A₀
    · simp [hf, Set.mem_setOf_eq, hω]
    · simp only [Set.mem_setOf_eq, hf, Set.indicator_of_notMem hω, zero_mul,
        Set.mem_inter_iff, hω, false_and, iff_false, not_le]
      exact ht
  -- the two layer-cake representations
  have hlcf : ∫ ω, f ω ∂μ = ∫ t in Ioc (0 : ℝ) 1, μ.real {ω | t ≤ f ω} :=
    (Arlib.integrable_of_forall_mem_Icc hfmeas hf0 hf1).integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hf1)
  have hlcg : ∫ ω, g (Y ω) ∂μ = ∫ t in Ioc (0 : ℝ) 1, μ.real {ω | t ≤ g (Y ω)} :=
    (Arlib.integrable_of_forall_mem_Icc hgYmeas (fun ω => hg0 (Y ω))
      (fun ω => hg1 (Y ω))).integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall fun ω => hg0 (Y ω))
      (Filter.Eventually.of_forall fun ω => hg1 (Y ω))
  have htf := Arlib.integrableOn_measureReal_tail μ f
  have htg := (Arlib.integrableOn_measureReal_tail μ fun ω => g (Y ω)).const_mul c
  calc |(∫ ω, f ω ∂μ) - c * ∫ ω, g (Y ω) ∂μ|
      = |∫ t in Ioc (0 : ℝ) 1,
          (μ.real {ω | t ≤ f ω} - c * μ.real {ω | t ≤ g (Y ω)})| := by
        rw [hlcf, hlcg, ← integral_const_mul, ← integral_sub htf htg]
    _ ≤ ∫ t in Ioc (0 : ℝ) 1,
          |μ.real {ω | t ≤ f ω} - c * μ.real {ω | t ≤ g (Y ω)}| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _t in Ioc (0 : ℝ) 1, ν := by
        refine setIntegral_mono_on (htf.sub htg).abs
          (integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc ?_
        intro t ht
        rw [hset t ht.1]
        exact h A₀ {y | t ≤ g y} hA₀ (measurableSet_le measurable_const hg)
    _ = ν := by rw [setIntegral_const]; simp

/-- **`lem:cov-bd` with one factor an indicator, unnormalised.** The same bound for
`g` with values in `[0, b]`, at cost `b ν` — the `a = 1` case of the paper's
`|E(XY) − E(X)E(Y)| ≤ a b μ(X,Y)`. Obtained from the normalised form by applying
it to `g / b`. -/
theorem abs_integral_indicator_mul_sub_le' {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β} {ν b : ℝ}
    (h : NuIndep μ X Y ν) (hX : Measurable X) (hY : Measurable Y)
    {A₀ : Set α} (hA₀ : MeasurableSet A₀) {g : β → ℝ} (hg : Measurable g)
    (hb : 0 < b) (hg0 : ∀ y, 0 ≤ g y) (hgb : ∀ y, g y ≤ b) :
    |(∫ ω, (X ⁻¹' A₀).indicator (fun _ => (1 : ℝ)) ω * g (Y ω) ∂μ)
      - μ.real (X ⁻¹' A₀) * ∫ ω, g (Y ω) ∂μ| ≤ b * ν := by
  have key := abs_integral_indicator_mul_sub_le h hX hY hA₀ (hg.div_const b)
    (fun y => div_nonneg (hg0 y) hb.le) (fun y => (div_le_one hb).2 (hgb y))
  have e1 : (fun ω => (X ⁻¹' A₀).indicator (fun _ => (1 : ℝ)) ω * (g (Y ω) / b))
      = fun ω => ((X ⁻¹' A₀).indicator (fun _ => (1 : ℝ)) ω * g (Y ω)) / b := by
    funext ω; ring
  simp only [e1] at key
  rw [integral_div, integral_div] at key
  have e2 : (∫ ω, (X ⁻¹' A₀).indicator (fun _ => (1 : ℝ)) ω * g (Y ω) ∂μ) / b
      - μ.real (X ⁻¹' A₀) * ((∫ ω, g (Y ω) ∂μ) / b)
      = ((∫ ω, (X ⁻¹' A₀).indicator (fun _ => (1 : ℝ)) ω * g (Y ω) ∂μ)
        - μ.real (X ⁻¹' A₀) * ∫ ω, g (Y ω) ∂μ) / b := by ring
  rw [e2, abs_div, abs_of_pos hb, div_le_iff₀ hb] at key
  linarith

/-! ## Axiom audit

Every theorem in this file, checked. All must read
`[propext, Classical.choice, Quot.sound]` — Mathlib's three foundational axioms
and nothing else. -/

#print axioms NuIndep.mono
#print axioms NuIndep.symm
#print axioms nuIndep_zero_iff_indepFun
#print axioms measureReal_inter_add_compl_inter
#print axioms nuIndep_of_approx_product
#print axioms nuIndep_compProd_of_tvLe
#print axioms indepFun_compProd_const
#print axioms abs_measureReal_sub_le_of_inter_eq
#print axioms NuIndep.of_coupling
#print axioms delta_ind_a
#print axioms delta_ind_a_bar
#print axioms delta_ind_b
#print axioms delta_ind_b_tuple
#print axioms delta_ind_c
#print axioms delta_ind_c_paper
#print axioms integrable_min_const
#print axioms expect_trunc_le
#print axioms expect_trunc_ge
#print axioms expect_trunc_ge_half
#print axioms expect_trunc_ge_half_of_seven_le
#print axioms abs_integral_indicator_mul_sub_le
#print axioms abs_integral_indicator_mul_sub_le'

end Arlib.GaussianCooling
