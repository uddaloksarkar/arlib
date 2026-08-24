/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.KLS97Shell
import Arlib.MarkovChains.Continuous.WastedSteps

/-!
# `λ ≥ 1/2` without Lovász–Vempala Lemma 6.3

Cousins–Vempala's `lem:lambda-bound` (`1409.6011/vol3_journal.tex:853`) asserts that the
average local conductance satisfies `λ(f) ≥ 1/2`, and proves it by way of Lovász–Vempala's
smoothing `f̂` and their Lemma 6.3 (RSA 30(3), 2007).  In this repository that route is
`LovaszSmoothing.lean` / `LovaszSmoothingSharp.lean`, and it terminates in the **unproved**
hypothesis `hLov`: Lemma 6.3 itself is not formalised, because its proof runs through
Kannan–Lovász–Simonovits 1997 Corollary 4.6, which needs the `(n−1)`-dimensional surface
measure of a convex body and the inequality `vol(K) ≥ (r/n)·vol_{n−1}(∂K)` — neither is
available in Mathlib in usable form.

**This file obtains `λ ≥ 1/2` — Cousins–Vempala's own constant — without any of that.**

The observation is that `Arlib.MarkovChains.avgLocalConductance K δ` is the *uniform* average
`(∫_K ℓ)/vol(K)`, and at a step size no larger than the shrink,

    ∫_K ℓ  ≥  ∫_{cK} ℓ  =  vol(cK)  =  cⁿ·vol(K)  ≥  (1/2)·vol(K),

where the middle equality is `Arlib.MarkovChains.ell_eq_one_on_shrunken` (the local
conductance is *identically* `1` on the shrunken body) and `cⁿ ≥ 1/2` at `c = 1 − 1/(2n)` is
`Arlib.MarkovChains.half_le_one_sub_inv_two_mul_pow`.  Both are already proved, so nothing
here is imported on faith.

## The regime, and what it costs

The argument needs `δ ≤ 1 − c = 1/(2n)`, which is **not** Cousins–Vempala's step size
`δ ≤ min{σ,1}/(4096√n)`; for large `n` it is the more restrictive of the two.  That is
precisely why Cousins–Vempala cannot argue this way and must invoke Lemma 6.3: at *their*
step, `ℓ ≡ 1` on `cK` is false.  The price of the smaller step is extra polynomial factors in
the mixing time (conductance is proportional to `δ`, so `1/Φ²` grows by `(σ√n/δ)²`), not a
loss of polynomiality.

The chain in this repository already runs at `δ = 1/(2n)` — see `SamplerStepCount.lean` — so
the restriction is not a new one.  The composed cold/warm step `δ := min(σ/(8√n), 1/(2n))` is
`≤ 1/(2n)` unconditionally, so this bound covers both regimes with no case split.

## What is proved here

* `Arlib.MarkovChains.volume_smul_set` — `vol(c·K) = cⁿ·vol(K)` for `c > 0`.
* `Arlib.MarkovChains.half_mul_volume_le_lintegral_ell` — the multiplicative form,
  `(1/2)·vol(K) ≤ ∫_K ℓ`, which is the robust statement (it says the right thing when
  `vol K ∈ {0, ⊤}`).
* `Arlib.MarkovChains.half_le_avgLocalConductance` — the divided form, `1/2 ≤ λ`, under the
  two guards `vol K ≠ 0`, `vol K ≠ ⊤`.
* `Arlib.MarkovChains.sum_lintegral_inv_ell_iterate_speedyWalk_le_uncond` — the wasted-step
  bound of `lem:speedy-to-ball` with its `λ` binder **discharged**: `∑ ≤ 2·t·M`.
* `Arlib.MarkovChains.exists_half_le_avgLocalConductance_witness` — a non-vacuity witness.

**Scope.**  This settles `λ` for the uniform average, which is the quantity every consumer in
this repository actually takes (`WastedSteps.lean`'s `hlam`).  It does **not** prove
Lovász–Vempala Lemma 6.3, and does not supply `λ` at Cousins–Vempala's larger step size; both
remain open, and `hLov` remains a carried hypothesis in the `LovaszSmoothing*` files.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1. Lebesgue scaling -/

/-- **`vol(c·K) = cⁿ·vol(K)`** for `c > 0`, on `EuclideanSpace ℝ (Fin n)`.

`MeasureTheory.Measure.addHaar_smul` states this with `|c ^ finrank ℝ E|`; here the rank is
`n` (`finrank_euclideanSpace_fin`) and `c > 0` removes the absolute value. -/
theorem volume_smul_set {c : ℝ} (hc : 0 < c) (K : Set (EuclideanSpace ℝ (Fin n))) :
    volume (c • K) = ENNReal.ofReal (c ^ n) * volume K := by
  rw [Measure.addHaar_smul volume c K, finrank_euclideanSpace_fin,
    abs_of_pos (by positivity : (0 : ℝ) < c ^ n)]

/-! ## 2. `λ ≥ 1/2`, multiplicative form -/

/-- **`(1/2)·vol(K) ≤ ∫_K ℓ`** — Cousins–Vempala's `lem:lambda-bound` at step `δ ≤ 1/(2n)`,
proved outright.

The hypotheses are those of `ell_eq_one_on_shrunken`: `K` convex, containing the unit ball,
measurable, and `0 < δ ≤ 1/(2n)`.  **No isoperimetry, no smoothing, no Lovász–Vempala
Lemma 6.3.**

Stated multiplicatively so that it carries information at `vol K ∈ {0, ⊤}` as well; the
divided form is `half_le_avgLocalConductance`. -/
theorem half_mul_volume_le_lintegral_ell (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {δ : ℝ}
    (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ))) :
    ENNReal.ofReal (1 / 2) * volume K ≤ ∫⁻ x in K, ell K δ x := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hinv : 0 < 1 / (2 * (n : ℝ)) := by positivity
  have hhalf : 1 / (2 * (n : ℝ)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set c : ℝ := 1 - 1 / (2 * (n : ℝ)) with hcdef
  have hc1 : c < 1 := by rw [hcdef]; linarith
  have hc0 : 0 < c := by rw [hcdef]; linarith
  have hδc : δ ≤ 1 - c := by rw [hcdef]; linarith
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (mem_ball_self one_pos)
  have hsub : c • K ⊆ K := smul_subset_of_convex hKc h0K hc0.le hc1.le
  have hcKm : MeasurableSet (c • K) := measurableSet_smul_set hK (ne_of_gt hc0)
  -- on the shrunken body the integrand is identically `1`
  have hone : (∫⁻ x in c • K, ell K δ x) = volume (c • K) := by
    rw [setLIntegral_congr_fun hcKm
      (fun x hx => ell_eq_one_on_shrunken hKc hball hc0 hc1 hδ hδc hx), setLIntegral_one]
  calc ENNReal.ofReal (1 / 2) * volume K
      ≤ ENNReal.ofReal (c ^ n) * volume K := by
        have hcn : ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal (c ^ n) :=
          ENNReal.ofReal_le_ofReal
            (by rw [hcdef]; exact half_le_one_sub_inv_two_mul_pow hn)
        exact mul_le_mul_right' hcn _
    _ = volume (c • K) := (volume_smul_set hc0 K).symm
    _ = ∫⁻ x in c • K, ell K δ x := hone.symm
    _ ≤ ∫⁻ x in K, ell K δ x := lintegral_mono_set hsub

/-! ## 3. `λ ≥ 1/2`, divided form -/

/-- **`1/2 ≤ avgLocalConductance K δ`** — the form `WastedSteps.lean`'s `hlam` binder takes,
with the two guards `ℝ≥0∞` division needs. -/
theorem half_le_avgLocalConductance (hn : 1 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {δ : ℝ}
    (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ)))
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) :
    ENNReal.ofReal (1 / 2) ≤ avgLocalConductance K δ := by
  rw [avgLocalConductance, ENNReal.le_div_iff_mul_le (Or.inl hK0) (Or.inl hKtop)]
  exact half_mul_volume_le_lintegral_ell hn hK hKc hball hδ hδn

/-! ## 4. The wasted-step bound, with `λ` discharged -/

/-- **`lem:speedy-to-ball`'s wasted-step count, unconditionally in `λ`.**

`WastedSteps.lean` proves `∑ᵢ ∫ ℓ⁻¹ dQᵢ ≤ t·M/λ` under the binder
`hlam : λ ≤ avgLocalConductance K δ`, which is Cousins–Vempala's `lem:lambda-bound` carried as
a hypothesis.  Here that binder is discharged at `λ = 1/2` by §3, giving Cousins–Vempala's
`M·t/λ` at their own constant:

    ∑ᵢ ∫ ℓ⁻¹ dQᵢ  ≤  2·t·M.

The remaining hypothesis is `hwarm`, the warm start — a genuinely separate input, not a
restatement of `λ`. -/
theorem sum_lintegral_inv_ell_iterate_speedyWalk_le_uncond (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {δ : ℝ}
    (hδ : 0 < δ) (hδn : δ ≤ 1 / (2 * (n : ℝ)))
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {M : ℝ≥0∞}
    {Q₀ : Measure (EuclideanSpace ℝ (Fin n))} (hwarm : IsWarm M Q₀ (ellProb K δ)) (t : ℕ) :
    ∑ i ∈ Finset.range t, ∫⁻ x, (ell K δ x)⁻¹ ∂(iterate (speedyWalk K δ) Q₀ i)
      ≤ 2 * ((t : ℝ≥0∞) * M) := by
  have hlam := half_le_avgLocalConductance hn hK hKc hball hδ hδn hK0 hKtop
  have h := sum_lintegral_inv_ell_iterate_speedyWalk_le hK hδ hK0 hKtop hlam
    (by simp) (by simp) hwarm t
  refine h.trans_eq ?_
  rw [show ENNReal.ofReal (1 / 2) = (2 : ℝ≥0∞)⁻¹ by
    rw [show (1 : ℝ) / 2 = ((2 : ℝ≥0∞)⁻¹).toReal by simp]
    exact ENNReal.ofReal_toReal (by simp)]
  rw [ENNReal.div_eq_inv_mul, inv_inv]

/-! ## 5. Non-vacuity -/

/-- **The hypothesis bundle of §3 is satisfiable, and its conclusion is not trivial.**

`K = B(0,1)` in dimension `n = 1` at `δ = 1/2` meets every hypothesis, and the conclusion
`1/2 ≤ λ` is a real constraint because `λ ≤ 1` always (`ell_le_one`): the statement is not of
the form `x ≤ ⊤`. -/
theorem exists_half_le_avgLocalConductance_witness :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 1))) (δ : ℝ),
      MeasurableSet K ∧ Convex ℝ K ∧ ball (0 : EuclideanSpace ℝ (Fin 1)) 1 ⊆ K ∧
      0 < δ ∧ volume K ≠ 0 ∧ volume K ≠ ⊤ ∧
      ENNReal.ofReal (1 / 2) ≤ avgLocalConductance K δ ∧
      avgLocalConductance K δ ≤ 1 := by
  refine ⟨ball (0 : EuclideanSpace ℝ (Fin 1)) 1, 1 / 2, measurableSet_ball, convex_ball _ _,
    subset_rfl, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin 1)) one_pos).ne'
  · exact measure_ball_lt_top.ne
  · refine half_le_avgLocalConductance le_rfl measurableSet_ball (convex_ball _ _) subset_rfl
      (by norm_num) (by norm_num) ?_ ?_
    · exact (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin 1)) one_pos).ne'
    · exact measure_ball_lt_top.ne
  · rw [avgLocalConductance]
    refine ENNReal.div_le_of_le_mul ?_
    calc (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin 1)) 1, ell (ball 0 1) (1 / 2) x)
        ≤ ∫⁻ _ in ball (0 : EuclideanSpace ℝ (Fin 1)) 1, 1 :=
          lintegral_mono fun x => ell_le_one _ _ x
      _ = volume (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) := setLIntegral_one _
      _ ≤ 1 * volume (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) := by rw [one_mul]

section AxiomCheck

#print axioms Arlib.MarkovChains.volume_smul_set
#print axioms Arlib.MarkovChains.half_mul_volume_le_lintegral_ell
#print axioms Arlib.MarkovChains.half_le_avgLocalConductance
#print axioms Arlib.MarkovChains.sum_lintegral_inv_ell_iterate_speedyWalk_le_uncond
#print axioms Arlib.MarkovChains.exists_half_le_avgLocalConductance_witness

end AxiomCheck

end Arlib.MarkovChains
