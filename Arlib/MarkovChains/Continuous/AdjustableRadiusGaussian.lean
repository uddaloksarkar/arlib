/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.RadiusFourGaussian
import Arlib.MarkovChains.Continuous.ColdTruncationRelativeAdjustable

/-!
# Speedy Gaussian conductance at an adjustable truncation radius

At body radius `q*σ*√n`, choose

`δ ≤ σ / (max 8 (2*q) * √n)`.

The `8` retains the small quadratic `δ²` term and the `2*q` controls `R*δ`.  Thus the same
`3/5` Metropolis acceptance floor and the same conductance expression in terms of `δ` hold.
The proof shows that the radius-four premise in `OverlapPerPair` was only used in the
Gaussian-density bracket, not in its cap/lens geometry.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : Nat}

/-- The adjustable step restriction implies the standard `σ/(8√n)` restriction. -/
theorem step_le_eight_of_le_adjustable {q σ δ : Real} (hσ : 0 < σ)
    (hδq : δ <= σ / (max 8 (2 * q) * Real.sqrt n)) :
    δ <= σ / (8 * Real.sqrt n) := by
  have hmax : (8 : Real) <= max 8 (2 * q) := le_max_left _ _
  by_cases hn0 : n = 0
  · simpa [hn0] using hδq
  · have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
    exact hδq.trans (div_le_div_of_nonneg_left hσ.le (by positivity)
      (mul_le_mul_of_nonneg_right hmax hsqrt.le))

/-- The adjustable step restriction also controls the radius-dependent cross term. -/
theorem step_le_two_mul_q_of_le_adjustable {q σ δ : Real} (hq : 1 < q) (hσ : 0 < σ)
    (hδq : δ <= σ / (max 8 (2 * q) * Real.sqrt n)) :
    δ <= σ / ((2 * q) * Real.sqrt n) := by
  have hmax : 2 * q <= max 8 (2 * q) := le_max_right _ _
  by_cases hn0 : n = 0
  · simpa [hn0] using hδq
  · have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
    exact hδq.trans (div_le_div_of_nonneg_left hσ.le (by positivity)
      (mul_le_mul_of_nonneg_right hmax hsqrt.le))

/-- `R ≤ qσ√n` and the adjustable step imply `2Rδ ≤ σ²`. -/
theorem two_mul_radius_mul_step_le_sq_adjustable {q σ δ R : Real}
    (hq : 1 < q) (hσ : 0 < σ) (hδ : 0 <= δ)
    (hδq : δ <= σ / (max 8 (2 * q) * Real.sqrt n))
    (hRσ : R <= q * σ * Real.sqrt n) :
    2 * R * δ <= σ ^ 2 := by
  by_cases hn0 : n = 0
  · simp [hn0] at hδq hRσ
    have : δ = 0 := le_antisymm hδq hδ
    subst δ
    simp [sq_nonneg]
  · have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
    have hstep := step_le_two_mul_q_of_le_adjustable (n := n) hq hσ hδq
    have hmul : δ * ((2 * q) * Real.sqrt n) <= σ :=
      (le_div_iff₀ (by positivity)).1 hstep
    calc
      2 * R * δ <= 2 * (q * σ * Real.sqrt n) * δ := by gcongr
      _ = σ * (δ * ((2 * q) * Real.sqrt n)) := by ring
      _ <= σ * σ := by gcongr
      _ = σ ^ 2 := by ring

/-- Gaussian density bracket with radius represented by the invariant `2Rδ ≤ σ²`. -/
theorem gaussianWeightReal_le_of_radius_step
    (hn : 21 <= n) {σ δ R : Real} (hσ : 0 < σ) (_hδ : 0 < δ)
    (hcross : 2 * R * δ <= σ ^ 2)
    {u v : EuclideanSpace Real (Fin n)} (hu : ‖u‖ <= R) (hv : ‖v‖ <= R)
    (huv : ‖u - v‖ <= δ / Real.sqrt n) :
    gaussianWeightReal (σ ^ 2) u <= 9 / 8 * gaussianWeightReal (σ ^ 2) v := by
  have hσ0 : σ ≠ 0 := hσ.ne'
  have hnR : (21 : Real) <= (n : Real) := by exact_mod_cast hn
  have hS : (4.5 : Real) <= Real.sqrt n := by
    nlinarith [Real.sq_sqrt (show (0 : Real) <= (n : Real) by linarith),
      Real.sqrt_nonneg (n : Real)]
  have hSpos : (0 : Real) < Real.sqrt n := by linarith
  have hR0 : (0 : Real) <= R := le_trans (norm_nonneg u) hu
  have hnorm : ‖v‖ - ‖u‖ <= ‖u - v‖ := by
    rw [norm_sub_rev u v]
    exact norm_sub_norm_le v u
  have he0 : (0 : Real) <= ‖u - v‖ := norm_nonneg _
  have hsep : ‖u - v‖ * Real.sqrt n <= δ := by
    have : ‖u - v‖ * Real.sqrt n <= δ / Real.sqrt n * Real.sqrt n := by
      nlinarith
    rwa [div_mul_cancel₀ δ hSpos.ne'] at this
  have hstep1 : ‖v‖ ^ 2 - ‖u‖ ^ 2 <= ‖u - v‖ * (2 * R) := by
    nlinarith [mul_nonneg he0 (by linarith [norm_nonneg u, norm_nonneg v] :
        (0 : Real) <= 2 * R - (‖v‖ + ‖u‖)),
      mul_nonneg (by linarith : (0 : Real) <= ‖u - v‖ - (‖v‖ - ‖u‖))
        (by positivity : (0 : Real) <= ‖v‖ + ‖u‖)]
  have hstep2 : ‖u - v‖ * (2 * R) * Real.sqrt n <= 2 * R * δ := by
    nlinarith [mul_le_mul_of_nonneg_right hsep (by positivity : (0 : Real) <= 2 * R)]
  have hstep3 : ‖u - v‖ * (2 * R) <= σ ^ 2 / Real.sqrt n := by
    rw [le_div_iff₀ hSpos]
    exact hstep2.trans hcross
  have hstep4 : σ ^ 2 / Real.sqrt n <= 2 * σ ^ 2 / 9 := by
    rw [div_le_iff₀ hSpos]
    nlinarith [sq_nonneg σ]
  have hkey : ‖v‖ ^ 2 - ‖u‖ ^ 2 <= 2 * σ ^ 2 / 9 :=
    hstep1.trans (hstep3.trans hstep4)
  have hexp19 : Real.exp (1 / 9 : Real) <= 9 / 8 := by
    have h9 : (8 : Real) / 9 <= Real.exp (-(1 / 9) : Real) := by
      have := Real.add_one_le_exp (-(1 / 9) : Real)
      linarith
    have hm := mul_le_mul_of_nonneg_left h9 (Real.exp_pos (1 / 9 : Real)).le
    rw [← Real.exp_add] at hm
    norm_num at hm ⊢
    nlinarith
  unfold gaussianWeightReal
  have hexp : -‖u‖ ^ 2 / (2 * σ ^ 2) <= 1 / 9 + -‖v‖ ^ 2 / (2 * σ ^ 2) := by
    field_simp [hσ0]
    nlinarith
  calc
    Real.exp (-‖u‖ ^ 2 / (2 * σ ^ 2)) <=
        Real.exp (1 / 9 + -‖v‖ ^ 2 / (2 * σ ^ 2)) := Real.exp_le_exp.2 hexp
    _ = Real.exp (1 / 9) * Real.exp (-‖v‖ ^ 2 / (2 * σ ^ 2)) := Real.exp_add _ _
    _ <= 9 / 8 * Real.exp (-‖v‖ ^ 2 / (2 * σ ^ 2)) := by gcongr

/-- The adjustable radius/step regime retains the radius-four `3/5` acceptance floor. -/
theorem three_le_five_mul_acceptance_floor_adjustable
    (hn : 2 <= n) {q σ δ R : Real} (hq : 1 < q) (hσ : 0 < σ) (hδ : 0 < δ)
    (hδq : δ <= σ / (max 8 (2 * q) * Real.sqrt n))
    (hRσ : R <= q * σ * Real.sqrt n) :
    (3 : ENNReal) <=
      5 * ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))) := by
  have hδ8 := step_le_eight_of_le_adjustable (n := n) hσ hδq
  have hcross := two_mul_radius_mul_step_le_sq_adjustable (n := n) hq hσ hδ.le hδq hRσ
  have hnreal : (2 : Real) <= n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
  have hsqrt_sq : Real.sqrt (n : Real) ^ 2 = n := Real.sq_sqrt (by positivity)
  have hδsq : δ ^ 2 <= σ ^ 2 / 128 := by
    have hcap : δ <= σ / (8 * Real.sqrt 2) := by
      calc
        δ <= σ / (8 * Real.sqrt n) := hδ8
        _ <= σ / (8 * Real.sqrt 2) := by
          have hsqrtmono : Real.sqrt 2 <= Real.sqrt n := Real.sqrt_le_sqrt hnreal
          exact div_le_div_of_nonneg_left hσ.le (by positivity)
            (mul_le_mul_of_nonneg_left hsqrtmono (by norm_num))
    have hsquare : δ ^ 2 <= (σ / (8 * Real.sqrt 2)) ^ 2 :=
      (sq_le_sq₀ hδ.le (by positivity)).2 hcap
    have hsqrt2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc
      δ ^ 2 <= (σ / (8 * Real.sqrt 2)) ^ 2 := hsquare
      _ = σ ^ 2 / 128 := by rw [div_pow, mul_pow, hsqrt2sq]; ring
  have hexponent : (2 * R * δ + δ ^ 2) / (2 * σ ^ 2) <= 65 / 128 := by
    rw [div_le_iff₀ (by positivity : (0 : Real) < 2 * σ ^ 2)]
    nlinarith
  let z : Real := (2 * R * δ + δ ^ 2) / (2 * σ ^ 2)
  have hexp : Real.exp z <= 5 / 3 :=
    (Real.exp_le_exp.mpr hexponent).trans exp_sixtyFive_div_oneTwentyEight_le_five_thirds
  have hprod : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
  have hmul := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-z)).le
  have hreal : (3 : Real) <= 5 * Real.exp (-z) := by nlinarith
  calc
    (3 : ENNReal) = ENNReal.ofReal 3 := by simp
    _ <= ENNReal.ofReal (5 * Real.exp (-z)) := ENNReal.ofReal_le_ofReal hreal
    _ = 5 * ENNReal.ofReal (Real.exp (-z)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ = 5 * ENNReal.ofReal
        (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))) := by
      congr 3
      dsimp [z]
      ring

/-- Per-pair speedy Metropolis overlap in the adjustable-radius regime. -/
theorem hoverlap_speedyMetropolisGaussian_adjustable
    (hn : 21 <= n) {q : Real} (hq : 1 < q)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hKb : Bornology.IsBounded K) (hK0 : volume K ≠ 0)
    {σ δ R : Real} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδq : δ <= σ / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 <= R) (hKR : ∀ x ∈ K, ‖x‖ <= R) (hRσ : R <= q * σ * Real.sqrt n) :
    ∀ T : Set (EuclideanSpace Real (Fin n)), MeasurableSet T ->
      ∀ u v : EuclideanSpace Real (Fin n), u ∈ T -> u ∈ K -> v ∈ K -> v ∉ T ->
      ‖u - v‖ < δ / Real.sqrt n ->
      densDist (Set.indicator K
        (fun x => (ell K δ x).toReal * gaussianWeightReal (σ ^ 2) x)) u v < 1 / 4 ->
      1 <= 20 * (speedyMetropolisGaussian K δ (σ ^ 2) u Tᶜ +
        speedyMetropolisGaussian K δ (σ ^ 2) v T) := by
  have hδ8 := step_le_eight_of_le_adjustable (n := n) hσ hδq
  have hcross := two_mul_radius_mul_step_le_sq_adjustable (n := n) hq hσ hδ.le hδq hRσ
  have hfloorENN := three_le_five_mul_acceptance_floor_adjustable
    (show 2 <= n by omega) hq hσ hδ hδq hRσ
  have hfloor : 1 <= 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) *
      (1 / 8) * (2 / 3) := by
    have hthree : (3 : Real) <=
        5 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) := by
      have h := ENNReal.toReal_mono (by finiteness) hfloorENN
      norm_num [ENNReal.toReal_ofReal, (Real.exp_pos _).le] at h
      convert h using 1 <;> ring
    nlinarith
  intro T hT u v _ huK hvK _ hsep hd
  rw [densDist_indicator_of_mem huK hvK] at hd
  have hell : ell K δ u <= ENNReal.ofReal (3 / 2) * ell K δ v ∧
      ell K δ v <= ENNReal.ofReal (3 / 2) * ell K δ u := by
    have hu0 := ell_ne_zero_of_volume_ball_inter_ne_zero hδ
      (volume_ball_inter_ne_zero_of_convex hKc hKb hK0 huK hδ)
    have hv0 := ell_ne_zero_of_volume_ball_inter_ne_zero hδ
      (volume_ball_inter_ne_zero_of_convex hKc hKb hK0 hvK hδ)
    have hutop : ell K δ u ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ u)
    have hvtop : ell K δ v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ v)
    have hA : 0 < (ell K δ u).toReal := ENNReal.toReal_pos hu0 hutop
    have hB : 0 < (ell K δ v).toReal := ENNReal.toReal_pos hv0 hvtop
    have hsep' : ‖v - u‖ <= δ / Real.sqrt n := by
      simpa [norm_sub_rev] using hsep.le
    obtain ⟨h1, h2⟩ := le_three_halves_of_densDist_mul_lt hA hB
      (gaussianWeightReal_pos (σ ^ 2) u) (gaussianWeightReal_pos (σ ^ 2) v)
      (gaussianWeightReal_le_of_radius_step hn hσ hδ hcross (hKR u huK) (hKR v hvK)
        hsep.le)
      (gaussianWeightReal_le_of_radius_step hn hσ hδ hcross (hKR v hvK) (hKR u huK)
        hsep')
      (by simpa only [densDist] using hd)
    exact ⟨ell_le_of_toReal_le h1, ell_le_of_toReal_le h2⟩
  exact one_le_twenty_mul_speedyMetropolisGaussian_add_of_comparable (by omega : 2 <= n)
    hK hKc hδ (by positivity : (0 : Real) < σ ^ 2) hR huK hvK (hKR u huK) (hKR v hvK)
    hsep.le (volume_ball_inter_ne_zero_of_convex hKc hKb hK0 huK hδ)
    (max_volume_ball_inter_le_of_ell_comparable hδ hell.1 hell.2) hfloor hT

end Arlib.MarkovChains

namespace Arlib

open Arlib.MarkovChains
open MeasureTheory
open scoped ENNReal

variable {n : Nat}

/-- Unconditional speedy Metropolis--Gaussian conductance at adjustable radius. -/
theorem conductance_speedyMetropolisGaussian_ge_uncond_adjustable
    (hn : 21 <= n) {q : Real} (hq : 1 < q) {σ δ R : Real}
    (hσ : 0 < σ) (hδ : 0 < δ)
    (hδq : δ <= σ / (max 8 (2 * q) * Real.sqrt n))
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hK0 : volume K ≠ 0) (hR : 0 <= R) (hKR : ∀ x ∈ K, ‖x‖ <= R)
    (hRσ : R <= q * σ * Real.sqrt n) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n)) <=
      conductance (speedyMetropolisGaussian K δ (σ ^ 2))
        (ellGaussianProb K δ (σ ^ 2)) := by
  have hn2 : 2 <= n := by omega
  have hs : (0 : Real) < σ ^ 2 := by positivity
  have hδ8 := step_le_eight_of_le_adjustable (n := n) hσ hδq
  have hKcb : K ⊆ Metric.closedBall (0 : EuclideanSpace Real (Fin n)) R := by
    intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hKR x hx
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hKcb
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKcb) measure_closedBall_lt_top)
  exact conductance_speedyGaussian_ge hn2 hσ hδ hδ8
    (fun x => Set.indicator_nonneg
      (fun y _ => mul_nonneg ENNReal.toReal_nonneg (gaussianWeightReal_pos _ y).le) x)
    (integral_ellGaussianIndicator_pos hs hK hKc hKb hK0 hKtop hδ)
    hK (speedyMetropolisGaussian K δ (σ ^ 2)) (ellGaussianProb K δ (σ ^ 2))
    (hpi_ellGaussian hs hK hKtop δ)
    (isReversible_speedyMetropolisGaussian_prob hK δ (σ ^ 2))
    (ellGaussianProb_compl_eq_zero hK δ (σ ^ 2))
    (hoverlap_speedyMetropolisGaussian_adjustable hn hq hK hKc hKb hK0 hσ hδ hδq
      hR hKR hRσ)
    (hiso_speedyMetropolisGaussian_uncond hn2 hσ hδ hK hKc hKb hK0)

/-- Direct consumer for the adjustable truncated body `K ∩ B(0,qσ√n)`. -/
theorem conductance_speedyMetropolisGaussian_ge_uncond_adjustable_truncated
    (hn : 21 <= n) {q : Real} (hq : 1 < q) {σ δ : Real}
    (hσ : 0 < σ) (hδ : 0 < δ)
    (hδq : δ <= σ / (max 8 (2 * q) * Real.sqrt n))
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : Metric.ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K)
    (hrad : 1 <= q * σ * Real.sqrt n) :
    let K' := K ∩ Metric.closedBall (0 : EuclideanSpace Real (Fin n))
      (q * σ * Real.sqrt n)
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n)) <=
      conductance (speedyMetropolisGaussian K' δ (σ ^ 2))
        (ellGaussianProb K' δ (σ ^ 2)) := by
  dsimp only
  let r : Real := q * σ * Real.sqrt n
  let K' := K ∩ Metric.closedBall (0 : EuclideanSpace Real (Fin n)) r
  have hK'm : MeasurableSet K' := measurableSet_inter_closedBall hK r
  have hK'c : Convex Real K' := convex_inter_closedBall hKc r
  have hK'0 : volume K' ≠ 0 := volume_inter_closedBall_ne_zero hball hrad
  have hr0 : 0 <= r := by dsimp [r]; positivity
  have hKr : ∀ x ∈ K', ‖x‖ <= r := fun _ hx => norm_le_of_mem_inter_closedBall hx
  have hc := conductance_speedyMetropolisGaussian_ge_uncond_adjustable hn hq hσ hδ hδq
    hK'm hK'c hK'0 hr0 hKr (show r <= q * σ * Real.sqrt n by rfl)
  simpa only [K', r] using hc

end Arlib

#print axioms Arlib.MarkovChains.gaussianWeightReal_le_of_radius_step
#print axioms Arlib.MarkovChains.three_le_five_mul_acceptance_floor_adjustable
#print axioms Arlib.MarkovChains.hoverlap_speedyMetropolisGaussian_adjustable
#print axioms Arlib.conductance_speedyMetropolisGaussian_ge_uncond_adjustable
#print axioms Arlib.conductance_speedyMetropolisGaussian_ge_uncond_adjustable_truncated
