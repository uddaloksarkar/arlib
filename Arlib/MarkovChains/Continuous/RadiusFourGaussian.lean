/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.WastedStepsGaussian
import Arlib.Convexity.SpeedyGaussianUncond
import Arlib.Convexity.SpeedyGaussianMixing
import Arlib.MarkovChains.Continuous.ColdTruncation

/-!
# Gaussian speedy walk in the radius `4σ√n` regime

At `δ ≤ σ/(8√n)` and `R ≤ 4σ√n`, the exponent in the uniform Metropolis acceptance floor is
at most `65/128`.  A cubic Taylor upper bound proves `exp (65/128) ≤ 5/3`, so the acceptance
floor is still at least `3/5`.  This extends both the wasted-step constant and the unconditional
speedy conductance theorem from radius `2σ√n` to the paper's radius `4σ√n`.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## Acceptance at radius four -/

/-- Cubic Taylor upper bound, specialized to the only numerical value needed here. -/
theorem exp_sixtyFive_div_oneTwentyEight_le_five_thirds :
    Real.exp (65 / 128 : ℝ) ≤ 5 / 3 := by
  have habs : |(65 / 128 : ℝ)| ≤ 1 := by norm_num
  have h := Real.exp_bound habs (n := 3) (by norm_num)
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 65 / 128)] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  have hu := (abs_le.mp h).2
  nlinarith

/-- The dimensionless Metropolis exponent is at most `65/128` under `R ≤ 4σ√n`. -/
theorem acceptance_exponent_le_sixtyFive_div_oneTwentyEight (hn : 2 ≤ n)
    {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    (hRσ : R ≤ 4 * σ * Real.sqrt n) :
    (2 * R * δ + δ ^ 2) / (2 * σ ^ 2) ≤ 65 / 128 := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hsqrt_sq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by linarith)
  have hδle : δ * (8 * Real.sqrt n) ≤ σ := by
    rwa [le_div_iff₀ (by positivity)] at hδσ
  have hRδ : R * δ ≤ σ ^ 2 / 2 := by
    calc
      R * δ ≤ (4 * σ * Real.sqrt n) * δ :=
        mul_le_mul_of_nonneg_right hRσ hδ.le
      _ = σ * (δ * (4 * Real.sqrt n)) := by ring
      _ ≤ σ * (σ / 2) := by
        gcongr
        nlinarith [hδle]
      _ = σ ^ 2 / 2 := by ring
  have hδsq : δ ^ 2 ≤ σ ^ 2 / 128 := by
    have hδnonneg : 0 ≤ δ := hδ.le
    have hcap : δ ≤ σ / (8 * Real.sqrt 2) := by
      calc
        δ ≤ σ / (8 * Real.sqrt n) := hδσ
        _ ≤ σ / (8 * Real.sqrt 2) := by
          have hsqrtmono : Real.sqrt 2 ≤ Real.sqrt n := Real.sqrt_le_sqrt (by linarith)
          exact div_le_div_of_nonneg_left hσ.le (by positivity)
            (mul_le_mul_of_nonneg_left hsqrtmono (by norm_num))
    have hsquare : δ ^ 2 ≤ (σ / (8 * Real.sqrt 2)) ^ 2 :=
      (sq_le_sq₀ hδ.le (by positivity)).2 hcap
    have hsqrt2sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    calc
      δ ^ 2 ≤ (σ / (8 * Real.sqrt 2)) ^ 2 := hsquare
      _ = σ ^ 2 / 128 := by rw [div_pow, mul_pow, hsqrt2sq]; ring
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * σ ^ 2)]
  nlinarith

/-- The radius-four regime retains the `3/5` acceptance floor. -/
theorem three_le_five_mul_acceptance_floor_radius_four (hn : 2 ≤ n)
    {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    (hRσ : R ≤ 4 * σ * Real.sqrt n) :
    (3 : ℝ≥0∞) ≤
      5 * ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))) := by
  let q : ℝ := (2 * R * δ + δ ^ 2) / (2 * σ ^ 2)
  have hq : q ≤ 65 / 128 :=
    acceptance_exponent_le_sixtyFive_div_oneTwentyEight hn hσ hδ hδσ hRσ
  have hexp : Real.exp q ≤ 5 / 3 :=
    (Real.exp_le_exp.mpr hq).trans exp_sixtyFive_div_oneTwentyEight_le_five_thirds
  have hprod : Real.exp (-q) * Real.exp q = 1 := by
    rw [← Real.exp_add]
    simp
  have hmul := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-q)).le
  have hreal : (3 : ℝ) ≤ 5 * Real.exp (-q) := by nlinarith
  calc
    (3 : ℝ≥0∞) = ENNReal.ofReal 3 := by simp
    _ ≤ ENNReal.ofReal (5 * Real.exp (-q)) := ENNReal.ofReal_le_ofReal hreal
    _ = 5 * ENNReal.ofReal (Real.exp (-q)) := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ = 5 * ENNReal.ofReal
        (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2))) := by
      congr 3
      dsimp [q]
      ring

/-- Real-valued form required by the overlap/conductance layer. -/
theorem acceptance_floor_radius_four (hn : 2 ≤ n)
    {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    (hRσ : R ≤ 4 * σ * Real.sqrt n) :
    1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 8) * (2 / 3) := by
  let q : ℝ := (2 * R * δ + δ ^ 2) / (2 * σ ^ 2)
  have hq : q ≤ 65 / 128 :=
    acceptance_exponent_le_sixtyFive_div_oneTwentyEight hn hσ hδ hδσ hRσ
  have hexp : Real.exp q ≤ 5 / 3 :=
    (Real.exp_le_exp.mpr hq).trans exp_sixtyFive_div_oneTwentyEight_le_five_thirds
  have hprod : Real.exp (-q) * Real.exp q = 1 := by rw [← Real.exp_add]; simp
  have hmul := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-q)).le
  have hreal : (3 : ℝ) ≤ 5 * Real.exp (-q) := by nlinarith
  dsimp [q] at hreal
  have hneg : -(2 * R * δ + δ ^ 2) / (2 * σ ^ 2) =
      -((2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) := by ring
  rw [hneg]
  nlinarith

/-! ## Wasted steps at radius four -/

/-- The fully discharged wasted-step bound remains `10/3` at radius `4σ√n`. -/
theorem three_mul_sum_lintegral_le_ten_mul_radius_four (hn : 2 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {δ σ R : ℝ}
    (hδ : 0 < δ) (hσ : 0 < σ) (hδn : δ ≤ 1 / (2 * (n : ℝ)))
    (hδσ : δ ≤ σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    (hRσ : R ≤ 4 * σ * Real.sqrt n) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {M : ℝ≥0∞} {Q₀ : Measure (EuclideanSpace ℝ (Fin n))}
    (hwarm : IsWarm M Q₀ (ellGaussianProb K δ (σ ^ 2))) (t : ℕ) :
    3 * ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
          ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i)
      ≤ 10 * ((t : ℝ≥0∞) * M) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have huncond := mul_sum_lintegral_inv_ell_mul_move_iterate_speedyMetropolisGaussian_le_uncond
    (le_trans (by norm_num) hn) hK hKc hball hδ hδn hs hR hKR hwarm t
  have hfloor := three_le_five_mul_acceptance_floor_radius_four hn hσ hδ hδσ hRσ
  calc
    3 * ∑ i ∈ Finset.range t,
        ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
          ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i)
      ≤ 5 * ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)))
          * ∑ i ∈ Finset.range t,
              ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
                ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i) := by gcongr
    _ = 5 * (ENNReal.ofReal (Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)))
          * ∑ i ∈ Finset.range t,
              ∫⁻ x, (ell K δ x * speedyMetropolisMove K δ (σ ^ 2) x)⁻¹
                ∂(iterate (speedyMetropolisGaussian K δ (σ ^ 2)) Q₀ i)) := by ring
    _ ≤ 5 * (2 * ((t : ℝ≥0∞) * M)) := by gcongr
    _ = 10 * ((t : ℝ≥0∞) * M) := by ring

/-! ## Conductance and mixing at radius four -/

/-- The unconditional speedy conductance theorem with the paper's radius `4σ√n`. -/
theorem conductance_speedyMetropolisGaussian_ge_uncond_radius_four (hn : 21 ≤ n)
    {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 4 * σ * Real.sqrt n) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ≤
      conductance (speedyMetropolisGaussian K δ (σ ^ 2))
        (ellGaussianProb K δ (σ ^ 2)) := by
  have hn2 : 2 ≤ n := by omega
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hKcb : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hKR x hx
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hKcb
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKcb) measure_closedBall_lt_top)
  exact conductance_speedyGaussian_ge hn2 hσ hδ hδσ
    (fun x => Set.indicator_nonneg
      (fun y _ => mul_nonneg ENNReal.toReal_nonneg (gaussianWeightReal_pos _ y).le) x)
    (integral_ellGaussianIndicator_pos hs hK hKc hKb hK0 hKtop hδ)
    hK (speedyMetropolisGaussian K δ (σ ^ 2)) (ellGaussianProb K δ (σ ^ 2))
    (hpi_ellGaussian hs hK hKtop δ)
    (isReversible_speedyMetropolisGaussian_prob hK δ (σ ^ 2))
    (ellGaussianProb_compl_eq_zero hK δ (σ ^ 2))
    (hoverlap_speedyMetropolisGaussian_perPair hn hK hKc hKb hK0 hσ hδ hδσ hR hKR hRσ
      (acceptance_floor_radius_four hn2 hσ hδ hδσ hRσ))
    (Arlib.hiso_speedyMetropolisGaussian_uncond hn2 hσ hδ hK hKc hKb hK0)

/-- Lazy speedy mixing with the unchanged conductance constant at radius `4σ√n`. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_uncond_radius_four (hn : 21 ≤ n)
    {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 4 * σ * Real.sqrt n)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0]
    {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellGaussianProb K δ (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * ((Real.log M + 2 * Real.log (1 / eps)) /
      (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2) + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy (speedyMetropolisGaussian K δ (σ ^ 2)))
      (ellGaussianProb K δ (σ ^ 2)) mu0 t (ENNReal.ofReal eps) := by
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hKcb : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x hx
    simpa [Metric.mem_closedBall, dist_eq_norm] using hKR x hx
  have hKb : Bornology.IsBounded K := Metric.isBounded_closedBall.subset hKcb
  have hKtop : volume K ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (measure_mono hKcb) measure_closedBall_lt_top)
  haveI : IsProbabilityMeasure (ellGaussianProb K δ (σ ^ 2)) :=
    isProbabilityMeasure_ellGaussianProb
      (ellGaussianMeasure_univ_ne_zero hK hKc hKb hK0 hδ (σ ^ 2))
      (ne_top_of_le_ne_top hKtop (ellGaussianMeasure_univ_le hs K δ))
  obtain ⟨S0, hS0m, hS0pos, hS0half⟩ :=
    exists_smallSet_of_absolutelyContinuous (n := n) (by omega)
      (ellGaussianProb K δ (σ ^ 2))
      (ellGaussianProb_absolutelyContinuous K δ (σ ^ 2))
  exact mixesWithin_lazy_of_conductance_sqrt (by omega) hσ hδ hδσ
    (isReversible_speedyMetropolisGaussian_prob hK δ (σ ^ 2))
    ⟨S0, hS0m, hS0pos, hS0half⟩ hM hwarm heps0 heps1
    (conductance_speedyMetropolisGaussian_ge_uncond_radius_four hn hσ hδ hδσ
      hK hKc hK0 hR hKR hRσ) ht

/-- Explicit algebraic form of the radius-four deadline. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit_radius_four
    (hn : 21 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (8 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 4 * σ * Real.sqrt n)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0]
    {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellGaussianProb K δ (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) *
      (Real.log M + 2 * Real.log (1 / eps)) / (δ * Real.log 2) ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy (speedyMetropolisGaussian K δ (σ ^ 2)))
      (ellGaussianProb K δ (σ ^ 2)) mu0 t (ENNReal.ofReal eps) := by
  refine mixesWithin_lazy_speedyMetropolisGaussian_uncond_radius_four hn hσ hδ hδσ
    hK hKc hK0 hR hKR hRσ hM hwarm heps0 heps1 ?_
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
  have heq : 4 * ((Real.log M + 2 * Real.log (1 / eps)) /
        (δ * Real.log 2 / (640 * σ * Real.sqrt n)) ^ 2)
      = 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * (Real.log M + 2 * Real.log (1 / eps)) /
        (δ * Real.log 2) ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, hsq, div_div_eq_mul_div]
    field_simp
  rw [heq]
  exact ht

/-- Radius-four truncation: no radius binder on the original body. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_radius_four_truncated
    (hn : 21 ≤ n) {σ : ℝ} (hσ : 0 < σ)
    (hcold : σ * Real.sqrt n ≤ 4)
    (hrad : 1 ≤ 4 * σ * Real.sqrt n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0]
    {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (ellGaussianProb
        (K ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 104857600 * (n : ℝ) ^ 2 *
      (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin
      (lazy (speedyMetropolisGaussian
        (K ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
      (ellGaussianProb
        (K ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2))
      mu0 t (ENNReal.ofReal eps) := by
  let K' := K ∩ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * σ * Real.sqrt n)
  let δ := min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))
  have hδ : 0 < δ := coldStep_pos (by omega) hσ
  have hδσ : δ ≤ σ / (8 * Real.sqrt n) := min_le_left _ _
  have hK'm : MeasurableSet K' := measurableSet_inter_closedBall hK _
  have hK'c : Convex ℝ K' := convex_inter_closedBall hKc _
  have hK'0 : volume K' ≠ 0 := volume_inter_closedBall_ne_zero hball hrad
  have hKR : ∀ x ∈ K', ‖x‖ ≤ 4 * σ * Real.sqrt n :=
    fun _ hx => norm_le_of_mem_inter_closedBall hx
  refine mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit_radius_four hn hσ hδ hδσ
    hK'm hK'c hK'0 (by positivity) hKR le_rfl hM hwarm heps0 heps1 ?_
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hmin : min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) =
      σ / (8 * Real.sqrt n) := coldStep_eq_cold (by omega) hcold
  dsimp [δ]
  rw [hmin]
  have heq : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * (Real.log M + 2 * Real.log (1 / eps)) /
        (σ / (8 * Real.sqrt n) * Real.log 2) ^ 2
      = 104857600 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps)) /
        Real.log 2 ^ 2 := by
    rw [mul_pow, div_pow, mul_pow, hsq]
    field_simp
    ring
  rw [heq]
  exact ht

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.three_le_five_mul_acceptance_floor_radius_four
#print axioms Arlib.MarkovChains.acceptance_floor_radius_four
#print axioms Arlib.MarkovChains.three_mul_sum_lintegral_le_ten_mul_radius_four
#print axioms Arlib.MarkovChains.conductance_speedyMetropolisGaussian_ge_uncond_radius_four
#print axioms Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit_radius_four
#print axioms Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_radius_four_truncated
