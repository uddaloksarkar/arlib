/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.SpeedyGaussianUncond
import Arlib.MarkovChains.Continuous.ColdTruncationRelativeFour

/-!
# Speedy Metropolis--Gaussian conductance on the radius-four truncation

The existing cold mixing theorem uses radius `2 * σ * √n`.  At the source truncation radius
`4 * σ * √n`, the same acceptance and overlap constants hold after halving the proposal radius
from `σ/(8√n)` to `σ/(16√n)`.  This file records the resulting conductance seam.  It does not
claim a mixing-time bound: the wasted-step and conductance-to-TV constants must still be
propagated for the smaller proposal radius.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace Arlib.MarkovChains

variable {n : ℕ}

/-- The `3/5` Gaussian acceptance floor remains valid on a body of radius `4σ√n` when
`δ ≤ σ/(16√n)`. -/
theorem acceptance_floor_of_cv_four (hn : 2 ≤ n) {σ δ R : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hδσ : δ ≤ σ / (16 * Real.sqrt n)) (hRσ : R ≤ 4 * σ * Real.sqrt n) :
    1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 8) * (2 / 3) := by
  have ht1 : (1 : ℝ) ≤ Real.sqrt n := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hn1
  have htpos : (0 : ℝ) < Real.sqrt n := lt_of_lt_of_le one_pos ht1
  have h16t : δ * (16 * Real.sqrt n) ≤ σ := (le_div_iff₀ (by positivity)).1 hδσ
  have hδ16 : 16 * δ ≤ σ := by nlinarith
  have hRδ : 2 * R * δ ≤ σ ^ 2 / 2 := by nlinarith
  have hδ2 : δ ^ 2 ≤ σ ^ 2 / 256 := by nlinarith
  refine acceptance_floor_of_le (by positivity) ?_
  nlinarith

end Arlib.MarkovChains

namespace Arlib

open Arlib.MarkovChains

variable {n : ℕ}

/-- The unconditional speedy Metropolis--Gaussian conductance bound on a radius-`4σ√n`
body, using proposal radius at most `σ/(16√n)`. -/
theorem conductance_speedyMetropolisGaussian_ge_uncond_four (hn : 21 ≤ n) {σ δ R : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (hδσ : δ ≤ σ / (16 * Real.sqrt n))
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 4 * σ * Real.sqrt n) :
    ENNReal.ofReal (δ * Real.log 2 / (640 * σ * Real.sqrt n))
      ≤ conductance (speedyMetropolisGaussian K δ (σ ^ 2))
          (ellGaussianProb K δ (σ ^ 2)) := by
  have hn2 : 2 ≤ n := by omega
  have hs : (0 : ℝ) < σ ^ 2 := by positivity
  have hδ8 : δ ≤ σ / (8 * Real.sqrt n) := by
    have hn0 : 0 < n := by omega
    have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 (by positivity)
    calc
      δ ≤ σ / (16 * Real.sqrt n) := hδσ
      _ ≤ σ / (8 * Real.sqrt n) := by
        rw [div_le_div_iff_of_pos_left hσ (by positivity) (by positivity)]
        nlinarith
  have hKcb : K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
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
    (hoverlap_speedyMetropolisGaussian_perPair hn hK hKc hKb hK0 hσ hδ hδ8 hR hKR hRσ
      (acceptance_floor_of_cv_four hn2 hσ hδ hδσ hRσ))
    (hiso_speedyMetropolisGaussian_uncond hn2 hσ hδ hK hKc hKb hK0)

end Arlib

#print axioms Arlib.MarkovChains.acceptance_floor_of_cv_four
#print axioms Arlib.conductance_speedyMetropolisGaussian_ge_uncond_four
