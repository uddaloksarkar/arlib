/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.GaussianCooling.PhaseSamplerTVTruncated
import Arlib.MarkovChains.Continuous.ColdTruncationRelative

/-!
# The cold truncated phase sampler with a relative tail bound

This is the narrow replacement for
`tvLe_speedyRejection_coolLaw_truncated_of_mixing`.  Its sampler and mixing hypotheses are
unchanged, but the external numeric truncation hypothesis `hCb` is gone.  The discarded
Gaussian mass is bounded directly relative to the normalising integral by
`lintegral_gaussianWeight_sdiff_le_relative`.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n : ℕ}

/-- One cold Gaussian-cooling phase on the truncated body, transported back to the phase law
on `K`, with no circumscribed-radius or normaliser hypothesis.

The truncation price is the explicit dimension-only quantity `(2 * exp (-3/2))^n`. -/
theorem tvLe_speedyRejection_coolLaw_truncated_relative_of_mixing (hn : 21 ≤ n)
    {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j) {σ : ℝ} (hσpos : 0 < σ)
    (hcold : σ * Real.sqrt n ≤ 4) (hrad : 1 ≤ 2 * σ * Real.sqrt n)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : ℕ} (hi : i < m) (hσsq : σsq i = σ ^ 2)
    {mu0 : Measure (EuclSpace n)} [IsProbabilityMeasure mu0] {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (MarkovChains.ellGaussianProb
        (K ∩ closedBall (0 : EuclSpace n) (2 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
    (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    {t : ℕ} (ht : 104857600 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    Arlib.TVLe
      (Arlib.condOn
        ((Measure.map (fun x : EuclSpace n => (1 - 1 / (2 * (n : ℝ)))⁻¹ • x)
            (Arlib.condOn
              (MarkovChains.iterate
                (MarkovChains.lazy (MarkovChains.speedyMetropolisGaussian
                  (K ∩ closedBall (0 : EuclSpace n) (2 * σ * Real.sqrt n))
                  (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σsq i))) mu0 t)
              ((1 - 1 / (2 * (n : ℝ))) •
                (K ∩ closedBall (0 : EuclSpace n) (2 * σ * Real.sqrt n))))).withDensity
          fun v => ENNReal.ofReal
            (MarkovChains.speedyAcceptReal (1 - 1 / (2 * (n : ℝ))) (σsq i) v))
        Set.univ)
      (coolLaw m σsq K i)
      (64 * ENNReal.ofReal eps
        + ENNReal.ofReal ((2 * Real.exp (-(3 : ℝ) / 2)) ^ n)) := by
  have hn1 : 1 ≤ n := by omega
  have hmix := MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_cold_truncated hn hσpos
    hcold hrad hKm hKc hball hM hwarm heps0 (le_trans heps32 (by norm_num)) ht
  rw [Arlib.MarkovChains.mixesWithin_iff, ← hσsq] at hmix
  have hsampler := tvLe_speedyRejection_coolLaw (n := n) hn1 (m := m) hσ
    (MarkovChains.measurableSet_inter_closedBall hKm _)
    (MarkovChains.convex_inter_closedBall hKc _)
    (MarkovChains.unitBall_subset_inter_closedBall hball hrad)
    (MarkovChains.volume_inter_closedBall_ne_top K _)
    (MarkovChains.coldStep_pos hn1 hσpos) MarkovChains.coldStep_le_kls hi hmix
    (ENNReal.ofReal_le_ofReal heps32)
  have htail := MarkovChains.tvLe_coolLaw_inter_closedBall_relative (n := n) hn1 hσ hσpos
    hKm hKc hball hfin hi hσsq hrad
  exact hsampler.trans htail

end Arlib.GaussianCooling

#print axioms Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_truncated_relative_of_mixing
