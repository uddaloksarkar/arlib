/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.AdaptiveRestartWarm
import Arlib.Convexity.GaussianCooling.PhaseSamplerTV
import Arlib.MarkovChains.Continuous.RadiusFourGaussian
import Arlib.MarkovChains.Continuous.ColdTruncationRelativeFour

/-!
# Adaptive cold restarts with radius-four truncation

This combines the radius-`4σ√n` speedy mixing theorem, the corresponding relative Gaussian
tail, the cold-ball independent restart, and the existing speedy rejection transport.
-/

namespace Arlib.GaussianCooling.Chunked

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n m : ℕ}

/-! ## Generic radius-four phase sampler -/

/-- One cold phase on `K ∩ closedBall 0 (4σ√n)`, transported to the full phase law. -/
theorem tvLe_speedyRejection_coolLaw_truncated_relative_four_of_mixing
    (hn : 21 ≤ n) {σsq : ℕ → ℝ} (hσsqpos : ∀ j, 0 < σsq j)
    {σ : ℝ} (hσ : 0 < σ) (hcold : σ * Real.sqrt n ≤ 4)
    (hrad : 1 ≤ 4 * σ * Real.sqrt n)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : ℕ} (hi : i < m) (hphase : σsq i = σ ^ 2)
    {mu0 : Measure (EuclSpace n)} [IsProbabilityMeasure mu0]
    {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (Arlib.MarkovChains.ellGaussianProb
        (K ∩ closedBall (0 : EuclSpace n) (4 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
    (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    {t : ℕ} (ht : 104857600 * (n : ℝ) ^ 2 *
      (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    Arlib.TVLe
      (Arlib.condOn
        ((Measure.map (fun x : EuclSpace n => (1 - 1 / (2 * (n : ℝ)))⁻¹ • x)
            (Arlib.condOn
              (Arlib.MarkovChains.iterate
                (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyMetropolisGaussian
                  (K ∩ closedBall (0 : EuclSpace n) (4 * σ * Real.sqrt n))
                  (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σsq i))) mu0 t)
              ((1 - 1 / (2 * (n : ℝ))) •
                (K ∩ closedBall (0 : EuclSpace n) (4 * σ * Real.sqrt n))))).withDensity
          fun v => ENNReal.ofReal
            (Arlib.MarkovChains.speedyAcceptReal
              (1 - 1 / (2 * (n : ℝ))) (σsq i) v))
        Set.univ)
      (coolLaw m σsq K i)
      (64 * ENNReal.ofReal eps +
        ENNReal.ofReal ((4 * Real.exp (-(15 : ℝ) / 2)) ^ n)) := by
  have hn1 : 1 ≤ n := by omega
  have hmix :=
    Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_radius_four_truncated
      hn hσ hcold hrad hKm hKc hball hM hwarm heps0
      (le_trans heps32 (by norm_num)) ht
  rw [Arlib.MarkovChains.mixesWithin_iff, ← hphase] at hmix
  have hsampler := tvLe_speedyRejection_coolLaw (n := n) hn1 (m := m) hσsqpos
    (Arlib.MarkovChains.measurableSet_inter_closedBall hKm _)
    (Arlib.MarkovChains.convex_inter_closedBall hKc _)
    (Arlib.MarkovChains.unitBall_subset_inter_closedBall hball hrad)
    (Arlib.MarkovChains.volume_inter_closedBall_ne_top K _)
    (Arlib.MarkovChains.coldStep_pos hn1 hσ)
    Arlib.MarkovChains.coldStep_le_kls hi hmix
    (ENNReal.ofReal_le_ofReal heps32)
  have htail := Arlib.MarkovChains.tvLe_coolLaw_inter_closedBall_relative_four
    hn1 hσsqpos hσ hKm hKc hball hfin hi hphase hrad
  exact hsampler.trans htail

/-! ## Adaptive cold-ball warm start on the radius-four body -/

/-- Direct truncated-body warmness for the adaptive independent restart. -/
theorem isWarm_coldBallStart_adaptive_ellGaussianProb_truncated_four
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hn : 21 ≤ n) (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    {N s₀ rho σ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (hσ : 0 < σ) (hrad : 1 ≤ 4 * σ * Real.sqrt n)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : ℝ)))
    (hcoldStart : 4 * (n : ℝ) * s₀ ≤ rho ^ 2)
    (hbelow : ∀ j, j + 1 < m →
      adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ j) ≤ N)
    {i : ℕ} (hi : i < m) :
    Arlib.IsWarm (ENNReal.ofReal (adaptiveRestartWarmConst n i))
      (coldBallStart (n := n) s₀ rho)
      (Arlib.MarkovChains.ellGaussianProb
        (K ∩ closedBall (0 : EuclSpace n) (4 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))))
        (adaptiveSigmaSq N s₀ i)) := by
  have hn1 : 1 ≤ n := by omega
  let K' : Set (EuclSpace n) :=
    K ∩ closedBall (0 : EuclSpace n) (4 * σ * Real.sqrt n)
  have hK'm : MeasurableSet K' :=
    Arlib.MarkovChains.measurableSet_inter_closedBall hKm _
  have hK'c : Convex ℝ K' :=
    Arlib.MarkovChains.convex_inter_closedBall hKc _
  have hK'ball : ball (0 : EuclSpace n) 1 ⊆ K' :=
    Arlib.MarkovChains.unitBall_subset_inter_closedBall hball hrad
  have hK'fin : volume K' ≠ ⊤ :=
    Arlib.MarkovChains.volume_inter_closedBall_ne_top K _
  have hc0 : 0 < 1 - 1 / (2 * (n : ℝ)) := by
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hden : (1 : ℝ) < 2 * (n : ℝ) := by nlinarith
    have hinv : 1 / (2 * (n : ℝ)) < 1 := (div_lt_one (by positivity)).2 hden
    linarith
  have hc1 : 1 - 1 / (2 * (n : ℝ)) < 1 := by
    have hnreal : (0 : ℝ) < n := by positivity
    have hinv : 0 < 1 / (2 * (n : ℝ)) := by positivity
    linarith
  have hδ : 0 < min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) :=
    Arlib.MarkovChains.coldStep_pos hn1 hσ
  have hδc : min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))) ≤
      1 - (1 - 1 / (2 * (n : ℝ))) := by
    simpa only [sub_sub_cancel] using
      (Arlib.MarkovChains.coldStep_le_kls (n := n) (σ := σ))
  exact isWarm_coldBallStart_adaptive_ellGaussianProb hK'm hK'c hn1 hK'ball hK'fin
    hN hs₀ hc0 hc1 hrho hrhoc hcoldStart hδ hδc hbelow hi

/-! ## End-to-end radius-four phase adapter -/

/-- One adaptive cold phase, independently restarted from `coldBallStart`, satisfies the
radius-four relative-tail sampler bound on the original body. -/
theorem tvLe_speedyRejection_adaptive_coldBallStart_truncated_four
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hn : 21 ≤ n) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {N s₀ rho σ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (hσ : 0 < σ) (hσcold : σ * Real.sqrt n ≤ 4)
    (hrad : 1 ≤ 4 * σ * Real.sqrt n)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : ℝ)))
    (hcoldStart : 4 * (n : ℝ) * s₀ ≤ rho ^ 2)
    (hbelow : ∀ j, j + 1 < m →
      adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ j) ≤ N)
    {i : ℕ} (hi : i < m) (hσsq : adaptiveSigmaSq N s₀ i = σ ^ 2)
    {eps : ℝ} (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    {t : ℕ} (ht :
      104857600 * (n : ℝ) ^ 2 *
          (Real.log (adaptiveRestartWarmConst n i) + 2 * Real.log (1 / eps)) /
          Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    Arlib.TVLe
      (Arlib.condOn
        ((Measure.map (fun x : EuclSpace n => (1 - 1 / (2 * (n : ℝ)))⁻¹ • x)
            (Arlib.condOn
              (Arlib.MarkovChains.iterate
                (Arlib.MarkovChains.lazy (Arlib.MarkovChains.speedyMetropolisGaussian
                  (K ∩ closedBall (0 : EuclSpace n) (4 * σ * Real.sqrt n))
                  (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))))
                  (adaptiveSigmaSq N s₀ i)))
                (coldBallStart (n := n) s₀ rho) t)
              ((1 - 1 / (2 * (n : ℝ))) •
                (K ∩ closedBall (0 : EuclSpace n) (4 * σ * Real.sqrt n))))).withDensity
          fun v => ENNReal.ofReal
            (Arlib.MarkovChains.speedyAcceptReal
              (1 - 1 / (2 * (n : ℝ))) (adaptiveSigmaSq N s₀ i) v))
        Set.univ)
      (coolLaw m (adaptiveSigmaSq N s₀) K i)
      (64 * ENNReal.ofReal eps
        + ENNReal.ofReal ((4 * Real.exp (-(15 : ℝ) / 2)) ^ n)) := by
  let M : ℝ := adaptiveRestartWarmConst n i
  have hM : 1 ≤ M := by
    dsimp [M, adaptiveRestartWarmConst]
    exact one_le_pow₀ (by norm_num)
  haveI : IsProbabilityMeasure (coldBallStart (n := n) s₀ rho) :=
    isProbabilityMeasure_coldBallStart hs₀ hrho
  have hwarm := isWarm_coldBallStart_adaptive_ellGaussianProb_truncated_four hKm hKc hn
    hball hN hs₀ hσ hrad hrho hrhoc hcoldStart hbelow hi
  rw [hσsq] at hwarm
  exact tvLe_speedyRejection_coolLaw_truncated_relative_four_of_mixing hn
    (fun j => adaptiveSigmaSq_pos hN hs₀ j) hσ hσcold hrad hKm hKc hball hfin hi hσsq
    hM hwarm heps0 heps32 ht

end Arlib.GaussianCooling.Chunked

#print axioms Arlib.GaussianCooling.Chunked.tvLe_speedyRejection_coolLaw_truncated_relative_four_of_mixing
#print axioms Arlib.GaussianCooling.Chunked.isWarm_coldBallStart_adaptive_ellGaussianProb_truncated_four
#print axioms Arlib.GaussianCooling.Chunked.tvLe_speedyRejection_adaptive_coldBallStart_truncated_four
