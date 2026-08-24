/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.AdaptiveRestartWarm
import Arlib.Convexity.GaussianCooling.PhaseSamplerTVTruncatedRelative

/-!
# Cold independent restarts on the truncated adaptive phases

The speedy stationary law for `K ∩ T` is not, in general, the full-body speedy law
conditioned on `T`: its local factor is `ell (K ∩ T)`, not `ell K`.  We therefore establish
the truncated warm start by applying the cold-ball theorem directly to the truncated convex
body.  This is possible because the truncation contains the unit ball and is automatically
finite-volume.

For reference, the generic supported-conditioning fact which would apply if the two targets
were related by conditioning is also recorded below.
-/

namespace Arlib.GaussianCooling.Chunked

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

/-! ## Supported warm laws and conditioning -/

/-- If an `M`-warm probability law is supported on `A`, it remains `M`-warm for the target
conditioned on `A`; unlike conditioning the source, this costs no reciprocal mass factor. -/
theorem isWarm_condOn_of_compl_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} [IsProbabilityMeasure ν] {M : ℝ≥0∞} (hw : Arlib.IsWarm M μ ν)
    {A : Set Ω} (hA : MeasurableSet A) (hμA : μ Aᶜ = 0) :
    Arlib.IsWarm M μ (Arlib.condOn ν A) := by
  intro S hS
  have hμ : μ S = μ (S ∩ A) := by
    rw [← MeasureTheory.measure_sdiff_null (s := S) (t := Aᶜ) hμA]
    simp only [sdiff_compl]
  rw [hμ, Arlib.condOn_apply ν hA hS]
  calc
    μ (S ∩ A) ≤ M * ν (S ∩ A) := hw _ (hS.inter hA)
    _ ≤ M * (ν (S ∩ A) / ν A) := by
      gcongr
      by_cases hνA : ν A = 0
      · have hzero : ν (S ∩ A) = 0 :=
          MeasureTheory.measure_mono_null inter_subset_right hνA
        simp [hzero]
      · rw [ENNReal.le_div_iff_mul_le (Or.inl hνA)
          (Or.inl (measure_ne_top ν A))]
        calc
          ν (S ∩ A) * ν A ≤ ν (S ∩ A) * 1 := by
            gcongr
            simpa only [measure_univ] using
              (MeasureTheory.measure_mono (μ := ν) (subset_univ A))
          _ = ν (S ∩ A) := mul_one _

/-! ## Warmness on the actual truncated speedy target -/

variable {n m : ℕ}

/-- A cold-ball start is supported in any larger closed-ball truncation. -/
theorem coldBallStart_truncation_compl_eq_zero {s rho R : ℝ} (hρR : rho ≤ R) :
    coldBallStart (n := n) s rho (closedBall (0 : EuclSpace n) R)ᶜ = 0 := by
  exact MeasureTheory.measure_mono_null
    (compl_subset_compl.mpr (closedBall_subset_closedBall hρR))
    (coldBallStart_compl_eq_zero s rho)

/-- The same cold independent restart is warm for the phase's truncated speedy target.

This is a direct application of `isWarm_coldBallStart_adaptive_ellGaussianProb` to the body
`K ∩ closedBall 0 (2σ√n)`.  No false conditioning identity between full and truncated `ell`
weights is used. -/
theorem isWarm_coldBallStart_adaptive_ellGaussianProb_truncated
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hn : 21 ≤ n) (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    {N s₀ rho σ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (hσ : 0 < σ) (hrad : 1 ≤ 2 * σ * Real.sqrt n)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : ℝ)))
    (hcold : 4 * (n : ℝ) * s₀ ≤ rho ^ 2)
    (hbelow : ∀ j, j + 1 < m →
      adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ j) ≤ N)
    {i : ℕ} (hi : i < m) :
    Arlib.IsWarm (ENNReal.ofReal (adaptiveRestartWarmConst n i))
      (coldBallStart (n := n) s₀ rho)
      (Arlib.MarkovChains.ellGaussianProb
        (K ∩ closedBall (0 : EuclSpace n) (2 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))))
        (adaptiveSigmaSq N s₀ i)) := by
  have hn1 : 1 ≤ n := by omega
  let K' : Set (EuclSpace n) :=
    K ∩ closedBall (0 : EuclSpace n) (2 * σ * Real.sqrt n)
  have hK'm : MeasurableSet K' :=
    Arlib.MarkovChains.measurableSet_inter_closedBall hKm _
  have hK'c : Convex ℝ K' :=
    Arlib.MarkovChains.convex_inter_closedBall hKc _
  have hK'ball : ball (0 : EuclSpace n) 1 ⊆ K' :=
    Arlib.MarkovChains.unitBall_subset_inter_closedBall hball hrad
  have hK'fin : volume K' ≠ ⊤ :=
    Arlib.MarkovChains.volume_inter_closedBall_ne_top K _
  have hrhoR : rho ≤ 2 * σ * Real.sqrt n := by
    have hrho1 : rho < 1 := hrhoc.trans (by
      have hnpos : (0 : ℝ) < n := by positivity
      have : 0 < 1 / (2 * (n : ℝ)) := by positivity
      linarith)
    linarith
  have _hsupportTruncation :
      coldBallStart (n := n) s₀ rho
        (closedBall (0 : EuclSpace n) (2 * σ * Real.sqrt n))ᶜ = 0 :=
    coldBallStart_truncation_compl_eq_zero hrhoR
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
    hN hs₀ hc0 hc1 hrho hrhoc hcold hδ hδc hbelow hi

/-! ## End-to-end truncated phase adapter -/

/-- One adaptive cold phase, independently restarted from `coldBallStart`, satisfies the
relative-tail sampler bound on the original body. -/
theorem tvLe_speedyRejection_adaptive_coldBallStart_truncated
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hn : 21 ≤ n) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {N s₀ rho σ : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (hσ : 0 < σ) (hσcold : σ * Real.sqrt n ≤ 4)
    (hrad : 1 ≤ 2 * σ * Real.sqrt n)
    (hrho : 0 < rho) (hrhoc : rho < 1 - 1 / (2 * (n : ℝ)))
    (hcold : 4 * (n : ℝ) * s₀ ≤ rho ^ 2)
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
                  (K ∩ closedBall (0 : EuclSpace n) (2 * σ * Real.sqrt n))
                  (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ))))
                  (adaptiveSigmaSq N s₀ i)))
                (coldBallStart (n := n) s₀ rho) t)
              ((1 - 1 / (2 * (n : ℝ))) •
                (K ∩ closedBall (0 : EuclSpace n) (2 * σ * Real.sqrt n))))).withDensity
          fun v => ENNReal.ofReal
            (Arlib.MarkovChains.speedyAcceptReal
              (1 - 1 / (2 * (n : ℝ))) (adaptiveSigmaSq N s₀ i) v))
        Set.univ)
      (coolLaw m (adaptiveSigmaSq N s₀) K i)
      (64 * ENNReal.ofReal eps
        + ENNReal.ofReal ((2 * Real.exp (-(3 : ℝ) / 2)) ^ n)) := by
  let M : ℝ := adaptiveRestartWarmConst n i
  have hM : 1 ≤ M := by
    dsimp [M, adaptiveRestartWarmConst]
    exact one_le_pow₀ (by norm_num)
  haveI : IsProbabilityMeasure (coldBallStart (n := n) s₀ rho) :=
    isProbabilityMeasure_coldBallStart hs₀ hrho
  have hwarm := isWarm_coldBallStart_adaptive_ellGaussianProb_truncated hKm hKc hn hball
    hN hs₀ hσ hrad hrho hrhoc hcold hbelow hi
  rw [hσsq] at hwarm
  exact tvLe_speedyRejection_coolLaw_truncated_relative_of_mixing hn
    (fun j => adaptiveSigmaSq_pos hN hs₀ j) hσ hσcold hrad hKm hKc hball hfin hi hσsq
    hM hwarm heps0 heps32 ht

end Arlib.GaussianCooling.Chunked

#print axioms Arlib.GaussianCooling.Chunked.isWarm_condOn_of_compl_eq_zero
#print axioms Arlib.GaussianCooling.Chunked.coldBallStart_truncation_compl_eq_zero
#print axioms Arlib.GaussianCooling.Chunked.isWarm_coldBallStart_adaptive_ellGaussianProb_truncated
#print axioms Arlib.GaussianCooling.Chunked.tvLe_speedyRejection_adaptive_coldBallStart_truncated
