/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.ColdWarmStart
import Arlib.Convexity.GaussianCooling.WarmSpeedy

/-!
# An algorithmic phase-zero start from a cold ambient Gaussian

Sample the ambient spherical Gaussian with variance `s` and reject until the point lies in
`closedBall 0 ρ`.  The resulting law is `coldBallStart s ρ`.  It is a probability measure,
and, if the ball carries at least half the ambient Gaussian mass, it is `2`-warm for the
Gaussian restricted to any body containing the ball.  If moreover `closedBall 0 ρ` lies in
the safe shrunken body `c • K`, `WarmSpeedy` transfers the same constant to the speedy
Gaussian stationary law.

The construction never evaluates the Gaussian normalizer on `K`: its only normalizer is
the explicit rejection event in the ambient Gaussian.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

open Arlib.MarkovChains

variable {n : ℕ}

/-- The law produced by drawing from the ambient Gaussian of variance `s` and rejecting
until the draw lies in `closedBall 0 ρ`. -/
noncomputable def coldBallStart (s ρ : ℝ) : Measure (EuclSpace n) :=
  Arlib.uniformOn
    ((volume : Measure (EuclSpace n)).withDensity (gaussianWeight s))
    (closedBall (0 : EuclSpace n) ρ)

/-- The phase-zero rejection law is a genuine probability measure. -/
theorem isProbabilityMeasure_coldBallStart {s ρ : ℝ} (hs : 0 < s) (hρ : 0 < ρ) :
    IsProbabilityMeasure (coldBallStart (n := n) s ρ) := by
  unfold coldBallStart
  exact isProbabilityMeasure_uniformOn_gaussianWeight measurableSet_closedBall
    (Metric.measure_closedBall_pos volume (0 : EuclSpace n) hρ).ne'
    measure_closedBall_lt_top.ne hs

/-- The start has no mass outside its rejection ball. -/
theorem coldBallStart_compl_eq_zero (s ρ : ℝ) :
    coldBallStart (n := n) s ρ (closedBall (0 : EuclSpace n) ρ)ᶜ = 0 := by
  exact Arlib.uniformOn_compl_eq_zero _ measurableSet_closedBall

/-- A strictly smaller closed ball lies in `c • K` when the open unit ball lies in `K`.
The strict inequality `ρ < c` is necessary because the body is only assumed to contain the
open unit ball; its boundary need not belong to `K`. -/
theorem closedBall_subset_smul_set_of_lt {K : Set (EuclSpace n)}
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) {ρ c : ℝ} (hρ : 0 ≤ ρ) (hρc : ρ < c) :
    closedBall (0 : EuclSpace n) ρ ⊆ c • K := by
  have hc : 0 < c := lt_of_le_of_lt hρ hρc
  exact fun x hx => MarkovChains.ball_subset_smul_set hball hc
    (by
      rw [mem_closedBall_zero_iff] at hx
      rw [mem_ball_zero_iff]
      exact lt_of_le_of_lt hx hρc)

/-- The cold rejection ball carries at least half of the ambient Gaussian mass. -/
theorem half_ambientGaussian_le_coldBall {s ρ : ℝ} (hn : 1 ≤ n) (hs : 0 < s)
    (hρ : 0 < ρ) (hcold : 4 * (n : ℝ) * s ≤ ρ ^ 2) :
    ENNReal.ofReal (1 / 2) *
        ((volume : Measure (EuclSpace n)).withDensity (gaussianWeight s)) Set.univ
      ≤ ((volume : Measure (EuclSpace n)).withDensity (gaussianWeight s))
          (closedBall (0 : EuclSpace n) ρ) := by
  rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ measurableSet_closedBall,
    Measure.restrict_univ]
  exact half_lintegral_gaussianWeight_univ_le_closedBall hn hs hρ hcold

/-- `coldBallStart` is `2`-warm for the Gaussian law restricted to `K`, without knowing or
computing the Gaussian normalizer on `K`.

The denominator comparison is

`Z_K ≤ Z_ambient ≤ 2 Z_ball`.
-/
theorem isWarm_coldBallStart_gaussian {K : Set (EuclSpace n)} {s ρ : ℝ}
    (hKm : MeasurableSet K) (hballρ : closedBall (0 : EuclSpace n) ρ ⊆ K)
    (hn : 1 ≤ n) (hs : 0 < s)
    (hρ : 0 < ρ) (hcold : 4 * (n : ℝ) * s ≤ ρ ^ 2) :
    Arlib.IsWarm (ENNReal.ofReal 2) (coldBallStart (n := n) s ρ)
      (Arlib.uniformOn ((volume : Measure (EuclSpace n)).withDensity (gaussianWeight s)) K) := by
  let ν : Measure (EuclSpace n) :=
    (volume : Measure (EuclSpace n)).withDensity (gaussianWeight s)
  let B : Set (EuclSpace n) := closedBall (0 : EuclSpace n) ρ
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hBvol0 : volume B ≠ 0 :=
    (Metric.measure_closedBall_pos volume (0 : EuclSpace n) hρ).ne'
  have hB0 : ν B ≠ 0 := by
    dsimp [ν]
    exact withDensity_gaussianWeight_ne_zero s hBvol0
  have hBtop : ν B ≠ ⊤ := by
    dsimp [ν]
    exact withDensity_gaussianWeight_ne_top hs hBm measure_closedBall_lt_top.ne
  have hK0 : ν K ≠ 0 := by
    exact (lt_of_lt_of_le (pos_iff_ne_zero.2 hB0)
      (measure_mono (by simpa [B] using hballρ))).ne'
  have hνtop : ν Set.univ ≠ ⊤ := by
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    simpa only [Measure.restrict_univ] using
      (lintegral_gaussianWeight_ne_top_of_univ (n := n) hs Set.univ)
  have hKtop : ν K ≠ ⊤ := ne_top_of_le_ne_top hνtop (measure_mono (subset_univ K))
  have hhalf : ENNReal.ofReal (1 / 2) * ν Set.univ ≤ ν B := by
    simpa [ν, B] using half_ambientGaussian_le_coldBall (n := n) hn hs hρ hcold
  have hamb_le : ν Set.univ ≤ ENNReal.ofReal 2 * ν B := by
    calc
      ν Set.univ = ENNReal.ofReal 2 * (ENNReal.ofReal (1 / 2) * ν Set.univ) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ ≤ ENNReal.ofReal 2 * ν B := mul_le_mul_left' hhalf _
  have hK_le : ν K ≤ ENNReal.ofReal 2 * ν B :=
    (measure_mono (subset_univ K)).trans hamb_le
  have hratio : ν K / ν B ≤ ENNReal.ofReal 2 := by
    rw [ENNReal.div_le_iff hB0 hBtop]
    simpa [mul_comm] using hK_le
  intro S hSm
  change Arlib.uniformOn ν B S ≤ ENNReal.ofReal 2 * Arlib.uniformOn ν K S
  rw [Arlib.uniformOn_apply ν hBm hSm, Arlib.uniformOn_apply ν hKm hSm]
  calc
    ν (S ∩ B) / ν B ≤ ν (S ∩ K) / ν B :=
      ENNReal.div_le_div_right
        (measure_mono (Set.inter_subset_inter_right S (by simpa [B] using hballρ))) _
    _ = (ν K / ν B) * (ν (S ∩ K) / ν K) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      have hcancel : ν K * (ν K)⁻¹ = 1 := ENNReal.mul_inv_cancel hK0 hKtop
      rw [show (ν K * (ν B)⁻¹) * (ν (S ∩ K) * (ν K)⁻¹) =
          (ν K * (ν K)⁻¹) * (ν (S ∩ K) * (ν B)⁻¹) by
        simp only [mul_comm, mul_assoc, mul_left_comm], hcancel, one_mul]
    _ ≤ ENNReal.ofReal 2 * (ν (S ∩ K) / ν K) := mul_le_mul_right' hratio _

/-- **Phase-zero warm start.**  A cold ambient Gaussian rejected onto a strictly inner
closed ball is `2`-warm for the speedy Gaussian law on `K`.

There is no `K`-normalizer in the construction or its hypotheses. -/
theorem isWarm_coldBallStart_ellGaussianProb {K : Set (EuclSpace n)}
    (hKm : MeasurableSet K) (hKc : Convex ℝ K) (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    {c ρ δ s : ℝ} (hn : 1 ≤ n) (hc0 : 0 < c) (hc1 : c < 1)
    (hρ : 0 < ρ) (hρc : ρ < c) (hs : 0 < s)
    (hcold : 4 * (n : ℝ) * s ≤ ρ ^ 2) (hδ : 0 < δ) (hδc : δ ≤ 1 - c) :
    Arlib.IsWarm (ENNReal.ofReal 2) (coldBallStart (n := n) s ρ)
      (MarkovChains.ellGaussianProb K δ s) := by
  have hBK : closedBall (0 : EuclSpace n) ρ ⊆ c • K :=
    closedBall_subset_smul_set_of_lt hball hρ.le hρc
  have hcK : c • K ⊆ K :=
    MarkovChains.smul_subset_of_convex hKc (hball (mem_ball_self one_pos)) hc0.le hc1.le
  have hB_K : closedBall (0 : EuclSpace n) ρ ⊆ K := hBK.trans hcK
  have hsupp : coldBallStart (n := n) s ρ ((c • K)ᶜ) = 0 := by
    refine measure_mono_null (compl_subset_compl.mpr hBK) ?_
    exact coldBallStart_compl_eq_zero (n := n) s ρ
  exact isWarm_ellGaussianProb_of_supported_on_shrunken hKm hKc hball hc0 hc1 hδ hδc
    hsupp (isWarm_coldBallStart_gaussian hKm hB_K hn hs hρ hcold)

/-! ## Axiom audit -/

#print axioms Arlib.GaussianCooling.isProbabilityMeasure_coldBallStart
#print axioms Arlib.GaussianCooling.isWarm_coldBallStart_gaussian
#print axioms Arlib.GaussianCooling.isWarm_coldBallStart_ellGaussianProb

end Arlib.GaussianCooling
