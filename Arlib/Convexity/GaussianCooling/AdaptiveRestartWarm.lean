/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.ColdBallStart
import Arlib.Convexity.GaussianCooling.ChunkedSchedule
import Arlib.Convexity.GaussianCooling.WarmChain

/-!
# Independent cold restarts along the adaptive Gaussian schedule

Restarting every phase from the same phase-zero rejection law is honest but accumulates
warmness.  The logarithm of the resulting constant remains polynomial.
-/

namespace Arlib.GaussianCooling.Chunked

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

/-- A coarse real warmness constant for a cold restart at global phase `i`.
Its logarithm is exactly `(1+n*i) log 2`. -/
noncomputable def adaptiveRestartWarmConst (n i : ℕ) : ℝ :=
  (2 : ℝ) ^ (1 + n * i)

theorem log_adaptiveRestartWarmConst (n i : ℕ) :
    Real.log (adaptiveRestartWarmConst n i) = (1 + n * i : ℕ) * Real.log 2 := by
  rw [adaptiveRestartWarmConst, Real.log_pow]

/-- Substituting the proven flattened phase-count estimate gives a fully explicit bound
on the logarithm charged by an independent restart in the first `J` chunks. -/
theorem log_adaptiveRestartWarmConst_le_phaseCount {n : ℕ} {N s₀ : ℝ}
    (hN : 0 < N) (hs₀ : 0 < s₀) {J i : ℕ}
    (hi : i < adaptiveChunkOffset N s₀ J) :
    Real.log (adaptiveRestartWarmConst n i) ≤
      (1 + (n : ℝ) * (4 * N / s₀ + J)) * Real.log 2 := by
  have hio : (i : ℝ) ≤ adaptiveTotalPhases N s₀ J := by
    rw [adaptiveChunkOffset_eq_totalPhases] at hi
    exact_mod_cast (Nat.le_of_lt hi)
  have htotal := adaptiveTotalPhases_le hN hs₀ J
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [log_adaptiveRestartWarmConst]
  push_cast
  have hinner : 1 + (n : ℝ) * i ≤ 1 + (n : ℝ) * (4 * N / s₀ + J) := by
    have hn0 : (0 : ℝ) ≤ n := by positivity
    nlinarith
  exact mul_le_mul_of_nonneg_right hinner hlog0

/-- `coldBallStart` is warm for every Gaussian target in the adaptive schedule.  The
assumption `hbelow` is needed only for transitions preceding the target; it implies the
piecewise-constant adaptive rate is at most `1/2` there.

The intentionally coarse bound is

`M_i = 2^(1+n*i)`, hence `log M_i = (1+n*i) log 2`.

The first factor `2` is the rejection start, and each Gaussian transition costs at most
`2^n` (the sharp factor is `(sqrt (1+alpha_j))^n`). -/
theorem isWarm_coldBallStart_adaptive_coolLaw {n m : ℕ}
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hn : 1 ≤ n) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {N s₀ rho : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀) (hrho : 0 < rho)
    (hcold : 4 * (n : ℝ) * s₀ ≤ rho ^ 2)
    (hballrho : closedBall (0 : EuclSpace n) rho ⊆ K)
    (hbelow : ∀ j, j + 1 < m →
      adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ j) ≤ N) :
    ∀ i, i < m →
      Arlib.IsWarm (ENNReal.ofReal (adaptiveRestartWarmConst n i))
        (coldBallStart (n := n) s₀ rho) (coolLaw m (adaptiveSigmaSq N s₀) K i) := by
  intro i
  induction i with
  | zero =>
      intro hm
      have hw := isWarm_coldBallStart_gaussian hKm hballrho hn hs₀ hrho hcold
      have hsigma0 : adaptiveSigmaSq N s₀ 0 = s₀ := by
        simpa [adaptiveChunkStart] using adaptiveSigmaSq_offset hN hs₀ 0
      have heq := coolLaw_eq_uniformOn_gaussianWeight
        (fun j ↦ adaptiveSigmaSq_pos hN hs₀ j) hKm hball hfin hm
      rw [heq]
      simpa [adaptiveRestartWarmConst, hsigma0] using hw
  | succ i ih =>
      intro him
      have hi : i < m := by omega
      have hprev := ih hi
      let a : ℝ := adaptiveChunkRate N s₀ (adaptivePhaseChunk N s₀ i)
      have ha0 : 0 ≤ a := (adaptiveChunkRate_pos hN hs₀ _).le
      have ha2 : a ≤ 1 / 2 := adaptiveChunkRate_le_half hN (hbelow i him)
      have hcc1 : (1 : ℝ) ≤ 1 + a := by linarith
      have hrate : adaptiveSigmaSq N s₀ (i + 1) =
          (1 + a) * adaptiveSigmaSq N s₀ i := by
        rw [adaptiveSigmaSq_succ hN hs₀ i]
        ring
      have hstep := isWarm_coolLaw_succ_of_ratio him hKm hfin hKc hball
        (fun j ↦ adaptiveSigmaSq_pos hN hs₀ j) hcc1 hrate
      have hsqrt : Real.sqrt (1 + a) ≤ 2 := by
        rw [Real.sqrt_le_iff]
        constructor
        · norm_num
        · nlinarith
      have hpow : Real.sqrt (1 + a) ^ n ≤ (2 : ℝ) ^ n :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt n
      have hstep' : Arlib.IsWarm (ENNReal.ofReal ((2 : ℝ) ^ n))
          (coolLaw m (adaptiveSigmaSq N s₀) K i)
          (coolLaw m (adaptiveSigmaSq N s₀) K (i + 1)) :=
        hstep.mono (ENNReal.ofReal_le_ofReal hpow)
      have hcomp := hprev.trans hstep'
      have hconst : ENNReal.ofReal (adaptiveRestartWarmConst n i) *
          ENNReal.ofReal ((2 : ℝ) ^ n) =
          ENNReal.ofReal (adaptiveRestartWarmConst n (i + 1)) := by
        unfold adaptiveRestartWarmConst
        rw [← ENNReal.ofReal_mul
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (1 + n * i))]
        apply congrArg ENNReal.ofReal
        calc
          (2 : ℝ) ^ (1 + n * i) * 2 ^ n = 2 ^ ((1 + n * i) + n) :=
            (pow_add 2 (1 + n * i) n).symm
          _ = 2 ^ (1 + n * (i + 1)) := by simp [Nat.mul_succ, Nat.add_assoc]
      rw [hconst] at hcomp
      exact hcomp

/-- The same independent-restart bound for the speedy Gaussian target.  Support of the
cold rejection law on `c K` transfers Gaussian warmness to `ellGaussianProb` at no extra
cost. -/
theorem isWarm_coldBallStart_adaptive_ellGaussianProb {n m : ℕ}
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hn : 1 ≤ n) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {N s₀ rho c delta : ℝ} (hN : 0 < N) (hs₀ : 0 < s₀)
    (hc0 : 0 < c) (hc1 : c < 1) (hrho : 0 < rho) (hrhoc : rho < c)
    (hcold : 4 * (n : ℝ) * s₀ ≤ rho ^ 2) (hdelta : 0 < delta)
    (hdeltac : delta ≤ 1 - c)
    (hbelow : ∀ j, j + 1 < m →
      adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ j) ≤ N)
    {i : ℕ} (hi : i < m) :
    Arlib.IsWarm (ENNReal.ofReal (adaptiveRestartWarmConst n i))
      (coldBallStart (n := n) s₀ rho)
      (Arlib.MarkovChains.ellGaussianProb K delta (adaptiveSigmaSq N s₀ i)) := by
  have hBK : closedBall (0 : EuclSpace n) rho ⊆ c • K :=
    closedBall_subset_smul_set_of_lt hball hrho.le hrhoc
  have hsupp : coldBallStart (n := n) s₀ rho ((c • K)ᶜ) = 0 :=
    measure_mono_null (compl_subset_compl.mpr hBK) (coldBallStart_compl_eq_zero s₀ rho)
  have hcK : c • K ⊆ K :=
    Arlib.MarkovChains.smul_subset_of_convex hKc (hball (mem_ball_self one_pos)) hc0.le hc1.le
  have hw := isWarm_coldBallStart_adaptive_coolLaw hKm hKc hn hball hfin hN hs₀ hrho hcold
    (hBK.trans hcK) hbelow i hi
  rw [coolLaw_eq_uniformOn_gaussianWeight (fun j ↦ adaptiveSigmaSq_pos hN hs₀ j)
    hKm hball hfin hi] at hw
  exact isWarm_ellGaussianProb_of_supported_on_shrunken hKm hKc hball hc0 hc1 hdelta
    hdeltac hsupp hw

/-! ## Axiom audit -/

#print axioms log_adaptiveRestartWarmConst
#print axioms log_adaptiveRestartWarmConst_le_phaseCount
#print axioms isWarm_coldBallStart_adaptive_coolLaw
#print axioms isWarm_coldBallStart_adaptive_ellGaussianProb

end Arlib.GaussianCooling.Chunked
