/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.ColdTruncation

/-!
# The phase-`0` warm start: a cold Gaussian on a ball inside the body

Placeholder docstring; filled in once the mathematics is green.
-/

open MeasureTheory Metric Set

open scoped ENNReal

namespace Arlib.GaussianCooling

open Arlib.MarkovChains

variable {n : ℕ}

/-! ## 1.  Positivity of Gaussian mass -/

/-- **A set of positive Lebesgue measure has positive Gaussian mass.**  The Gaussian weight is
strictly positive everywhere, so its integral vanishes only on a null set. -/
theorem lintegral_gaussianWeight_pos_of_volume_ne_zero {s : ℝ}
    {A : Set (EuclideanSpace ℝ (Fin n))} (_hA : MeasurableSet A) (h : volume A ≠ 0) :
    0 < ∫⁻ x in A, gaussianWeight s x := by
  rw [pos_iff_ne_zero]
  intro h0
  rw [lintegral_eq_zero_iff (measurable_gaussianWeight s)] at h0
  have hset : {x : EuclideanSpace ℝ (Fin n) | ¬ gaussianWeight s x = (0 : ℝ≥0∞)} = Set.univ :=
    Set.eq_univ_of_forall fun x => gaussianWeight_ne_zero s x
  rw [Filter.EventuallyEq, ae_iff] at h0
  simp only [Pi.zero_apply] at h0
  rw [hset, Measure.restrict_apply_univ] at h0
  exact h h0

/-! ## 2.  Concentration: a cold Gaussian keeps half its mass in the unit-scale ball -/

/-- **The cold Gaussian keeps at least half its mass in `closedBall 0 ρ`**, as soon as
`4·n·s ≤ ρ²`.

Cousins–Vempala's `lem:starting-gauss` (`1409.6011/vol3_journal.tex:1321`) with the constants
made explicit: the `t`-split of `Arlib.MarkovChains.lintegral_gaussianWeight_norm_gt_le` at
`t = 3/4` bounds the discarded mass by `(2·e^{-3/2})^n ≤ 2^{-n} ≤ 1/2`. -/
theorem half_lintegral_gaussianWeight_univ_le_closedBall (hn : 1 ≤ n) {s ρ : ℝ}
    (hs : 0 < s) (hρ : 0 < ρ) (hcold : 4 * (n : ℝ) * s ≤ ρ ^ 2) :
    ENNReal.ofReal (1 / 2) * (∫⁻ x : EuclideanSpace ℝ (Fin n), gaussianWeight s x)
      ≤ ∫⁻ x in closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ, gaussianWeight s x := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- the real-number heart: the tail bound at `t = 3/4` is at most half the total mass
  have hexp32 : (4 : ℝ) ≤ Real.exp (3 / 2) := by
    have hsum := Real.sum_le_exp_of_nonneg (x := (3 / 2 : ℝ)) (by norm_num) 4
    norm_num [Finset.sum_range_succ] at hsum ⊢
    linarith
  have hkey : Real.exp (-(3 / 4 * ρ ^ 2) / (2 * s))
      * (2 * Real.pi * (s / (1 - 3 / 4))) ^ ((n : ℝ) / 2)
      ≤ 1 / 2 * (2 * Real.pi * s) ^ ((n : ℝ) / 2) := by
    -- the rpow identity `(2π·4s)^{n/2} = 2ⁿ·(2πs)^{n/2}`
    have hbase : 2 * Real.pi * (s / (1 - 3 / 4)) = 4 * (2 * Real.pi * s) := by ring
    have hfour : (4 : ℝ) ^ ((n : ℝ) / 2) = 2 ^ n := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
      rw [h4, ← Real.rpow_mul (by norm_num), show (2 : ℝ) * ((n : ℝ) / 2) = (n : ℝ) by ring,
        Real.rpow_natCast]
    have hrpow : (2 * Real.pi * (s / (1 - 3 / 4))) ^ ((n : ℝ) / 2)
        = 2 ^ n * (2 * Real.pi * s) ^ ((n : ℝ) / 2) := by
      rw [hbase, Real.mul_rpow (by norm_num) (by positivity), hfour]
    -- the exponential factor
    have hquot : (3 : ℝ) * (n : ℝ) / 2 ≤ (3 / 4 * ρ ^ 2) / (2 * s) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * s)]
      nlinarith
    have hE1 : Real.exp (-(3 / 4 * ρ ^ 2) / (2 * s)) ≤ Real.exp (-(3 * (n : ℝ) / 2)) := by
      apply Real.exp_le_exp.2
      rw [neg_div]
      linarith
    have hE2 : Real.exp (-(3 * (n : ℝ) / 2)) ≤ (1 / 4 : ℝ) ^ n := by
      have hpow : (4 : ℝ) ^ n ≤ Real.exp (3 / 2) ^ n :=
        pow_le_pow_left₀ (by norm_num) hexp32 n
      have hE : Real.exp (3 / 2) ^ n = Real.exp (3 * (n : ℝ) / 2) := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [hE] at hpow
      rw [Real.exp_neg, one_div, inv_pow]
      exact (inv_le_inv₀ (Real.exp_pos (3 * (n : ℝ) / 2))
        (pow_pos (by norm_num : (0 : ℝ) < 4) n)).2 hpow
    have hfin : Real.exp (-(3 * (n : ℝ) / 2)) * 2 ^ n ≤ 1 / 2 := by
      calc Real.exp (-(3 * (n : ℝ) / 2)) * 2 ^ n ≤ (1 / 4 : ℝ) ^ n * 2 ^ n :=
            mul_le_mul_of_nonneg_right hE2 (by positivity)
        _ = (1 / 2 : ℝ) ^ n := by rw [← mul_pow]; norm_num
        _ ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
        _ = 1 / 2 := pow_one _
    have hnn : (0 : ℝ) ≤ (2 * Real.pi * s) ^ ((n : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    calc Real.exp (-(3 / 4 * ρ ^ 2) / (2 * s))
          * (2 * Real.pi * (s / (1 - 3 / 4))) ^ ((n : ℝ) / 2)
        = (Real.exp (-(3 / 4 * ρ ^ 2) / (2 * s)) * 2 ^ n)
            * (2 * Real.pi * s) ^ ((n : ℝ) / 2) := by rw [hrpow]; ring
      _ ≤ (1 / 2 : ℝ) * (2 * Real.pi * s) ^ ((n : ℝ) / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ hnn
          exact le_trans (mul_le_mul_of_nonneg_right hE1 (by positivity)) hfin
  have htail :
      ∫⁻ x in {x : EuclideanSpace ℝ (Fin n) | ρ < ‖x‖}, gaussianWeight s x
        ≤ ENNReal.ofReal (1 / 2) *
          (∫⁻ x : EuclideanSpace ℝ (Fin n), gaussianWeight s x) := by
    calc
      ∫⁻ x in {x : EuclideanSpace ℝ (Fin n) | ρ < ‖x‖}, gaussianWeight s x
          ≤ ENNReal.ofReal (Real.exp (-(3 / 4 * ρ ^ 2) / (2 * s))
              * (2 * Real.pi * (s / (1 - 3 / 4))) ^ ((n : ℝ) / 2)) :=
            lintegral_gaussianWeight_norm_gt_le hs hρ.le (by norm_num) (by norm_num)
      _ ≤ ENNReal.ofReal (1 / 2 * (2 * Real.pi * s) ^ ((n : ℝ) / 2)) :=
            ENNReal.ofReal_le_ofReal hkey
      _ = ENNReal.ofReal (1 / 2) *
          (∫⁻ x : EuclideanSpace ℝ (Fin n), gaussianWeight s x) := by
            rw [lintegral_gaussianWeight_univ hs, ENNReal.ofReal_mul (by norm_num)]
  have hcompl :
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ)ᶜ =
        {x : EuclideanSpace ℝ (Fin n) | ρ < ‖x‖} := by
    ext x
    simp only [mem_compl_iff, mem_closedBall_zero_iff, mem_setOf_eq, not_le]
  have hsplit := lintegral_add_compl (μ := volume) (gaussianWeight s)
    (measurableSet_closedBall : MeasurableSet (closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ))
  rw [hcompl] at hsplit
  let M : ℝ≥0∞ := ∫⁻ x : EuclideanSpace ℝ (Fin n), gaussianWeight s x
  let H : ℝ≥0∞ := ENNReal.ofReal (1 / 2)
  have hMtop : M ≠ ⊤ := by
    simpa [M] using
      (lintegral_gaussianWeight_ne_top_of_univ (n := n) hs Set.univ)
  have hHMtop : H * M ≠ ⊤ := ENNReal.mul_ne_top (by simp [H]) hMtop
  have htwohalf : H * M + H * M = M := by
    rw [← add_mul]
    have hHH : H + H = 1 := by
      change ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) = 1
      rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)]
      norm_num
    rw [hHH, one_mul]
  apply ENNReal.le_of_add_le_add_right hHMtop
  calc
    H * M + H * M = M := htwohalf
    _ = (∫⁻ x in closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ, gaussianWeight s x) +
        ∫⁻ x in {x : EuclideanSpace ℝ (Fin n) | ρ < ‖x‖}, gaussianWeight s x := hsplit.symm
    _ ≤ (∫⁻ x in closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ, gaussianWeight s x) +
        H * M := by gcongr

end Arlib.GaussianCooling

#print axioms Arlib.GaussianCooling.lintegral_gaussianWeight_pos_of_volume_ne_zero
#print axioms Arlib.GaussianCooling.half_lintegral_gaussianWeight_univ_le_closedBall
