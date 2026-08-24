/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.ColdTruncationRelative

/-!
# A relative Gaussian truncation bound at radius `4 * σ * √n`

Quarter-dilating the part of a convex body outside `4 * σ * √n` gives a subset of the
same body.  Comparing the Gaussian density before and after this dilation bounds the relative
tail by `(4 * exp (-15/2))^n`.
-/

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

namespace Arlib.MarkovChains

open Arlib.GaussianCooling

variable {n : ℕ}

/-- Quartering the part of a convex body outside `4 * σ * √n` sends it back into the body,
where the Gaussian density is exponentially larger. -/
theorem lintegral_gaussianWeight_sdiff_le_relative_four (_hn : 1 ≤ n) {σ : ℝ} (hσ : 0 < σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K) :
    ∫⁻ x in K \ closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * σ * Real.sqrt n),
        gaussianWeight (σ ^ 2) x
      ≤ ENNReal.ofReal ((4 * Real.exp (-(15 : ℝ) / 2)) ^ n)
          * ∫⁻ x in K, gaussianWeight (σ ^ 2) x := by
  set E : Set (EuclideanSpace ℝ (Fin n)) :=
    K \ closedBall (0 : EuclideanSpace ℝ (Fin n)) (4 * σ * Real.sqrt n) with hEdef
  set A : Set (EuclideanSpace ℝ (Fin n)) := (1 / 4 : ℝ) • E with hAdef
  have hEm : MeasurableSet E := hK.diff measurableSet_closedBall
  have hAm : MeasurableSet A := measurableSet_smul_set hEm (by norm_num)
  have hAK : A ⊆ K := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hKc.smul_mem_of_zero_mem h0K hx.1 ⟨by norm_num, by norm_num⟩
  have hEA : (4 : ℝ) • A = E := by
    rw [hAdef, smul_smul]
    norm_num
  have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have hpoint : ∀ y ∈ A,
      gaussianWeight (σ ^ 2 / (4 : ℝ) ^ 2) y
        ≤ ENNReal.ofReal (Real.exp (-(15 : ℝ) * (n : ℝ) / 2))
            * gaussianWeight (σ ^ 2) y := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxnorm : 4 * σ * Real.sqrt n < ‖x‖ := by
      have hout := hx.2
      rw [mem_closedBall_zero_iff, not_le] at hout
      exact hout
    have hynorm : σ * Real.sqrt n < ‖(1 / 4 : ℝ) • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      nlinarith
    have hy2 : σ ^ 2 * (n : ℝ) < ‖(1 / 4 : ℝ) • x‖ ^ 2 := by
      have hy2' := (sq_lt_sq₀ (mul_nonneg hσ.le (Real.sqrt_nonneg _)) (norm_nonneg _)).2 hynorm
      rw [mul_pow, hsqrt] at hy2'
      exact hy2'
    have hq : (15 : ℝ) * (n : ℝ) / 2
        ≤ 15 * ‖(1 / 4 : ℝ) • x‖ ^ 2 / (2 * σ ^ 2) := by
      have hσ2 : 0 < σ ^ 2 := sq_pos_of_pos hσ
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hexp : Real.exp (-(15 : ℝ) * ‖(1 / 4 : ℝ) • x‖ ^ 2 / (2 * σ ^ 2))
        ≤ Real.exp (-(15 : ℝ) * (n : ℝ) / 2) := by
      apply Real.exp_le_exp.2
      have hneg := neg_le_neg hq
      calc
        -(15 : ℝ) * ‖(1 / 4 : ℝ) • x‖ ^ 2 / (2 * σ ^ 2)
            = -(15 * ‖(1 / 4 : ℝ) • x‖ ^ 2 / (2 * σ ^ 2)) := by ring
        _ ≤ -(15 * (n : ℝ) / 2) := hneg
        _ = -(15 : ℝ) * (n : ℝ) / 2 := by ring
    unfold gaussianWeight gaussianWeightReal
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hden : σ ^ 2 / (4 : ℝ) ^ 2 = σ ^ 2 / 16 := by norm_num
    rw [hden]
    have hsplit : -‖(1 / 4 : ℝ) • x‖ ^ 2 / (2 * (σ ^ 2 / 16))
        = -(15 : ℝ) * ‖(1 / 4 : ℝ) • x‖ ^ 2 / (2 * σ ^ 2)
          + -‖(1 / 4 : ℝ) • x‖ ^ 2 / (2 * σ ^ 2) := by
      field_simp [ne_of_gt hσ]
      ring
    rw [hsplit, Real.exp_add]
    exact mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
  have htail : (∫⁻ x in E, gaussianWeight (σ ^ 2) x)
      = ENNReal.ofReal ((4 : ℝ) ^ n)
          * ∫⁻ y in A, gaussianWeight (σ ^ 2 / (4 : ℝ) ^ 2) y := by
    rw [← hEA]
    exact lintegral_gaussianWeight_smul_set hAm (by norm_num) (σ ^ 2)
  rw [htail]
  calc ENNReal.ofReal ((4 : ℝ) ^ n)
        * ∫⁻ y in A, gaussianWeight (σ ^ 2 / (4 : ℝ) ^ 2) y
      ≤ ENNReal.ofReal ((4 : ℝ) ^ n) *
          (ENNReal.ofReal (Real.exp (-(15 : ℝ) * (n : ℝ) / 2))
            * ∫⁻ y in A, gaussianWeight (σ ^ 2) y) := by
        gcongr
        calc ∫⁻ y in A, gaussianWeight (σ ^ 2 / (4 : ℝ) ^ 2) y
            ≤ ∫⁻ y in A,
                ENNReal.ofReal (Real.exp (-(15 : ℝ) * (n : ℝ) / 2))
                  * gaussianWeight (σ ^ 2) y := by
              refine lintegral_mono_ae ?_
              filter_upwards [self_mem_ae_restrict hAm] with y hy using hpoint y hy
          _ = ENNReal.ofReal (Real.exp (-(15 : ℝ) * (n : ℝ) / 2))
                * ∫⁻ y in A, gaussianWeight (σ ^ 2) y := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ n) *
          (ENNReal.ofReal (Real.exp (-(15 : ℝ) * (n : ℝ) / 2))
            * ∫⁻ y in K, gaussianWeight (σ ^ 2) y) := by
        gcongr
    _ = ENNReal.ofReal ((4 * Real.exp (-(15 : ℝ) / 2)) ^ n)
          * ∫⁻ y in K, gaussianWeight (σ ^ 2) y := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [mul_pow]
        have he : Real.exp (-(15 : ℝ) * (n : ℝ) / 2)
            = Real.exp (-(15 : ℝ) / 2) ^ n := by
          calc Real.exp (-(15 : ℝ) * (n : ℝ) / 2)
              = Real.exp ((n : ℝ) * (-(15 : ℝ) / 2)) := by congr 1; ring
            _ = Real.exp (-(15 : ℝ) / 2) ^ n := Real.exp_nat_mul _ _
        rw [he]

/-- The phase law on `K ∩ B(0, 4σ√n)` is close to the phase law on `K`, with the
source-radius relative-tail constant `(4 * exp (-15/2))^n`. -/
theorem tvLe_coolLaw_inter_closedBall_relative_four (hn : 1 ≤ n) {m : ℕ} {σsq : ℕ → ℝ}
    (hσpos : ∀ j, 0 < σsq j) {σ : ℝ} (hσ : 0 < σ)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : ℕ} (hi : i < m) (hσsq : σsq i = σ ^ 2) (hr : 1 ≤ 4 * σ * Real.sqrt n) :
    Arlib.TVLe
      (coolLaw m σsq (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n))
        (4 * σ * Real.sqrt n)) i)
      (coolLaw m σsq K i)
      (ENNReal.ofReal ((4 * Real.exp (-(15 : ℝ) / 2)) ^ n)) := by
  set r : ℝ := 4 * σ * Real.sqrt n with hrdef
  set A : Set (EuclideanSpace ℝ (Fin n)) := K ∩ closedBall 0 r with hAdef
  set μ : Measure (EuclideanSpace ℝ (Fin n)) :=
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σsq i))
      with hμdef
  have hAm : MeasurableSet A := hK.inter measurableSet_closedBall
  have hAball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ A := by
    rw [hAdef]
    exact unitBall_subset_inter_closedBall hball (hrdef ▸ hr)
  have hAfin : volume A ≠ ⊤ := by
    rw [hAdef]
    exact volume_inter_closedBall_ne_top K r
  have hμapply : ∀ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S →
      μ S = ∫⁻ x in S, gaussianWeight (σsq i) x := fun S hS => withDensity_apply _ hS
  have hA0 : μ A ≠ 0 := by
    rw [hμapply A hAm]
    intro hz
    have hle := le_lintegral_gaussianWeight_of_unitBall_subset (hσpos i) hAball
    rw [hz, le_zero_iff, mul_eq_zero] at hle
    rcases hle with h1 | h2
    · exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' h1
    · exact (measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne' h2
  have hKtop : μ K ≠ ⊤ := by
    rw [hμapply K hK]
    exact lintegral_gaussianWeight_ne_top_of_univ (hσpos i) K
  have htail : μ (K \ A) ≤
      ENNReal.ofReal ((4 * Real.exp (-(15 : ℝ) / 2)) ^ n) * μ K := by
    rw [hμapply _ (hK.diff hAm), hμapply K hK, hAdef, Set.sdiff_self_inter, hσsq,
      hrdef]
    exact lintegral_gaussianWeight_sdiff_le_relative_four hn hσ hK hKc
      (hball (mem_ball_self one_pos))
  have hratio : μ (K \ A) / μ K ≤
      ENNReal.ofReal ((4 * Real.exp (-(15 : ℝ) / 2)) ^ n) := by
    have hK0 : μ K ≠ 0 := fun hz => hA0 (le_antisymm (hz ▸ measure_mono inter_subset_left) (by simp))
    rw [ENNReal.div_le_iff hK0 hKtop]
    exact htail
  rw [coolLaw_eq_uniformOn_gaussianWeight hσpos hAm hAball hAfin hi,
    coolLaw_eq_uniformOn_gaussianWeight hσpos hK hball hfin hi]
  exact (tvLe_condOn_subset hAm hK inter_subset_left hA0 hKtop).mono hratio

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.lintegral_gaussianWeight_sdiff_le_relative_four
#print axioms Arlib.MarkovChains.tvLe_coolLaw_inter_closedBall_relative_four
