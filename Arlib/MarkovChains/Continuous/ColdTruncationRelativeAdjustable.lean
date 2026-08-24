/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.MarkovChains.Continuous.ColdTruncationRelative

/-!
# Adjustable-radius relative Gaussian truncation

For `q > 1`, dilating the portion of a convex body outside `q * σ * √n` by `1/q`
sends it back into the body.  The Jacobian and Gaussian-density comparison give the relative
tail

`(q * exp (-(q^2 - 1)/2))^n`.

This simultaneously specializes to the existing radius-two and radius-four constants.
-/

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

namespace Arlib.MarkovChains

open Arlib.GaussianCooling

variable {n : Nat}

/-- Relative Gaussian tail outside the adjustable radius `q*σ*√n`. -/
theorem lintegral_gaussianWeight_sdiff_le_relative_adjustable
    (_hn : 1 <= n) {q σ : Real} (hq : 1 < q) (hσ : 0 < σ)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K) (hKc : Convex Real K)
    (h0K : (0 : EuclideanSpace Real (Fin n)) ∈ K) :
    ∫⁻ x in K \ closedBall (0 : EuclideanSpace Real (Fin n))
        (q * σ * Real.sqrt n), gaussianWeight (σ ^ 2) x
      <= ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n) *
          ∫⁻ x in K, gaussianWeight (σ ^ 2) x := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hqne : q ≠ 0 := ne_of_gt hq0
  have hqdiff : 0 < q ^ 2 - 1 := by nlinarith
  set E : Set (EuclideanSpace Real (Fin n)) :=
    K \ closedBall (0 : EuclideanSpace Real (Fin n)) (q * σ * Real.sqrt n) with hEdef
  set A : Set (EuclideanSpace Real (Fin n)) := (1 / q : Real) • E with hAdef
  have hEm : MeasurableSet E := hK.diff measurableSet_closedBall
  have hAm : MeasurableSet A := measurableSet_smul_set hEm (by positivity)
  have hAK : A ⊆ K := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hKc.smul_mem_of_zero_mem h0K hx.1
      ⟨by positivity, (div_le_one hq0).2 hq.le⟩
  have hEA : q • A = E := by
    rw [hAdef, smul_smul]
    field_simp
    simp
  have hsqrt : Real.sqrt (n : Real) ^ 2 = (n : Real) :=
    Real.sq_sqrt (Nat.cast_nonneg n)
  have hpoint : ∀ y ∈ A,
      gaussianWeight (σ ^ 2 / q ^ 2) y
        <= ENNReal.ofReal (Real.exp (-(q ^ 2 - 1) * (n : Real) / 2)) *
            gaussianWeight (σ ^ 2) y := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxnorm : q * σ * Real.sqrt n < ‖x‖ := by
      have hout := hx.2
      rw [mem_closedBall_zero_iff, not_le] at hout
      exact hout
    have hynorm : σ * Real.sqrt n < ‖(1 / q : Real) • x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : Real) < 1 / q)]
      rw [one_div, inv_mul_eq_div, lt_div_iff₀ hq0]
      nlinarith
    have hy2 : σ ^ 2 * (n : Real) < ‖(1 / q : Real) • x‖ ^ 2 := by
      have hy2' :=
        (sq_lt_sq₀ (mul_nonneg hσ.le (Real.sqrt_nonneg _)) (norm_nonneg _)).2 hynorm
      rw [mul_pow, hsqrt] at hy2'
      exact hy2'
    have hcoef : (q ^ 2 - 1) * (n : Real) / 2 <=
        (q ^ 2 - 1) * ‖(1 / q : Real) • x‖ ^ 2 / (2 * σ ^ 2) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : Real) < 2)
        (by positivity : (0 : Real) < 2 * σ ^ 2)]
      nlinarith
    have hexp :
        Real.exp (-(q ^ 2 - 1) * ‖(1 / q : Real) • x‖ ^ 2 / (2 * σ ^ 2)) <=
          Real.exp (-(q ^ 2 - 1) * (n : Real) / 2) := by
      apply Real.exp_le_exp.2
      have hneg := neg_le_neg hcoef
      calc
        -(q ^ 2 - 1) * ‖(1 / q : Real) • x‖ ^ 2 / (2 * σ ^ 2) =
            -((q ^ 2 - 1) * ‖(1 / q : Real) • x‖ ^ 2 / (2 * σ ^ 2)) := by ring
        _ <= -((q ^ 2 - 1) * (n : Real) / 2) := hneg
        _ = -(q ^ 2 - 1) * (n : Real) / 2 := by ring
    unfold gaussianWeight gaussianWeightReal
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    have hsplit : -‖(1 / q : Real) • x‖ ^ 2 / (2 * (σ ^ 2 / q ^ 2)) =
        -(q ^ 2 - 1) * ‖(1 / q : Real) • x‖ ^ 2 / (2 * σ ^ 2) +
          -‖(1 / q : Real) • x‖ ^ 2 / (2 * σ ^ 2) := by
      field_simp [ne_of_gt hσ, hqne]
      ring
    rw [hsplit, Real.exp_add]
    exact mul_le_mul_of_nonneg_right hexp (Real.exp_pos _).le
  have htail : (∫⁻ x in E, gaussianWeight (σ ^ 2) x) =
      ENNReal.ofReal (q ^ n) * ∫⁻ y in A, gaussianWeight (σ ^ 2 / q ^ 2) y := by
    rw [← hEA]
    exact lintegral_gaussianWeight_smul_set hAm hq0 (σ ^ 2)
  rw [htail]
  calc
    ENNReal.ofReal (q ^ n) * ∫⁻ y in A, gaussianWeight (σ ^ 2 / q ^ 2) y <=
        ENNReal.ofReal (q ^ n) *
          (ENNReal.ofReal (Real.exp (-(q ^ 2 - 1) * (n : Real) / 2)) *
            ∫⁻ y in A, gaussianWeight (σ ^ 2) y) := by
      gcongr
      calc
        ∫⁻ y in A, gaussianWeight (σ ^ 2 / q ^ 2) y <=
            ∫⁻ y in A,
              ENNReal.ofReal (Real.exp (-(q ^ 2 - 1) * (n : Real) / 2)) *
                gaussianWeight (σ ^ 2) y := by
          refine lintegral_mono_ae ?_
          filter_upwards [self_mem_ae_restrict hAm] with y hy using hpoint y hy
        _ = ENNReal.ofReal (Real.exp (-(q ^ 2 - 1) * (n : Real) / 2)) *
              ∫⁻ y in A, gaussianWeight (σ ^ 2) y := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ <= ENNReal.ofReal (q ^ n) *
          (ENNReal.ofReal (Real.exp (-(q ^ 2 - 1) * (n : Real) / 2)) *
            ∫⁻ y in K, gaussianWeight (σ ^ 2) y) := by
      gcongr
    _ = ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n) *
          ∫⁻ y in K, gaussianWeight (σ ^ 2) y := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [mul_pow]
      have he : Real.exp (-(q ^ 2 - 1) * (n : Real) / 2) =
          Real.exp (-(q ^ 2 - 1) / 2) ^ n := by
        calc
          Real.exp (-(q ^ 2 - 1) * (n : Real) / 2) =
              Real.exp ((n : Real) * (-(q ^ 2 - 1) / 2)) := by congr 1; ring
          _ = Real.exp (-(q ^ 2 - 1) / 2) ^ n := Real.exp_nat_mul _ _
      rw [he]

/-- TV form of the adjustable-radius relative tail bound. -/
theorem tvLe_coolLaw_inter_closedBall_relative_adjustable
    (hn : 1 <= n) {q : Real} (hq : 1 < q) {m : Nat} {σsq : Nat -> Real}
    (hσpos : ∀ j, 0 < σsq j) {σ : Real} (hσ : 0 < σ)
    {K : Set (EuclideanSpace Real (Fin n))} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m) (hσsq : σsq i = σ ^ 2)
    (hr : 1 <= q * σ * Real.sqrt n) :
    Arlib.TVLe
      (coolLaw m σsq (K ∩ closedBall (0 : EuclideanSpace Real (Fin n))
        (q * σ * Real.sqrt n)) i)
      (coolLaw m σsq K i)
      (ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n)) := by
  set r : Real := q * σ * Real.sqrt n with hrdef
  set A : Set (EuclideanSpace Real (Fin n)) := K ∩ closedBall 0 r with hAdef
  set μ : Measure (EuclideanSpace Real (Fin n)) :=
    (volume : Measure (EuclideanSpace Real (Fin n))).withDensity (gaussianWeight (σsq i))
      with hμdef
  have hAm : MeasurableSet A := hK.inter measurableSet_closedBall
  have hAball : ball (0 : EuclideanSpace Real (Fin n)) 1 ⊆ A := by
    rw [hAdef]
    exact unitBall_subset_inter_closedBall hball (hrdef ▸ hr)
  have hAfin : volume A ≠ ⊤ := by
    rw [hAdef]
    exact volume_inter_closedBall_ne_top K r
  have hμapply : ∀ S : Set (EuclideanSpace Real (Fin n)), MeasurableSet S ->
      μ S = ∫⁻ x in S, gaussianWeight (σsq i) x := fun S hS => withDensity_apply _ hS
  have hA0 : μ A ≠ 0 := by
    rw [hμapply A hAm]
    intro hz
    have hle := le_lintegral_gaussianWeight_of_unitBall_subset (hσpos i) hAball
    rw [hz, le_zero_iff, mul_eq_zero] at hle
    rcases hle with h1 | h2
    · exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' h1
    · exact (measure_ball_pos (volume : Measure (EuclideanSpace Real (Fin n))) 0 one_pos).ne' h2
  have hKtop : μ K ≠ ⊤ := by
    rw [hμapply K hK]
    exact lintegral_gaussianWeight_ne_top_of_univ (hσpos i) K
  have htail : μ (K \ A) <=
      ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n) * μ K := by
    rw [hμapply _ (hK.diff hAm), hμapply K hK, hAdef, Set.sdiff_self_inter, hσsq,
      hrdef]
    exact lintegral_gaussianWeight_sdiff_le_relative_adjustable hn hq hσ hK hKc
      (hball (mem_ball_self one_pos))
  have hratio : μ (K \ A) / μ K <=
      ENNReal.ofReal ((q * Real.exp (-(q ^ 2 - 1) / 2)) ^ n) := by
    have hK0 : μ K ≠ 0 := fun hz =>
      hA0 (le_antisymm (hz ▸ measure_mono inter_subset_left) (by simp))
    rw [ENNReal.div_le_iff hK0 hKtop]
    exact htail
  rw [coolLaw_eq_uniformOn_gaussianWeight hσpos hAm hAball hAfin hi,
    coolLaw_eq_uniformOn_gaussianWeight hσpos hK hball hfin hi]
  exact (tvLe_condOn_subset hAm hK inter_subset_left hA0 hKtop).mono hratio

end Arlib.MarkovChains

#print axioms Arlib.MarkovChains.lintegral_gaussianWeight_sdiff_le_relative_adjustable
#print axioms Arlib.MarkovChains.tvLe_coolLaw_inter_closedBall_relative_adjustable
