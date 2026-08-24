/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Probability.AccuracySecondMoment

/-!
# Corrected lower recursion for the Cousins--Vempala accuracy proof

The recursion as defined in the paper truncates already at `U₁`.  Charging the
proved truncation and covariance errors at every successor therefore gives

`E(U_i) ≥ (1 - i/α) E(V₁)⋯E(V_i)`.

The paper displays `1-(i-1)/α`; that stronger base at `i=1` would require
`U₁=V₁` almost surely, which does not follow from its definitions.  This file
uses the source recursion literally and records the corrected `i/α` loss.

Likewise, the raw square estimate uses the honest `(i+1)` coefficient proved
in `AccuracySecondMoment`.  Both corrections change only constant arithmetic;
the eventual source choice of `α` is kept as an explicit scalar obligation.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Set Real ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A single uniform scalar condition for all lower-recursion steps before
`m`.  The first clause allocates half of the `1/α` decrement to covariance; the
second allocates the other half to truncation using the corrected raw square
coefficient. -/
def AccuracyLowerScalar (μ : Measure Ω) (V : ℕ → Ω → ℝ)
    (α ν : ℝ) (m : ℕ) : Prop :=
  2 * ν * α ^ 2 ≤ 1 / (2 * α) ∧
  ∀ i < m,
    (1 + 2 * ν * α ^ 4 * ((i + 1 : ℕ) : ℝ)) * prefixSecondMean μ V (i + 1)
      ≤ 2 * (prefixMean μ V (i + 1)) ^ 2

/-- Positive phase means give a positive prefix product. -/
theorem prefixMean_pos (V : ℕ → Ω → ℝ)
    (hEpos : ∀ j, 0 < ∫ ω, V j ω ∂μ) (i : ℕ) :
    0 < prefixMean μ V i := by
  exact Finset.prod_pos fun j _ => hEpos (j + 1)

/-- Square-integrability of the raw product `U_i V_(i+1)`. -/
theorem integrable_accuracyU_mul_V_sq [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {α : ℝ} (hα : 1 ≤ α)
    (hVm : ∀ j, Measurable (V j))
    (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ) (i : ℕ) :
    Integrable (fun ω => (accuracyU μ V α i ω * V (i + 1) ω) ^ 2) μ := by
  have hUsq := integrable_accuracyU_sq (μ := μ) V hα hVm hV0 hV2 i
  have hVsq := hV2 (i + 1)
  have hprod : Integrable
      (fun ω => (accuracyU μ V α i ω) ^ 2 * (V (i + 1) ω) ^ 2) μ :=
    hVsq.bdd_mul
      ((measurable_accuracyU V α hVm i).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact accuracyU_sq_le_cap V hα hVm hV0 hV2 i ω)
  simpa [mul_pow] using hprod

/-- One corrected lower step.  The two halves of `AccuracyLowerScalar` combine
the covariance and truncation losses into exactly `prefixMean/α`. -/
theorem integral_accuracyU_succ_ge_sub [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {α ν : ℝ} (hα : 1 ≤ α)
    (hVm : ∀ j, Measurable (V j))
    (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hEpos : ∀ j, 0 < ∫ ω, V j ω ∂μ)
    (hVcap : ∀ j ω, V j ω ≤ 2 * α * ∫ z, V j z ∂μ)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ)
    (hV2cap : ∀ j ω,
      (V j ω) ^ 2 ≤ 2 * α ^ 2 * ∫ z, (V j z) ^ 2 ∂μ)
    (hindep : ∀ i, NuIndep μ (accuracyU μ V α i) (V (i + 1)) ν)
    (hindepSq : ∀ i, NuIndep μ (fun ω => (accuracyU μ V α i ω) ^ 2)
      (fun ω => (V (i + 1) ω) ^ 2) ν)
    {m i : ℕ} (hi : i < m) (hscalar : AccuracyLowerScalar μ V α ν m) :
    (∫ ω, accuracyU μ V α i ω ∂μ) * (∫ ω, V (i + 1) ω ∂μ) -
        prefixMean μ V (i + 1) / α
      ≤ ∫ ω, accuracyU μ V α (i + 1) ω ∂μ := by
  have hα0 : 0 < α := lt_of_lt_of_le zero_lt_one hα
  have hPpos : 0 < prefixMean μ V (i + 1) := prefixMean_pos V hEpos (i + 1)
  have hlevel : 0 < α * prefixMean μ V (i + 1) := mul_pos hα0 hPpos
  have hraw2int := integrable_accuracyU_mul_V_sq V hα hVm hV0 hV2 i
  have htrunc := integral_accuracyU_succ_ge_of_raw_second V hα hVm hV0 hVcap i
    hlevel hraw2int
  have hU2 := integral_accuracyU_sq_le (μ := μ) V hα hVm hV0 hV2 hV2cap hindepSq i
  have hraw2 := integral_accuracyU_sq_mul_V_sq_le (μ := μ) V hα hVm hV0 hV2
    hV2cap hindepSq i hU2
  have hraw2' :
      (∫ ω, (accuracyU μ V α i ω * V (i + 1) ω) ^ 2 ∂μ) ≤
        2 * (prefixMean μ V (i + 1)) ^ 2 := by
    rw [show (fun ω => (accuracyU μ V α i ω * V (i + 1) ω) ^ 2) =
        fun ω => (accuracyU μ V α i ω) ^ 2 * (V (i + 1) ω) ^ 2 by
      funext ω; ring]
    exact hraw2.trans (hscalar.2 i hi)
  have hpenalty := rawSecond_penalty_le_half hα0 hPpos hraw2'
  have hcov := accuracyU_mul_V_covariance_le (μ := μ) V hα hVm hV0 hVcap i
    (hindep i)
  rw [abs_le] at hcov
  have hP0 := hPpos.le
  have hcovBudget :
      2 * ν * α ^ 2 * prefixMean μ V (i + 1) ≤
        prefixMean μ V (i + 1) / (2 * α) := by
    calc
      2 * ν * α ^ 2 * prefixMean μ V (i + 1)
          ≤ (1 / (2 * α)) * prefixMean μ V (i + 1) :=
            mul_le_mul_of_nonneg_right hscalar.1 hP0
      _ = prefixMean μ V (i + 1) / (2 * α) := by ring
  have hrawLower :
      (∫ ω, accuracyU μ V α i ω ∂μ) * (∫ ω, V (i + 1) ω ∂μ) -
          prefixMean μ V (i + 1) / (2 * α)
        ≤ ∫ ω, accuracyU μ V α i ω * V (i + 1) ω ∂μ := by
    linarith [hcov.1, hcovBudget]
  calc
    (∫ ω, accuracyU μ V α i ω ∂μ) * (∫ ω, V (i + 1) ω ∂μ) -
          prefixMean μ V (i + 1) / α
        = ((∫ ω, accuracyU μ V α i ω ∂μ) * (∫ ω, V (i + 1) ω ∂μ) -
            prefixMean μ V (i + 1) / (2 * α)) -
              prefixMean μ V (i + 1) / (2 * α) := by ring
    _ ≤ (∫ ω, accuracyU μ V α i ω * V (i + 1) ω ∂μ) -
          prefixMean μ V (i + 1) / (2 * α) := sub_le_sub_right hrawLower _
    _ ≤ (∫ ω, accuracyU μ V α i ω * V (i + 1) ω ∂μ) -
          (∫ ω, (accuracyU μ V α i ω * V (i + 1) ω) ^ 2 ∂μ) /
            (4 * (α * prefixMean μ V (i + 1))) := sub_le_sub_left hpenalty _
    _ ≤ ∫ ω, accuracyU μ V α (i + 1) ω ∂μ := htrunc

/-- Corrected inductive lower expectation, uniformly through phase `m`. -/
theorem integral_accuracyU_ge [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {α ν : ℝ} (hα : 1 ≤ α)
    (hVm : ∀ j, Measurable (V j))
    (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hEpos : ∀ j, 0 < ∫ ω, V j ω ∂μ)
    (hVcap : ∀ j ω, V j ω ≤ 2 * α * ∫ z, V j z ∂μ)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ)
    (hV2cap : ∀ j ω,
      (V j ω) ^ 2 ≤ 2 * α ^ 2 * ∫ z, (V j z) ^ 2 ∂μ)
    (hindep : ∀ i, NuIndep μ (accuracyU μ V α i) (V (i + 1)) ν)
    (hindepSq : ∀ i, NuIndep μ (fun ω => (accuracyU μ V α i ω) ^ 2)
      (fun ω => (V (i + 1) ω) ^ 2) ν)
    {m i : ℕ} (hi : i ≤ m) (hscalar : AccuracyLowerScalar μ V α ν m) :
    (1 - (i : ℝ) / α) * prefixMean μ V i ≤
      ∫ ω, accuracyU μ V α i ω ∂μ := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hα0 : 0 < α := lt_of_lt_of_le zero_lt_one hα
      have him : i < m := Nat.lt_of_succ_le hi
      have hstep := integral_accuracyU_succ_ge_sub V hα hVm hV0 hEpos hVcap hV2
        hV2cap hindep hindepSq him hscalar
      have hE0 : 0 ≤ ∫ ω, V (i + 1) ω ∂μ := (hEpos (i + 1)).le
      have hmul := mul_le_mul_of_nonneg_right (ih (Nat.le_of_lt him)) hE0
      rw [prefixMean_succ]
      push_cast
      calc
        (1 - ((i : ℝ) + 1) / α) *
              (prefixMean μ V i * ∫ ω, V (i + 1) ω ∂μ)
            = ((1 - (i : ℝ) / α) * prefixMean μ V i) *
                (∫ ω, V (i + 1) ω ∂μ) -
                  (prefixMean μ V i * ∫ ω, V (i + 1) ω ∂μ) / α := by
                    field_simp [ne_of_gt hα0]
                    ring
        _ ≤ (∫ ω, accuracyU μ V α i ω ∂μ) *
                (∫ ω, V (i + 1) ω ∂μ) -
                  (prefixMean μ V i * ∫ ω, V (i + 1) ω ∂μ) / α :=
              sub_le_sub_right hmul _
        _ ≤ ∫ ω, accuracyU μ V α (i + 1) ω ∂μ := by
          simpa [prefixMean_succ] using hstep

/-- Mean sandwich together with a caller-selected relative second-moment
constant `q`.  This is the exact package a subsequent Chebyshev argument needs.
The final scalar premise is pure schedule arithmetic. -/
theorem accuracyU_mean_and_secondMoment [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {α ν q : ℝ} (hα : 1 ≤ α) (hq : 0 ≤ q)
    (hVm : ∀ j, Measurable (V j))
    (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hEpos : ∀ j, 0 < ∫ ω, V j ω ∂μ)
    (hVcap : ∀ j ω, V j ω ≤ 2 * α * ∫ z, V j z ∂μ)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ)
    (hV2cap : ∀ j ω,
      (V j ω) ^ 2 ≤ 2 * α ^ 2 * ∫ z, (V j z) ^ 2 ∂μ)
    (hindep : ∀ i, NuIndep μ (accuracyU μ V α i) (V (i + 1)) ν)
    (hindepSq : ∀ i, NuIndep μ (fun ω => (accuracyU μ V α i ω) ^ 2)
      (fun ω => (V (i + 1) ω) ^ 2) ν)
    {m i : ℕ} (hi : i ≤ m) (hscalar : AccuracyLowerScalar μ V α ν m)
    (hLpos : 0 < 1 - (i : ℝ) / α)
    (hsecondScalar :
      (1 + 2 * ν * α ^ 4 * (i : ℝ)) * prefixSecondMean μ V i ≤
        q * (1 - (i : ℝ) / α) ^ 2 * (prefixMean μ V i) ^ 2) :
    ((1 - (i : ℝ) / α) * prefixMean μ V i ≤
        ∫ ω, accuracyU μ V α i ω ∂μ) ∧
    ((∫ ω, accuracyU μ V α i ω ∂μ) ≤
        (1 + 2 * ν * α ^ 2 * (i : ℝ)) * prefixMean μ V i) ∧
    ((∫ ω, (accuracyU μ V α i ω) ^ 2 ∂μ) ≤
        q * (∫ ω, accuracyU μ V α i ω ∂μ) ^ 2) := by
  have hlower := integral_accuracyU_ge V hα hVm hV0 hEpos hVcap hV2 hV2cap
    hindep hindepSq hi hscalar
  have hupper := integral_accuracyU_le (μ := μ) V hα hVm hV0 hVcap hindep i
  have hU2 := integral_accuracyU_sq_le (μ := μ) V hα hVm hV0 hV2 hV2cap hindepSq i
  refine ⟨hlower, hupper, ?_⟩
  have hLP0 : 0 ≤ (1 - (i : ℝ) / α) * prefixMean μ V i :=
    mul_nonneg hLpos.le (prefixMean_pos V hEpos i).le
  have hEU0 : 0 ≤ ∫ ω, accuracyU μ V α i ω ∂μ :=
    integral_nonneg fun ω => accuracyU_nonneg V (le_trans zero_le_one hα) hV0 i ω
  have hsquares := (sq_le_sq₀ hLP0 hEU0).2 hlower
  calc
    (∫ ω, (accuracyU μ V α i ω) ^ 2 ∂μ)
        ≤ (1 + 2 * ν * α ^ 4 * (i : ℝ)) * prefixSecondMean μ V i := hU2
    _ ≤ q * (1 - (i : ℝ) / α) ^ 2 * (prefixMean μ V i) ^ 2 := hsecondScalar
    _ = q * (((1 - (i : ℝ) / α) * prefixMean μ V i) ^ 2) := by ring
    _ ≤ q * (∫ ω, accuracyU μ V α i ω ∂μ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquares hq

#print axioms integrable_accuracyU_mul_V_sq
#print axioms integral_accuracyU_succ_ge_sub
#print axioms integral_accuracyU_ge
#print axioms accuracyU_mean_and_secondMoment

end Arlib.GaussianCooling
