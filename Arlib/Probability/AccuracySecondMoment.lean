/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Probability.AccuracyRecursion

/-!
# Second moments in the Cousins--Vempala accuracy recursion

This file proves the square analogue of the upper `U` recursion and isolates
the exact analytic/arithmetic inputs for its lower half.  Dependence of
`U_i²` and `V_(i+1)²` remains an explicit hypothesis, ready to be discharged
by a measurable-history factorisation and the inhomogeneous Markov theorem.

Applying `lem:cov-bd` at step `i` adds one dependence increment.  Consequently
the honest raw-product estimate is

`E(U_i² V_(i+1)²) ≤ (1 + 2ν α⁴ (i+1)) ∏_{j≤i+1} E(V_j²)`.

The paper prints `i` in both `eqn:u2-bound` and `eqn:uv2-bound`; that literal
pair does not follow from the displayed covariance recursion without deleting
the current step's covariance error.  The `i+1` form below is what the proof
establishes and is exactly what is needed to obtain the successor `u2` bound.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Set Real ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `E(V₁²) ⋯ E(Vᵢ²)`. -/
noncomputable def prefixSecondMean (μ : Measure Ω) (V : ℕ → Ω → ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.range i, ∫ ω, (V (j + 1) ω) ^ 2 ∂μ

@[simp] theorem prefixSecondMean_zero (μ : Measure Ω) (V : ℕ → Ω → ℝ) :
    prefixSecondMean μ V 0 = 1 := by
  simp [prefixSecondMean]

theorem prefixSecondMean_succ (μ : Measure Ω) (V : ℕ → Ω → ℝ) (i : ℕ) :
    prefixSecondMean μ V (i + 1) =
      prefixSecondMean μ V i * ∫ ω, (V (i + 1) ω) ^ 2 ∂μ := by
  simp [prefixSecondMean, Finset.prod_range_succ]

theorem prefixSecondMean_nonneg (V : ℕ → Ω → ℝ) (i : ℕ) :
    0 ≤ prefixSecondMean μ V i := by
  exact Finset.prod_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

/-- Jensen/Cauchy for one real observable, derived from nonnegativity of its
variance. -/
theorem sq_integral_le_integral_sq [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hXm : Measurable X) (hX2 : Integrable (fun ω => (X ω) ^ 2) μ) :
    (∫ ω, X ω ∂μ) ^ 2 ≤ ∫ ω, (X ω) ^ 2 ∂μ := by
  have hLp : MemLp X 2 μ :=
    (memLp_two_iff_integrable_sq hXm.aestronglyMeasurable).2 hX2
  have hv := variance_nonneg X μ
  rw [variance_eq_sub hLp] at hv
  exact sub_nonneg.mp hv

/-- The product of squared means is bounded by the product of second moments. -/
theorem prefixMean_sq_le_prefixSecondMean [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) (hVm : ∀ j, Measurable (V j))
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ) (i : ℕ) :
    (prefixMean μ V i) ^ 2 ≤ prefixSecondMean μ V i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [prefixMean_succ, prefixSecondMean_succ, mul_pow]
      exact mul_le_mul ih
        (sq_integral_le_integral_sq (hVm (i + 1)) (hV2 (i + 1)))
        (sq_nonneg _) (prefixSecondMean_nonneg V i)

/-- The square of `U_i` is capped by `α² ∏ E(V_j²)`. -/
theorem accuracyU_sq_le_cap [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {α : ℝ} (hα : 1 ≤ α)
    (hVm : ∀ j, Measurable (V j))
    (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ)
    (i : ℕ) (ω : Ω) :
    (accuracyU μ V α i ω) ^ 2 ≤ α ^ 2 * prefixSecondMean μ V i := by
  have hU0 := accuracyU_nonneg (μ := μ) V (le_trans zero_le_one hα) hV0 i ω
  have hU := accuracyU_le_cap (μ := μ) V hα i ω
  have hcap0 : 0 ≤ α * prefixMean μ V i :=
    mul_nonneg (le_trans zero_le_one hα) (prefixMean_nonneg V hV0 i)
  have hsquare : (accuracyU μ V α i ω) ^ 2 ≤
      (α * prefixMean μ V i) ^ 2 := (sq_le_sq₀ hU0 hcap0).2 hU
  calc
    (accuracyU μ V α i ω) ^ 2 ≤ (α * prefixMean μ V i) ^ 2 := hsquare
    _ = α ^ 2 * (prefixMean μ V i) ^ 2 := by ring
    _ ≤ α ^ 2 * prefixSecondMean μ V i := by
      gcongr
      exact prefixMean_sq_le_prefixSecondMean V hVm hV2 i

/-- The square of `U_i` is integrable by its deterministic cap. -/
theorem integrable_accuracyU_sq [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {α : ℝ} (hα : 1 ≤ α)
    (hVm : ∀ j, Measurable (V j))
    (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ) (i : ℕ) :
    Integrable (fun ω => (accuracyU μ V α i ω) ^ 2) μ := by
  refine Integrable.mono' (integrable_const (α ^ 2 * prefixSecondMean μ V i))
    ((measurable_accuracyU V α hVm i).pow_const 2).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact accuracyU_sq_le_cap V hα hVm hV0 hV2 i ω

/-- Square covariance with the source-shaped cap
`V_j² ≤ 2 α² E(V_j²)`.  The latter is the precise truncation consequence
needed to retain the paper's coefficient `2ν α⁴`. -/
theorem accuracyU_sq_mul_V_sq_covariance_le [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {α ν : ℝ} (hα : 1 ≤ α)
    (hVm : ∀ j, Measurable (V j))
    (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ)
    (hV2cap : ∀ j ω,
      (V j ω) ^ 2 ≤ 2 * α ^ 2 * ∫ z, (V j z) ^ 2 ∂μ)
    (i : ℕ)
    (hindepSq : NuIndep μ (fun ω => (accuracyU μ V α i ω) ^ 2)
      (fun ω => (V (i + 1) ω) ^ 2) ν) :
    |(∫ ω, (accuracyU μ V α i ω) ^ 2 * (V (i + 1) ω) ^ 2 ∂μ) -
        (∫ ω, (accuracyU μ V α i ω) ^ 2 ∂μ) *
          ∫ ω, (V (i + 1) ω) ^ 2 ∂μ|
      ≤ 2 * ν * α ^ 4 * prefixSecondMean μ V (i + 1) := by
  have hP20 := prefixSecondMean_nonneg (μ := μ) V i
  have hE20 : 0 ≤ ∫ ω, (V (i + 1) ω) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  let aU : ℝ := α ^ 2 * prefixSecondMean μ V i
  let bV : ℝ := 2 * α ^ 2 * ∫ z, (V (i + 1) z) ^ 2 ∂μ
  let f : ℝ → ℝ := fun x => min (max x 0) aU
  let g : ℝ → ℝ := fun x => min (max x 0) bV
  have haU : 0 ≤ aU := mul_nonneg (sq_nonneg _) hP20
  have hbV : 0 ≤ bV := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hE20
  have hfmeas : Measurable f := (measurable_id.max measurable_const).min measurable_const
  have hgmeas : Measurable g := (measurable_id.max measurable_const).min measurable_const
  have hcov := abs_integral_mul_sub_mul_integral_le hindepSq
    ((measurable_accuracyU V α hVm i).pow_const 2) ((hVm (i + 1)).pow_const 2)
    hfmeas hgmeas haU hbV
    (fun x => le_min (le_max_right _ _) haU) (fun x => min_le_right _ _)
    (fun x => le_min (le_max_right _ _) hbV) (fun x => min_le_right _ _)
  have hfactual : ∀ ω, f ((accuracyU μ V α i ω) ^ 2) =
      (accuracyU μ V α i ω) ^ 2 := by
    intro ω
    change min (max ((accuracyU μ V α i ω) ^ 2) 0) aU = _
    rw [max_eq_left (sq_nonneg _)]
    exact min_eq_left (by simpa [aU] using accuracyU_sq_le_cap V hα hVm hV0 hV2 i ω)
  have hgactual : ∀ ω, g ((V (i + 1) ω) ^ 2) = (V (i + 1) ω) ^ 2 := by
    intro ω
    change min (max ((V (i + 1) ω) ^ 2) 0) bV = _
    rw [max_eq_left (sq_nonneg _)]
    exact min_eq_left (by simpa [bV] using hV2cap (i + 1) ω)
  simp_rw [hfactual, hgactual] at hcov
  rw [prefixSecondMean_succ]
  dsimp [aU, bV] at hcov
  nlinarith

/-- The honest `eqn:uv2-bound`: the raw square product at step `i` pays the
new covariance increment and therefore carries `(i+1)`. -/
theorem integral_accuracyU_sq_mul_V_sq_le [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {α ν : ℝ} (hα : 1 ≤ α)
    (hVm : ∀ j, Measurable (V j))
    (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ)
    (hV2cap : ∀ j ω,
      (V j ω) ^ 2 ≤ 2 * α ^ 2 * ∫ z, (V j z) ^ 2 ∂μ)
    (hindepSq : ∀ i, NuIndep μ (fun ω => (accuracyU μ V α i ω) ^ 2)
      (fun ω => (V (i + 1) ω) ^ 2) ν)
    (i : ℕ)
    (hU2 : (∫ ω, (accuracyU μ V α i ω) ^ 2 ∂μ) ≤
      (1 + 2 * ν * α ^ 4 * (i : ℝ)) * prefixSecondMean μ V i)
    :
    (∫ ω, (accuracyU μ V α i ω) ^ 2 * (V (i + 1) ω) ^ 2 ∂μ) ≤
      (1 + 2 * ν * α ^ 4 * ((i + 1 : ℕ) : ℝ)) *
        prefixSecondMean μ V (i + 1) := by
  have hcov := accuracyU_sq_mul_V_sq_covariance_le V hα hVm hV0 hV2 hV2cap i
    (hindepSq i)
  rw [abs_le] at hcov
  have hE20 : 0 ≤ ∫ ω, (V (i + 1) ω) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hU2 hE20
  rw [prefixSecondMean_succ] at hcov ⊢
  push_cast
  calc
    (∫ ω, (accuracyU μ V α i ω) ^ 2 * (V (i + 1) ω) ^ 2 ∂μ)
        ≤ (∫ ω, (accuracyU μ V α i ω) ^ 2 ∂μ) *
            (∫ ω, (V (i + 1) ω) ^ 2 ∂μ) +
              2 * ν * α ^ 4 *
                (prefixSecondMean μ V i * ∫ ω, (V (i + 1) ω) ^ 2 ∂μ) := by
          linarith [hcov.2]
    _ ≤ (1 + 2 * ν * α ^ 4 * (i : ℝ)) * prefixSecondMean μ V i *
            (∫ ω, (V (i + 1) ω) ^ 2 ∂μ) +
              2 * ν * α ^ 4 *
                (prefixSecondMean μ V i * ∫ ω, (V (i + 1) ω) ^ 2 ∂μ) :=
          add_le_add hmul le_rfl
    _ = (1 + 2 * ν * α ^ 4 * ((i : ℝ) + 1)) *
          (prefixSecondMean μ V i * ∫ ω, (V (i + 1) ω) ^ 2 ∂μ) := by ring

/-- **`eqn:u2-bound`.** Nat induction using the raw square-product estimate. -/
theorem integral_accuracyU_sq_le [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {α ν : ℝ} (hα : 1 ≤ α)
    (hVm : ∀ j, Measurable (V j))
    (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hV2 : ∀ j, Integrable (fun ω => (V j ω) ^ 2) μ)
    (hV2cap : ∀ j ω,
      (V j ω) ^ 2 ≤ 2 * α ^ 2 * ∫ z, (V j z) ^ 2 ∂μ)
    (hindepSq : ∀ i, NuIndep μ (fun ω => (accuracyU μ V α i ω) ^ 2)
      (fun ω => (V (i + 1) ω) ^ 2) ν)
    (i : ℕ) :
    (∫ ω, (accuracyU μ V α i ω) ^ 2 ∂μ) ≤
      (1 + 2 * ν * α ^ 4 * (i : ℝ)) * prefixSecondMean μ V i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hraw := integral_accuracyU_sq_mul_V_sq_le V hα hVm hV0 hV2 hV2cap
        hindepSq i ih
      have hUsq := integrable_accuracyU_sq V hα hVm hV0 hV2 (i + 1)
      have hVraw : Integrable
          (fun ω => (accuracyU μ V α i ω) ^ 2 * (V (i + 1) ω) ^ 2) μ :=
        (hV2 (i + 1)).bdd_mul
          ((measurable_accuracyU V α hVm i).pow_const 2).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            exact accuracyU_sq_le_cap V hα hVm hV0 hV2 i ω)
      refine (integral_mono hUsq hVraw fun ω => ?_).trans hraw
      simpa [mul_pow] using (sq_le_sq₀
        (accuracyU_nonneg V (le_trans zero_le_one hα) hV0 (i + 1) ω)
        (mul_nonneg (accuracyU_nonneg V (le_trans zero_le_one hα) hV0 i ω)
          (hV0 (i + 1) ω))).2
            (min_le_left (accuracyU μ V α i ω * V (i + 1) ω)
              (α * prefixMean μ V (i + 1)))

/-! ## Phase moment ratios and the remaining arithmetic -/

/-- Product of the per-phase second-moment ratios. -/
noncomputable def prefixMomentRatio (c : ℕ → ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.range i, c (j + 1)

@[simp] theorem prefixMomentRatio_zero (c : ℕ → ℝ) : prefixMomentRatio c 0 = 1 := by
  simp [prefixMomentRatio]

theorem prefixMomentRatio_succ (c : ℕ → ℝ) (i : ℕ) :
    prefixMomentRatio c (i + 1) = prefixMomentRatio c i * c (i + 1) := by
  simp [prefixMomentRatio, Finset.prod_range_succ]

/-- Explicit per-phase hypotheses `E(V_j²) ≤ c_j E(V_j)²` tensorise into
the corresponding prefix bound; no independence is used here. -/
theorem prefixSecondMean_le_mul_prefixMean_sq
    (V : ℕ → Ω → ℝ) (c : ℕ → ℝ)
    (hV0 : ∀ j ω, 0 ≤ V j ω) (hc0 : ∀ j, 0 ≤ c j)
    (hratio : ∀ j, (∫ ω, (V j ω) ^ 2 ∂μ) ≤ c j * (∫ ω, V j ω ∂μ) ^ 2)
    (i : ℕ) :
    prefixSecondMean μ V i ≤ prefixMomentRatio c i * (prefixMean μ V i) ^ 2 := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [prefixSecondMean_succ, prefixMomentRatio_succ, prefixMean_succ, mul_pow]
      have hE20 : 0 ≤ ∫ ω, (V (i + 1) ω) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
      have hC0 : 0 ≤ prefixMomentRatio c i :=
        Finset.prod_nonneg fun j _ => hc0 (j + 1)
      have hP0 : 0 ≤ prefixMean μ V i := prefixMean_nonneg V hV0 i
      exact (mul_le_mul ih (hratio (i + 1)) hE20
        (mul_nonneg hC0 (sq_nonneg _))).trans_eq (by ring)

/-- This is the exact scalar condition needed to turn the raw second-moment
penalty into the paper's factor `2`.  The schedule proof must establish
`C * ∏ c_j ≤ 2`; the probabilistic recursion has no stronger hidden need. -/
theorem rawSecond_arithmetic_of_phaseRatios
    (V : ℕ → Ω → ℝ) (c : ℕ → ℝ) {C : ℝ}
    (hV0 : ∀ j ω, 0 ≤ V j ω) (hc0 : ∀ j, 0 ≤ c j)
    (hratio : ∀ j, (∫ ω, (V j ω) ^ 2 ∂μ) ≤ c j * (∫ ω, V j ω ∂μ) ^ 2)
    {i : ℕ} (hC0 : 0 ≤ C) (hscalar : C * prefixMomentRatio c i ≤ 2) :
    C * prefixSecondMean μ V i ≤ 2 * (prefixMean μ V i) ^ 2 := by
  calc
    C * prefixSecondMean μ V i ≤
        C * (prefixMomentRatio c i * (prefixMean μ V i) ^ 2) := by
      gcongr
      exact prefixSecondMean_le_mul_prefixMean_sq V c hV0 hc0 hratio i
    _ = (C * prefixMomentRatio c i) * (prefixMean μ V i) ^ 2 := by ring
    _ ≤ 2 * (prefixMean μ V i) ^ 2 :=
      mul_le_mul_of_nonneg_right hscalar (sq_nonneg _)

/-- Once the raw second moment is at most twice the squared prefix mean,
`lem:exp-bd` charges exactly the paper's decrement `prefixMean/(2α)`. -/
theorem rawSecond_penalty_le_half {α P R : ℝ} (hα : 0 < α) (hP : 0 < P)
    (hR : R ≤ 2 * P ^ 2) :
    R / (4 * (α * P)) ≤ P / (2 * α) := by
  rw [div_le_iff₀ (by positivity)]
  calc
    R ≤ 2 * P ^ 2 := hR
    _ = P / (2 * α) * (4 * (α * P)) := by field_simp; ring

/-! ## Exact lower-recursion interface -/

/-- The first lower step is precisely `lem:exp-bd` applied to
`U_i V_(i+1)`, with truncation level `α prefixMean(i+1)`. -/
theorem integral_accuracyU_succ_ge_of_raw_second [IsProbabilityMeasure μ]
    (V : ℕ → Ω → ℝ) {α : ℝ} (hα : 1 ≤ α)
    (hVm : ∀ j, Measurable (V j))
    (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hVcap : ∀ j ω, V j ω ≤ 2 * α * ∫ z, V j z ∂μ)
    (i : ℕ) (hlevel : 0 < α * prefixMean μ V (i + 1))
    (hraw2 : Integrable
      (fun ω => (accuracyU μ V α i ω * V (i + 1) ω) ^ 2) μ) :
    (∫ ω, accuracyU μ V α i ω * V (i + 1) ω ∂μ) -
        (∫ ω, (accuracyU μ V α i ω * V (i + 1) ω) ^ 2 ∂μ) /
          (4 * (α * prefixMean μ V (i + 1)))
      ≤ ∫ ω, accuracyU μ V α (i + 1) ω ∂μ := by
  have hraw : Integrable (fun ω => accuracyU μ V α i ω * V (i + 1) ω) μ := by
    have hUi := integrable_accuracyU (μ := μ) V hα hVm hV0 i
    have hVi := integrable_V_of_le_two_mul (μ := μ) V hVm hV0 hVcap (i + 1)
    exact hVi.bdd_mul (measurable_accuracyU V α hVm i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (accuracyU_nonneg V (le_trans zero_le_one hα) hV0 i ω)]
        exact accuracyU_le_cap V hα i ω)
  exact expect_min_ge hlevel
    (fun ω => mul_nonneg (accuracyU_nonneg V (le_trans zero_le_one hα) hV0 i ω)
      (hV0 (i + 1) ω))
    ((measurable_accuracyU V α hVm i).mul (hVm (i + 1))) hraw hraw2

/-!
To turn the preceding exact inequality into the paper's decrement
`prefixMean / (2α)`, the remaining arithmetic assumption is exactly

`C * prefixSecondMean(i+1) ≤ 2 * prefixMean(i+1)^2`,

where `C = 1 + 2ν α⁴(i+1)` is the honest raw-second-moment coefficient.
This is where the phase moment ratios
`E(V_j²) ≤ c_j E(V_j)²` and the schedule inequalities on `k,m,α,ν` enter.
They are deliberately not hidden inside the generic probability recursion.
-/

#print axioms sq_integral_le_integral_sq
#print axioms prefixMean_sq_le_prefixSecondMean
#print axioms accuracyU_sq_le_cap
#print axioms accuracyU_sq_mul_V_sq_covariance_le
#print axioms integral_accuracyU_sq_mul_V_sq_le
#print axioms integral_accuracyU_sq_le
#print axioms prefixSecondMean_le_mul_prefixMean_sq
#print axioms rawSecond_arithmetic_of_phaseRatios
#print axioms rawSecond_penalty_le_half
#print axioms integral_accuracyU_succ_ge_of_raw_second

end Arlib.GaussianCooling
