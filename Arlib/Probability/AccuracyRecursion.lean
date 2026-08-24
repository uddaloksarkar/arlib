/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Probability.DependenceCovariance

/-!
# The `U`/`V` recursion in Cousins--Vempala's accuracy proof

This file formalises the upper half of the recursion following `lem:delta-ind`
and `lem:cov-bd`.  Indices are paper-shaped: `prefixMean μ V i` is
`E(V₁)⋯E(Vᵢ)`, and the successor step uses `V (i+1)`.

The hypothesis

`V j ≤ 2 α E(V j)`

is the exact bound used in `eqn:uv-bound`: in the paper it follows from
`V_j ≤ α E(W̄_j)` and `E(W̄_j) ≤ 2 E(V_j)`.  Keeping it explicit cleanly
separates this generic recursion from the earlier truncation calculation.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Set Real ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- `E(V₁) ⋯ E(Vᵢ)`. -/
noncomputable def prefixMean (μ : Measure Ω) (V : ℕ → Ω → ℝ) (i : ℕ) : ℝ :=
  ∏ j ∈ Finset.range i, ∫ ω, V (j + 1) ω ∂μ

@[simp] theorem prefixMean_zero (μ : Measure Ω) (V : ℕ → Ω → ℝ) :
    prefixMean μ V 0 = 1 := by
  simp [prefixMean]

theorem prefixMean_succ (μ : Measure Ω) (V : ℕ → Ω → ℝ) (i : ℕ) :
    prefixMean μ V (i + 1) = prefixMean μ V i * ∫ ω, V (i + 1) ω ∂μ := by
  simp [prefixMean, Finset.prod_range_succ]

/-- The paper's recursively truncated product:

`U₀ = 1` and
`Uᵢ₊₁ = min (Uᵢ Vᵢ₊₁) (α E(V₁)⋯E(Vᵢ₊₁))`. -/
noncomputable def accuracyU (μ : Measure Ω) (V : ℕ → Ω → ℝ) (α : ℝ) :
    ℕ → Ω → ℝ
  | 0 => fun _ => 1
  | i + 1 => fun ω =>
      min (accuracyU μ V α i ω * V (i + 1) ω) (α * prefixMean μ V (i + 1))

@[simp] theorem accuracyU_zero (V : ℕ → Ω → ℝ) (α : ℝ) (ω : Ω) :
    accuracyU μ V α 0 ω = 1 := by
  rfl

@[simp] theorem accuracyU_succ (V : ℕ → Ω → ℝ) (α : ℝ) (i : ℕ) (ω : Ω) :
    accuracyU μ V α (i + 1) ω =
      min (accuracyU μ V α i ω * V (i + 1) ω) (α * prefixMean μ V (i + 1)) := by
  rfl

/-- Every prefix mean is nonnegative when the `Vᵢ` are nonnegative. -/
theorem prefixMean_nonneg (V : ℕ → Ω → ℝ) (hV0 : ∀ j ω, 0 ≤ V j ω) (i : ℕ) :
    0 ≤ prefixMean μ V i := by
  refine Finset.prod_nonneg fun j _ => integral_nonneg fun ω => hV0 (j + 1) ω

/-- Measurability of the recursively truncated products. -/
theorem measurable_accuracyU (V : ℕ → Ω → ℝ) (α : ℝ)
    (hVm : ∀ j, Measurable (V j)) (i : ℕ) : Measurable (accuracyU μ V α i) := by
  induction i with
  | zero => exact measurable_const
  | succ i ih => exact (ih.mul (hVm (i + 1))).min measurable_const

/-- Pointwise nonnegativity of `Uᵢ`. -/
theorem accuracyU_nonneg (V : ℕ → Ω → ℝ) {α : ℝ} (hα : 0 ≤ α)
    (hV0 : ∀ j ω, 0 ≤ V j ω) (i : ℕ) (ω : Ω) :
    0 ≤ accuracyU μ V α i ω := by
  induction i with
  | zero => simp
  | succ i ih =>
      simp only [accuracyU_succ]
      exact le_min (mul_nonneg ih (hV0 (i + 1) ω))
        (mul_nonneg hα (prefixMean_nonneg V hV0 (i + 1)))

/-- The cap in the definition bounds every `Uᵢ`; `α ≥ 1` also handles `U₀`. -/
theorem accuracyU_le_cap (V : ℕ → Ω → ℝ) {α : ℝ} (hα : 1 ≤ α)
    (i : ℕ) (ω : Ω) :
    accuracyU μ V α i ω ≤ α * prefixMean μ V i := by
  cases i with
  | zero => simpa using hα
  | succ i => exact min_le_right _ _

/-- The explicit self-relative bound used after truncating `W̄ᵢ` to `Vᵢ`
makes each `Vᵢ` integrable. -/
theorem integrable_V_of_le_two_mul (V : ℕ → Ω → ℝ) {α : ℝ}
    [IsProbabilityMeasure μ] (hVm : ∀ j, Measurable (V j))
    (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hVcap : ∀ j ω, V j ω ≤ 2 * α * ∫ z, V j z ∂μ) (j : ℕ) :
    Integrable (V j) μ := by
  refine Integrable.mono' (integrable_const (2 * α * ∫ z, V j z ∂μ))
    (hVm j).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (hV0 j ω)]
  exact hVcap j ω

/-- Boundedness and measurability make every `Uᵢ` integrable. -/
theorem integrable_accuracyU (V : ℕ → Ω → ℝ) {α : ℝ} [IsProbabilityMeasure μ]
    (hα : 1 ≤ α) (hVm : ∀ j, Measurable (V j))
    (hV0 : ∀ j ω, 0 ≤ V j ω) (i : ℕ) :
    Integrable (accuracyU μ V α i) μ := by
  have hα0 : 0 ≤ α := le_trans zero_le_one hα
  refine Integrable.mono' (integrable_const (α * prefixMean μ V i))
    (measurable_accuracyU V α hVm i).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (accuracyU_nonneg V hα0 hV0 i ω)]
  exact accuracyU_le_cap V hα i ω

/-- **`eqn:uv-bound`.** If `Uᵢ` and `Vᵢ₊₁` are `ν`-independent, then the
bounded-covariance lemma and the two truncation caps give

`|E(UᵢVᵢ₊₁) - E(Uᵢ)E(Vᵢ₊₁)| ≤ 2 ν α² E(V₁)⋯E(Vᵢ₊₁)`.
-/
theorem accuracyU_mul_V_covariance_le (V : ℕ → Ω → ℝ) {α ν : ℝ}
    [IsProbabilityMeasure μ] (hα : 1 ≤ α)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hVcap : ∀ j ω, V j ω ≤ 2 * α * ∫ z, V j z ∂μ)
    (i : ℕ) (hindep : NuIndep μ (accuracyU μ V α i) (V (i + 1)) ν) :
    |(∫ ω, accuracyU μ V α i ω * V (i + 1) ω ∂μ) -
        (∫ ω, accuracyU μ V α i ω ∂μ) * ∫ ω, V (i + 1) ω ∂μ|
      ≤ 2 * ν * α ^ 2 * prefixMean μ V (i + 1) := by
  have hα0 : 0 ≤ α := le_trans zero_le_one hα
  have hP0 := prefixMean_nonneg (μ := μ) V hV0 i
  have hE0 : 0 ≤ ∫ ω, V (i + 1) ω ∂μ := integral_nonneg fun ω => hV0 (i + 1) ω
  let aU : ℝ := α * prefixMean μ V i
  let bV : ℝ := 2 * α * ∫ z, V (i + 1) z ∂μ
  let f : ℝ → ℝ := fun x => min (max x 0) aU
  let g : ℝ → ℝ := fun x => min (max x 0) bV
  have haU : 0 ≤ aU := mul_nonneg hα0 hP0
  have hbV : 0 ≤ bV := mul_nonneg (mul_nonneg (by norm_num) hα0) hE0
  have hfmeas : Measurable f := (measurable_id.max measurable_const).min measurable_const
  have hgmeas : Measurable g := (measurable_id.max measurable_const).min measurable_const
  have hf0 : ∀ x, 0 ≤ f x := fun x => le_min (le_max_right _ _) haU
  have hfa : ∀ x, f x ≤ aU := fun x => min_le_right _ _
  have hg0 : ∀ x, 0 ≤ g x := fun x => le_min (le_max_right _ _) hbV
  have hgb : ∀ x, g x ≤ bV := fun x => min_le_right _ _
  have hcov := abs_integral_mul_sub_mul_integral_le hindep
    (measurable_accuracyU V α hVm i) (hVm (i + 1)) hfmeas hgmeas
    haU hbV hf0 hfa hg0 hgb
  have hfactual : ∀ ω, f (accuracyU μ V α i ω) = accuracyU μ V α i ω := by
    intro ω
    change min (max (accuracyU μ V α i ω) 0) aU = accuracyU μ V α i ω
    rw [max_eq_left (accuracyU_nonneg V hα0 hV0 i ω)]
    exact min_eq_left (by simpa [aU] using accuracyU_le_cap (μ := μ) V hα i ω)
  have hgactual : ∀ ω, g (V (i + 1) ω) = V (i + 1) ω := by
    intro ω
    change min (max (V (i + 1) ω) 0) bV = V (i + 1) ω
    rw [max_eq_left (hV0 (i + 1) ω)]
    exact min_eq_left (by simpa [bV] using hVcap (i + 1) ω)
  simp_rw [hfactual, hgactual] at hcov
  rw [prefixMean_succ]
  dsimp [aU, bV] at hcov
  nlinarith

/-- **`eqn:u-upperbound`.** The upper expectation recursion obtained from
`eqn:uv-bound`, by induction on the number of phases. -/
theorem integral_accuracyU_le (V : ℕ → Ω → ℝ) {α ν : ℝ}
    [IsProbabilityMeasure μ] (hα : 1 ≤ α)
    (hVm : ∀ j, Measurable (V j)) (hV0 : ∀ j ω, 0 ≤ V j ω)
    (hVcap : ∀ j ω, V j ω ≤ 2 * α * ∫ z, V j z ∂μ)
    (hindep : ∀ i, NuIndep μ (accuracyU μ V α i) (V (i + 1)) ν)
    (i : ℕ) :
    (∫ ω, accuracyU μ V α i ω ∂μ) ≤
      (1 + 2 * ν * α ^ 2 * (i : ℝ)) * prefixMean μ V i := by
  induction i with
  | zero => simp
  | succ i ih =>
      have hUi := integrable_accuracyU (μ := μ) V hα hVm hV0 i
      have hUs := integrable_accuracyU (μ := μ) V hα hVm hV0 (i + 1)
      have hVi := integrable_V_of_le_two_mul (μ := μ) V hVm hV0 hVcap (i + 1)
      have hprod : Integrable (fun ω => accuracyU μ V α i ω * V (i + 1) ω) μ :=
        hVi.bdd_mul (measurable_accuracyU V α hVm i).aestronglyMeasurable
          (Filter.Eventually.of_forall fun ω => by
            rw [Real.norm_eq_abs,
              abs_of_nonneg (accuracyU_nonneg V (le_trans zero_le_one hα) hV0 i ω)]
            exact accuracyU_le_cap V hα i ω)
      have hmin : (∫ ω, accuracyU μ V α (i + 1) ω ∂μ) ≤
          ∫ ω, accuracyU μ V α i ω * V (i + 1) ω ∂μ := by
        refine integral_mono hUs hprod fun ω => ?_
        exact min_le_left _ _
      have hcov := accuracyU_mul_V_covariance_le (μ := μ) V hα hVm hV0 hVcap i (hindep i)
      have hcovUpper :
          (∫ ω, accuracyU μ V α i ω * V (i + 1) ω ∂μ) ≤
            (∫ ω, accuracyU μ V α i ω ∂μ) * (∫ ω, V (i + 1) ω ∂μ) +
              2 * ν * α ^ 2 * prefixMean μ V (i + 1) := by
        rw [abs_le] at hcov
        linarith
      have hE0 : 0 ≤ ∫ ω, V (i + 1) ω ∂μ := integral_nonneg fun ω => hV0 (i + 1) ω
      have hmul := mul_le_mul_of_nonneg_right ih hE0
      rw [prefixMean_succ]
      calc
        (∫ ω, accuracyU μ V α (i + 1) ω ∂μ)
            ≤ ∫ ω, accuracyU μ V α i ω * V (i + 1) ω ∂μ := hmin
        _ ≤ (∫ ω, accuracyU μ V α i ω ∂μ) * (∫ ω, V (i + 1) ω ∂μ) +
              2 * ν * α ^ 2 *
                (prefixMean μ V i * ∫ ω, V (i + 1) ω ∂μ) := by
              simpa [prefixMean_succ] using hcovUpper
        _ ≤ (1 + 2 * ν * α ^ 2 * ((i + 1 : ℕ) : ℝ)) *
              (prefixMean μ V i * ∫ ω, V (i + 1) ω ∂μ) := by
              push_cast
              nlinarith [hmul]

#print axioms prefixMean_nonneg
#print axioms measurable_accuracyU
#print axioms accuracyU_nonneg
#print axioms accuracyU_le_cap
#print axioms integrable_V_of_le_two_mul
#print axioms integrable_accuracyU
#print axioms accuracyU_mul_V_covariance_le
#print axioms integral_accuracyU_le

end Arlib.GaussianCooling
