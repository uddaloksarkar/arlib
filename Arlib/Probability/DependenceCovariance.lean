/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Probability.DeltaIndependence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Bounded covariance from event dependence

This closes the remaining analytic part of Cousins--Vempala's `lem:cov-bd`.
The paper's coefficient is represented in the repository by
`GaussianCooling.NuIndep`: `NuIndep μ X Y ν` says exactly that the supremum of
the event-rectangle defects defining `μ(X,Y)` is at most `ν`.

`NuIndep.comp` is `lem:fn-indep`, and
`nuIndep_compProd_of_tvLe` is the Markov mixing bridge.  The theorem below adds
the full bounded covariance inequality, using one outer layer-cake integral and
the already-proved indicator-factor case.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Set Real ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ## The numerical coefficient from the paper -/

/-- A measurable event, used to make the two suprema in the paper's definition
ordinary suprema over types. -/
abbrev MeasurableEvent (α : Type*) [MeasurableSpace α] :=
  {A : Set α // MeasurableSet A}

/-- The defect of one measurable event rectangle. -/
noncomputable def eventDependenceDefect
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) (X : Ω → α) (Y : Ω → β)
    (p : MeasurableEvent α × MeasurableEvent β) : ℝ :=
  |μ.real (X ⁻¹' p.1.1 ∩ Y ⁻¹' p.2.1) -
    μ.real (X ⁻¹' p.1.1) * μ.real (Y ⁻¹' p.2.1)|

/-- The paper's dependence coefficient

`μ(X,Y) = sup_{A,B} |P(X∈A,Y∈B)-P(X∈A)P(Y∈B)|`.

The repository's older `NuIndep μ X Y ν` is the proposition that this
coefficient is at most `ν`; `nuIndep_iff_dependenceCoeff_le` proves the exact
equivalence below. -/
noncomputable def dependenceCoeff
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  sSup (Set.range (eventDependenceDefect μ X Y))

private theorem eventDependenceDefect_le_one
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β}
    (p : MeasurableEvent α × MeasurableEvent β) :
    eventDependenceDefect μ X Y p ≤ 1 := by
  have hjoint0 : 0 ≤ μ.real (X ⁻¹' p.1.1 ∩ Y ⁻¹' p.2.1) := measureReal_nonneg
  have hX0 : 0 ≤ μ.real (X ⁻¹' p.1.1) := measureReal_nonneg
  have hY0 : 0 ≤ μ.real (Y ⁻¹' p.2.1) := measureReal_nonneg
  have hjoint1 : μ.real (X ⁻¹' p.1.1 ∩ Y ⁻¹' p.2.1) ≤ 1 := by
    rw [← probReal_univ (μ := μ)]
    exact measureReal_mono (subset_univ _) (measure_ne_top μ _)
  have hX1 : μ.real (X ⁻¹' p.1.1) ≤ 1 := by
    rw [← probReal_univ (μ := μ)]
    exact measureReal_mono (subset_univ _) (measure_ne_top μ _)
  have hY1 : μ.real (Y ⁻¹' p.2.1) ≤ 1 := by
    rw [← probReal_univ (μ := μ)]
    exact measureReal_mono (subset_univ _) (measure_ne_top μ _)
  rw [eventDependenceDefect, abs_le]
  constructor <;> nlinarith [mul_nonneg hX0 hY0, mul_le_one₀ hX1 hY0 hY1]

private theorem dependenceDefects_bddAbove
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β} :
    BddAbove (Set.range (eventDependenceDefect μ X Y)) := by
  refine ⟨1, ?_⟩
  rintro z ⟨p, rfl⟩
  exact eventDependenceDefect_le_one p

/-- The numerical supremum is exactly the event-wise `NuIndep` API already
used by the cooling development. -/
theorem nuIndep_iff_dependenceCoeff_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β} {ν : ℝ} :
    NuIndep μ X Y ν ↔ dependenceCoeff μ X Y ≤ ν := by
  constructor
  · intro h
    refine csSup_le (Set.range_nonempty _) ?_
    rintro z ⟨⟨A, B⟩, rfl⟩
    exact h A.1 B.1 A.2 B.2
  · intro h A B hA hB
    have hmem : eventDependenceDefect μ X Y
        (⟨A, hA⟩, ⟨B, hB⟩) ∈ Set.range (eventDependenceDefect μ X Y) :=
      ⟨(⟨A, hA⟩, ⟨B, hB⟩), rfl⟩
    exact (le_csSup dependenceDefects_bddAbove hmem).trans h

/-- **`lem:fn-indep`, numerical form.** Measurable postprocessing cannot
increase the paper's dependence coefficient. -/
theorem dependenceCoeff_comp_le
    {α β α' β' : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace α'] [MeasurableSpace β'] [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → β} {f : α → α'} {g : β → β'}
    (hf : Measurable f) (hg : Measurable g) :
    dependenceCoeff μ (f ∘ X) (g ∘ Y) ≤ dependenceCoeff μ X Y := by
  rw [← nuIndep_iff_dependenceCoeff_le]
  exact (nuIndep_iff_dependenceCoeff_le.mpr le_rfl).comp hf hg

/-- Numerical form of the Markov mixing bridge: if every conditional next-step
law is within `ν` of one fixed target, the past/next dependence coefficient is
at most `ν`, with no factor loss. -/
theorem dependenceCoeff_compProd_le_of_tvLe
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {ρ : Measure α} [IsProbabilityMeasure ρ]
    {κ : ProbabilityTheory.Kernel α β} [ProbabilityTheory.IsMarkovKernel κ]
    {τ : Measure β} [IsProbabilityMeasure τ] {ν : ℝ≥0∞} (hν : ν ≠ ⊤)
    (hmix : ∀ a, TVLe (κ a) τ ν) :
    dependenceCoeff (ρ ⊗ₘ κ) (Prod.fst : α × β → α) (Prod.snd : α × β → β)
      ≤ ν.toReal :=
  nuIndep_iff_dependenceCoeff_le.mp (nuIndep_compProd_of_tvLe hν hmix)

section Unit

variable [IsProbabilityMeasure μ]

/-- A weighted layer-cake identity.  It is the outer layer cake needed for
`lem:cov-bd`: the weight is absorbed into a finite density measure. -/
private theorem integral_mul_eq_integral_Ioc_indicator
    {F G : Ω → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hF0 : ∀ ω, 0 ≤ F ω) (hF1 : ∀ ω, F ω ≤ 1)
    (hG0 : ∀ ω, 0 ≤ G ω) (hG1 : ∀ ω, G ω ≤ 1) :
    (∫ ω, F ω * G ω ∂μ) =
      ∫ t in Ioc (0 : ℝ) 1, ∫ ω, {ω | t ≤ F ω}.indicator G ω ∂μ := by
  let νm : Measure Ω := μ.withDensity fun ω => ENNReal.ofReal (G ω)
  have hGint : Integrable G μ :=
    Arlib.integrable_of_forall_mem_Icc hG hG0 hG1
  letI : IsFiniteMeasure νm :=
    isFiniteMeasure_withDensity_ofReal hGint.hasFiniteIntegral
  have hFintν : Integrable F νm :=
    Arlib.integrable_of_forall_mem_Icc hF hF0 hF1
  have hdensity : ∀ S : Set Ω, MeasurableSet S →
      νm.real S = ∫ ω, S.indicator G ω ∂μ := by
    intro S hS
    calc
      νm.real S = ∫ ω, S.indicator (fun _ => (1 : ℝ)) ω ∂νm :=
        (integral_indicator_one hS).symm
      _ = ∫ ω, (ENNReal.ofReal (G ω)).toReal •
          S.indicator (fun _ => (1 : ℝ)) ω ∂μ := by
        exact integral_withDensity_eq_integral_toReal_smul
          (hG.ennreal_ofReal) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _
      _ = ∫ ω, S.indicator G ω ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        by_cases hω : ω ∈ S
        · simp [Set.indicator_of_mem hω, ENNReal.toReal_ofReal (hG0 ω)]
        · simp [Set.indicator_of_notMem hω]
  have hleft : (∫ ω, F ω * G ω ∂μ) = ∫ ω, F ω ∂νm := by
    rw [integral_withDensity_eq_integral_toReal_smul
      (hG.ennreal_ofReal) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards with ω
    rw [ENNReal.toReal_ofReal (hG0 ω)]
    simp only [smul_eq_mul]
    ring
  rw [hleft, hFintν.integral_eq_integral_Ioc_meas_le
    (Filter.Eventually.of_forall hF0) (Filter.Eventually.of_forall hF1)]
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  exact hdensity {ω | t ≤ F ω} (measurableSet_le measurable_const hF)

/-- `lem:cov-bd` for observables taking values in `[0,1]`. -/
theorem abs_integral_mul_sub_mul_integral_le_of_unit
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {X : Ω → α} {Y : Ω → β} {ν : ℝ}
    (hindep : NuIndep μ X Y ν) (hX : Measurable X) (hY : Measurable Y)
    {f : α → ℝ} {g : β → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    |(∫ ω, f (X ω) * g (Y ω) ∂μ) -
        (∫ ω, f (X ω) ∂μ) * ∫ ω, g (Y ω) ∂μ| ≤ ν := by
  let F : Ω → ℝ := fun ω => f (X ω)
  let G : Ω → ℝ := fun ω => g (Y ω)
  have hFm : Measurable F := hf.comp hX
  have hGm : Measurable G := hg.comp hY
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => hf0 (X ω)
  have hF1 : ∀ ω, F ω ≤ 1 := fun ω => hf1 (X ω)
  have hG0 : ∀ ω, 0 ≤ G ω := fun ω => hg0 (Y ω)
  have hG1 : ∀ ω, G ω ≤ 1 := fun ω => hg1 (Y ω)
  have hprod := integral_mul_eq_integral_Ioc_indicator (μ := μ) hFm hGm hF0 hF1 hG0 hG1
  have hcake : (∫ ω, F ω ∂μ) =
      ∫ t in Ioc (0 : ℝ) 1, μ.real {ω | t ≤ F ω} :=
    (Arlib.integrable_of_forall_mem_Icc hFm hF0 hF1).integral_eq_integral_Ioc_meas_le
      (Filter.Eventually.of_forall hF0) (Filter.Eventually.of_forall hF1)
  have htail := Arlib.integrableOn_measureReal_tail μ F
  have hconst := htail.mul_const (∫ ω, G ω ∂μ)
  have hGint : Integrable G μ := Arlib.integrable_of_forall_mem_Icc hGm hG0 hG1
  have hwind : IntegrableOn
      (fun t : ℝ => ∫ ω, {ω | t ≤ F ω}.indicator G ω ∂μ) (Ioc 0 1) volume := by
    have hanti : Antitone (fun t : ℝ => ∫ ω, {ω | t ≤ F ω}.indicator G ω ∂μ) := by
      intro s t hst
      have hs : MeasurableSet {ω | s ≤ F ω} := measurableSet_le measurable_const hFm
      have ht : MeasurableSet {ω | t ≤ F ω} := measurableSet_le measurable_const hFm
      refine integral_mono (hGint.indicator ht) (hGint.indicator hs) fun ω => ?_
      by_cases hωt : t ≤ F ω
      · have hωs : s ≤ F ω := hst.trans hωt
        rw [Set.indicator_of_mem (show ω ∈ {ω | t ≤ F ω} from hωt),
          Set.indicator_of_mem (show ω ∈ {ω | s ≤ F ω} from hωs)]
      · rw [Set.indicator_of_notMem (show ω ∉ {ω | t ≤ F ω} from hωt)]
        by_cases hωs : s ≤ F ω
        · rw [Set.indicator_of_mem (show ω ∈ {ω | s ≤ F ω} from hωs)]
          exact hG0 ω
        · rw [Set.indicator_of_notMem (show ω ∉ {ω | s ≤ F ω} from hωs)]
    have hwind_meas : Measurable
        (fun t : ℝ => ∫ ω, {ω | t ≤ F ω}.indicator G ω ∂μ) := hanti.measurable
    refine Integrable.mono' (integrableOn_const (by simp [Real.volume_Ioc]) :
      IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 1) volume)
      hwind_meas.aestronglyMeasurable ?_
    filter_upwards with t
    have ht : MeasurableSet {ω | t ≤ F ω} := measurableSet_le measurable_const hFm
    have hnonneg : 0 ≤ ∫ ω, {ω | t ≤ F ω}.indicator G ω ∂μ :=
      integral_nonneg fun ω => Set.indicator_nonneg (fun z _ => hG0 z) ω
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    calc
      (∫ ω, {ω | t ≤ F ω}.indicator G ω ∂μ) ≤ ∫ ω, G ω ∂μ :=
        integral_mono (hGint.indicator ht) hGint fun ω => by
          by_cases hω : t ≤ F ω
          · rw [Set.indicator_of_mem (show ω ∈ {ω | t ≤ F ω} from hω)]
          · rw [Set.indicator_of_notMem (show ω ∉ {ω | t ≤ F ω} from hω)]
            exact hG0 ω
      _ ≤ ∫ _ω, (1 : ℝ) ∂μ := integral_mono hGint (integrable_const 1) hG1
      _ = 1 := by simp
  change |(∫ ω, F ω * G ω ∂μ) - (∫ ω, F ω ∂μ) * ∫ ω, G ω ∂μ| ≤ ν
  rw [hprod, hcake, ← integral_mul_const]
  rw [← integral_sub]
  · calc
      |∫ t in Ioc (0 : ℝ) 1,
          ((∫ ω, {ω | t ≤ F ω}.indicator G ω ∂μ) -
            μ.real {ω | t ≤ F ω} * ∫ ω, G ω ∂μ)|
          ≤ ∫ t in Ioc (0 : ℝ) 1,
              |(∫ ω, {ω | t ≤ F ω}.indicator G ω ∂μ) -
                μ.real {ω | t ≤ F ω} * ∫ ω, G ω ∂μ| :=
            abs_integral_le_integral_abs
      _ ≤ ∫ _t in Ioc (0 : ℝ) 1, ν := by
        refine setIntegral_mono_on (hwind.sub hconst).abs
          (integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc ?_
        intro t ht
        have hA : MeasurableSet {x : α | t ≤ f x} :=
          measurableSet_le measurable_const hf
        have hkey := abs_integral_indicator_mul_sub_le hindep hX hY hA hg hg0 hg1
        have hindicator :
            (fun ω => {ω | t ≤ F ω}.indicator (fun _ => (1 : ℝ)) ω * G ω) =
              fun ω => {ω | t ≤ F ω}.indicator G ω := by
          funext ω
          by_cases hω : t ≤ F ω <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
        rw [← hindicator]
        simpa [F, G, Set.preimage_setOf_eq] using hkey
      _ = ν := by rw [setIntegral_const]; simp
  · exact hwind
  · exact hconst

end Unit

/-- **Cousins--Vempala `lem:cov-bd`.** If `X` and `Y` are `ν`-independent and
the nonnegative observables `f(X)` and `g(Y)` are bounded respectively by
`a` and `b`, then their covariance is at most `a b ν`. -/
theorem abs_integral_mul_sub_mul_integral_le
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β} {ν a b : ℝ}
    (hindep : NuIndep μ X Y ν) (hX : Measurable X) (hY : Measurable Y)
    {f : α → ℝ} {g : β → ℝ} (hf : Measurable f) (hg : Measurable g)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf0 : ∀ x, 0 ≤ f x) (hfa : ∀ x, f x ≤ a)
    (hg0 : ∀ y, 0 ≤ g y) (hgb : ∀ y, g y ≤ b) :
    |(∫ ω, f (X ω) * g (Y ω) ∂μ) -
        (∫ ω, f (X ω) ∂μ) * ∫ ω, g (Y ω) ∂μ| ≤ a * b * ν := by
  rcases ha.eq_or_lt with rfl | ha
  · have hfz : ∀ x, f x = 0 := fun x => le_antisymm (hfa x) (hf0 x)
    simp_rw [hfz]
    simp
  rcases hb.eq_or_lt with rfl | hb
  · have hgz : ∀ y, g y = 0 := fun y => le_antisymm (hgb y) (hg0 y)
    simp_rw [hgz]
    simp
  have hunit := abs_integral_mul_sub_mul_integral_le_of_unit hindep hX hY
    (hf.div_const a) (hg.div_const b)
    (fun x => div_nonneg (hf0 x) ha.le) (fun x => (div_le_one ha).2 (hfa x))
    (fun y => div_nonneg (hg0 y) hb.le) (fun y => (div_le_one hb).2 (hgb y))
  have hab : 0 < a * b := mul_pos ha hb
  have heq :
      ((∫ ω, (f (X ω) / a) * (g (Y ω) / b) ∂μ) -
          (∫ ω, f (X ω) / a ∂μ) * ∫ ω, g (Y ω) / b ∂μ) =
        ((∫ ω, f (X ω) * g (Y ω) ∂μ) -
          (∫ ω, f (X ω) ∂μ) * ∫ ω, g (Y ω) ∂μ) / (a * b) := by
    rw [integral_div, integral_div]
    have hmul : (fun ω => (f (X ω) / a) * (g (Y ω) / b)) =
        fun ω => (f (X ω) * g (Y ω)) / (a * b) := by
      funext ω
      field_simp
    rw [hmul, integral_div]
    ring
  rw [heq, abs_div, abs_of_pos hab, div_le_iff₀ hab] at hunit
  simpa [mul_comm] using hunit

/-- The literal numerical-coefficient form of `lem:cov-bd`. -/
theorem abs_integral_mul_sub_mul_integral_le_dependenceCoeff
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β} {a b : ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    {f : α → ℝ} {g : β → ℝ} (hf : Measurable f) (hg : Measurable g)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf0 : ∀ x, 0 ≤ f x) (hfa : ∀ x, f x ≤ a)
    (hg0 : ∀ y, 0 ≤ g y) (hgb : ∀ y, g y ≤ b) :
    |(∫ ω, f (X ω) * g (Y ω) ∂μ) -
        (∫ ω, f (X ω) ∂μ) * ∫ ω, g (Y ω) ∂μ|
      ≤ a * b * dependenceCoeff μ X Y :=
  abs_integral_mul_sub_mul_integral_le
    (nuIndep_iff_dependenceCoeff_le.mpr le_rfl) hX hY hf hg ha hb hf0 hfa hg0 hgb

#print axioms nuIndep_iff_dependenceCoeff_le
#print axioms dependenceCoeff_comp_le
#print axioms dependenceCoeff_compProd_le_of_tvLe
#print axioms abs_integral_mul_sub_mul_integral_le_of_unit
#print axioms abs_integral_mul_sub_mul_integral_le
#print axioms abs_integral_mul_sub_mul_integral_le_dependenceCoeff

end Arlib.GaussianCooling
