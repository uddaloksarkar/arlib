/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.MarkovChains.Continuous.EuclideanLSCurve

/-!
# Warm Euclidean LS curve recurrence
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- A concave exact-mass LS curve can be selected simultaneously at every time. -/
theorem exists_concave_exactMassLSCurve_family_euclidean {n : Nat} [NeZero n]
    (pi : Measure (EuclideanSpace Real (Fin n))) [IsProbabilityMeasure pi]
    (hpi : pi ≪ volume) {P : Kernel (EuclideanSpace Real (Fin n))
      (EuclideanSpace Real (Fin n))} [IsMarkovKernel P]
    (hrev : IsReversible P pi) {h : EuclideanSpace Real (Fin n) → Real}
    (hhm : Measurable h) (hhLp : MemLp h 2 pi) :
    ∃ F : Nat → Real → Real,
      (∀ t, ConcaveOn Real (Icc (0 : Real) 1) (F t)) ∧
      ∀ t, IsExactMassLSCurve pi (fun x => markovIter P h t x - 1) (F t) := by
  have hex : ∀ t : Nat, ∃ Ft : Real → Real,
      ConcaveOn Real (Icc (0 : Real) 1) Ft ∧
      IsExactMassLSCurve pi (fun x => markovIter P h t x - 1) Ft := by
    intro t
    apply exists_concave_exactMassLSCurve_euclidean pi hpi
      ((measurable_markovIter P hhm t).sub_const 1)
    exact (memLp_markovIter hrev.invariant hhm hhLp t).integrable (by norm_num) |>.sub
      (integrable_const (1 : Real))
  choose F hF using hex
  exact ⟨F, fun t => (hF t).1, fun t => (hF t).2⟩

/-- The exact actual-flow midpoint recurrence for consecutive warm LS curves. -/
theorem exactMassLSCurve_oneStep_actualFlow {n : Nat} [NeZero n]
    {P : Kernel (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n))}
    [IsMarkovKernel P] {pi : Measure (EuclideanSpace Real (Fin n))}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    {h : EuclideanSpace Real (Fin n) → Real} (hhm : Measurable h) (hhLp : MemLp h 2 pi)
    {F : Nat → Real → Real}
    (hcurve : ∀ t, IsExactMassLSCurve pi (fun z => markovIter (lazy P) h t z - 1) (F t))
    (t : Nat) {x : Real} (hx : x ∈ Icc (0 : Real) 1) :
    ∃ S : Set (EuclideanSpace Real (Fin n)), MeasurableSet S ∧
      pi S = ENNReal.ofReal x ∧
      let q := (flow (lazy P) pi S Sᶜ).toReal
      (x - 2 * q ∈ Icc (0 : Real) 1) ∧ (x + 2 * q ∈ Icc (0 : Real) 1) ∧
        F (t + 1) x ≤ (F t (x - 2 * q) + F t (x + 2 * q)) / 2 := by
  obtain ⟨S, hS, hSx, hFx, -⟩ := hcurve (t + 1) x hx
  let g := markovOp (lazy P) (S.indicator fun _ => (1 : Real))
  let u := lazyProfileLower S g
  let v := lazyProfileUpper S g
  let q := (flow (lazy P) pi S Sᶜ).toReal
  have hb := lazy_markovOp_indicator_profile_bounds P hS
  have huw := fun z => lazyProfile_weights_mem_Icc hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 z
  have hum : Measurable u := measurable_lazyProfileLower hS
    (measurable_markovOp (lazy P) (measurable_const.indicator hS))
  have hvm : Measurable v := measurable_lazyProfileUpper hS
    (measurable_markovOp (lazy P) (measurable_const.indicator hS))
  have hm := integral_lazyProfileLowerUpper_markovOp_indicator (isReversible_lazy hrev) hS
  have hxreal : (pi S).toReal = x := by
    rw [hSx, ENNReal.toReal_ofReal hx.1]
  have humass : ∫ z, u z ∂pi = x - 2 * q := by
    simpa [u, g, q, hxreal] using hm.1
  have hvmass : ∫ z, v z ∂pi = x + 2 * q := by
    simpa [v, g, q, hxreal] using hm.2
  have hui : Integrable u pi := Integrable.of_bound hum.aestronglyMeasurable 1
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (huw z).1.1]
      exact (huw z).1.2)
  have hvi : Integrable v pi := Integrable.of_bound hvm.aestronglyMeasurable 1
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (huw z).2.1]
      exact (huw z).2.2)
  have hxu : x - 2 * q ∈ Icc (0 : Real) 1 := by
    rw [← humass]
    constructor
    · exact integral_nonneg (fun z => (huw z).1.1)
    · calc
        ∫ z, u z ∂pi ≤ ∫ _z, (1 : Real) ∂pi :=
          integral_mono hui (integrable_const 1) (fun z => (huw z).1.2)
        _ = 1 := by simp
  have hxv : x + 2 * q ∈ Icc (0 : Real) 1 := by
    rw [← hvmass]
    constructor
    · exact integral_nonneg (fun z => (huw z).2.1)
    · calc
        ∫ z, v z ∂pi ≤ ∫ _z, (1 : Real) ∂pi :=
          integral_mono hvi (integrable_const 1) (fun z => (huw z).2.2)
        _ = 1 := by simp
  obtain ⟨U, hU, hUa, hFU, huMax⟩ := hcurve t (x - 2 * q) hxu
  obtain ⟨V, hV, hVa, hFV, hvMax⟩ := hcurve t (x + 2 * q) hxv
  have huBound : ∫ z, (markovIter (lazy P) h t z - 1) * u z ∂pi ≤
      ∫ z in U, (markovIter (lazy P) h t z - 1) ∂pi := by
    rw [← hFU]
    exact huMax u hum (fun z => (huw z).1.1) (fun z => (huw z).1.2) humass
  have hvBound : ∫ z, (markovIter (lazy P) h t z - 1) * v z ∂pi ≤
      ∫ z in V, (markovIter (lazy P) h t z - 1) ∂pi := by
    rw [← hFV]
    exact hvMax v hvm (fun z => (huw z).2.1) (fun z => (huw z).2.2) hvmass
  have hfint : Integrable (fun z => markovIter (lazy P) h t z - 1) pi :=
    ((memLp_markovIter (isReversible_lazy hrev).invariant hhm hhLp t).integrable
      (by norm_num)).sub (integrable_const (1 : Real))
  have hmid' := integral_mul_le_average_setIntegrals_of_weight_bounds hfint hum hvm
      (fun z => (huw z).1.1) (fun z => (huw z).1.2)
      (fun z => (huw z).2.1) (fun z => (huw z).2.2)
      lazyProfile_decomposition huBound hvBound
  have hmid : ∫ z, (markovIter (lazy P) h t z - 1) * g z ∂pi ≤
      (F t (x - 2 * q) + F t (x + 2 * q)) / 2 := by
    simpa [hFU, hFV] using hmid'
  refine ⟨S, hS, hSx, hxu, hxv, ?_⟩
  change F (t + 1) x ≤ (F t (x - 2 * q) + F t (x + 2 * q)) / 2
  rw [hFx]
  rw [show t + 1 = Nat.succ t by omega, markovIter_succ]
  rw [setIntegral_markovOp_sub_one_eq_centered_mul_markovOp_indicator
    (isReversible_lazy hrev) (measurable_markovIter (lazy P) hhm t)
    (memLp_markovIter (isReversible_lazy hrev).invariant hhm hhLp t) hS]
  exact hmid

/-- Real form of the symmetric `s`-conductance flow bound at an exact-mass set. -/
theorem real_conductanceS_mul_lsShapeMass_le_flow {Omega : Type*} [MeasurableSpace Omega]
    {P : Kernel Omega Omega} [IsMarkovKernel P] {pi : Measure Omega}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    {s ph x : Real} (hs0 : 0 ≤ s) (hph0 : 0 ≤ ph)
    (hx : x ∈ Icc s (1 - s))
    (hc : ENNReal.ofReal ph ≤ conductanceS P pi (ENNReal.ofReal s))
    {S : Set Omega} (hS : MeasurableSet S) (hSx : pi S = ENNReal.ofReal x) :
    ph * min (x - s) (1 - x - s) ≤ (flow P pi S Sᶜ).toReal := by
  have hx0 : 0 ≤ x := hs0.trans hx.1
  have hflowtop : flow P pi S Sᶜ ≠ ⊤ :=
    ne_top_of_le_ne_top (measure_ne_top pi S) (flow_le P pi S Sᶜ)
  by_cases hhalf : x ≤ 1 / 2
  · by_cases hsx : s = x
    · rw [hsx, sub_self, min_eq_left (by linarith), mul_zero]
      exact ENNReal.toReal_nonneg
    · have hsxlt : s < x := lt_of_le_of_ne hx.1 hsx
      have hmasslt : ENNReal.ofReal s < pi S := by
        rw [hSx]
        exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hs0 hsxlt)).2 hsxlt
      have hmasshalf : pi S ≤ 1 / 2 := by
        rw [hSx, ← ofReal_one_half]
        exact ENNReal.ofReal_le_ofReal hhalf
      have hf := conductanceS_mul_tsub_measure_le_flow P pi hc hS hmasslt hmasshalf
      have hf' : ENNReal.ofReal (ph * (x - s)) ≤ flow P pi S Sᶜ := by
        rw [ENNReal.ofReal_mul hph0, ENNReal.ofReal_sub x hs0, ← hSx]
        exact hf
      have hreal := ENNReal.toReal_mono hflowtop hf'
      rw [ENNReal.toReal_ofReal (mul_nonneg hph0 (sub_nonneg.mpr hx.1))] at hreal
      exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hph0).trans hreal
  · have hhalfc : 1 - x ≤ 1 / 2 := by linarith
    have hcompmass : pi Sᶜ = ENNReal.ofReal (1 - x) := by
      rw [measure_compl hS (measure_ne_top pi S), measure_univ, hSx,
        ENNReal.ofReal_sub 1 hx0]
      simp
    by_cases hsx : s = 1 - x
    · rw [hsx, sub_self, min_eq_right (by linarith), mul_zero]
      exact ENNReal.toReal_nonneg
    · have hsxlt : s < 1 - x := lt_of_le_of_ne (by linarith [hx.2]) hsx
      have hmasslt : ENNReal.ofReal s < pi Sᶜ := by
        rw [hcompmass]
        exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hs0 hsxlt)).2 hsxlt
      have hmasshalf : pi Sᶜ ≤ 1 / 2 := by
        rw [hcompmass, ← ofReal_one_half]
        exact ENNReal.ofReal_le_ofReal hhalfc
      have hf := conductanceS_mul_tsub_measure_le_flow P pi hc hS.compl hmasslt hmasshalf
      rw [compl_compl, hrev Sᶜ S hS.compl hS] at hf
      have hf' : ENNReal.ofReal (ph * (1 - x - s)) ≤ flow P pi S Sᶜ := by
        rw [ENNReal.ofReal_mul hph0, ENNReal.ofReal_sub (1 - x) hs0, ← hcompmass]
        exact hf
      have hreal := ENNReal.toReal_mono hflowtop hf'
      rw [ENNReal.toReal_ofReal (mul_nonneg hph0 (by linarith [hx.2]))] at hreal
      exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hph0).trans hreal

/-- Canonical one-step LS recurrence supplied by `s`-conductance. -/
theorem exactMassLSCurve_oneStep_conductanceS {n : Nat} [NeZero n]
    {P : Kernel (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n))}
    [IsMarkovKernel P] {pi : Measure (EuclideanSpace Real (Fin n))}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    {h : EuclideanSpace Real (Fin n) → Real} (hhm : Measurable h) (hhLp : MemLp h 2 pi)
    {F : Nat → Real → Real}
    (hconc : ∀ t, ConcaveOn Real (Icc (0 : Real) 1) (F t))
    (hcurve : ∀ t, IsExactMassLSCurve pi (fun z => markovIter (lazy P) h t z - 1) (F t))
    {s ph : Real} (hs0 : 0 ≤ s) (hph0 : 0 ≤ ph)
    (hc : ENNReal.ofReal ph ≤ conductanceS (lazy P) pi (ENNReal.ofReal s)) :
    ∀ t x, s ≤ x → x ≤ 1 - s →
      let y := min (x - s) (1 - x - s)
      F (t + 1) x ≤ (F t (x - 2 * ph * y) + F t (x + 2 * ph * y)) / 2 := by
  intro t x hxl hxu
  have hx0 : x ∈ Icc (0 : Real) 1 := ⟨hs0.trans hxl, by linarith⟩
  obtain ⟨S, hS, hSx, hxm, hxp, hactual⟩ :=
    exactMassLSCurve_oneStep_actualFlow hrev hhm hhLp hcurve t hx0
  let q := (flow (lazy P) pi S Sᶜ).toReal
  let y := min (x - s) (1 - x - s)
  have hy0 : 0 ≤ y := le_min (sub_nonneg.mpr hxl) (by linarith)
  have hq : ph * y ≤ q :=
    real_conductanceS_mul_lsShapeMass_le_flow (isReversible_lazy hrev) hs0 hph0
      ⟨hxl, hxu⟩ hc hS hSx
  change F (t + 1) x ≤ (F t (x - 2 * ph * y) + F t (x + 2 * ph * y)) / 2
  change F (t + 1) x ≤ (F t (x - 2 * q) + F t (x + 2 * q)) / 2 at hactual
  change x - 2 * q ∈ Icc (0 : Real) 1 at hxm
  change x + 2 * q ∈ Icc (0 : Real) 1 at hxp
  exact hactual.trans (average_le_average_of_concaveOn_symmetric (hconc t)
    (mul_nonneg (mul_nonneg (by positivity) hph0) hy0) (by linarith) hxm hxp)

#print axioms Arlib.MarkovChains.exists_concave_exactMassLSCurve_family_euclidean
#print axioms Arlib.MarkovChains.exactMassLSCurve_oneStep_actualFlow
#print axioms Arlib.MarkovChains.real_conductanceS_mul_lsShapeMass_le_flow
#print axioms Arlib.MarkovChains.exactMassLSCurve_oneStep_conductanceS

end Arlib.MarkovChains
