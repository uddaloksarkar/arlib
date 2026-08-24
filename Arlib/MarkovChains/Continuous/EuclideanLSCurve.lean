/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.MarkovChains.Continuous.EuclideanWeightedBathtub

/-!
# Exact-mass Euclidean Lovász--Simonovits curves
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- A curve is an exact-mass LS curve for `f` when each value is represented by one set
which simultaneously dominates all fractional weights of that mass. -/
def IsExactMassLSCurve {Omega : Type*} [MeasurableSpace Omega]
    (pi : Measure Omega) (f : Omega → Real) (F : Real → Real) : Prop :=
  ∀ x : Real, x ∈ Icc 0 1 →
    ∃ S : Set Omega, MeasurableSet S ∧ pi S = ENNReal.ofReal x ∧
      F x = ∫ z in S, f z ∂pi ∧
      ∀ w : Omega → Real, Measurable w → (∀ z, 0 ≤ w z) → (∀ z, w z ≤ 1) →
        (∫ z, w z ∂pi = x) → ∫ z, f z * w z ∂pi ≤ F x

/-- Exact-mass LS curves exist and are concave for Euclidean atomless probability laws. -/
theorem exists_concave_exactMassLSCurve_euclidean {n : Nat} [NeZero n]
    (pi : Measure (EuclideanSpace Real (Fin n))) [IsProbabilityMeasure pi]
    (hpi : pi ≪ volume) {f : EuclideanSpace Real (Fin n) → Real}
    (hfm : Measurable f) (hfi : Integrable f pi) :
    ∃ F : Real → Real, ConcaveOn Real (Icc (0 : Real) 1) F ∧
      IsExactMassLSCurve pi f F := by
  classical
  have hsel : ∀ x : Real, ∃ S : Set (EuclideanSpace Real (Fin n)),
      x ∈ Icc (0 : Real) 1 →
        MeasurableSet S ∧ pi S = ENNReal.ofReal x ∧
        ∀ w : EuclideanSpace Real (Fin n) → Real, Measurable w →
          (∀ z, 0 ≤ w z) → (∀ z, w z ≤ 1) →
          (∫ z, w z ∂pi = x) → ∫ z, f z * w z ∂pi ≤ ∫ z in S, f z ∂pi := by
    intro x
    by_cases hx : x ∈ Icc (0 : Real) 1
    · have ha : ENNReal.ofReal x ≤ pi Set.univ := by
        rw [measure_univ]
        exact ENNReal.ofReal_le_one.mpr hx.2
      obtain ⟨S, hS, hSa, hmax⟩ :=
        exists_common_weighted_bathtub_maximizer_euclidean pi hpi hfm hfi ha
      refine ⟨S, fun _ => ⟨hS, hSa, ?_⟩⟩
      intro w hwm hw0 hw1 hmass
      apply hmax w hwm hw0 hw1
      simpa [ENNReal.toReal_ofReal hx.1] using hmass
    · exact ⟨∅, fun h => (hx h).elim⟩
  choose S hS using hsel
  let F : Real → Real := fun x => ∫ z in S x, f z ∂pi
  refine ⟨F, ?_, ?_⟩
  · refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy p q hp hq hpq
    have hz : p • x + q • y ∈ Icc (0 : Real) 1 := by
      simp only [smul_eq_mul]
      constructor <;> nlinarith [hx.1, hx.2, hy.1, hy.2]
    obtain ⟨hSx, hSxa, hSxmax⟩ := hS x hx
    obtain ⟨hSy, hSya, hSymax⟩ := hS y hy
    obtain ⟨hSz, hSza, hSzmax⟩ := hS (p • x + q • y) hz
    let w : EuclideanSpace Real (Fin n) → Real := fun z =>
      p * (S x).indicator (fun _ => (1 : Real)) z +
        q * (S y).indicator (fun _ => (1 : Real)) z
    have hwm : Measurable w :=
      ((measurable_const.mul (measurable_const.indicator hSx))).add
        (measurable_const.mul (measurable_const.indicator hSy))
    have hw0 : ∀ z, 0 ≤ w z := by
      intro z
      have hix : 0 ≤ (S x).indicator (fun _ => (1 : Real)) z := by
        by_cases hzx : z ∈ S x <;> simp [hzx]
      have hiy : 0 ≤ (S y).indicator (fun _ => (1 : Real)) z := by
        by_cases hzy : z ∈ S y <;> simp [hzy]
      dsimp [w]
      exact add_nonneg (mul_nonneg hp hix) (mul_nonneg hq hiy)
    have hw1 : ∀ z, w z ≤ 1 := by
      intro z
      have hix : (S x).indicator (fun _ => (1 : Real)) z ≤ 1 := by
        by_cases hzx : z ∈ S x <;> simp [hzx]
      have hiy : (S y).indicator (fun _ => (1 : Real)) z ≤ 1 := by
        by_cases hzy : z ∈ S y <;> simp [hzy]
      dsimp [w]
      nlinarith
    have hmass : ∫ z, w z ∂pi = p • x + q • y := by
      have hixint : Integrable ((S x).indicator fun _ => (1 : Real)) pi :=
        (integrable_const (1 : Real)).indicator hSx
      have hiyint : Integrable ((S y).indicator fun _ => (1 : Real)) pi :=
        (integrable_const (1 : Real)).indicator hSy
      have hxmass : ∫ z, (S x).indicator (fun _ => (1 : Real)) z ∂pi = x := by
        simpa [measureReal_def, hSxa, ENNReal.toReal_ofReal hx.1] using
          integral_indicator_const (μ := pi) (1 : Real) hSx
      have hymass : ∫ z, (S y).indicator (fun _ => (1 : Real)) z ∂pi = y := by
        simpa [measureReal_def, hSya, ENNReal.toReal_ofReal hy.1] using
          integral_indicator_const (μ := pi) (1 : Real) hSy
      change ∫ z, p * (S x).indicator (fun _ => (1 : Real)) z +
          q * (S y).indicator (fun _ => (1 : Real)) z ∂pi = _
      rw [integral_add (hixint.const_mul p) (hiyint.const_mul q),
        integral_const_mul, integral_const_mul, hxmass, hymass]
      simp only [smul_eq_mul]
    have hweighted := hSzmax w hwm hw0 hw1 hmass
    have hprod : ∫ z, f z * w z ∂pi =
        p * (∫ z in S x, f z ∂pi) + q * ∫ z in S y, f z ∂pi := by
      have hfx : Integrable (fun z => f z * (S x).indicator (fun _ => (1 : Real)) z) pi :=
        hfi.mul_bdd (c := 1) (measurable_const.indicator hSx).aestronglyMeasurable
          (Eventually.of_forall fun z => by by_cases hz : z ∈ S x <;> simp [hz])
      have hfy : Integrable (fun z => f z * (S y).indicator (fun _ => (1 : Real)) z) pi :=
        hfi.mul_bdd (c := 1) (measurable_const.indicator hSy).aestronglyMeasurable
          (Eventually.of_forall fun z => by by_cases hz : z ∈ S y <;> simp [hz])
      have hfun : (fun z => f z * w z) = fun z =>
          p * (f z * (S x).indicator (fun _ => (1 : Real)) z) +
            q * (f z * (S y).indicator (fun _ => (1 : Real)) z) := by
        funext z
        dsimp [w]
        ring
      rw [hfun, integral_add (hfx.const_mul p) (hfy.const_mul q),
        integral_const_mul, integral_const_mul]
      have hxint : ∫ z, f z * (S x).indicator (fun _ => (1 : Real)) z ∂pi =
          ∫ z in S x, f z ∂pi := by
        rw [← integral_indicator hSx]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ S x <;> simp [hz]
      have hyint : ∫ z, f z * (S y).indicator (fun _ => (1 : Real)) z ∂pi =
          ∫ z in S y, f z ∂pi := by
        rw [← integral_indicator hSy]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ S y <;> simp [hz]
      rw [hxint, hyint]
    change p • F x + q • F y ≤ F (p • x + q • y)
    rw [show F x = ∫ z in S x, f z ∂pi by rfl,
      show F y = ∫ z in S y, f z ∂pi by rfl,
      show F (p • x + q • y) = ∫ z in S (p • x + q • y), f z ∂pi by rfl,
      smul_eq_mul, smul_eq_mul, ← hprod]
    exact hweighted
  · intro x hx
    obtain ⟨hSxm, hSxa, hSxmax⟩ := hS x hx
    exact ⟨S x, hSxm, hSxa, rfl, hSxmax⟩

#print axioms Arlib.MarkovChains.exists_concave_exactMassLSCurve_euclidean

end Arlib.MarkovChains
