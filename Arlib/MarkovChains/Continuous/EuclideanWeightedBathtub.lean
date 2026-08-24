/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.MarkovChains.Continuous.LSScalarDecay

/-!
# A common weighted bathtub maximizer

At a prescribed mass, one quantile set simultaneously dominates every measurable
`[0,1]`-valued weight of that mass.  The endpoint masses are treated separately.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-- One Euclidean quantile set simultaneously maximizes against every fractional weight of
the prescribed mass. -/
theorem exists_common_weighted_bathtub_maximizer_euclidean {n : Nat} [NeZero n]
    (mu : Measure (EuclideanSpace Real (Fin n))) [IsFiniteMeasure mu]
    (hmu : mu ≪ volume) {f : EuclideanSpace Real (Fin n) → Real}
    (hfm : Measurable f) (hfi : Integrable f mu) {a : ENNReal} (ha : a ≤ mu Set.univ) :
    ∃ S : Set (EuclideanSpace Real (Fin n)), MeasurableSet S ∧ mu S = a ∧
      ∀ w : EuclideanSpace Real (Fin n) → Real, Measurable w →
        (∀ x, 0 ≤ w x) → (∀ x, w x ≤ 1) →
        (∫ x, w x ∂mu = a.toReal) →
        ∫ x, f x * w x ∂mu ≤ ∫ x in S, f x ∂mu := by
  rcases eq_or_lt_of_le (show 0 ≤ a from zero_le) with rfl | ha0
  · refine ⟨∅, MeasurableSet.empty, measure_empty, ?_⟩
    intro w hwm hw0 hw1 hmass
    have hwint : Integrable w mu :=
      Integrable.of_bound hwm.aestronglyMeasurable 1
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
          exact hw1 x)
    have hwzero : w =ᵐ[mu] 0 :=
      (integral_eq_zero_iff_of_nonneg hw0 hwint).mp (by simpa using hmass)
    rw [setIntegral_empty]
    have hprod : (fun x => f x * w x) =ᵐ[mu] 0 := by
      filter_upwards [hwzero] with x hx
      have hx' : w x = 0 := by simpa only [Pi.zero_apply] using hx
      simpa only [Pi.zero_apply, hx', mul_zero]
    rw [integral_congr_ae hprod]
    simp only [Pi.zero_apply, integral_zero]
    exact le_rfl
  rcases eq_or_lt_of_le ha with rfl | haU
  · refine ⟨Set.univ, MeasurableSet.univ, rfl, ?_⟩
    intro w hwm hw0 hw1 hmass
    have hwint : Integrable w mu :=
      Integrable.of_bound hwm.aestronglyMeasurable 1
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
          exact hw1 x)
    have hsubint : Integrable (fun x => 1 - w x) mu :=
      (integrable_const (1 : Real)).sub hwint
    have hsubmean : ∫ x, (1 - w x) ∂mu = 0 := by
      rw [integral_sub (integrable_const (1 : Real)) hwint, integral_const,
        measureReal_def, hmass]
      ring
    have hwae : w =ᵐ[mu] 1 := by
      have hz : (fun x => 1 - w x) =ᵐ[mu] 0 :=
        (integral_eq_zero_iff_of_nonneg (fun x => sub_nonneg.mpr (hw1 x)) hsubint).mp hsubmean
      filter_upwards [hz] with x hx
      have hx' : 1 - w x = 0 := by simpa only [Pi.zero_apply] using hx
      simpa only [Pi.one_apply] using (sub_eq_zero.mp hx').symm
    rw [setIntegral_univ]
    refine le_of_eq (integral_congr_ae ?_)
    filter_upwards [hwae] with x hx
    have hx' : w x = 1 := by simpa only [Pi.one_apply] using hx
    simpa only [hx', mul_one]
  · obtain ⟨q, S, hS, hSa, hstrict, hweak, -⟩ :=
      exists_bathtub_maximizer_euclidean_interior mu hmu hfm hfi ha0 haU
    refine ⟨S, hS, hSa, ?_⟩
    intro w hwm hw0 hw1 hmass
    exact integral_mul_le_setIntegral_of_between_superlevels hfi hwm hw0 hw1 hS
      hstrict hweak (hmass.trans (congrArg ENNReal.toReal hSa).symm)

#print axioms Arlib.MarkovChains.exists_common_weighted_bathtub_maximizer_euclidean

end Arlib.MarkovChains
