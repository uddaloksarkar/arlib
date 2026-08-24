/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Convexity.LocalizationLemma
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Exact-mass slicing for Euclidean absolutely continuous measures

The general Lovasz--Simonovits curve argument needs an atomless probability measure to be
divisible: inside every measurable set one must be able to select a measurable subset of any
prescribed smaller mass.  Mathlib's `NullSingletonClass` does not provide that property.

This file proves the specialization needed by Gaussian cooling.  A finite measure absolutely
continuous with respect to Euclidean volume can be sliced by a fixed nonzero linear functional.
The proof writes the measure using its Radon--Nikodym density and applies the repository's
continuity theorem for integrals over moving halfspaces.

The final theorem also packages the exact slice of a level set used in the bathtub principle:
given a level `q` bracketing the requested mass `a`, it constructs an exact-mass measurable set
between the strict and weak superlevel sets of `f`.
-/

namespace Arlib.MarkovChains

open MeasureTheory Set Bornology Filter
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional Real E]
  {vol : Measure E} [vol.IsAddHaarMeasure]

/-- A bounded-set version of arbitrary (not merely bisecting) halfspace slicing.

The assumptions on `c` are exactly the endpoint inequalities needed by the intermediate value
theorem.  No sign condition on `f` is needed beyond those two scalar inequalities. -/
theorem exists_halfSpace_setIntegral_eq {f : E → Real} {K : Set E}
    (hf : IntegrableOn f K vol) (hKb : IsBounded K)
    {L : E →L[Real] Real} (hL : L ≠ 0) {c : Real}
    (hc0 : 0 ≤ c) (hcK : c ≤ ∫ x in K, f x ∂vol) :
    ∃ s : Real, ∫ x in K ∩ {x : E | L x ≤ s}, f x ∂vol = c := by
  let F : Real → Real := fun s => ∫ x in K ∩ {x : E | L x ≤ s}, f x ∂vol
  have hFc : Continuous F := Arlib.continuous_setIntegral_halfSpace hf hL
  obtain ⟨r, hr⟩ := hKb.subset_closedBall (0 : E)
  have hLb : ∀ x ∈ K, |L x| ≤ ‖L‖ * r := by
    intro x hx
    have hx' : ‖x‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hr hx
    calc
      |L x| = ‖L x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
      _ ≤ ‖L‖ * r := mul_le_mul_of_nonneg_left hx' (norm_nonneg L)
  have hlow : F (- (‖L‖ * r) - 1) = 0 := by
    have hempty : K ∩ {x : E | L x ≤ -(‖L‖ * r) - 1} = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx => ?_
      have h1 : -(‖L‖ * r) ≤ L x := neg_le_of_abs_le (hLb x hx.1)
      have h2 : L x ≤ -(‖L‖ * r) - 1 := hx.2
      linarith
    change ∫ x in K ∩ {x : E | L x ≤ -(‖L‖ * r) - 1}, f x ∂vol = 0
    rw [hempty, setIntegral_empty]
  have hhigh : F (‖L‖ * r) = ∫ x in K, f x ∂vol := by
    have hall : K ∩ {x : E | L x ≤ ‖L‖ * r} = K := by
      exact Set.inter_eq_self_of_subset_left fun x hx => le_of_abs_le (hLb x hx)
    change ∫ x in K ∩ {x : E | L x ≤ ‖L‖ * r}, f x ∂vol = ∫ x in K, f x ∂vol
    rw [hall]
  refine intermediate_value_univ₂ (a := -(‖L‖ * r) - 1) (b := ‖L‖ * r) hFc
    continuous_const ?_ ?_
  · change F (- (‖L‖ * r) - 1) ≤ c
    rw [hlow]
    exact hc0
  · change c ≤ F (‖L‖ * r)
    rw [hhigh]
    exact hcK

/-- On a bounded measurable set, a finite measure absolutely continuous with respect to volume
has a halfspace slice of every prescribed smaller mass. -/
theorem exists_halfSpace_measure_eq_of_ac (mu : Measure E) [IsFiniteMeasure mu]
    (hmu : mu ≪ vol) {K : Set E} (hKb : IsBounded K)
    {L : E →L[Real] Real} (hL : L ≠ 0) {a : ENNReal} (ha : a ≤ mu K) :
    ∃ s : Real, mu (K ∩ {x : E | L x ≤ s}) = a := by
  let f : E → Real := fun x => (mu.rnDeriv vol x).toReal
  have hf : IntegrableOn f K vol :=
    Measure.integrableOn_toReal_rnDeriv (μ := mu) (ν := vol) (measure_ne_top mu K)
  have htotal : ∫ x in K, f x ∂vol = (mu K).toReal := by
    simpa [f, measureReal_def] using Measure.setIntegral_toReal_rnDeriv hmu K
  have haTop : a ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top mu K) ha
  have hac : a.toReal ≤ ∫ x in K, f x ∂vol := by
    rw [htotal]
    exact ENNReal.toReal_mono (measure_ne_top mu K) ha
  obtain ⟨s, hs⟩ := exists_halfSpace_setIntegral_eq hf hKb hL ENNReal.toReal_nonneg hac
  refine ⟨s, (ENNReal.toReal_eq_toReal_iff' (measure_ne_top mu _) haTop).mp ?_⟩
  calc
    (mu (K ∩ {x : E | L x ≤ s})).toReal
        = ∫ x in K ∩ {x : E | L x ≤ s}, f x ∂vol := by
          symm
          simpa [f, measureReal_def] using
            Measure.setIntegral_toReal_rnDeriv hmu (K ∩ {x : E | L x ≤ s})
    _ = a.toReal := hs

/-- **Euclidean measure divisibility.**  If `mu` is finite and absolutely continuous with
respect to volume, every measurable `A` contains a measurable subset of every mass `a ≤ mu A`.

The functional `L` is explicit so the theorem makes the necessary positive-dimensional
hypothesis honest.  When `a < mu A`, first intersect `A` with a sufficiently large closed ball;
continuity from below makes that bounded intersection carry at least mass `a`, and the bounded
halfspace theorem makes the final exact cut. -/
theorem exists_measurable_subset_measure_eq_of_ac (mu : Measure E) [IsFiniteMeasure mu]
    (hmu : mu ≪ vol) {L : E →L[Real] Real} (hL : L ≠ 0)
    {A : Set E} (hA : MeasurableSet A) {a : ENNReal} (ha : a ≤ mu A) :
    ∃ B : Set E, MeasurableSet B ∧ B ⊆ A ∧ mu B = a := by
  rcases eq_or_lt_of_le ha with rfl | halt
  · exact ⟨A, hA, Subset.rfl, rfl⟩
  · let K : Nat → Set E := fun n => A ∩ Metric.closedBall 0 n
    have hmono : Monotone K := by
      intro m n hmn x hx
      refine ⟨hx.1, ?_⟩
      exact Metric.closedBall_subset_closedBall (by exact_mod_cast hmn) hx.2
    have hUnion : (⋃ n : Nat, K n) = A := by
      ext x
      simp only [K, Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
      constructor
      · rintro ⟨n, hxA, -⟩
        exact hxA
      · intro hxA
        obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
        exact ⟨n, hxA, hn⟩
    have hlim := tendsto_measure_iUnion_atTop (μ := mu) hmono
    rw [hUnion] at hlim
    obtain ⟨n, hn⟩ := (hlim.eventually_const_lt halt).exists
    have hKn : MeasurableSet (K n) := hA.inter measurableSet_closedBall
    have hKnb : IsBounded (K n) := Metric.isBounded_closedBall.subset inter_subset_right
    obtain ⟨s, hs⟩ := exists_halfSpace_measure_eq_of_ac mu hmu hKnb hL hn.le
    let B : Set E := K n ∩ {x : E | L x ≤ s}
    refine ⟨B, hKn.inter (measurableSet_le L.continuous.measurable measurable_const), ?_, hs⟩
    exact fun x hx => hx.1.1

/-- Exact-mass superlevel selection, the set-theoretic core of the bathtub principle.

If the strict and weak superlevel masses at `q` bracket `a`, divisibility supplies exactly the
missing amount from the level set `{f=q}`.  The returned set has mass `a` and lies between the
strict and weak superlevel sets. -/
theorem exists_exactMass_between_superlevels_of_ac (mu : Measure E) [IsFiniteMeasure mu]
    (hmu : mu ≪ vol) {L : E →L[Real] Real} (hL : L ≠ 0)
    {f : E → Real} (hf : Measurable f) {q : Real} {a : ENNReal}
    (hlower : mu {x | q < f x} ≤ a) (hupper : a ≤ mu {x | q ≤ f x}) :
    ∃ S : Set E, MeasurableSet S ∧ mu S = a ∧
      {x | q < f x} ⊆ S ∧ S ⊆ {x | q ≤ f x} := by
  let G : Set E := {x | q < f x}
  let Z : Set E := {x | f x = q}
  have hG : MeasurableSet G := measurableSet_lt measurable_const hf
  have hZ : MeasurableSet Z := measurableSet_eq_fun hf measurable_const
  have hdisj : Disjoint G Z := by
    rw [Set.disjoint_left]
    intro x hxG hxZ
    exact (ne_of_gt hxG) hxZ
  have hweak : {x | q ≤ f x} = G ∪ Z := by
    ext x
    simp only [G, Z, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hx
      rcases eq_or_lt_of_le hx with heq | hlt
      · exact Or.inr heq.symm
      · exact Or.inl hlt
    · rintro (hlt | heq)
      · exact hlt.le
      · exact heq.ge
  have hsum : mu G + mu Z = mu {x | q ≤ f x} := by
    rw [hweak, measure_union hdisj hZ]
  let b : ENNReal := a - mu G
  have hb : b ≤ mu Z := by
    change a - mu G ≤ mu Z
    rw [tsub_le_iff_right, add_comm, hsum]
    exact hupper
  obtain ⟨B, hB, hBZ, hBm⟩ :=
    exists_measurable_subset_measure_eq_of_ac mu hmu hL hZ hb
  refine ⟨G ∪ B, hG.union hB, ?_, Set.subset_union_left, ?_⟩
  · rw [measure_union (hdisj.mono_right hBZ) hB, hBm]
    exact add_tsub_cancel_of_le hlower
  · rw [hweak]
    exact Set.union_subset_union_right G hBZ

/-! ## Direct Euclidean-volume interfaces -/

/-- The divisibility theorem with the nonzero coordinate functional constructed internally.
This is the interface used by positive-dimensional Gaussian phase laws. -/
theorem exists_measurable_subset_measure_eq_euclidean {n : Nat} [NeZero n]
    (mu : Measure (EuclideanSpace Real (Fin n))) [IsFiniteMeasure mu]
    (hmu : mu ≪ volume) {A : Set (EuclideanSpace Real (Fin n))} (hA : MeasurableSet A)
    {a : ENNReal} (ha : a ≤ mu A) :
    ∃ B : Set (EuclideanSpace Real (Fin n)), MeasurableSet B ∧ B ⊆ A ∧ mu B = a := by
  let j : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  let L : EuclideanSpace Real (Fin n) →L[Real] Real :=
    EuclideanSpace.proj (𝕜 := Real) j
  have hL : L ≠ 0 := by
    intro hz
    have hz' := DFunLike.congr_fun hz (EuclideanSpace.single j (1 : Real))
    simp [L] at hz'
  exact exists_measurable_subset_measure_eq_of_ac (vol := volume) mu hmu hL hA ha

/-- The exact-mass superlevel selector specialized to positive-dimensional Euclidean volume. -/
theorem exists_exactMass_between_superlevels_euclidean {n : Nat} [NeZero n]
    (mu : Measure (EuclideanSpace Real (Fin n))) [IsFiniteMeasure mu]
    (hmu : mu ≪ volume) {f : EuclideanSpace Real (Fin n) → Real} (hf : Measurable f)
    {q : Real} {a : ENNReal} (hlower : mu {x | q < f x} ≤ a)
    (hupper : a ≤ mu {x | q ≤ f x}) :
    ∃ S : Set (EuclideanSpace Real (Fin n)), MeasurableSet S ∧ mu S = a ∧
      {x | q < f x} ⊆ S ∧ S ⊆ {x | q ≤ f x} := by
  let j : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  let L : EuclideanSpace Real (Fin n) →L[Real] Real :=
    EuclideanSpace.proj (𝕜 := Real) j
  have hL : L ≠ 0 := by
    intro hz
    have hz' := DFunLike.congr_fun hz (EuclideanSpace.single j (1 : Real))
    simp [L] at hz'
  exact exists_exactMass_between_superlevels_of_ac (vol := volume) mu hmu hL hf hlower hupper

#print axioms Arlib.MarkovChains.exists_halfSpace_setIntegral_eq
#print axioms Arlib.MarkovChains.exists_halfSpace_measure_eq_of_ac
#print axioms Arlib.MarkovChains.exists_measurable_subset_measure_eq_of_ac
#print axioms Arlib.MarkovChains.exists_exactMass_between_superlevels_of_ac
#print axioms Arlib.MarkovChains.exists_measurable_subset_measure_eq_euclidean
#print axioms Arlib.MarkovChains.exists_exactMass_between_superlevels_euclidean

end Arlib.MarkovChains
