/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.MarkovChains.Continuous.EuclideanMeasureSlicing
import Arlib.MarkovChains.Continuous.SConductanceCoarea

/-!
# Quantiles and the Euclidean bathtub principle

This is the rearrangement layer needed after exact-mass divisibility in the
Lovasz--Simonovits curve proof.  Interior target masses admit a finite bracketing quantile.
The endpoint masses are treated separately: a finite quantile is false in general there
(for example for the identity under a Gaussian law), while the optimizing sets are simply
the empty set and the whole space.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

variable {Omega : Type*} [MeasurableSpace Omega]

/-- An interior lower-tail quantile.  The level `q` brackets `a` between the strict and weak
sublevel masses. -/
theorem exists_measure_lt_le_bracket {mu : Measure Omega} [IsFiniteMeasure mu]
    {f : Omega → Real} (hf : Measurable f) {a : ENNReal}
    (ha0 : 0 < a) (haU : a < mu Set.univ) :
    ∃ q : Real, mu {x | f x < q} ≤ a ∧ a ≤ mu {x | f x ≤ q} := by
  have hle : ∀ t : Real, MeasurableSet {x : Omega | f x ≤ t} := fun t =>
    measurableSet_le hf measurable_const
  have hmono : ∀ s t : Real, s ≤ t → mu {x : Omega | f x ≤ s} ≤ mu {x | f x ≤ t} :=
    fun s t hst => measure_mono fun _ hx => hx.trans hst
  let B : Set Real := {t | a ≤ mu {x : Omega | f x ≤ t}}
  have hup : ∀ s ∈ B, ∀ t : Real, s ≤ t → t ∈ B := fun s hs t hst =>
    hs.trans (hmono s t hst)
  have hne : B.Nonempty := by
    have hU : (⋃ n : Nat, {x : Omega | f x ≤ (n : Real)}) = Set.univ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact exists_nat_ge (f x)
    have hm : Monotone fun n : Nat => {x : Omega | f x ≤ (n : Real)} := by
      intro m n hmn x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact hx.trans (by exact_mod_cast hmn)
    have hlim := tendsto_measure_iUnion_atTop (μ := mu) hm
    rw [hU] at hlim
    obtain ⟨n, hn⟩ := (hlim.eventually_const_lt haU).exists
    exact ⟨(n : Real), hn.le⟩
  have hbdd : BddBelow B := by
    have hI : (⋂ n : Nat, {x : Omega | f x ≤ -(n : Real)}) = ∅ := by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_forall, not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-(f x))
      exact ⟨n, by linarith⟩
    have hm : Antitone fun n : Nat => {x : Omega | f x ≤ -(n : Real)} := by
      intro m n hmn x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      have hmn' : (m : Real) ≤ n := by exact_mod_cast hmn
      exact hx.trans (by linarith)
    have hlim := tendsto_measure_iInter_atTop (μ := mu)
      (fun n : Nat => (hle (-(n : Real))).nullMeasurableSet) hm
      ⟨0, measure_ne_top mu _⟩
    rw [hI, measure_empty] at hlim
    obtain ⟨n, hn⟩ := (hlim.eventually_lt_const ha0).exists
    refine ⟨-(n : Real), fun t ht => ?_⟩
    by_contra htn
    have hmass : a ≤ mu {x : Omega | f x ≤ -(n : Real)} :=
      ht.trans (hmono t (-(n : Real)) (not_le.mp htn).le)
    exact (not_le.mpr hn) hmass
  let q : Real := sInf B
  have hqB : a ≤ mu {x : Omega | f x ≤ q} := by
    have hI : (⋂ n : Nat, {x : Omega | f x ≤ q + 1 / (n + 1 : Real)})
        = {x : Omega | f x ≤ q} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro hx
        exact le_of_forall_pos_le_add fun eps heps => by
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt heps
          exact (hx n).trans (by linarith)
      · intro hx n
        exact hx.trans (le_add_of_nonneg_right (by positivity))
    have hm : Antitone fun n : Nat => {x : Omega | f x ≤ q + 1 / (n + 1 : Real)} := by
      intro m n hmn x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      have hmn' : (m : Real) + 1 ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
      have hdiv : 1 / ((n : Real) + 1) ≤ 1 / ((m : Real) + 1) :=
        one_div_le_one_div_of_le (by positivity) hmn'
      exact hx.trans (by linarith)
    have hlim := tendsto_measure_iInter_atTop (μ := mu)
      (fun n : Nat => (hle (q + 1 / (n + 1 : Real))).nullMeasurableSet) hm
      ⟨0, measure_ne_top mu _⟩
    rw [hI] at hlim
    refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
    have hpos : 0 < 1 / (n + 1 : Real) := by positivity
    obtain ⟨s, hsB, hs⟩ := exists_lt_of_csInf_lt hne
      (by change sInf B < q + 1 / (n + 1 : Real); simpa [q] using lt_add_of_pos_right q hpos)
    exact hup s hsB _ hs.le
  refine ⟨q, ?_, hqB⟩
  have hU : (⋃ n : Nat, {x : Omega | f x ≤ q - 1 / (n + 1 : Real)})
      = {x : Omega | f x < q} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn⟩
      have : 0 < 1 / (n + 1 : Real) := by positivity
      exact lt_of_le_of_lt hn (by linarith)
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
      exact ⟨n, by linarith⟩
  have hm : Monotone fun n : Nat => {x : Omega | f x ≤ q - 1 / (n + 1 : Real)} := by
    intro m n hmn x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have hmn' : (m : Real) + 1 ≤ n + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    have hdiv : 1 / ((n : Real) + 1) ≤ 1 / ((m : Real) + 1) :=
      one_div_le_one_div_of_le (by positivity) hmn'
    exact hx.trans (by linarith)
  have hlim := tendsto_measure_iUnion_atTop (μ := mu) hm
  rw [hU] at hlim
  refine le_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  by_contra hna
  have hmem : q ≤ q - 1 / (n + 1 : Real) := csInf_le hbdd (not_le.mp hna).le
  have : 0 < 1 / (n + 1 : Real) := by positivity
  linarith

/-- Interior upper-tail quantile, obtained by applying the lower-tail result to `-f`. -/
theorem exists_measure_superlevel_bracket {mu : Measure Omega} [IsFiniteMeasure mu]
    {f : Omega → Real} (hf : Measurable f) {a : ENNReal}
    (ha0 : 0 < a) (haU : a < mu Set.univ) :
    ∃ q : Real, mu {x | q < f x} ≤ a ∧ a ≤ mu {x | q ≤ f x} := by
  obtain ⟨m, hm1, hm2⟩ := exists_measure_lt_le_bracket hf.neg ha0 haU
  refine ⟨-m, ?_, ?_⟩
  · have hset : {x : Omega | -f x < m} = {x | -m < f x} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor <;> intro hx <;> linarith
    rw [← hset]
    exact hm1
  · have hset : {x : Omega | -f x ≤ m} = {x | -m ≤ f x} := by
      ext x
      simp only [Set.mem_setOf_eq]
      constructor <;> intro hx <;> linarith
    rw [← hset]
    exact hm2

/-- Equal finite masses have equal masses after deleting their intersection. -/
theorem measure_sdiff_eq_measure_sdiff_of_eq {mu : Measure Omega} [IsFiniteMeasure mu]
    {S T : Set Omega} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hmass : mu S = mu T) : mu (S \ T) = mu (T \ S) := by
  apply (ENNReal.add_right_inj (measure_ne_top mu (S ∩ T))).mp
  calc
    mu (S ∩ T) + mu (S \ T) = mu S := measure_inter_add_sdiff S hT
    _ = mu T := hmass
    _ = mu (T ∩ S) + mu (T \ S) := (measure_inter_add_sdiff T hS).symm
    _ = mu (S ∩ T) + mu (T \ S) := by rw [inter_comm]

/-- **Bathtub exchange inequality.**  An exact-mass set lying between the strict and weak
superlevel sets at `q` maximizes the integral of `f` among all measurable sets of that mass. -/
theorem setIntegral_le_of_between_superlevels {mu : Measure Omega} [IsFiniteMeasure mu]
    {f : Omega → Real} (hf : Integrable f mu) {q : Real} {S T : Set Omega}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hmass : mu S = mu T)
    (hstrict : {x | q < f x} ⊆ S) (hweak : S ⊆ {x | q ≤ f x}) :
    ∫ x in T, f x ∂mu ≤ ∫ x in S, f x ∂mu := by
  let D : Set Omega := S \ T
  let E : Set Omega := T \ S
  have hD : MeasurableSet D := hS.diff hT
  have hE : MeasurableSet E := hT.diff hS
  have hmDE : mu D = mu E := measure_sdiff_eq_measure_sdiff_of_eq hS hT hmass
  have hDlow : q * (mu D).toReal ≤ ∫ x in D, f x ∂mu := by
    have hmono := setIntegral_mono_on (integrableOn_const (measure_ne_top mu D))
      hf.integrableOn hD (fun x hx => hweak hx.1)
    rw [setIntegral_const, smul_eq_mul, measureReal_def] at hmono
    simpa [mul_comm] using hmono
  have hEhigh : (∫ x in E, f x ∂mu) ≤ q * (mu E).toReal := by
    have hpoint : ∀ x ∈ E, f x ≤ q := by
      intro x hx
      by_contra hqx
      exact hx.2 (hstrict (lt_of_not_ge hqx))
    have hmono := setIntegral_mono_on hf.integrableOn
      (integrableOn_const (measure_ne_top mu E)) hE hpoint
    rw [setIntegral_const, smul_eq_mul, measureReal_def] at hmono
    simpa [mul_comm] using hmono
  have hcross : (∫ x in E, f x ∂mu) ≤ ∫ x in D, f x ∂mu := by
    calc
      (∫ x in E, f x ∂mu) ≤ q * (mu E).toReal := hEhigh
      _ = q * (mu D).toReal := by rw [hmDE]
      _ ≤ ∫ x in D, f x ∂mu := hDlow
  have hsplitS : ∫ x in S, f x ∂mu =
      (∫ x in D, f x ∂mu) + ∫ x in S ∩ T, f x ∂mu := by
    change ∫ x in S, f x ∂mu =
      (∫ x in S \ T, f x ∂mu) + ∫ x in S ∩ T, f x ∂mu
    conv_lhs => rw [← sdiff_union_inter S T]
    rw [setIntegral_union disjoint_sdiff_inter (hS.inter hT)
      (hf.integrableOn.mono_set sdiff_subset) (hf.integrableOn.mono_set inter_subset_left)]
  have hsplitT : ∫ x in T, f x ∂mu =
      (∫ x in E, f x ∂mu) + ∫ x in S ∩ T, f x ∂mu := by
    change ∫ x in T, f x ∂mu =
      (∫ x in T \ S, f x ∂mu) + ∫ x in S ∩ T, f x ∂mu
    conv_lhs => rw [← sdiff_union_inter T S]
    rw [setIntegral_union disjoint_sdiff_inter (hT.inter hS)
      (hf.integrableOn.mono_set sdiff_subset) (hf.integrableOn.mono_set inter_subset_left),
      inter_comm]
  rw [hsplitS, hsplitT]
  exact add_le_add hcross le_rfl

/-- Interior Euclidean bathtub principle, including the quantile and the exact-mass selector. -/
theorem exists_bathtub_maximizer_euclidean_interior {n : Nat} [NeZero n]
    (mu : Measure (EuclideanSpace Real (Fin n))) [IsFiniteMeasure mu]
    (hmu : mu ≪ volume) {f : EuclideanSpace Real (Fin n) → Real}
    (hfm : Measurable f) (hfi : Integrable f mu) {a : ENNReal}
    (ha0 : 0 < a) (haU : a < mu Set.univ) :
    ∃ (q : Real) (S : Set (EuclideanSpace Real (Fin n))),
      MeasurableSet S ∧ mu S = a ∧ {x | q < f x} ⊆ S ∧ S ⊆ {x | q ≤ f x} ∧
      ∀ T : Set (EuclideanSpace Real (Fin n)), MeasurableSet T → mu T = a →
        ∫ x in T, f x ∂mu ≤ ∫ x in S, f x ∂mu := by
  obtain ⟨q, hql, hqu⟩ := exists_measure_superlevel_bracket hfm ha0 haU
  obtain ⟨S, hSm, hSa, hstrict, hweak⟩ :=
    exists_exactMass_between_superlevels_euclidean mu hmu hfm hql hqu
  refine ⟨q, S, hSm, hSa, hstrict, hweak, fun T hTm hTa => ?_⟩
  exact setIntegral_le_of_between_superlevels hfi hSm hTm (hSa.trans hTa.symm) hstrict hweak

/-- **Euclidean bathtub principle for every target mass.**  At the two endpoint masses the
maximizers are `∅` and `univ`; at an interior mass this is the quantile construction above. -/
theorem exists_bathtub_maximizer_euclidean {n : Nat} [NeZero n]
    (mu : Measure (EuclideanSpace Real (Fin n))) [IsFiniteMeasure mu]
    (hmu : mu ≪ volume) {f : EuclideanSpace Real (Fin n) → Real}
    (hfm : Measurable f) (hfi : Integrable f mu) {a : ENNReal} (ha : a ≤ mu Set.univ) :
    ∃ S : Set (EuclideanSpace Real (Fin n)), MeasurableSet S ∧ mu S = a ∧
      ∀ T : Set (EuclideanSpace Real (Fin n)), MeasurableSet T → mu T = a →
        ∫ x in T, f x ∂mu ≤ ∫ x in S, f x ∂mu := by
  rcases eq_or_lt_of_le (show 0 ≤ a from zero_le) with rfl | ha0
  · refine ⟨∅, MeasurableSet.empty, measure_empty, fun T _ hT => ?_⟩
    rw [setIntegral_measure_zero f hT, setIntegral_empty]
  rcases eq_or_lt_of_le ha with rfl | haU
  · refine ⟨Set.univ, MeasurableSet.univ, rfl, fun T hTm hT => ?_⟩
    have hcomp : mu Tᶜ = 0 := by
      apply (ENNReal.add_right_inj (measure_ne_top mu Set.univ)).mp
      calc
        mu Set.univ + mu Tᶜ = mu T + mu Tᶜ := by rw [hT]
        _ = mu Set.univ := measure_add_measure_compl hTm
        _ = mu Set.univ + 0 := by simp
    rw [setIntegral_univ, ← integral_add_compl hTm hfi,
      setIntegral_measure_zero f hcomp, add_zero]
  · obtain ⟨q, S, hSm, hSa, -, -, hmax⟩ :=
      exists_bathtub_maximizer_euclidean_interior mu hmu hfm hfi ha0 haU
    exact ⟨S, hSm, hSa, hmax⟩

/-- The strongest direct LS-curve/conductance component available from the current APIs.
At a prescribed mass `a ∈ (s,1/2]`, choose an exact bathtub maximizer and simultaneously
obtain the discounted boundary-flow lower bound supplied by `s`-conductance. -/
theorem exists_bathtub_maximizer_with_sConductance_boundary {n : Nat} [NeZero n]
    {P : Kernel (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n))}
    {pi : Measure (EuclideanSpace Real (Fin n))} [IsProbabilityMeasure pi] (hpi : pi ≪ volume)
    {f : EuclideanSpace Real (Fin n) → Real} (hfm : Measurable f) (hfi : Integrable f pi)
    {s a c : ENNReal} (hsa : s < a) (hahalf : a ≤ 1 / 2)
    (hc : c ≤ conductanceS P pi s) :
    ∃ S : Set (EuclideanSpace Real (Fin n)), MeasurableSet S ∧ pi S = a ∧
      (∀ T : Set (EuclideanSpace Real (Fin n)), MeasurableSet T → pi T = a →
        ∫ x in T, f x ∂pi ≤ ∫ x in S, f x ∂pi) ∧
      c * (a - s) ≤ flow P pi S Sᶜ := by
  have ha : a ≤ pi Set.univ := by
    rw [measure_univ]
    exact hahalf.trans (by norm_num)
  obtain ⟨S, hSm, hSa, hmax⟩ := exists_bathtub_maximizer_euclidean pi hpi hfm hfi ha
  refine ⟨S, hSm, hSa, hmax, ?_⟩
  rw [← hSa]
  exact conductanceS_mul_tsub_measure_le_flow P pi hc hSm (hSa.symm ▸ hsa)
    (hSa.symm ▸ hahalf)

#print axioms Arlib.MarkovChains.exists_measure_lt_le_bracket
#print axioms Arlib.MarkovChains.exists_measure_superlevel_bracket
#print axioms Arlib.MarkovChains.measure_sdiff_eq_measure_sdiff_of_eq
#print axioms Arlib.MarkovChains.setIntegral_le_of_between_superlevels
#print axioms Arlib.MarkovChains.exists_bathtub_maximizer_euclidean_interior
#print axioms Arlib.MarkovChains.exists_bathtub_maximizer_euclidean
#print axioms Arlib.MarkovChains.exists_bathtub_maximizer_with_sConductance_boundary

end Arlib.MarkovChains
