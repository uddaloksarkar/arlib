/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.MarkovChains.Continuous.L2Mixing
import Arlib.MarkovChains.Continuous.EuclideanBathtub

/-!
# The first operator identity in the warm-start LS recursion

For a reversible chain and an `L2` density `h`, the discrepancy of the next density on a set
`S` is the current centered density paired with the one-step set profile `x ↦ P x S`.
This is the exact starting identity of the Lovasz--Simonovits curve recursion.  The remaining
step is a sharp rearrangement inequality for that set profile, using laziness and its boundary
flow; it is deliberately not hidden behind an LS-shaped predicate here.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A finite warm probability law has an honest nonnegative `L2` density of mean one.

This packages the Radon--Nikodym construction previously embedded inside the ordinary
conductance mixing proof, so the LS recursion can start from a concrete density. -/
theorem exists_density_memLp_two_of_isWarm {pi mu : Measure Omega}
    [IsProbabilityMeasure pi] [IsProbabilityMeasure mu] {M : Real} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu pi) :
    ∃ h : Omega → Real, Measurable h ∧ (∀ x, 0 ≤ h x) ∧ MemLp h 2 pi ∧
      ∫ x, h x ∂pi = 1 ∧ mu = pi.withDensity (fun x => ENNReal.ofReal (h x)) := by
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM
  have hac : mu ≪ pi := by
    refine Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_
    have hs := hwarm S hS
    rw [hS0, mul_zero] at hs
    exact nonpos_iff_eq_zero.mp hs
  let r : Omega → ENNReal := mu.rnDeriv pi
  let h : Omega → Real := fun x => (r x).toReal
  have hrm : Measurable r := Measure.measurable_rnDeriv mu pi
  have hrlt : ∀ᵐ x ∂pi, r x < ⊤ := Measure.rnDeriv_lt_top mu pi
  have hhm : Measurable h := hrm.ennreal_toReal
  have hh0 : ∀ x, 0 ≤ h x := fun _ => ENNReal.toReal_nonneg
  have hofReal : (fun x => ENNReal.ofReal (h x)) =ᵐ[pi] r := by
    filter_upwards [hrlt] with x hx
    exact ENNReal.ofReal_toReal hx.ne
  have hrepr : pi.withDensity (fun x => ENNReal.ofReal (h x)) = mu := by
    rw [withDensity_congr_ae hofReal]
    exact Measure.withDensity_rnDeriv_eq mu pi hac
  have hrint : ∫⁻ x, r x ∂pi = 1 := by
    have hu : (pi.withDensity r) Set.univ = 1 := by
      rw [Measure.withDensity_rnDeriv_eq mu pi hac, measure_univ]
    rwa [withDensity_apply r MeasurableSet.univ, Measure.restrict_univ] at hu
  have hmean : ∫ x, h x ∂pi = 1 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hh0)
      hhm.aestronglyMeasurable, lintegral_congr_ae hofReal, hrint]
    simp
  have hsqae : (fun x => ENNReal.ofReal (h x ^ 2)) =ᵐ[pi] fun x => r x * r x := by
    filter_upwards [hrlt] with x hx
    rw [pow_two, ENNReal.ofReal_mul (hh0 x)]
    change ENNReal.ofReal (r x).toReal * ENNReal.ofReal (r x).toReal = r x * r x
    rw [ENNReal.ofReal_toReal hx.ne]
  have hsqbound : ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂pi ≤ ENNReal.ofReal M := by
    rw [lintegral_congr_ae hsqae]
    have h1 : ∫⁻ x, r x ∂( pi.withDensity r) = ∫⁻ x, r x * r x ∂pi := by
      rw [lintegral_withDensity_eq_lintegral_mul pi hrm hrm]
      rfl
    rw [← h1, Measure.withDensity_rnDeriv_eq mu pi hac]
    calc
      ∫⁻ x, r x ∂mu ≤ ∫⁻ x, r x ∂(ENNReal.ofReal M • pi) :=
        lintegral_mono' ((isWarm_iff_le_smul _ _).mp hwarm) le_rfl
      _ = ENNReal.ofReal M * ∫⁻ x, r x ∂pi := lintegral_smul_measure _ _
      _ = ENNReal.ofReal M := by rw [hrint, mul_one]
  have hhmem : MemLp h 2 pi := by
    refine (memLp_two_iff_integrable_sq hhm.aestronglyMeasurable).2 ?_
    refine ⟨(hhm.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => sq_nonneg (h x))]
    exact lt_of_le_of_lt hsqbound ENNReal.ofReal_lt_top
  exact ⟨h, hhm, hh0, hhmem, hmean, hrepr.symm⟩

/-- Reversibility moves the Markov operator from a density to a set indicator, after centering.

`integral_S (T h - 1) = integral (h - 1) * T(1_S)`.
-/
theorem setIntegral_markovOp_sub_one_eq_centered_mul_markovOp_indicator
    {P : Kernel Omega Omega} [IsMarkovKernel P] {pi : Measure Omega}
    [IsProbabilityMeasure pi] (hrev : IsReversible P pi)
    {h : Omega → Real} (hh : Measurable h) (hhmem : MemLp h 2 pi)
    {S : Set Omega} (hS : MeasurableSet S) :
    ∫ x in S, (markovOp P h x - 1) ∂pi =
      ∫ x, (h x - 1) * markovOp P (Set.indicator S fun _ => (1 : Real)) x ∂pi := by
  let i : Omega → Real := Set.indicator S fun _ => (1 : Real)
  have hi : Measurable i := measurable_const.indicator hS
  have himem : MemLp i 2 pi := memLp_two_indicator hS
  have hTimem : MemLp (markovOp P i) 2 pi := memLp_markovOp hrev.invariant hi himem
  have hThmem : MemLp (markovOp P h) 2 pi := memLp_markovOp hrev.invariant hh hhmem
  have hpair : ∫ x, i x * markovOp P h x ∂pi = ∫ x, h x * markovOp P i x ∂pi := by
    have hih := integrable_mul_compProd hrev hi hh himem hhmem
    have hhi := integrable_mul_compProd hrev hh hi hhmem himem
    calc
      (∫ x, i x * markovOp P h x ∂pi) = pairing P pi i h :=
        (pairing_eq_integral_mul_markovOp hih).symm
      _ = pairing P pi h i := pairing_comm hrev hi hh
      _ = ∫ x, h x * markovOp P i x ∂pi := pairing_eq_integral_mul_markovOp hhi
  have hTi : ∫ x, markovOp P i x ∂pi = (pi S).toReal := by
    rw [integral_markovOp hrev hi (himem.integrable (by norm_num))]
    simpa [i, measureReal_def] using integral_indicator_const (1 : Real) hS
  have hleft : ∫ x in S, (markovOp P h x - 1) ∂pi =
      (∫ x, i x * markovOp P h x ∂pi) - (pi S).toReal := by
    rw [integral_sub ((hThmem.integrable (by norm_num)).integrableOn)
      (integrable_const (1 : Real)),
      setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    congr 1
    rw [← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S <;> simp [i, hx]
  have hright : ∫ x, (h x - 1) * markovOp P i x ∂pi =
      (∫ x, h x * markovOp P i x ∂pi) - (pi S).toReal := by
    have hprod : Integrable (h * markovOp P i) pi := hhmem.integrable_mul hTimem
    have hprod' : Integrable (fun x => h x * markovOp P i x) pi :=
      hprod.congr (Eventually.of_forall fun _ => rfl)
    have hTiInt : Integrable (markovOp P i) pi := hTimem.integrable (by norm_num)
    have hfun : (fun x => (h x - 1) * markovOp P i x) =
        fun x => h x * markovOp P i x - markovOp P i x := by
      funext x
      ring
    rw [hfun, integral_sub hprod' hTiInt, hTi]
  rw [hleft, hright, hpair]

/-- **Warm LS one-step package.**  At time `t+1`, choose the exact bathtub top set of mass
`a`; it has the `s`-conductance boundary lower bound, and its discrepancy is exactly the
current centered density paired with the set profile `T 1_S`.

This reaches the last source-specific analytic step before the LS midpoint recursion. -/
theorem exists_warm_ls_topSet_oneStep {n : Nat} [NeZero n]
    {P : Kernel (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n))}
    [IsMarkovKernel P] {pi mu : Measure (EuclideanSpace Real (Fin n))}
    [IsProbabilityMeasure pi] [IsProbabilityMeasure mu]
    (hrev : IsReversible P pi) (hpi : pi ≪ volume) {M : Real} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu pi) (t : Nat)
    {s a c : ENNReal} (hsa : s < a) (hahalf : a ≤ 1 / 2)
    (hc : c ≤ conductanceS P pi s) :
    ∃ (h : EuclideanSpace Real (Fin n) → Real)
      (S : Set (EuclideanSpace Real (Fin n))),
      Measurable h ∧ (∀ x, 0 ≤ h x) ∧ MemLp h 2 pi ∧
      mu = pi.withDensity (fun x => ENNReal.ofReal (h x)) ∧
      MeasurableSet S ∧ pi S = a ∧
      (∀ T : Set (EuclideanSpace Real (Fin n)), MeasurableSet T → pi T = a →
        ∫ x in T, (markovIter P h (t + 1) x - 1) ∂pi ≤
          ∫ x in S, (markovIter P h (t + 1) x - 1) ∂pi) ∧
      c * (a - s) ≤ flow P pi S Sᶜ ∧
      ∫ x in S, (markovIter P h (t + 1) x - 1) ∂pi =
        ∫ x, (markovIter P h t x - 1) *
          markovOp P (Set.indicator S fun _ => (1 : Real)) x ∂pi := by
  obtain ⟨h, hhm, hh0, hhmem, -, hrepr⟩ := exists_density_memLp_two_of_isWarm hM hwarm
  have htm : Measurable (markovIter P h (t + 1)) := measurable_markovIter P hhm _
  have htmem : MemLp (markovIter P h (t + 1)) 2 pi :=
    memLp_markovIter hrev.invariant hhm hhmem _
  have hfint : Integrable (fun x => markovIter P h (t + 1) x - 1) pi :=
    (htmem.integrable (by norm_num)).sub (integrable_const (1 : Real))
  obtain ⟨S, hSm, hSa, hmax, hflow⟩ :=
    exists_bathtub_maximizer_with_sConductance_boundary hpi (htm.sub_const 1) hfint
      hsa hahalf hc
  refine ⟨h, S, hhm, hh0, hhmem, hrepr, hSm, hSa, hmax, hflow, ?_⟩
  simpa only [markovIter_succ] using
    (setIntegral_markovOp_sub_one_eq_centered_mul_markovOp_indicator hrev
      (measurable_markovIter P hhm t) (memLp_markovIter hrev.invariant hhm hhmem t) hSm)

#print axioms Arlib.MarkovChains.setIntegral_markovOp_sub_one_eq_centered_mul_markovOp_indicator
#print axioms Arlib.MarkovChains.exists_density_memLp_two_of_isWarm
#print axioms Arlib.MarkovChains.exists_warm_ls_topSet_oneStep

end Arlib.MarkovChains
