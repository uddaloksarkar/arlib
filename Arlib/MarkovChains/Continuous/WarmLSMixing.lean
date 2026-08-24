/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.MarkovChains.Continuous.WarmLSCurveRecurrence

/-!
# Warm-start Euclidean mixing from `s`-conductance
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

theorem setIntegral_nonneg_density_eq_measureReal {Omega : Type*} [MeasurableSpace Omega]
    {pi : Measure Omega} {h : Omega → Real} (hhm : Measurable h) (hh0 : ∀ x, 0 ≤ h x)
    {S : Set Omega} (hS : MeasurableSet S) :
    ∫ x in S, h x ∂pi =
      (pi.withDensity (fun x => ENNReal.ofReal (h x)) S).toReal := by
  rw [withDensity_apply _ hS]
  exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hh0)
    hhm.aestronglyMeasurable

/-- Warmness supplies the source square-root envelope at time zero. -/
theorem exactMassLSCurve_base_of_isWarm {Omega : Type*} [MeasurableSpace Omega]
    {pi mu : Measure Omega} [IsProbabilityMeasure pi] [IsProbabilityMeasure mu]
    {h : Omega → Real} (hhm : Measurable h) (hh0 : ∀ x, 0 ≤ h x) (hhint : Integrable h pi)
    (hrepr : mu = pi.withDensity (fun x => ENNReal.ofReal (h x)))
    {F : Real → Real} (hcurve : IsExactMassLSCurve pi (fun x => h x - 1) F)
    {M s : Real} (hM : 1 ≤ M) (hs0 : 0 ≤ s)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu pi) :
    ∀ x, s ≤ x → x ≤ 1 - s → F x ≤ M * s + M * lsShape s x := by
  intro x hxl hxu
  have hx0 : x ∈ Icc (0 : Real) 1 := ⟨hs0.trans hxl, by linarith⟩
  obtain ⟨S, hS, hSx, hFx, -⟩ := hcurve x hx0
  have hpiReal : (pi S).toReal = x := by rw [hSx, ENNReal.toReal_ofReal hx0.1]
  have hmuReal : ∫ z in S, h z ∂pi = (mu S).toReal := by
    rw [hrepr]
    exact setIntegral_nonneg_density_eq_measureReal hhm hh0 hS
  have hcenter : F x = (mu S).toReal - x := by
    rw [hFx, integral_sub hhint.integrableOn (integrable_const (1 : Real)),
      hmuReal, setIntegral_const, smul_eq_mul, mul_one, measureReal_def, hpiReal]
  have hw := hwarm S hS
  have hwreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top pi S)) hw
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ M), hpiReal] at hwreal
  have hmuone : (mu S).toReal ≤ 1 :=
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  by_cases hside : x - s ≤ 1 - x - s
  · have hz0 : 0 ≤ x - s := sub_nonneg.mpr hxl
    have hz1 : x - s ≤ 1 := by linarith
    have hzsqrt : x - s ≤ Real.sqrt (x - s) := Real.le_sqrt_self_iff.mpr hz1
    rw [lsShape, min_eq_left hside]
    nlinarith
  · have hside' : 1 - x - s ≤ x - s := le_of_not_ge hside
    have hz0 : 0 ≤ 1 - x - s := by linarith
    have hz1 : 1 - x - s ≤ 1 := by linarith
    have hzsqrt : 1 - x - s ≤ Real.sqrt (1 - x - s) := Real.le_sqrt_self_iff.mpr hz1
    rw [lsShape, min_eq_right hside']
    nlinarith

/-- A uniform bound on an exact-mass curve bounds TV for its density law. -/
theorem tvLe_withDensity_of_exactMassLSCurve_uniform {Omega : Type*} [MeasurableSpace Omega]
    {pi : Measure Omega} [IsProbabilityMeasure pi] {h : Omega → Real}
    (hhm : Measurable h) (hh0 : ∀ x, 0 ≤ h x) (hhint : Integrable h pi)
    (hmean : ∫ x, h x ∂pi = 1) {F : Real → Real}
    (hcurve : IsExactMassLSCurve pi (fun x => h x - 1) F)
    {D : Real} (hD0 : 0 ≤ D) (hFD : ∀ x, x ∈ Icc (0 : Real) 1 → F x ≤ D) :
    Arlib.TVLe (pi.withDensity fun x => ENNReal.ofReal (h x)) pi (ENNReal.ofReal D) := by
  have hmuuniv : (pi.withDensity fun x => ENNReal.ofReal (h x)) Set.univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hhint (Eventually.of_forall hh0), hmean]
    simp
  letI : IsProbabilityMeasure (pi.withDensity fun x => ENNReal.ofReal (h x)) := ⟨hmuuniv⟩
  refine tvLe_of_forall_le fun S hS => ?_
  have hx : (pi S).toReal ∈ Icc (0 : Real) 1 := ⟨ENNReal.toReal_nonneg,
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)⟩
  obtain ⟨-, -, -, -, hmax⟩ := hcurve (pi S).toReal hx
  let w : Omega → Real := S.indicator fun _ => 1
  have hwm : Measurable w := measurable_const.indicator hS
  have hmass : ∫ x, w x ∂pi = (pi S).toReal := by
    simpa [w, measureReal_def] using integral_indicator_const (μ := pi) (1 : Real) hS
  have hbound := hmax w hwm (fun x => by by_cases hx : x ∈ S <;> simp [w, hx])
    (fun x => by by_cases hx : x ∈ S <;> simp [w, hx]) hmass
  have hprod : ∫ x, (h x - 1) * w x ∂pi = ∫ x in S, (h x - 1) ∂pi := by
    rw [← integral_indicator hS]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ S <;> simp [w, hx]
  rw [hprod] at hbound
  have hcenter : ∫ x in S, h x ∂pi ≤ (pi S).toReal + D := by
    have hsplit : ∫ x in S, (h x - 1) ∂pi =
        (∫ x in S, h x ∂pi) - (pi S).toReal := by
      rw [integral_sub hhint.integrableOn (integrable_const (1 : Real)),
        setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    linarith [hFD _ hx]
  have hmuS : (pi.withDensity fun x => ENNReal.ofReal (h x)) S =
      ENNReal.ofReal (∫ x in S, h x ∂pi) := by
    rw [withDensity_apply _ hS,
      ← ofReal_integral_eq_lintegral_ofReal hhint.restrict (Eventually.of_forall hh0)]
  have hpiS : pi S = ENNReal.ofReal (pi S).toReal :=
    (ENNReal.ofReal_toReal (measure_ne_top pi S)).symm
  rw [hmuS, hpiS, ← ENNReal.ofReal_add ENNReal.toReal_nonneg hD0]
  exact ENNReal.ofReal_le_ofReal hcenter

/-- Warm-specialized Lovász--Simonovits TV decay for lazy reversible Euclidean chains. -/
theorem tvLe_iterate_lazy_of_sConductance_euclidean {n : Nat} [NeZero n]
    {P : Kernel (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n))}
    [IsMarkovKernel P] {pi mu : Measure (EuclideanSpace Real (Fin n))}
    [IsProbabilityMeasure pi] [IsProbabilityMeasure mu]
    (hrev : IsReversible P pi) (hpi : pi ≪ volume)
    {M s ph : Real} (hM : 1 ≤ M) (hs0 : 0 ≤ s) (hshalf : s ≤ 1 / 2)
    (hph0 : 0 ≤ ph) (hphhalf : ph ≤ 1 / 2)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu pi)
    (hc : ENNReal.ofReal ph ≤ conductanceS (lazy P) pi (ENNReal.ofReal s)) (t : Nat) :
    Arlib.TVLe (iterate (lazy P) mu t) pi
      (ENNReal.ofReal (M * s + M * (1 - ph ^ 2 / 2) ^ t)) := by
  obtain ⟨h, hhm, hh0, hhLp, hmean, hrepr⟩ :=
    exists_density_memLp_two_of_isWarm hM hwarm
  obtain ⟨F, hconc, hcurve⟩ :=
    exists_concave_exactMassLSCurve_family_euclidean pi hpi (isReversible_lazy hrev) hhm hhLp
  have hstep := exactMassLSCurve_oneStep_conductanceS hrev hhm hhLp hconc hcurve hs0 hph0 hc
  have hbase := exactMassLSCurve_base_of_isWarm hhm hh0 (hhLp.integrable (by norm_num))
    hrepr (by simpa using hcurve 0) hM hs0 hwarm
  have hdecay := lsCurve_uniform_decay hs0 (by positivity : 0 ≤ M) hph0 hphhalf hstep hbase
  rw [hrepr, iterate_withDensity_ofReal (isReversible_lazy hrev) hhm hh0 hhLp t]
  apply tvLe_withDensity_of_exactMassLSCurve_uniform
    (measurable_markovIter (lazy P) hhm t) (markovIter_nonneg (lazy P) hh0 t)
    ((memLp_markovIter (isReversible_lazy hrev).invariant hhm hhLp t).integrable (by norm_num))
  · rw [integral_markovIter (isReversible_lazy hrev) hhm hhLp t]
    exact hmean
  · exact hcurve t
  · have hr0 : 0 ≤ 1 - ph ^ 2 / 2 := by nlinarith [sq_nonneg ph]
    exact add_nonneg (mul_nonneg (by linarith) hs0)
      (mul_nonneg (by linarith) (pow_nonneg hr0 t))
  · intro x hx
    by_cases hxs : x ≤ s
    · obtain ⟨S, hS, hSx, hFx, -⟩ := hcurve t x hx
      have hwarmt := isWarm_iterate_of_invariant hwarm (isReversible_lazy hrev).invariant t
      have hmuEq := iterate_withDensity_ofReal (isReversible_lazy hrev) hhm hh0 hhLp t
      have hbound := hwarmt S hS
      rw [hrepr, hmuEq] at hbound
      have hreal := ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top pi S)) hbound
      have hxreal : (pi S).toReal = x := by rw [hSx, ENNReal.toReal_ofReal hx.1]
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith : 0 ≤ M), hxreal] at hreal
      have hset := setIntegral_nonneg_density_eq_measureReal (pi := pi)
        (measurable_markovIter (lazy P) hhm t) (markovIter_nonneg (lazy P) hh0 t) hS
      rw [hFx, integral_sub
        ((memLp_markovIter (isReversible_lazy hrev).invariant hhm hhLp t).integrable
          (by norm_num)).integrableOn (integrable_const (1 : Real)),
        hset, setIntegral_const, smul_eq_mul, mul_one, measureReal_def, hxreal]
      nlinarith [pow_nonneg (by nlinarith [sq_nonneg ph] : 0 ≤ 1 - ph ^ 2 / 2) t]
    · by_cases hxu : x ≤ 1 - s
      · exact hdecay t x (le_of_not_ge hxs) hxu
      · obtain ⟨S, hS, hSx, hFx, -⟩ := hcurve t x hx
        have hmuone : ((iterate (lazy P) mu t) S).toReal ≤ 1 :=
          ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
        have hiterEq := iterate_withDensity_ofReal (isReversible_lazy hrev) hhm hh0 hhLp t
        have hlaw : iterate (lazy P) mu t =
            pi.withDensity (fun x => ENNReal.ofReal (markovIter (lazy P) h t x)) := by
          rw [hrepr]
          exact hiterEq
        have hset := setIntegral_nonneg_density_eq_measureReal (pi := pi)
          (measurable_markovIter (lazy P) hhm t) (markovIter_nonneg (lazy P) hh0 t) hS
        rw [← hlaw] at hset
        have hxreal : (pi S).toReal = x := by rw [hSx, ENNReal.toReal_ofReal hx.1]
        rw [hFx, integral_sub
          ((memLp_markovIter (isReversible_lazy hrev).invariant hhm hhLp t).integrable
            (by norm_num)).integrableOn (integrable_const (1 : Real)),
          hset, setIntegral_const, smul_eq_mul, mul_one, measureReal_def, hxreal]
        nlinarith [pow_nonneg (by nlinarith [sq_nonneg ph] : 0 ≤ 1 - ph ^ 2 / 2) t]

/-- Deadline form: choose `s = eps/(2M)` and obtain the standard warm-start TV guarantee
without an `hLSs` binder. -/
theorem tvLe_iterate_lazy_of_sConductance_warm_euclidean {n : Nat} [NeZero n]
    {P : Kernel (EuclideanSpace Real (Fin n)) (EuclideanSpace Real (Fin n))}
    [IsMarkovKernel P] {pi mu : Measure (EuclideanSpace Real (Fin n))}
    [IsProbabilityMeasure pi] [IsProbabilityMeasure mu]
    (hrev : IsReversible P pi) (hpi : pi ≪ volume)
    {M ph eps : Real} (hM : 1 ≤ M) (hph0 : 0 < ph) (hphhalf : ph ≤ 1 / 2)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu pi)
    (hc : ENNReal.ofReal ph ≤
      conductanceS (lazy P) pi (ENNReal.ofReal (eps / (2 * M))))
    {m : Nat} (hm : lsThresholdS M ph eps ≤ (m : Real)) :
    Arlib.TVLe (iterate (lazy P) mu m) pi (ENNReal.ofReal eps) := by
  have hM0 : 0 < M := lt_of_lt_of_le one_pos hM
  have hs0 : 0 ≤ eps / (2 * M) := by positivity
  have hshalf : eps / (2 * M) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hdecay := tvLe_iterate_lazy_of_sConductance_euclidean hrev hpi hM hs0 hshalf
    hph0.le hphhalf hwarm hc m
  refine hdecay.mono (ENNReal.ofReal_le_ofReal ?_)
  have hpow := mul_pow_le_of_lsThresholdS_le hM hph0 (hphhalf.trans (by norm_num)) heps0 hm
  have hsimp : M * (eps / (2 * M)) = eps / 2 := by field_simp
  rw [hsimp]
  linarith

#print axioms Arlib.MarkovChains.exactMassLSCurve_base_of_isWarm
#print axioms Arlib.MarkovChains.tvLe_withDensity_of_exactMassLSCurve_uniform
#print axioms Arlib.MarkovChains.tvLe_iterate_lazy_of_sConductance_euclidean
#print axioms Arlib.MarkovChains.tvLe_iterate_lazy_of_sConductance_warm_euclidean

end Arlib.MarkovChains
