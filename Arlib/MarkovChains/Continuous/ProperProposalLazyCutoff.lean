/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Ttc.Exec.RawGaussianLazyStoppedExecution
import Arlib.Probability.TVCoupling
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# A finite cutoff for the actual lazy stopped Gaussian execution

`Ttc.RawGaussianLazyStoppedExecution` already supplies the source-faithful operational object:
each active lazy step runs the retained raw membership-query path until its next proper proposal,
its output law is exactly the lazy speedy iterate, and its expected recorded-query count obeys
the adjustable-radius `10/6` bound.  Here Markov's inequality converts that mean bound into the
constant timeout failure used by the Cousins--Vempala runtime proof.
-/

namespace Ttc.RawGaussianLazyStoppedExecution

open MeasureTheory ProbabilityTheory
open Arlib Arlib.MarkovChains
open scoped ENNReal

variable {n : Nat}

/-- Output the state after `t` lazy stopped steps if their directly recorded membership-query
count is below `cutoff`; use an arbitrary fixed fallback state on timeout. -/
noncomputable def cutoffOutput (fallback : State n) (t : Nat) (cutoff : ENNReal)
    (omega : Nat → ENNReal × State n) : State n :=
  if actualMembershipQueryCount t omega < cutoff then (omega t).2 else fallback

theorem measurable_cutoffOutput (fallback : State n) (t : Nat) (cutoff : ENNReal) :
    Measurable (cutoffOutput fallback t cutoff) := by
  apply Measurable.ite
  · exact measurableSet_lt (measurable_actualMembershipQueryCount t) measurable_const
  · exact measurable_snd.comp (measurable_pi_apply t)
  · exact measurable_const

/-- Markov cutoff for the raw execution, before using any geometric cost estimate. -/
theorem tvLe_cutoffOutput_of_lintegral_div_le
    {K : Set (State n)} (hK : MeasurableSet K) (delta s : Real) (hdelta : 0 < delta)
    (mu : Measure (State n)) [IsProbabilityMeasure mu]
    (fallback : State n) (t : Nat) {cutoff eta : ENNReal}
    (hcut0 : cutoff ≠ 0) (hcuttop : cutoff ≠ ⊤)
    (hmean : (∫⁻ omega, actualMembershipQueryCount t omega
        ∂lazyRawStoppedExecution K hK delta s hdelta mu) / cutoff ≤ eta) :
    Arlib.TVLe
      ((lazyRawStoppedExecution K hK delta s hdelta mu).map
        (cutoffOutput fallback t cutoff))
      (iterate (lazy (speedyMetropolisGaussian K delta s)) mu t) eta := by
  let xi := lazyRawStoppedExecution K hK delta s hdelta mu
  have htimeout : xi {omega | cutoff ≤ actualMembershipQueryCount t omega} ≤ eta := by
    exact (meas_ge_le_lintegral_div
      (measurable_actualMembershipQueryCount t).aemeasurable hcut0 hcuttop).trans hmean
  have hcoup : Arlib.TVLe
      (xi.map (cutoffOutput fallback t cutoff))
      (xi.map (fun omega => (omega t).2)) eta := by
    apply Arlib.tvLe_map_map_of_measure_ne_le
      (measurable_cutoffOutput fallback t cutoff)
      (measurable_snd.comp (measurable_pi_apply t))
    apply htimeout.trans' (measure_mono ?_)
    intro omega homega
    by_contra hnot
    simp [cutoffOutput] at homega
    exact hnot homega.1
  rw [map_lazyRawStoppedExecution_output hK delta s hdelta mu t] at hcoup
  exact hcoup

/-- Adjustable-radius actual-query cutoff.  The scalar budget is exactly what Markov needs:

`6 E[queries] ≤ 10 t M ≤ 6 (cutoff/20)`.

Consequently timeout has probability at most `1/20`.  The statement accepts an arbitrary
starting probability measure; its only distributional requirement is the same `M`-warmness
used by the expected-cost theorem. -/
theorem tvLe_cutoffOutput_one_twentieth_adjustable
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : Metric.ball (0 : State n) 1 ⊆ K)
    {q delta sigma R : Real} (hq : 1 < q)
    (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {M : ENNReal} {mu : Measure (State n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta (sigma ^ 2)))
    (fallback : State n) (t : Nat) {cutoff : ENNReal}
    (hcut0 : cutoff ≠ 0) (hcuttop : cutoff ≠ ⊤)
    (hbudget : 10 * ((t : ENNReal) * M) ≤ 6 * (cutoff / 20)) :
    Arlib.TVLe
      ((lazyRawStoppedExecution K hK delta (sigma ^ 2) hdelta mu).map
        (cutoffOutput fallback t cutoff))
      (iterate (lazy (speedyMetropolisGaussian K delta (sigma ^ 2))) mu t) (1 / 20) := by
  have hcost := six_mul_expected_actualMembershipQueryCount_le_ten_mul_adjustable
    hn hK hKc hball hq hdelta hsigma hdeltan hdeltaq hR hRsigma hKR hwarm t
  have hsix :
      6 * (∫⁻ omega, actualMembershipQueryCount t omega
          ∂lazyRawStoppedExecution K hK delta (sigma ^ 2) hdelta mu) ≤
        6 * (cutoff / 20) := hcost.trans hbudget
  have hmean :
      (∫⁻ omega, actualMembershipQueryCount t omega
          ∂lazyRawStoppedExecution K hK delta (sigma ^ 2) hdelta mu) ≤
        cutoff / 20 := by
    exact (ENNReal.mul_le_mul_iff_left
      (a := ∫⁻ omega, actualMembershipQueryCount t omega
        ∂lazyRawStoppedExecution K hK delta (sigma ^ 2) hdelta mu)
      (b := cutoff / 20) (c := 6) (by norm_num) (by norm_num)).mp (by
        simpa [mul_comm] using hsix)
  apply tvLe_cutoffOutput_of_lintegral_div_le hK delta (sigma ^ 2) hdelta mu
    fallback t hcut0 hcuttop
  calc
    (∫⁻ omega, actualMembershipQueryCount t omega
        ∂lazyRawStoppedExecution K hK delta (sigma ^ 2) hdelta mu) / cutoff
      ≤ (cutoff / 20) / cutoff := by gcongr
    _ = (cutoff / cutoff) / 20 := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = 1 / 20 := by rw [ENNReal.div_self hcut0 hcuttop]

/-- Final source runtime composition: if the lazy speedy iterate has TV error `eps`, the
finite actual-query execution with timeout has error at most `1/20 + eps`. -/
theorem tvLe_cutoffOutput_target_adjustable
    (hn : 2 ≤ n) {K : Set (State n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : Metric.ball (0 : State n) 1 ⊆ K)
    {q delta sigma R : Real} (hq : 1 < q)
    (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltaq : delta ≤ sigma / (max 8 (2 * q) * Real.sqrt n))
    (hR : 0 ≤ R) (hRsigma : R ≤ q * sigma * Real.sqrt n)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {M : ENNReal} {mu : Measure (State n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta (sigma ^ 2)))
    (fallback : State n) (t : Nat) {cutoff eps : ENNReal}
    (hcut0 : cutoff ≠ 0) (hcuttop : cutoff ≠ ⊤)
    (hbudget : 10 * ((t : ENNReal) * M) ≤ 6 * (cutoff / 20))
    {target : Measure (State n)}
    (hmix : Arlib.TVLe
      (iterate (lazy (speedyMetropolisGaussian K delta (sigma ^ 2))) mu t) target eps) :
    Arlib.TVLe
      ((lazyRawStoppedExecution K hK delta (sigma ^ 2) hdelta mu).map
        (cutoffOutput fallback t cutoff)) target (1 / 20 + eps) :=
  (tvLe_cutoffOutput_one_twentieth_adjustable hn hK hKc hball hq hdelta hsigma
    hdeltan hdeltaq hR hRsigma hKR hwarm fallback t hcut0 hcuttop hbudget).trans hmix

#print axioms Ttc.RawGaussianLazyStoppedExecution.measurable_cutoffOutput
#print axioms Ttc.RawGaussianLazyStoppedExecution.tvLe_cutoffOutput_of_lintegral_div_le
#print axioms Ttc.RawGaussianLazyStoppedExecution.tvLe_cutoffOutput_one_twentieth_adjustable
#print axioms Ttc.RawGaussianLazyStoppedExecution.tvLe_cutoffOutput_target_adjustable

end Ttc.RawGaussianLazyStoppedExecution
