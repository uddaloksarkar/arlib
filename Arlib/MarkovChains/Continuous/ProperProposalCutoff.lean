/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.MarkovChains.Continuous.ProperProposalCostedRestart
import Arlib.Probability.TVCoupling
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Finite cutoffs for costed proper-proposal executions

The source runtime argument needs only constant timeout failure.  Markov's inequality therefore
converts the existing expected membership-proposal bound into a finite operational cutoff,
without any deterministic-time mixing theorem for the ordinary Metropolis chain.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- Return the intended state after `t` independently restarted costed steps when their total
cost is below `cutoff`; return an arbitrary fixed fallback state on timeout. -/
noncomputable def restartedCutoffOutput (fallback : S) (t : Nat) (cutoff : ENNReal)
    (omega : Nat → ENNReal × S) : S :=
  if restartedTotalCost t omega < cutoff then (omega t).2 else fallback

theorem measurable_restartedCutoffOutput (fallback : S) (t : Nat) (cutoff : ENNReal) :
    Measurable (restartedCutoffOutput fallback t cutoff) := by
  apply Measurable.ite
  · exact measurableSet_lt (measurable_restartedTotalCost t) measurable_const
  · exact measurable_snd.comp (measurable_pi_apply t)
  · exact measurable_const

/-- Generic cutoff coupling: if expected total cost divided by the cutoff is at most `eta`,
the cutoff output law is within `eta` of the unbounded costed execution's output law. -/
theorem tvLe_restartedCutoffOutput_of_lintegral_div_le
    (Q : Kernel S (ENNReal × S)) [IsMarkovKernel Q]
    (mu : Measure S) [IsProbabilityMeasure mu] (fallback : S) (t : Nat)
    {cutoff eta : ENNReal} (hcut0 : cutoff ≠ 0) (hcuttop : cutoff ≠ ⊤)
    (hmean : (∫⁻ omega, restartedTotalCost t omega ∂(restartedCostExecution Q mu)) /
      cutoff ≤ eta) :
    Arlib.TVLe
      ((restartedCostExecution Q mu).map (restartedCutoffOutput fallback t cutoff))
      ((restartedCostExecution Q mu).map (fun omega => (omega t).2)) eta := by
  let xi := restartedCostExecution Q mu
  have htimeout : xi {omega | cutoff ≤ restartedTotalCost t omega} ≤ eta := by
    exact (meas_ge_le_lintegral_div
      (measurable_restartedTotalCost t).aemeasurable hcut0 hcuttop).trans hmean
  apply Arlib.tvLe_map_map_of_measure_ne_le
    (measurable_restartedCutoffOutput fallback t cutoff)
    (measurable_snd.comp (measurable_pi_apply t))
  exact htimeout.trans' (measure_mono (by
    intro omega homega
    by_contra hnot
    simp [restartedCutoffOutput] at homega
    exact hnot homega.1))

/-- Convenient `1/20` form.  The hypothesis is deliberately multiplicative, matching the
existing radius-four estimate `3 * E[cost] ≤ 10 * t * M`. -/
theorem tvLe_restartedCutoffOutput_one_twentieth_of_three_mul_lintegral_le
    (Q : Kernel S (ENNReal × S)) [IsMarkovKernel Q]
    (mu : Measure S) [IsProbabilityMeasure mu] (fallback : S) (t : Nat)
    {cutoff B : ENNReal} (hcut0 : cutoff ≠ 0) (hcuttop : cutoff ≠ ⊤)
    (hmean : 3 * (∫⁻ omega, restartedTotalCost t omega ∂(restartedCostExecution Q mu))
      ≤ B)
    (hbudget : B ≤ 3 * (cutoff / 20)) :
    Arlib.TVLe
      ((restartedCostExecution Q mu).map (restartedCutoffOutput fallback t cutoff))
      ((restartedCostExecution Q mu).map (fun omega => (omega t).2)) (1 / 20) := by
  have hthree :
      3 * (∫⁻ omega, restartedTotalCost t omega ∂(restartedCostExecution Q mu)) ≤
        3 * (cutoff / 20) := hmean.trans hbudget
  have hmean' :
      (∫⁻ omega, restartedTotalCost t omega ∂(restartedCostExecution Q mu)) ≤
        cutoff / 20 := by
    apply (ENNReal.mul_le_mul_iff_left (a :=
      ∫⁻ omega, restartedTotalCost t omega ∂(restartedCostExecution Q mu))
      (b := cutoff / 20) (c := 3) (by norm_num) (by norm_num)).mp
    simpa [mul_comm] using hthree
  apply tvLe_restartedCutoffOutput_of_lintegral_div_le Q mu fallback t hcut0 hcuttop
  calc
    (∫⁻ omega, restartedTotalCost t omega ∂(restartedCostExecution Q mu)) / cutoff
        ≤ (cutoff / 20) / cutoff := by gcongr
    _ = (cutoff / cutoff) / 20 := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = 1 / 20 := by rw [ENNReal.div_self hcut0 hcuttop]

/-! ## Gaussian operational specialization -/

variable {n : Nat}

/-- Source-faithful radius-four runtime capstone.  The unbounded independently restarted
execution has exactly the `t`-step speedy law.  Cutting it off at a budget satisfying the
displayed scalar inequality adds at most `1/20` to any speedy-iterate TV guarantee.

Each cost increment is realized by actual ordinary Gaussian proposals stopped at the next
proper proposal; no claim about deterministic-time ordinary-chain mixing is used. -/
theorem tvLe_cutoff_properProposalExecution_radius_four
    (hn : 2 ≤ n) {K : Set (GaussianState n)} (hK : MeasurableSet K)
    (hKc : Convex Real K) (hball : Metric.ball (0 : GaussianState n) 1 ⊆ K)
    {delta sigma R : Real} (hdelta : 0 < delta) (hsigma : 0 < sigma)
    (hdeltan : delta ≤ 1 / (2 * (n : Real)))
    (hdeltasigma : delta ≤ sigma / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    (hRsigma : R ≤ 4 * sigma * Real.sqrt n) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {M : ENNReal} {mu : Measure (GaussianState n)} [IsProbabilityMeasure mu]
    (hwarm : IsWarm M mu (ellGaussianProb K delta (sigma ^ 2)))
    (fallback : GaussianState n) (t : Nat) {cutoff eps : ENNReal}
    (hcut0 : cutoff ≠ 0) (hcuttop : cutoff ≠ ⊤)
    (hbudget : 10 * ((t : ENNReal) * M) ≤ 3 * (cutoff / 20))
    {target : Measure (GaussianState n)}
    (hmix : Arlib.TVLe (iterate (speedyMetropolisGaussian K delta (sigma ^ 2)) mu t)
      target eps) :
    Arlib.TVLe
      ((restartedCostExecution
          (properProposalCostedKernel K hK delta (sigma ^ 2)) mu).map
        (restartedCutoffOutput fallback t cutoff))
      target (1 / 20 + eps) := by
  have hcost := three_mul_lintegral_properProposalTotalCost_le_ten_mul_radius_four
    hn hK hKc hball hdelta hsigma hdeltan hdeltasigma hR hRsigma hKR hwarm t
  have htimeout :=
    tvLe_restartedCutoffOutput_one_twentieth_of_three_mul_lintegral_le
      (properProposalCostedKernel K hK delta (sigma ^ 2)) mu fallback t
      hcut0 hcuttop hcost hbudget
  rw [map_properProposalCostedExecution_output hK delta (sigma ^ 2) mu t] at htimeout
  exact htimeout.trans hmix

#print axioms Arlib.MarkovChains.measurable_restartedCutoffOutput
#print axioms Arlib.MarkovChains.tvLe_restartedCutoffOutput_of_lintegral_div_le
#print axioms Arlib.MarkovChains.tvLe_restartedCutoffOutput_one_twentieth_of_three_mul_lintegral_le
#print axioms Arlib.MarkovChains.tvLe_cutoff_properProposalExecution_radius_four

end Arlib.MarkovChains
