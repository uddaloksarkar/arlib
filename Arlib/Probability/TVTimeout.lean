/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Probability.TVKernelHeterogeneous
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Transferring timeout bounds through total variation

An unbounded-cost experiment can have a small expected cost from an ideal warm start while
the operational start is only TV-close to that ideal law.  TV alone cannot compare the
unbounded expectations.  It *can* compare the bounded timeout event.  Markov's inequality
controls that event under the ideal law and randomized data processing transfers it to the
actual law.

This is the sound replacement for the false step `TVLe -> IsWarm` in a sequential Gaussian
cooling execution.
-/

namespace Arlib

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

/-- Multiplied form of the timeout transfer, avoiding any finiteness side conditions on the
threshold.  If the ideal expected cost is at most `B`, then

`L * P_actual(cost >= L) <= B + L * eps`.
-/
theorem mul_bind_kernel_timeout_le_of_tvLe
    {mu nu : Measure E} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps : ENNReal} (htv : TVLe mu nu eps)
    (P : Kernel E F) [IsMarkovKernel P]
    (cost : F -> ENNReal) (hcost : Measurable cost)
    (L B : ENNReal)
    (hmean : (∫⁻ y, cost y ∂nu.bind P) <= B) :
    L * (mu.bind P) {y | L <= cost y} <= B + L * eps := by
  have hS : MeasurableSet {y | L <= cost y} :=
    measurableSet_le measurable_const hcost
  have htvS : (mu.bind P) {y | L <= cost y} <=
      (nu.bind P) {y | L <= cost y} + eps :=
    htv.bind_kernel_apply_le P hS
  calc
    L * (mu.bind P) {y | L <= cost y}
        <= L * ((nu.bind P) {y | L <= cost y} + eps) := by gcongr
    _ = L * (nu.bind P) {y | L <= cost y} + L * eps := by
      rw [mul_add]
    _ <= (∫⁻ y, cost y ∂nu.bind P) + L * eps := by
      gcongr
      exact mul_meas_ge_le_lintegral hcost L
    _ <= B + L * eps := by gcongr

/-- Divided probability form.  A positive finite timeout `L` gives the familiar

`P_actual(cost >= L) <= B / L + eps`.
-/
theorem bind_kernel_timeout_le_of_tvLe
    {mu nu : Measure E} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps : ENNReal} (htv : TVLe mu nu eps)
    (P : Kernel E F) [IsMarkovKernel P]
    (cost : F -> ENNReal) (hcost : Measurable cost)
    {L B : ENNReal} (hL0 : L ≠ 0) (hLtop : L ≠ ⊤)
    (hmean : (∫⁻ y, cost y ∂nu.bind P) <= B) :
    (mu.bind P) {y | L <= cost y} <= B / L + eps := by
  have hmul := mul_bind_kernel_timeout_le_of_tvLe htv P cost hcost L B hmean
  have hdiv : (mu.bind P) {y | L <= cost y} <= (B + L * eps) / L := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hL0) (Or.inl hLtop)).2
    simpa [mul_comm] using hmul
  calc
    (mu.bind P) {y | L <= cost y} <= (B + L * eps) / L := hdiv
    _ = B / L + eps := by
      rw [ENNReal.add_div, mul_comm L eps, ENNReal.mul_div_cancel_right hL0 hLtop]

#print axioms mul_bind_kernel_timeout_le_of_tvLe
#print axioms bind_kernel_timeout_le_of_tvLe

end Arlib
