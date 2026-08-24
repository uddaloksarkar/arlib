/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Probability.TVKernel

/-!
# Total-variation data processing through a heterogeneous kernel

`TVKernel.lean` proves data processing for `Kernel E E`.  Operational executions usually
change type: a state kernel returns a cost/output pair.  This file packages the same fact
for `Kernel E F`.  In particular, a bounded-cost experiment may be compared under an
actual start and an ideal warm start without attempting the false implication
`TVLe -> IsWarm`.
-/

namespace Arlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]

private noncomputable def kernelHitReal (P : Kernel E F) (S : Set F) (x : E) : Real :=
  (P x S).toReal

private theorem measurable_kernelHitReal (P : Kernel E F) {S : Set F}
    (hS : MeasurableSet S) : Measurable (kernelHitReal P S) :=
  (Kernel.measurable_coe P hS).ennreal_toReal

private theorem kernelHitReal_nonneg (P : Kernel E F) (S : Set F) (x : E) :
    0 <= kernelHitReal P S x :=
  ENNReal.toReal_nonneg

private theorem kernelHitReal_le_one (P : Kernel E F) [IsMarkovKernel P]
    (S : Set F) (x : E) : kernelHitReal P S x <= 1 := by
  exact ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := P x) (s := S))

private theorem bind_apply_eq_ofReal_integral_kernel
    (mu : Measure E) [IsProbabilityMeasure mu]
    (P : Kernel E F) [IsMarkovKernel P] {S : Set F} (hS : MeasurableSet S) :
    (mu.bind P) S = ENNReal.ofReal (∫ x, kernelHitReal P S x ∂mu) := by
  have hint : Integrable (kernelHitReal P S) mu :=
    integrable_of_forall_mem_Icc (measurable_kernelHitReal P hS)
      (kernelHitReal_nonneg P S) (kernelHitReal_le_one P S)
  rw [Measure.bind_apply hS P.aemeasurable,
    ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (kernelHitReal_nonneg P S))]
  exact lintegral_congr fun x =>
    (ENNReal.ofReal_toReal (measure_ne_top (P x) S)).symm

/-- Randomized data processing for a kernel whose output type differs from its input type. -/
theorem TVLe.bind_kernel {mu nu : Measure E}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps : ENNReal} (h : TVLe mu nu eps)
    (P : Kernel E F) [IsMarkovKernel P] :
    TVLe (mu.bind P) (nu.bind P) eps := by
  rcases eq_or_ne eps (⊤ : ENNReal) with rfl | heps
  · intro S hS
    simp
  intro S hS
  have hmu := bind_apply_eq_ofReal_integral_kernel mu P hS
  have hnu := bind_apply_eq_ofReal_integral_kernel nu P hS
  have key :
      |(∫ x, kernelHitReal P S x ∂mu) -
          (∫ x, kernelHitReal P S x ∂nu)| <= eps.toReal :=
    h.integral_le heps (measurable_kernelHitReal P hS)
      (kernelHitReal_nonneg P S) (kernelHitReal_le_one P S)
  rw [abs_sub_le_iff] at key
  have hmu0 : 0 <= ∫ x, kernelHitReal P S x ∂mu :=
    integral_nonneg (kernelHitReal_nonneg P S)
  have hnu0 : 0 <= ∫ x, kernelHitReal P S x ∂nu :=
    integral_nonneg (kernelHitReal_nonneg P S)
  have push : forall a b : Real, 0 <= b -> a <= b + eps.toReal ->
      ENNReal.ofReal a <= ENNReal.ofReal b + eps := by
    intro a b hb hab
    calc
      ENNReal.ofReal a <= ENNReal.ofReal (b + eps.toReal) :=
        ENNReal.ofReal_le_ofReal hab
      _ = ENNReal.ofReal b + ENNReal.ofReal eps.toReal :=
        ENNReal.ofReal_add hb ENNReal.toReal_nonneg
      _ = ENNReal.ofReal b + eps := by rw [ENNReal.ofReal_toReal heps]
  rw [hmu, hnu]
  exact
    ⟨push _ _ hnu0 (by linarith [key.1]),
      push _ _ hmu0 (by linarith [key.2])⟩

/-- A failure event of a randomized experiment costs at most its ideal probability plus
the TV error in the starting law.  This is the basic timeout-transfer rule. -/
theorem TVLe.bind_kernel_apply_le {mu nu : Measure E}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {eps : ENNReal} (h : TVLe mu nu eps)
    (P : Kernel E F) [IsMarkovKernel P]
    {S : Set F} (hS : MeasurableSet S) :
    (mu.bind P) S <= (nu.bind P) S + eps :=
  (h.bind_kernel P S hS).1

#print axioms TVLe.bind_kernel
#print axioms TVLe.bind_kernel_apply_le

end Arlib
