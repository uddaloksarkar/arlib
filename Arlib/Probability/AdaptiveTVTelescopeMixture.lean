/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Arlib.Probability.AdaptiveTVTelescope

/-!
# Adaptive TV telescoping with errors averaged under the ideal law

The pointwise adaptive telescope is too strong for warm-start Markov samplers: their
mixing and timeout bounds hold after averaging over a warm starting distribution, not
from every Dirac start.  A standard hybrid argument only needs the weaker statement
below.  At transition `i`, compare the two kernels after mixing both against the exact
ideal marginal at time `i`; these errors still add.
-/

namespace Arlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X]

/-- Adaptive TV telescope whose transition error is measured under the ideal marginal.

This is the distributional-warm form of the usual hybrid argument.  It deliberately
does not require `TVLe (P i x) (Q i x) (e i)` for every point `x`. -/
theorem TVLe.adaptiveMarginal_of_idealMixture
    (P Q : Nat → Kernel X X)
    [∀ i, IsMarkovKernel (P i)] [∀ i, IsMarkovKernel (Q i)]
    {mu nu : Measure X} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {d : ENNReal} (e : Nat → ENNReal) (hmunu : TVLe mu nu d)
    (hstep : ∀ i, TVLe
      ((Arlib.adaptiveMarginal Q nu i).bind (P i))
      ((Arlib.adaptiveMarginal Q nu i).bind (Q i)) (e i)) :
    ∀ t, TVLe (Arlib.adaptiveMarginal P mu t)
      (Arlib.adaptiveMarginal Q nu t) (d + ∑ i ∈ Finset.range t, e i) := by
  intro t
  induction t with
  | zero =>
      simpa only [Arlib.adaptiveMarginal, Finset.sum_range_zero, add_zero] using hmunu
  | succ t ih =>
      change TVLe
        ((Arlib.adaptiveMarginal P mu t).bind (P t))
        ((Arlib.adaptiveMarginal Q nu t).bind (Q t))
        (d + ∑ i ∈ Finset.range (t + 1), e i)
      rw [Finset.sum_range_succ]
      have hinput : TVLe
          ((Arlib.adaptiveMarginal P mu t).bind (P t))
          ((Arlib.adaptiveMarginal Q nu t).bind (P t))
          (d + ∑ i ∈ Finset.range t, e i) := ih.bind (P t)
      simpa only [add_assoc] using hinput.trans (hstep t)

/-- Common-initial-law specialization. -/
theorem TVLe.adaptiveMarginal_of_idealMixture_same
    (P Q : Nat → Kernel X X)
    [∀ i, IsMarkovKernel (P i)] [∀ i, IsMarkovKernel (Q i)]
    (mu : Measure X) [IsProbabilityMeasure mu]
    (e : Nat → ENNReal)
    (hstep : ∀ i, TVLe
      ((Arlib.adaptiveMarginal Q mu i).bind (P i))
      ((Arlib.adaptiveMarginal Q mu i).bind (Q i)) (e i)) (t : Nat) :
    TVLe (Arlib.adaptiveMarginal P mu t)
      (Arlib.adaptiveMarginal Q mu t) (∑ i ∈ Finset.range t, e i) := by
  have h := TVLe.adaptiveMarginal_of_idealMixture P Q e
    (TVLe.refl mu) hstep t
  simpa using h

/-- Measurable postprocessing of the final state preserves the accumulated error. -/
theorem TVLe.map_adaptiveMarginal_of_idealMixture
    (P Q : Nat → Kernel X X)
    [∀ i, IsMarkovKernel (P i)] [∀ i, IsMarkovKernel (Q i)]
    {mu nu : Measure X} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {d : ENNReal} (e : Nat → ENNReal) (hmunu : TVLe mu nu d)
    (hstep : ∀ i, TVLe
      ((Arlib.adaptiveMarginal Q nu i).bind (P i))
      ((Arlib.adaptiveMarginal Q nu i).bind (Q i)) (e i))
    {Y : Type*} [MeasurableSpace Y] (f : X → Y) (hf : Measurable f) (t : Nat) :
    TVLe ((Arlib.adaptiveMarginal P mu t).map f)
      ((Arlib.adaptiveMarginal Q nu t).map f)
      (d + ∑ i ∈ Finset.range t, e i) :=
  (TVLe.adaptiveMarginal_of_idealMixture P Q e hmunu hstep t).map hf

#print axioms TVLe.adaptiveMarginal_of_idealMixture
#print axioms TVLe.adaptiveMarginal_of_idealMixture_same
#print axioms TVLe.map_adaptiveMarginal_of_idealMixture

end Arlib
