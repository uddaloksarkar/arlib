/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Probability.TVKernel
import Arlib.Probability.TVTensor

/-!
# Total-variation telescoping for adaptive kernels

This file supplies the finite-horizon comparison needed when an algorithm draws its next
sample from a law depending on the entire history, while the proof describes an ideal fresh
draw.  A uniform pointwise error at each transition adds, rather than multiplies.

The statement is deliberately about arbitrary kernels on one state space.  The state may
itself contain the complete finite history, so this applies directly to adaptive rejection
loops once the caller packages “append the new draw” as a Markov kernel.
-/

namespace Arlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X]

/-- Changing a Markov kernel pointwise by at most `e` changes its mixture under a
probability law by at most `e`. -/
theorem TVLe.bind_pointwise (mu : Measure X) [IsProbabilityMeasure mu]
    (P Q : Kernel X X) [IsMarkovKernel P] [IsMarkovKernel Q] {e : ENNReal}
    (hPQ : ∀ x, TVLe (P x) (Q x) e) :
    TVLe (mu.bind P) (mu.bind Q) e := by
  intro S hS
  rw [Measure.bind_apply hS P.aemeasurable, Measure.bind_apply hS Q.aemeasurable]
  constructor
  · calc
      ∫⁻ x, P x S ∂mu ≤ ∫⁻ x, (Q x S + e) ∂mu :=
        lintegral_mono fun x => (hPQ x S hS).1
      _ = (∫⁻ x, Q x S ∂mu) + e := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  · calc
      ∫⁻ x, Q x S ∂mu ≤ ∫⁻ x, (P x S + e) ∂mu :=
        lintegral_mono fun x => (hPQ x S hS).2
      _ = (∫⁻ x, P x S ∂mu) + e := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]

/-- One adaptive transition: an error in the input law and a uniform pointwise error in
the transition kernel add. -/
theorem TVLe.bind_pointwise_of_tvLe {mu nu : Measure X}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (P Q : Kernel X X) [IsMarkovKernel P] [IsMarkovKernel Q]
    {d e : ENNReal} (hmunu : TVLe mu nu d) (hPQ : ∀ x, TVLe (P x) (Q x) e) :
    TVLe (mu.bind P) (nu.bind Q) (d + e) :=
  (hmunu.bind P).trans (TVLe.bind_pointwise nu P Q hPQ)

/-- Marginal law after `t` transitions of a time-inhomogeneous Markov process. -/
noncomputable def adaptiveMarginal (P : Nat → Kernel X X) (mu : Measure X) : Nat → Measure X
  | 0 => mu
  | t + 1 => (adaptiveMarginal P mu t).bind (P t)

instance adaptiveMarginal_isProbabilityMeasure (P : Nat → Kernel X X)
    [∀ t, IsMarkovKernel (P t)] (mu : Measure X) [IsProbabilityMeasure mu] (t : Nat) :
    IsProbabilityMeasure (adaptiveMarginal P mu t) := by
  induction t with
  | zero => simpa [adaptiveMarginal]
  | succ t ih =>
      rw [adaptiveMarginal]
      infer_instance

/-- **Adaptive TV telescope.**  If the initial laws differ by `d` and transition `i`
differs pointwise by `e i`, the laws after `t` adaptive transitions differ by at most
`d + ∑ i < t, e i`.

No independence is assumed.  In particular, `P i x` may depend on an `x` containing the
entire previously generated history. -/
theorem TVLe.adaptiveMarginal
    (P Q : Nat → Kernel X X) [∀ t, IsMarkovKernel (P t)] [∀ t, IsMarkovKernel (Q t)]
    {mu nu : Measure X} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {d : ENNReal} (e : Nat → ENNReal) (hmunu : TVLe mu nu d)
    (hPQ : ∀ i x, TVLe (P i x) (Q i x) (e i)) (t : Nat) :
    TVLe (Arlib.adaptiveMarginal P mu t) (Arlib.adaptiveMarginal Q nu t)
      (d + ∑ i ∈ Finset.range t, e i) := by
  induction t with
  | zero => simpa only [Arlib.adaptiveMarginal, Finset.sum_range_zero, add_zero] using hmunu
  | succ t ih =>
      change TVLe
        ((Arlib.adaptiveMarginal P mu t).bind (P t))
        ((Arlib.adaptiveMarginal Q nu t).bind (Q t))
        (d + ∑ i ∈ Finset.range (t + 1), e i)
      rw [Finset.sum_range_succ]
      have hstep := TVLe.bind_pointwise_of_tvLe (P t) (Q t) ih (hPQ t)
      simpa [add_assoc] using hstep

/-- Constant-error form of the adaptive telescope. -/
theorem TVLe.adaptiveMarginal_const
    (P Q : Nat → Kernel X X) [∀ t, IsMarkovKernel (P t)] [∀ t, IsMarkovKernel (Q t)]
    {mu nu : Measure X} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {d e : ENNReal} (hmunu : TVLe mu nu d)
    (hPQ : ∀ i x, TVLe (P i x) (Q i x) e) (t : Nat) :
    TVLe (Arlib.adaptiveMarginal P mu t) (Arlib.adaptiveMarginal Q nu t) (d + t * e) := by
  simpa using TVLe.adaptiveMarginal P Q (fun _ => e) hmunu hPQ t

/-- Postprocessed adaptive telescope.  This is the form used by a bounded rejection loop:
`f` reads the first accepted draw from the retained history, and `hideal` bounds the ideal
iid loop's cutoff/tail error against the desired conditional law. -/
theorem TVLe.map_adaptiveMarginal_to_target
    (P Q : Nat → Kernel X X) [∀ t, IsMarkovKernel (P t)] [∀ t, IsMarkovKernel (Q t)]
    {mu nu : Measure X} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {Y : Type*} [MeasurableSpace Y] (f : X → Y) (hf : Measurable f)
    {tau : Measure Y} {d b : ENNReal} (e : Nat → ENNReal)
    (hmunu : TVLe mu nu d) (hPQ : ∀ i x, TVLe (P i x) (Q i x) (e i))
    (t : Nat)
    (hideal : TVLe ((Arlib.adaptiveMarginal Q nu t).map f) tau b) :
    TVLe ((Arlib.adaptiveMarginal P mu t).map f) tau
      ((d + ∑ i ∈ Finset.range t, e i) + b) :=
  ((TVLe.adaptiveMarginal P Q e hmunu hPQ t).map hf).trans hideal

/-- Constant transition-error specialization of `map_adaptiveMarginal_to_target`. -/
theorem TVLe.map_adaptiveMarginal_const_to_target
    (P Q : Nat → Kernel X X) [∀ t, IsMarkovKernel (P t)] [∀ t, IsMarkovKernel (Q t)]
    {mu nu : Measure X} [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    {Y : Type*} [MeasurableSpace Y] (f : X → Y) (hf : Measurable f)
    {tau : Measure Y} {d e b : ENNReal}
    (hmunu : TVLe mu nu d) (hPQ : ∀ i x, TVLe (P i x) (Q i x) e)
    (t : Nat)
    (hideal : TVLe ((Arlib.adaptiveMarginal Q nu t).map f) tau b) :
    TVLe ((Arlib.adaptiveMarginal P mu t).map f) tau ((d + t * e) + b) :=
  ((TVLe.adaptiveMarginal_const P Q hmunu hPQ t).map hf).trans hideal

#print axioms TVLe.bind_pointwise
#print axioms TVLe.bind_pointwise_of_tvLe
#print axioms TVLe.adaptiveMarginal
#print axioms TVLe.adaptiveMarginal_const
#print axioms TVLe.map_adaptiveMarginal_to_target
#print axioms TVLe.map_adaptiveMarginal_const_to_target

end Arlib
