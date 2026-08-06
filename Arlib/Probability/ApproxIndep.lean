/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner

/-
# Approximate independence

Two random variables are **`ν`-independent** when every joint event decouples up to an
additive `ν`:

  `|P(X ∈ A, Y ∈ B) − P(X ∈ A)·P(Y ∈ B)| ≤ ν`   for all measurable `A`, `B`.

Equivalently, `ν` bounds the *dependence coefficient*
`sup_{A,B} |P(X∈A,Y∈B) − P(X∈A)P(Y∈B)|`. This file takes the bounded form
(`Arlib.IndepUpTo`) as primitive rather than constructing the supremum: it is the form
consumers actually use, and it avoids `sSup` bookkeeping entirely.

The notion arises whenever a process is *almost* memoryless — for instance when successive
samples come from a Markov chain that has only approximately mixed, so that consecutive
draws are independent only up to the total variation error. Analyses of such samplers need
exactly this: independence is unavailable, but a quantitative surrogate is.

## Main definitions

* `Arlib.IndepUpTo` — `ν`-independence.

## Main results

* `Arlib.IndepUpTo.mono` — a weaker bound still holds.
* `Arlib.IndepUpTo.comp` — measurable functions do not increase dependence.
* `Arlib.indepUpTo_zero_of_indepFun` — genuine independence is `0`-independence, so the
  notion is a strict generalisation and is non-vacuous.
-/

namespace Arlib

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **`ν`-independence**: every joint event decouples up to an additive `ν`.

`ν = 0` is genuine independence (`Arlib.indepUpTo_zero_of_indepFun`); larger `ν` is a
quantitative relaxation. -/
def IndepUpTo (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) (ν : ℝ) : Prop :=
  ∀ A : Set α, ∀ B : Set β, MeasurableSet A → MeasurableSet B →
    |(μ (X ⁻¹' A ∩ Y ⁻¹' B)).toReal
      - (μ (X ⁻¹' A)).toReal * (μ (Y ⁻¹' B)).toReal| ≤ ν

/-- A `ν`-independent pair is `ν'`-independent for any larger `ν'`. -/
theorem IndepUpTo.mono {X : Ω → α} {Y : Ω → β} {ν ν' : ℝ}
    (h : IndepUpTo μ X Y ν) (hle : ν ≤ ν') : IndepUpTo μ X Y ν' :=
  fun A B hA hB => le_trans (h A B hA hB) hle

/-- **`ν`-independence is symmetric.** -/
theorem IndepUpTo.symm {X : Ω → α} {Y : Ω → β} {ν : ℝ}
    (h : IndepUpTo μ X Y ν) : IndepUpTo μ Y X ν := by
  intro B A hB hA
  have hset : Y ⁻¹' B ∩ X ⁻¹' A = X ⁻¹' A ∩ Y ⁻¹' B := Set.inter_comm _ _
  rw [hset, mul_comm]
  exact h A B hA hB

/-- **Measurable functions do not increase dependence** — the paper's `lem:fn-indep`.

`μ(f(X), g(Y)) ≤ μ(X, Y)`: post-composing with measurable maps can only merge events, so
the supremum defining the dependence coefficient is taken over a sub-family.

The proof is the observation that `(f ∘ X)⁻¹(A) = X⁻¹(f⁻¹(A))`, so every constraint on the
composed pair is already a constraint on the original pair. -/
theorem IndepUpTo.comp {X : Ω → α} {Y : Ω → β} {ν : ℝ}
    {α' β' : Type*} [MeasurableSpace α'] [MeasurableSpace β']
    {f : α → α'} {g : β → β'} (hf : Measurable f) (hg : Measurable g)
    (h : IndepUpTo μ X Y ν) : IndepUpTo μ (f ∘ X) (g ∘ Y) ν := by
  intro A B hA hB
  have hX : (f ∘ X) ⁻¹' A = X ⁻¹' (f ⁻¹' A) := rfl
  have hY : (g ∘ Y) ⁻¹' B = Y ⁻¹' (g ⁻¹' B) := rfl
  rw [hX, hY]
  exact h _ _ (hf hA) (hg hB)

/-- **Genuine independence is `0`-independence.**

Establishes that the notion generalises `ProbabilityTheory.IndepFun` rather than replacing
it, and — since independent pairs exist — that `Arlib.IndepUpTo` is not vacuous. -/
theorem indepUpTo_zero_of_indepFun [IsProbabilityMeasure μ] {X : Ω → α} {Y : Ω → β}
    (h : IndepFun X Y μ) : IndepUpTo μ X Y 0 := by
  intro A B hA hB
  have hmul := h.measure_inter_preimage_eq_mul A B hA hB
  rw [hmul, ENNReal.toReal_mul, sub_self, abs_zero]

end Arlib
