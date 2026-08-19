/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Probability.TV
import Mathlib.Probability.Kernel.Invariance

/-!
# Data processing for a Markov kernel

`Arlib.Probability.TV` proves the *deterministic* data-processing inequality
(`Arlib.TVLe.map`): pushing two measures forward along the same measurable map cannot
increase their total variation distance.  Its module docstring (`Arlib/Probability/TV.lean`,
"## Scope") then records that the *randomised* version — pushing two measures through the
same Markov **kernel** — is missing.  This file supplies it:

  `Arlib.TVLe.bind : TVLe μ ν ε → TVLe (μ.bind P) (ν.bind P) ε`.

The error does **not** grow.  A Markov kernel is non-expansive in total variation, which is
what makes a mixing argument composable: a chain started from two nearby laws keeps them
nearby forever, and a sampler's accumulated error is only ever spent at the places where
something other than a kernel step happens (conditioning, rejection, restarts).

## The proof

The docstring in `TV.lean` feared a layer-cake argument.  None is written here, because the
layer cake has already been paid for once: `Arlib.TVLe.integral_le` (`TV.lean`) transfers a
`TVLe` bound to the Bochner integral of any measurable `[0,1]`-valued observable.  Applying
it to the observable

  `f x = (P x S).toReal`  —  the chance of landing in `S` from `x`,

which is `[0,1]`-valued precisely because `P` is a Markov kernel, gives
`|∫ f ∂μ − ∫ f ∂ν| ≤ ε.toReal`; and `Measure.bind_apply` says `(μ.bind P) S = ∫⁻ P x S ∂μ`,
which is `ENNReal.ofReal (∫ f ∂μ)`.  So the whole argument is a translation between the
`ℝ≥0∞`-valued and `ℝ`-valued forms of the same integral.

## Duplication warning

⚠ **The same mathematical fact is already proved elsewhere in this repository**, in a
different layer and in a stronger form: `Arlib.tvLe_step` and `Arlib.tvLe_iterate` in
`Arlib/MarkovChains/Continuous/Warmness.lean`, resting on `Arlib.lintegral_le_of_tvLe` in
the same file.  Those versions need **neither** `IsProbabilityMeasure μ`/`ν` **nor**
`ε ≠ ⊤`, because they run the layer cake directly in `ℝ≥0∞`.  Prefer them when you have a
choice.  This file exists so that the statement is available in the `Arlib.Probability`
layer, which — per the repository's import direction (`Arlib.MarkovChains.*` imports
`Arlib.Probability.*`, never the reverse) — cannot see `Warmness.lean`.

That import direction is also why `TVLe.step` and `TVLe.iterate`, phrased for
`Arlib.MarkovChains.step`/`iterate`, are **not** in this file: putting them here would make
`Arlib/Probability` depend on `Arlib/MarkovChains` and invert the layering.  They live in
`Arlib/Convexity/GaussianCooling/PhaseInduction.lean` instead, which already imports both
areas.

## Main results

* `Arlib.TVLe.bind` — the data-processing inequality for a Markov kernel.
* `Arlib.TVLe.bind_iterate` — the same for `n`-fold composition, written directly as
  iterated `Measure.bind`, so that the non-growth of the error is visible without any
  Markov-chain vocabulary.
-/

namespace Arlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The chance of landing in `S`, as a real-valued observable on the starting point.
This is the integrand the data-processing proof feeds to `Arlib.TVLe.integral_le`. -/
private noncomputable def hitReal (P : Kernel Ω Ω) (S : Set Ω) (x : Ω) : ℝ := (P x S).toReal

private theorem measurable_hitReal (P : Kernel Ω Ω) {S : Set Ω} (hS : MeasurableSet S) :
    Measurable (hitReal P S) :=
  (Kernel.measurable_coe P hS).ennreal_toReal

private theorem hitReal_nonneg (P : Kernel Ω Ω) (S : Set Ω) (x : Ω) : 0 ≤ hitReal P S x :=
  ENNReal.toReal_nonneg

private theorem hitReal_le_one (P : Kernel Ω Ω) [IsMarkovKernel P] (S : Set Ω) (x : Ω) :
    hitReal P S x ≤ 1 := by
  have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := P x) (s := S))
  simpa [hitReal] using this

/-- `(μ.bind P) S`, the mass the one-step law puts on `S`, as `ENNReal.ofReal` of a Bochner
integral.  This is the bridge between the `ℝ≥0∞` world `TVLe` lives in and the `ℝ` world
`Arlib.TVLe.integral_le` lives in. -/
private theorem bind_apply_eq_ofReal_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : Kernel Ω Ω) [IsMarkovKernel P] {S : Set Ω} (hS : MeasurableSet S) :
    (μ.bind P) S = ENNReal.ofReal (∫ x, hitReal P S x ∂μ) := by
  have hint : Integrable (hitReal P S) μ :=
    integrable_of_forall_mem_Icc (measurable_hitReal P hS) (hitReal_nonneg P S)
      (hitReal_le_one P S)
  rw [Measure.bind_apply hS P.aemeasurable,
    ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (hitReal_nonneg P S))]
  exact lintegral_congr fun x => (ENNReal.ofReal_toReal (measure_ne_top (P x) S)).symm

/-- **Data processing for a Markov kernel.**  Running two laws through the *same* Markov
kernel cannot increase the total variation distance between them:

  `TVLe μ ν ε  →  TVLe (μ.bind P) (ν.bind P) ε`.

The bound `ε` is unchanged — this is the whole point.  A kernel is non-expansive in total
variation, so a chain never amplifies the error in its starting law, no matter how many
steps it takes.

Compare `Arlib.TVLe.map`, the deterministic case (`P = Kernel.deterministic f`), and see the
module docstring for the stronger hypothesis-free version proved in
`Arlib/MarkovChains/Continuous/Warmness.lean`. -/
theorem TVLe.bind {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ≥0∞} (h : TVLe μ ν ε) (P : Kernel Ω Ω) [IsMarkovKernel P] :
    TVLe (μ.bind P) (ν.bind P) ε := by
  rcases eq_or_ne ε ⊤ with rfl | hε
  · intro S _
    simp
  intro S hS
  -- The two masses, as `ENNReal.ofReal` of real integrals.
  have hμ := bind_apply_eq_ofReal_integral μ P hS
  have hν := bind_apply_eq_ofReal_integral ν P hS
  -- The real-valued transfer lemma, applied to the hitting probability.
  have key : |∫ x, hitReal P S x ∂μ - ∫ x, hitReal P S x ∂ν| ≤ ε.toReal :=
    h.integral_le hε (measurable_hitReal P hS) (hitReal_nonneg P S) (hitReal_le_one P S)
  rw [abs_sub_le_iff] at key
  have hμ0 : 0 ≤ ∫ x, hitReal P S x ∂μ :=
    integral_nonneg (hitReal_nonneg P S)
  have hν0 : 0 ≤ ∫ x, hitReal P S x ∂ν :=
    integral_nonneg (hitReal_nonneg P S)
  -- Transport `a ≤ b + ε.toReal` (and its mirror) across `ENNReal.ofReal`.
  have push : ∀ a b : ℝ, 0 ≤ b → a ≤ b + ε.toReal →
      ENNReal.ofReal a ≤ ENNReal.ofReal b + ε := by
    intro a b hb hab
    calc ENNReal.ofReal a ≤ ENNReal.ofReal (b + ε.toReal) := ENNReal.ofReal_le_ofReal hab
      _ = ENNReal.ofReal b + ENNReal.ofReal ε.toReal :=
          ENNReal.ofReal_add hb ENNReal.toReal_nonneg
      _ = ENNReal.ofReal b + ε := by rw [ENNReal.ofReal_toReal hε]
  rw [hμ, hν]
  exact ⟨push _ _ hν0 (by linarith [key.1]), push _ _ hμ0 (by linarith [key.2])⟩

/-- **Data processing for `n` steps of a Markov kernel**, phrased purely with
`Measure.bind` so that no Markov-chain vocabulary is needed to read it.

`Nat.rec`-style iteration of `fun ρ => ρ.bind P`: the error stays `ε` for every `n`.  This
is the statement a mixing argument consumes when it has to compare the chain started from
the sampler's actual initial law with the chain started from the ideal one. -/
theorem TVLe.bind_iterate {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ≥0∞} (h : TVLe μ ν ε) (P : Kernel Ω Ω) [IsMarkovKernel P] (n : ℕ) :
    TVLe ((fun ρ => Measure.bind ρ P)^[n] μ) ((fun ρ => Measure.bind ρ P)^[n] ν) ε := by
  induction n generalizing μ ν with
  | zero => simpa using h
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      have hb : IsProbabilityMeasure (μ.bind P) := by
        show IsProbabilityMeasure (P ∘ₘ μ); infer_instance
      have hb' : IsProbabilityMeasure (ν.bind P) := by
        show IsProbabilityMeasure (P ∘ₘ ν); infer_instance
      exact ih (h.bind P)

section AxiomCheck

#print axioms Arlib.TVLe.bind
#print axioms Arlib.TVLe.bind_iterate

end AxiomCheck

end Arlib
