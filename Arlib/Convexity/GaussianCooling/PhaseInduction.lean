/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Probability.TVKernel
import Arlib.MarkovChains.Continuous.Warmness
import Arlib.MarkovChains.Continuous.MapSpeedyToTarget

/-!
# Composing the phases: how the sampler's error accumulates across a cooling schedule

Cousins–Vempala's `lem:accuracy` (`1409.6011/vol3_journal.tex:1419`) has to say what happens
when the volume algorithm's `m` phases are run one after another, each phase producing
samples from a law that is only *approximately* the phase's target.  Their equation
`eqn:exact-chance` (`vol3_journal.tex:1429`) reads

  "Using induction and the definition of total variation distance, we see that
   `Pr(X_i^j = X̄_i^j, ∀ i,j) ≥ 1 − tν`."

That is an **additive** accumulation: `t` samples, each `ν`-off, cost `tν` in total.  The
step is legitimate, but the justification is a *coupling*: `X̄` is constructed on the same
probability space as `X`, agreeing with it except on an event of probability `ν`, and the
union bound over the `t` samples does the rest.

## Why this file cannot reproduce CV's constant

This library has no coupling characterisation of total variation.  `Arlib/Probability/TV.lean`
says so explicitly in its "## Scope" section: there is no coupling lemma, no maximal-coupling
construction, no `∃ (X, Y), law X = μ ∧ law Y = ν ∧ Pr(X ≠ Y) ≤ ε`.  `Arlib.TVLe` is a purely
setwise predicate, and setwise predicates propagate along **laws**, not along random
variables.

So we take the law-propagation route instead, and it costs something.  Along a chain of
kernel steps the route is free — `TVLe.step`/`TVLe.iterate` below show a Markov kernel is
non-expansive, so running the chain does not degrade the bound at all, which is *better*
than a union bound over the steps.  The price is paid at the one place per phase where the
sampler does something that is not a kernel step: it **conditions** on an event (the
rejection loop that keeps only the samples landing in the shrunken body).  Conditioning is
not non-expansive.  `Arlib.tvLe_condOn_half`
(`Arlib/MarkovChains/Continuous/MapSpeedyToTarget.lean`) gives the sharp constant available
here:

  `TVLe μ ν ε  →  ν A ≥ 1/2  →  TVLe (condOn μ A) (condOn ν A) (8 * ε)`,

so the per-phase inflation factor is `C = 8`.  (Not `4`: the numerator and the denominator of
the conditional probability each contribute `ε/m` at `m = 1/4`, giving `2ε/(1/4) = 8ε`.)

The upshot is a **geometric** rather than linear accumulation:

  `error after m phases ≤ ν · (1 + 8 + 8² + ⋯ + 8^(m−1)) = ν · ∑_{j<m} 8^j`.

This is genuinely weaker than CV's `mν`, and the difference is not an artefact of a sloppy
proof — it is exactly the cost of not having a coupling.  It is still usable: `∑_{j<m} 8^j`
is a fixed function of the phase count, so a caller who can drive the per-phase accuracy `ν`
down by a factor `8^m` recovers any target accuracy.  Whether that is affordable is a
question about the sampler's cost, not about this file.  **Do not quote `mν` for this
route.**

## Where `TVLe.step` and `TVLe.iterate` live, and why here

`Arlib.TVLe.bind` — the data-processing inequality for a Markov kernel — is proved in
`Arlib/Probability/TVKernel.lean`, in the `Arlib.Probability` layer, where it belongs.  Its
restatement for `Arlib.MarkovChains.step`/`iterate` cannot go there: `Arlib.MarkovChains.*`
imports `Arlib.Probability.*` and never the reverse, so a `TVLe.step` in
`Arlib/Probability/TVKernel.lean` would invert the layering.  It is therefore stated here,
in a file that already imports both areas.

⚠ Both are **duplicates** of `Arlib.tvLe_step` and `Arlib.tvLe_iterate`
(`Arlib/MarkovChains/Continuous/Warmness.lean`), which are strictly stronger: they need
neither `IsProbabilityMeasure` nor `ε ≠ ⊤`, being proved by a layer cake directly in
`ℝ≥0∞`.  The versions here exist only to give `TVLe` dot-notation and to route the phase
argument through `TVLe.bind`.  New code should prefer `Arlib.tvLe_step`.

## Main results

* `Arlib.TVLe.step`, `Arlib.TVLe.iterate` — a kernel step, and `t` kernel steps, do not
  increase the error.
* `Arlib.GaussianCooling.le_geom_sum_of_rec` — the pure arithmetic: `e 0 = 0` and
  `e (i+1) ≤ C · e i + ν` force `e m ≤ ν · ∑_{j<m} C^j`.
* `Arlib.GaussianCooling.tvLe_phase_step` — one phase, at the measure level: run the chain
  `t` steps (free) then condition on a half-mass event (factor `8`).
* `Arlib.GaussianCooling.tvLe_phaseChain` — **the headline.**  The abstract phase chain:
  `m` phases of per-phase accuracy `ν` and per-phase inflation `8` land the realised law
  within `ν · ∑_{j<m} 8^j` of the exact law.
* `Arlib.GaussianCooling.exists_phaseChain_witness` — a concrete instance of every
  hypothesis of `tvLe_phaseChain` at once, with the two laws genuinely distinct and the
  error strictly between `0` and `1`.  Without this the phase chain could be vacuous.
-/

namespace Arlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## A kernel step does not increase the error -/

/-- **One step of a Markov chain does not increase total variation distance**, phrased for
`Arlib.MarkovChains.step`.  Definitionally `Arlib.TVLe.bind`, since `step P μ = μ.bind P`.

See the module docstring: `Arlib.tvLe_step` is the same statement with weaker hypotheses. -/
theorem TVLe.step {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ≥0∞} (h : TVLe μ ν ε) (P : Kernel Ω Ω) [IsMarkovKernel P] :
    TVLe (MarkovChains.step P μ) (MarkovChains.step P ν) ε :=
  h.bind P

/-- **`t` steps of a Markov chain do not increase total variation distance.**

The error does **not** grow with `t` — there is no union bound over the steps, because a
Markov kernel is non-expansive in total variation.  This is the reason the geometric loss of
`tvLe_phaseChain` is charged once per *phase* and not once per *sample*. -/
theorem TVLe.iterate {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ≥0∞} (h : TVLe μ ν ε) (P : Kernel Ω Ω) [IsMarkovKernel P] (t : ℕ) :
    TVLe (MarkovChains.iterate P μ t) (MarkovChains.iterate P ν t) ε := by
  induction t with
  | zero => simpa using h
  | succ t ih => exact ih.step P

namespace GaussianCooling

open Finset

/-! ## Step 1: the arithmetic of a geometric recursion

No measure theory here.  This is the shape of the error recursion — inflate by `C`, then add
`ν` — solved in closed form. -/

/-- **A geometric error recursion, solved.**  If `e 0 = 0` and each step inflates the error
by a factor `C` and then adds `ν`, then after `m` steps the error is at most
`ν · ∑_{j<m} C^j`.

This is the only place the geometric growth enters; everything else in this file is
bookkeeping around it.  Stated in `ℝ≥0∞` so that `C = ⊤` or `ν = ⊤` are permitted (and
give the vacuous bound). -/
theorem le_geom_sum_of_rec {C nu : ℝ≥0∞} {e : ℕ → ℝ≥0∞} (h0 : e 0 = 0)
    (hrec : ∀ i, e (i + 1) ≤ C * e i + nu) (m : ℕ) :
    e m ≤ nu * ∑ j ∈ Finset.range m, C ^ j := by
  induction m with
  | zero => simp [h0]
  | succ m ih =>
      calc e (m + 1) ≤ C * e m + nu := hrec m
        _ ≤ C * (nu * ∑ j ∈ Finset.range m, C ^ j) + nu := by gcongr
        _ = nu * ((C * ∑ j ∈ Finset.range m, C ^ j) + 1) := by ring
        _ = nu * ∑ j ∈ Finset.range (m + 1), C ^ j := by rw [geom_sum_succ]

/-! ## Step 2: one phase, at the level of measures

A phase of the Cousins–Vempala sampler is: run the walk for `t` steps, then condition on the
event that the sample landed in the shrunken body.  The first half is free
(`Arlib.TVLe.iterate`); the second half costs a factor `8`
(`Arlib.tvLe_condOn_half`). -/

/-- **One phase of the sampler, as a map on laws.**  Running the chain `t` steps and then
conditioning on a set that carries at least half the exact law's mass turns an `ε`-accurate
start into an `8ε`-accurate conditional law.

The hypothesis `hνA` — the event has exact-law mass at least `1/2` — is the one the cooling
schedule supplies: `Arlib.GaussianCooling.half_le_coolLaw_smul_set`
(`Arlib/Convexity/GaussianCooling/WarmSpeedy.lean`) proves exactly
`ENNReal.ofReal (1/2) ≤ coolLaw m σsq K i ((1 − 1/(2n)) • K)`.

Note where the loss is and is not: the `t` chain steps contribute **nothing**, however large
`t` is.  All `8` of the inflation comes from the single conditioning. -/
theorem tvLe_phase_step {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ≥0∞} (h : TVLe μ ν ε) (P : Kernel Ω Ω) [IsMarkovKernel P] (t : ℕ)
    {A : Set Ω} (hA : MeasurableSet A)
    (hνA : ENNReal.ofReal (1 / 2) ≤ MarkovChains.iterate P ν t A) :
    TVLe (condOn (MarkovChains.iterate P μ t) A) (condOn (MarkovChains.iterate P ν t) A)
      (8 * ε) :=
  tvLe_condOn_half (h.iterate P t) hA hνA

/-! ## Step 3: the phase chain

Stated over abstract data so that it is provable without re-deriving the sampler:

* `Q i`   — the *exact* law the `i`-th phase is supposed to hand on;
* `Qh i`  — the law the sampler's `i`-th phase actually hands on;
* `Φ i`   — what phase `i` does to a law (run the walk, then condition);
* `nu`    — the accuracy of one phase *when started from the exact law*.

The two hypotheses that carry content are `htransfer` (phase `i` inflates whatever error it
is handed by at most `8` — supplied by `tvLe_phase_step`) and `haccuracy` (started from the
exact law, phase `i` lands within `nu` of the next exact law — supplied by the mixing
theorem for the walk). -/

/-- The error the phase chain has accumulated after `i` phases: start at `0`, and at each
phase inflate by `C` and add `nu`.  Auxiliary to `tvLe_phaseChain`; the closed form is
`chainErr_le`. -/
noncomputable def chainErr (C nu : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 0
  | i + 1 => C * chainErr C nu i + nu

@[simp] theorem chainErr_zero (C nu : ℝ≥0∞) : chainErr C nu 0 = 0 := rfl

@[simp] theorem chainErr_succ (C nu : ℝ≥0∞) (i : ℕ) :
    chainErr C nu (i + 1) = C * chainErr C nu i + nu := rfl

/-- The closed form of `chainErr`, by `le_geom_sum_of_rec`. -/
theorem chainErr_le (C nu : ℝ≥0∞) (m : ℕ) :
    chainErr C nu m ≤ nu * ∑ j ∈ Finset.range m, C ^ j :=
  le_geom_sum_of_rec (chainErr_zero C nu) (fun i => (chainErr_succ C nu i).le) m

/-- **The phase chain.**  `m` phases, each inflating the error it is handed by a factor `8`
and each contributing a fresh error `nu` of its own, leave the realised law `Qh m` within

  `nu · ∑_{j<m} 8^j`

of the exact law `Q m`.

This is this repository's replacement for Cousins–Vempala `eqn:exact-chance`
(`1409.6011/vol3_journal.tex:1429`), which claims the additive bound `m·nu`.  CV get
additivity from a coupling; without a coupling characterisation of total variation the
conditioning step at each phase costs a factor `8` and the accumulation is geometric.  See
the module docstring.

Nothing here is assumed about the shape of `Φ`, `Q` or `Qh` beyond the four hypotheses, and
in particular no hypothesis is equivalent to the conclusion: `htransfer` is a statement
about `Φ i` applied to `Qh i` and `Q i`, `haccuracy` is a statement about `Φ i` applied to
`Q i` only, and neither mentions `Qh m` for `m > i + 1`.  `exists_phaseChain_witness`
exhibits data satisfying all four with `Qh 2 ≠ Q 2`. -/
theorem tvLe_phaseChain {Q Qh : ℕ → Measure Ω} {Φ : ℕ → Measure Ω → Measure Ω} {nu : ℝ≥0∞}
    (hstart : Qh 0 = Q 0)
    (htransfer : ∀ (i : ℕ) (e : ℝ≥0∞), TVLe (Qh i) (Q i) e →
      TVLe (Φ i (Qh i)) (Φ i (Q i)) (8 * e))
    (haccuracy : ∀ i : ℕ, TVLe (Φ i (Q i)) (Q (i + 1)) nu)
    (hrun : ∀ i : ℕ, Qh (i + 1) = Φ i (Qh i)) (m : ℕ) :
    TVLe (Qh m) (Q m) (nu * ∑ j ∈ Finset.range m, (8 : ℝ≥0∞) ^ j) := by
  have key : ∀ k : ℕ, TVLe (Qh k) (Q k) (chainErr 8 nu k) := by
    intro k
    induction k with
    | zero => rw [hstart, chainErr_zero]; exact TVLe.refl _
    | succ k ih =>
        rw [hrun k, chainErr_succ]
        exact (htransfer k _ ih).trans (haccuracy k)
  exact (key m).mono (chainErr_le 8 nu m)

/-! ## Non-vacuity

`tvLe_phaseChain` quantifies over a bundle of four hypotheses.  If that bundle were
unsatisfiable the theorem would be true and worthless.  The witness below satisfies all four
simultaneously, on `Bool`, with a phase map `Φ` that genuinely moves its argument (a
pushforward, so `htransfer` is discharged by the *deterministic* data-processing inequality
rather than by ignoring the hypothesis), with `Qh 2 ≠ Q 2` so the conclusion is a genuine
non-reflexive total variation bound, and with the error `nu · ∑_{j<2} 8^j = 9/10` strictly
inside `(0, 1)` — in particular not `⊤`, so the bound is not the vacuous one. -/

/-- Witness datum: a sub-probability measure on `Bool`, `9/10` of a Dirac mass at `true`.
It is within `1/10` of `Measure.dirac true` in total variation, and distinct from it. -/
private noncomputable def wRho : Measure Bool :=
  ENNReal.ofReal (9 / 10) • Measure.dirac true

/-- Witness datum: the exact phase laws.  Phase `0` is exactly `Measure.dirac true`; every
later phase's exact law is `wRho`, so the very first phase incurs a real error. -/
private noncomputable def wQ : ℕ → Measure Bool
  | 0 => Measure.dirac true
  | _ + 1 => wRho

/-- Witness datum: the realised phase laws.  The sampler never leaves `Measure.dirac true`. -/
private noncomputable def wQh : ℕ → Measure Bool := fun _ => Measure.dirac true

/-- Witness datum: the phase map, a pushforward along the constant map `_ ↦ true`. -/
private noncomputable def wPhi : ℕ → Measure Bool → Measure Bool :=
  fun _ μ => μ.map fun _ => true

private theorem wRho_apply {S : Set Bool} (hS : MeasurableSet S) :
    wRho S = ENNReal.ofReal (9 / 10) * S.indicator 1 true := by
  rw [wRho, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hS]

private theorem wRho_univ : wRho Set.univ = ENNReal.ofReal (9 / 10) := by
  rw [wRho_apply MeasurableSet.univ]
  simp

private theorem tvLe_dirac_wRho :
    TVLe (Measure.dirac (true : Bool)) wRho (ENNReal.ofReal (1 / 10)) := by
  have hsum : ENNReal.ofReal (9 / 10) + ENNReal.ofReal (1 / 10) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  have hle1 : ENNReal.ofReal (9 / 10) ≤ 1 := ENNReal.ofReal_le_one.2 (by norm_num)
  intro S hS
  rw [Measure.dirac_apply' _ hS, wRho_apply hS]
  by_cases htrue : (true : Bool) ∈ S
  · rw [Set.indicator_of_mem htrue]
    simp only [Pi.one_apply, mul_one]
    exact ⟨hsum.ge, hle1.trans le_self_add⟩
  · rw [Set.indicator_of_notMem htrue]
    simp

/-- **Non-vacuity witness for `tvLe_phaseChain`.**  Concrete data satisfying every
hypothesis of the phase chain at once, with a non-degenerate conclusion.

The last three conjuncts are what makes it a *witness* rather than a formality: `wQh 2 ≠ wQ 2`
says the two laws really do differ, so the conclusion of `tvLe_phaseChain` is not the trivial
`TVLe μ μ ε`; and `0 < nu · ∑_{j<2} 8^j < 1` says the error bound is a real number strictly
inside the meaningful range, not `0` (which would make the chain exact) and not `⊤` or `≥ 1`
(which would make it vacuous, since `Arlib.tvLe_one` gives `1` for free). -/
theorem exists_phaseChain_witness :
    ∃ (Q Qh : ℕ → Measure Bool) (Φ : ℕ → Measure Bool → Measure Bool) (nu : ℝ≥0∞),
      Qh 0 = Q 0 ∧
      (∀ (i : ℕ) (e : ℝ≥0∞), TVLe (Qh i) (Q i) e → TVLe (Φ i (Qh i)) (Φ i (Q i)) (8 * e)) ∧
      (∀ i : ℕ, TVLe (Φ i (Q i)) (Q (i + 1)) nu) ∧
      (∀ i : ℕ, Qh (i + 1) = Φ i (Qh i)) ∧
      Qh 2 ≠ Q 2 ∧
      0 < nu * ∑ j ∈ Finset.range 2, (8 : ℝ≥0∞) ^ j ∧
      nu * ∑ j ∈ Finset.range 2, (8 : ℝ≥0∞) ^ j < 1 := by
  have hmeas : Measurable (fun _ : Bool => true) := measurable_const
  -- `wPhi` sends every measure of total mass `c` to `c • dirac true`.
  have hPhi : ∀ (i : ℕ) (μ : Measure Bool), wPhi i μ = μ Set.univ • Measure.dirac true :=
    fun _ μ => Measure.map_const μ true
  have hPhi_dirac : ∀ i : ℕ, wPhi i (Measure.dirac (true : Bool)) = Measure.dirac true := by
    intro i
    rw [hPhi]
    simp
  have hPhi_rho : ∀ i : ℕ, wPhi i wRho = wRho := by
    intro i
    rw [hPhi, wRho_univ, wRho]
  -- The nine-tenths mass is strictly between `0` and `1`.
  have hval : ENNReal.ofReal (1 / 10) * ∑ j ∈ Finset.range 2, (8 : ℝ≥0∞) ^ j
      = ENNReal.ofReal (9 / 10) := by
    have h9 : ((8 : ℝ≥0∞) + 1) = ENNReal.ofReal 9 := by
      simp; norm_num
    rw [geom_sum_two, h9, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  refine ⟨wQ, wQh, wPhi, ENNReal.ofReal (1 / 10), rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `htransfer`: `wPhi` is a pushforward, so the deterministic DPI applies, and
    -- `e ≤ 8 * e` always.
    intro i e h
    refine (h.map hmeas).mono ?_
    calc e = 1 * e := (one_mul e).symm
      _ ≤ 8 * e := by gcongr; norm_num
  · -- `haccuracy`.
    intro i
    cases i with
    | zero =>
        show TVLe (wPhi 0 (Measure.dirac true)) wRho (ENNReal.ofReal (1 / 10))
        rw [hPhi_dirac 0]
        exact tvLe_dirac_wRho
    | succ i =>
        show TVLe (wPhi (i + 1) wRho) wRho (ENNReal.ofReal (1 / 10))
        rw [hPhi_rho (i + 1)]
        exact (TVLe.refl _).mono (by simp)
  · -- `hrun`.
    intro i
    show Measure.dirac (true : Bool) = wPhi i (Measure.dirac true)
    rw [hPhi_dirac i]
  · -- The two laws really differ.
    show Measure.dirac (true : Bool) ≠ wRho
    intro hEq
    have h1 : (Measure.dirac (true : Bool)) Set.univ = wRho Set.univ := by rw [hEq]
    rw [wRho_univ] at h1
    simp only [measure_univ] at h1
    have : ENNReal.ofReal (9 / 10) < 1 := ENNReal.ofReal_lt_one.2 (by norm_num)
    exact absurd h1.symm this.ne
  · rw [hval]
    exact ENNReal.ofReal_pos.2 (by norm_num)
  · rw [hval]
    exact ENNReal.ofReal_lt_one.2 (by norm_num)

section AxiomCheck

#print axioms Arlib.TVLe.step
#print axioms Arlib.TVLe.iterate
#print axioms Arlib.GaussianCooling.le_geom_sum_of_rec
#print axioms Arlib.GaussianCooling.tvLe_phase_step
#print axioms Arlib.GaussianCooling.chainErr_le
#print axioms Arlib.GaussianCooling.tvLe_phaseChain
#print axioms Arlib.GaussianCooling.exists_phaseChain_witness

end AxiomCheck

end GaussianCooling

end Arlib
