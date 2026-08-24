/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt

/-!
# The Gaussian-cooling schedule: repetition count and variance budget

The volume algorithm of

> Ben Cousins, Santosh Vempala, *Gaussian Cooling and O\*(n³) Algorithms for Volume and
> Gaussian Volume* (arXiv:1409.6011)

is parametrized by two purely arithmetic schedule functions:

* `reps ε p` — how many independent runs to median together, given a target failure
  probability `p`;
* `varBudget ε` — the total relative-variance budget `κ` spread over the phases, given a
  target relative accuracy `ε`.

Everything in this file is **explicit data plus its proof**: `reps` and `varBudget` are
closed-form formulas, and the four facts the algorithm consumes about them are theorems,
not hypotheses.

## Main definitions

* `Arlib.GaussianCooling.reps` — `⌈log(1/p) / (2·(4/5 − 1/2)²)⌉₊ + 1 = ⌈(50/9)·log(1/p)⌉₊ + 1`.
  The denominator `2·(4/5 − 1/2)²` is the Hoeffding exponent for boosting a run that
  succeeds with probability `4/5` past the median threshold `1/2`. The `+ 1` is what makes
  the count positive for `p` close to `1`, where `log(1/p) ≤ 0` and `Nat.ceil` collapses
  to `0`.
* `Arlib.GaussianCooling.varBudget` — `log(1 + ε²/5)`, the exact inverse of the constraint
  `e^κ − 1 ≤ ε²/5`.

## Main results

The four schedule facts, stated exactly as the volume algorithm's hypotheses
`hreps_pos`, `hreps`, `hbudget0`, `hbudget` require them:

* `Arlib.GaussianCooling.reps_pos`     — `0 < reps ε p`;
* `Arlib.GaussianCooling.reps_spec`    — `log (1/p) / (2·(4/5 − 1/2)²) ≤ reps ε p`;
* `Arlib.GaussianCooling.varBudget_nonneg` — `0 ≤ varBudget ε`;
* `Arlib.GaussianCooling.varBudget_spec`   — `exp (varBudget ε) − 1 ≤ ε²/5`.

## Scope: what this file discharges and what it does not

This file discharges **exactly the schedule arithmetic** of the Cousins–Vempala volume
algorithm — the four hypotheses `hreps_pos`, `hreps`, `hbudget0`, `hbudget` — and nothing
else. In particular it says nothing about, and provides nothing towards:

* the sampler (`hphase_mean`: unbiasedness of a phase score under the logconcave density
  `∝ 1_K(x)e^{−‖x‖²/(2σ²)}`, which needs isoperimetry → conductance → ball-walk mixing);
* the per-phase variance bound `hphase_var` transported to the *sampled* score;
* phase or run independence (`hphase_indep`, `hindep_runs`);
* the cooling chain itself (`hchain_pos`, `hchain_end`) or the number of phases;
* any measurability / integrability guard (`hW_meas`, `hmed_meas`, `hmed`, `hprodLp`).

The two functions here do not depend on the body, the dimension, or the sampler, which is
why the schedule can be settled in isolation.

## Non-vacuity (`CLAUDE.md` §11)

A schedule that is secretly constant, or a budget that is secretly `0`, would satisfy the
four facts above while certifying nothing (`varBudget ≡ 0` makes `hbudget` read
`0 ≤ ε²/5`). The following lemmas pin the definitions to concrete values and show both
are genuinely nontrivial:

* `reps_eq_five_of_half` — `reps ε (1/2) = 5`, a computed value, not a placeholder;
* `reps_antitone_snd` — smaller failure probability demands at least as many runs;
* `reps_unbounded` — `reps` exceeds every `N`, so it is not constant;
* `exp_varBudget` — `e^{varBudget ε} = 1 + ε²/5` *exactly*, so `varBudget_spec` is tight;
* `varBudget_pos` — the budget is strictly positive for `ε > 0`, i.e. not the trivial `0`;
* `varBudget_one`, `varBudget_sqrt_five` — computed values `log(6/5)` and `log 2`;
* `varBudget_lt_varBudget` — strictly increasing in `ε`, so it is not constant either.
-/

namespace Arlib.GaussianCooling

open Real

/-- The number of independent runs to median together at failure probability `p`:
`⌈log(1/p) / (2·(4/5 − 1/2)²)⌉₊ + 1`, i.e. `⌈(50/9)·log(1/p)⌉₊ + 1`.

The denominator `2·(4/5 − 1/2)²` is the Hoeffding exponent for amplifying a per-run
success probability of `4/5` past the median threshold of `1/2`; the numerals are kept in
this unreduced form to match the volume algorithm's hypothesis syntactically. The `+ 1`
guarantees positivity even when `p` is close to `1` and `log(1/p) ≤ 0`, where `Nat.ceil`
would otherwise return `0`.

The accuracy parameter `ε` is accepted for uniformity with the algorithm's
`reps : ℝ → ℝ → ℕ` signature; the repetition count depends only on `p`. -/
noncomputable def reps (_ε p : ℝ) : ℕ :=
  ⌈Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2)⌉₊ + 1

/-- The total relative-variance budget `κ` at target accuracy `ε`: `log(1 + ε²/5)`.

This is the exact inverse of the algorithm's constraint `e^κ − 1 ≤ ε²/5`; see
`Arlib.GaussianCooling.exp_varBudget`, which shows the constraint holds with equality. -/
noncomputable def varBudget (ε : ℝ) : ℝ :=
  Real.log (1 + ε ^ 2 / 5)

/-- The `2 * (4 / 5 - 1 / 2) ^ 2` appearing in the repetition bound is `9 / 50`. -/
theorem hoeffding_denom : (2 : ℝ) * (4 / 5 - 1 / 2) ^ 2 = 9 / 50 := by norm_num

/-! ### The repetition count -/

/-- **Schedule fact 1** (`hreps_pos`): the repetition count is positive.

Stated with the `0 < p`, `p < 1` side conditions of the volume algorithm's hypothesis even
though the construction is positive unconditionally. -/
theorem reps_pos : ∀ ε p : ℝ, 0 < p → p < 1 → 0 < reps ε p := by
  intro ε p _ _
  simp [reps]

/-- **Schedule fact 2** (`hreps`): the repetition count meets the Hoeffding median-boost
bound `log(1/p) / (2·(4/5 − 1/2)²) ≤ reps ε p`. Immediate from `Nat.le_ceil`, which holds
for negative arguments too. -/
theorem reps_spec : ∀ ε p : ℝ, 0 < p → p < 1 →
    Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2) ≤ (reps ε p : ℝ) := by
  intro ε p _ _
  have h := Nat.le_ceil (Real.log (1 / p) / (2 * (4 / 5 - 1 / 2) ^ 2))
  rw [reps]
  push_cast
  linarith

/-- Non-vacuity: a computed value. At failure probability `1/2` the schedule asks for
exactly `5` runs (`⌈(50/9)·log 2⌉₊ + 1 = ⌈3.85…⌉₊ + 1`). -/
theorem reps_eq_five_of_half (ε : ℝ) : reps ε (1 / 2) = 5 := by
  have hp : (1 : ℝ) / (1 / 2) = 2 := by norm_num
  have hceil : ⌈Real.log 2 / (2 * (4 / 5 - 1 / 2 : ℝ) ^ 2)⌉₊ = 4 := by
    rw [hoeffding_denom, Nat.ceil_eq_iff (by norm_num)]
    have h1 := Real.log_two_gt_d9
    have h2 := Real.log_two_lt_d9
    constructor
    · push_cast
      linarith
    · push_cast
      linarith
  rw [reps, hp, hceil]

/-- Non-vacuity: the schedule is antitone in the failure probability — demanding a smaller
`p` never asks for fewer runs. -/
theorem reps_antitone_snd (ε : ℝ) {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    reps ε q ≤ reps ε p := by
  have hq : (0 : ℝ) < q := lt_of_lt_of_le hp hpq
  have hinv : 1 / q ≤ 1 / p := by
    rw [div_le_div_iff_of_pos_left one_pos hq hp]
    exact hpq
  have hlog : Real.log (1 / q) ≤ Real.log (1 / p) :=
    Real.log_le_log (by positivity) hinv
  have hdiv : Real.log (1 / q) / (2 * (4 / 5 - 1 / 2 : ℝ) ^ 2)
      ≤ Real.log (1 / p) / (2 * (4 / 5 - 1 / 2 : ℝ) ^ 2) := by
    rw [hoeffding_denom]
    linarith
  exact Nat.add_le_add_right (Nat.ceil_le_ceil hdiv) 1

/-- Non-vacuity: the schedule is unbounded, hence not secretly constant. For every `N`
there is a legitimate failure probability `p ∈ (0, 1)` at which more than `N` runs are
required. -/
theorem reps_unbounded (ε : ℝ) (N : ℕ) : ∃ p : ℝ, 0 < p ∧ p < 1 ∧ N ≤ reps ε p := by
  refine ⟨Real.exp (-((N : ℝ) + 1)), Real.exp_pos _, ?_, ?_⟩
  · rw [Real.exp_lt_one_iff]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  · have hlog : Real.log (1 / Real.exp (-((N : ℝ) + 1))) = (N : ℝ) + 1 := by
      rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
    have h := reps_spec ε (Real.exp (-((N : ℝ) + 1))) (Real.exp_pos _) (by
      rw [Real.exp_lt_one_iff]
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith)
    rw [hlog, hoeffding_denom] at h
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : (N : ℝ) ≤ (reps ε (Real.exp (-((N : ℝ) + 1))) : ℝ) := by linarith
    exact_mod_cast this

/-! ### The variance budget -/

/-- The budget is the exact solution of `e^κ − 1 = ε²/5`: `e^{varBudget ε} = 1 + ε²/5`.

This is the non-vacuity certificate for `varBudget_spec` — the inequality there is an
equality, so the budget is the largest one the algorithm's constraint allows. -/
theorem exp_varBudget (ε : ℝ) : Real.exp (varBudget ε) = 1 + ε ^ 2 / 5 := by
  rw [varBudget, Real.exp_log]
  positivity

/-- **Schedule fact 3** (`hbudget0`): the variance budget is nonnegative. -/
theorem varBudget_nonneg : ∀ ε : ℝ, 0 < ε → 0 ≤ varBudget ε := by
  intro ε _
  exact Real.log_nonneg (by nlinarith [sq_nonneg ε])

/-- **Schedule fact 4** (`hbudget`): the variance budget respects the accuracy constraint
`e^κ − 1 ≤ ε²/5`. Holds with equality, by `exp_varBudget`. -/
theorem varBudget_spec : ∀ ε : ℝ, 0 < ε → Real.exp (varBudget ε) - 1 ≤ ε ^ 2 / 5 := by
  intro ε _
  rw [exp_varBudget]
  linarith

/-- Non-vacuity: the budget is *strictly* positive for every positive accuracy, so it is
not the degenerate `varBudget ≡ 0` that would satisfy facts 3 and 4 vacuously. -/
theorem varBudget_pos {ε : ℝ} (hε : 0 < ε) : 0 < varBudget ε := by
  refine Real.log_pos ?_
  nlinarith

/-- Non-vacuity: a computed value, `varBudget 1 = log(6/5)`. -/
theorem varBudget_one : varBudget 1 = Real.log (6 / 5) := by
  rw [varBudget]
  norm_num

/-- Non-vacuity: a second computed value, `varBudget √5 = log 2`, since `(√5)²/5 = 1`. -/
theorem varBudget_sqrt_five : varBudget (Real.sqrt 5) = Real.log 2 := by
  rw [varBudget, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num

/-- Non-vacuity: the budget is strictly increasing in the accuracy parameter on
`[0, ∞)`, hence not constant. -/
theorem varBudget_lt_varBudget {ε₁ ε₂ : ℝ} (h₁ : 0 ≤ ε₁) (h : ε₁ < ε₂) :
    varBudget ε₁ < varBudget ε₂ := by
  refine Real.log_lt_log (by positivity) ?_
  nlinarith

end Arlib.GaussianCooling
