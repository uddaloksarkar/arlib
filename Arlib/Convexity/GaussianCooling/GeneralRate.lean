/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.IndicatorVariance
import Arlib.Convexity.GaussianCooling.Schedule

/-!
# Resolving the fixed-rate obstruction: an admissible general cooling rate `α`

## The contradiction this file removes

`Arlib.Convexity.GaussianCooling.PhaseVar` proves two theorems that together rule out the
fixed cooling rate `α = 1/n`:

* `Arlib.GaussianCooling.fixedRate_meets_budget_iff` (`PhaseVar.lean:572`) — the fixed-rate
  per-phase constant `1 + 2/n` meets the algorithm's per-phase budget `1 + κ/m` **iff**
  `2m ≤ nκ`;
* `Arlib.GaussianCooling.geomSchedule_total_cooling_lt` (`PhaseVar.lean:620`) — but under
  `2m ≤ n·varBudget ε` with `ε ≤ 1`, the schedule's *total* cooling factor satisfies
  `(1 + 1/n)^m < 11/10`.

A Gaussian-cooling schedule has to raise `σ²` from `≈ 1/n` to `≈ R²`, a factor of order
`nR²`, so `1.1` is not enough and the fixed rate is self-contradictory. The docstring of
`geomSchedule_total_cooling_lt` names the fix: keep the *general*-`α` transport step

  `Arlib.GaussianCooling.G_mul_G_le_of_zLogconcave` (`Variance.lean:1322`),
  `G(σ²/(1-α))·G(σ²/(1+α)) ≤ (1-α²)^{-(n+1)}·G(σ²)²`,

whose per-phase constant is `(1-α²)^{-(n+1)}` rather than `1 + 2/n`, and choose `α` small.
Its `ZLogconcaveHypothesis` is already discharged for the indicator of a convex body by
`Arlib.GaussianCooling.zLogconcaveHypothesis_indicator`, packaged as
`Arlib.GaussianCooling.G_mul_G_le_indicator`; nothing about it is reproved here.

**The obstruction is genuinely removed:** `exists_admissible` below produces, for *every*
target cooling factor `T`, a rate `α` and a phase count `m` that meet the budget
`(1-α²)^{-(n+1)} ≤ 1 + κ/m` and still cool by `T` or more. The fixed rate's `11/10` ceiling
is an artefact of `α = 1/n` being far too large, not of the budget.

## The answer, in three parts

**1. When does a general `α` meet the budget?** The exact characterisation is
`generalRate_meets_budget_iff` (a rearrangement with no loss), and it is bracketed by a
matching necessary and sufficient condition in closed form:

* `generalRate_budget_necessary` — the budget **forces** `(n+1)α²m ≤ κ`;
* `generalRate_budget_sufficient` — `4(n+1)α²m ≤ κ` (with `α² ≤ 1/2`, `κ ≤ m`) **implies**
  the budget.

So "meets the budget" is `(n+1)α²m ≍ κ` up to the factor `4`, which is the honest general-`α`
analogue of `fixedRate_meets_budget_iff`'s `2m ≤ nκ`. (Sanity check: at `α = 1/n` the
necessary condition reads `(n+1)m/n² ≤ κ`, i.e. `m ≲ nκ` — the same regime.)

**2. How large can the total cooling `(1 + α)^m` be?** This is the crux, and the answer is
**arbitrarily large**, in sharp contrast with the fixed rate:

* `totalCooling_ge_exp` — `(1+α)^m ≥ e^{mα/2}` for `α ≤ 1`, the achievability side;
* `generalPhaseCount_ge_of_budget` — the matching converse: any `(α, m)` meeting the budget and
  cooling by `T ≥ 1` must have `(n+1)·(log T)² ≤ κ·m`.

The converse is what fixes the shape of the answer: with `L := log T` the target
log-cooling, **`m ≥ (n+1)L²/κ` phases are forced**, and the explicit construction below
achieves `m ≤ 32(n+1)L²/κ + 1`. Hence `m = Θ(nL²/κ)` and `α = Θ(κ/(nL))`, tight up to an
absolute constant.

**3. An explicit admissible `(α, m)`.** `generalCoolRate n κ L = κ/(16(n+1)L)` and
`generalPhaseCount n κ L = ⌈32(n+1)L²/κ⌉₊` are admissible for every `0 < κ ≤ 1` and `1 ≤ L`
(`generalCoolRate_meets_budget`, `generalCoolRate_total_cooling`). Instantiated at the volume algorithm's
parameters — `κ = varBudget ε = log(1 + ε²/5)` and `L = log(nR²)` — this is
`exists_admissible_volume`, whose phase count is

  `⌈32(n+1)·log(nR²)² / log(1 + ε²/5)⌉₊ = Θ(n·log²(nR²)/ε²)`.

## Scope: why this schedule is admissible but slower than the paper's

Cousins–Vempala do **not** shrink `α`. Their accuracy accounting (`vol3_journal.tex:1440`,
eq. `var-bound`) spreads the budget as `1 + (cᵢ-1)/kᵢ` with `kᵢ` *samples averaged per
phase*, so a per-phase constant `cᵢ = 1 + 2/n` is paid down by taking `kᵢ = Θ̃(1/ε²)`
samples and they keep `O*(n)` phases at `α = 1/n`.

The budget shape this repo's volume algorithm consumes, `1 + κ/m` with `m` the number of
phases, is the `kᵢ = 1` specialisation of that accounting: one sample per phase. Under
`k = 1` the *only* remaining freedom is `α`, and `generalPhaseCount_ge_of_budget` shows the
resulting `Θ(nL²/κ)` phase count is then forced, not an artefact of the construction. So
this file resolves the contradiction faithfully *within the stated budget shape*; recovering
the paper's `O*(n)` phase count needs the `kᵢ`-sample averaging, which is a change to the
algorithm's hypothesis shape and is out of scope here.

Nothing below concerns runtime, mixing, or the sampler. `G_mul_G_le_budget_indicator` and
`second_moment_le_budget_indicator` are the only statements about a body, and they are the
exact-sample per-phase bounds; transporting them across a TV error is `PhaseVar.lean`'s job.

## Semantic `def`s (`CLAUDE.md` §11)

`generalCoolRate` and `generalPhaseCount` are **closed-form abbreviations and nothing more** — they assert
no property, exactly as `Arlib.GaussianCooling.phaseVarBudget` does. Everything claimed of
them is a theorem: `generalCoolRate_meets_budget`, `generalCoolRate_total_cooling`, `generalPhaseCount_ge`,
`generalPhaseCount_le`, `generalPhaseCount_pos`, `generalCoolRate_lt_fixedRate`.

## Non-vacuity (`CLAUDE.md` §11)

The hypotheses `0 < κ ≤ 1`, `1 ≤ L` are not vacuous, and the `∃` statements are not empty:

* `varBudget_pos_le_one` — `0 < varBudget ε ≤ 1` for `0 < ε ≤ 1`, so the volume corollary's
  `κ` really is in range;
* `admissible_witness` — a fully concrete instance at `n = 3`, `ε = 1`, `R = 2`, with every
  hypothesis discharged numerically;
* `exists_admissible` is *constructive*: it hands back `generalCoolRate` and `generalPhaseCount`, not an
  abstract witness.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Set Real

variable {n : ℕ}

/-! ## An elementary two-sided bracket for `1 + t`

`Real.add_one_le_exp` gives `1 + t ≤ e^t`. The construction needs the *other* direction —
a lower bound for `1 + t` by an exponential — which is false for `e^t` but true for
`e^{t/2}` on `[0, 1]`. -/

/-- `e^{t/2} ≤ 1 + t` for `0 ≤ t ≤ 1`.

Route: `1 - t/2 ≤ e^{-t/2}` (`Real.add_one_le_exp`) inverts to `e^{t/2} ≤ (1 - t/2)⁻¹`,
which is `≤ 1 + t` because `(1 + t)(1 - t/2) - 1 = t(1 - t)/2 ≥ 0` on `[0, 1]`. Both steps
are tight at `t = 0`. -/
theorem exp_half_le_one_add {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Real.exp (t / 2) ≤ 1 + t := by
  have hpos : (0 : ℝ) < 1 - t / 2 := by linarith
  have hstep : Real.exp (t / 2) ≤ (1 - t / 2)⁻¹ := by
    rw [le_inv_comm₀ (Real.exp_pos _) hpos, ← Real.exp_neg]
    linarith [Real.add_one_le_exp (-(t / 2))]
  refine hstep.trans ?_
  rw [inv_le_iff_one_le_mul₀ hpos]
  nlinarith

/-- `(1 + α)^m ≥ e^{mα/2}` for `0 ≤ α ≤ 1`: the achievable total cooling of a geometric
schedule at rate `α` over `m` phases. Immediate from `exp_half_le_one_add`. -/
theorem totalCooling_ge_exp {m : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    Real.exp ((m : ℝ) * α / 2) ≤ (1 + α) ^ m := by
  have hstep : (Real.exp (α / 2)) ^ m ≤ (1 + α) ^ m :=
    pow_le_pow_left₀ (Real.exp_pos _).le (exp_half_le_one_add hα0 hα1) m
  refine le_trans (le_of_eq ?_) hstep
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- `(1 + α)^m ≤ e^{mα}`, the matching upper bound, from `1 + t ≤ e^t`. -/
theorem totalCooling_le_exp {m : ℕ} {α : ℝ} (hα0 : 0 ≤ α) :
    (1 + α) ^ m ≤ Real.exp ((m : ℝ) * α) := by
  have hstep : (1 + α) ^ m ≤ (Real.exp α) ^ m :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp α]) m
  refine hstep.trans (le_of_eq ?_)
  rw [← Real.exp_nat_mul]

/-! ## Deliverable 1: for which `(α, m, n, κ)` does `(1-α²)^{-(n+1)} ≤ 1 + κ/m` hold?

The general-`α` analogue of `fixedRate_meets_budget_iff`. The exact statement is a
rearrangement (`generalRate_meets_budget_iff`); the usable content is the pair of closed-form
bounds `generalRate_budget_necessary` / `generalRate_budget_sufficient`, which bracket the
condition as `(n+1)α²m ≍ κ` within a factor of `4`. -/

/-- **The exact relation.** For `0 ≤ α < 1`, the general-`α` per-phase constant
`(1-α²)^{-(n+1)}` meets the algorithm's budget `1 + κ/m` **iff**
`1 ≤ (1 + κ/m)·(1-α²)^{n+1}`.

This is the general-`α` counterpart of `fixedRate_meets_budget_iff`, and like it, it is an
exact `iff` with no loss: clearing the inverse is the whole content. `m` may be `0` (then
`κ/m = 0` by Lean's convention and both sides read `(1-α²)^{n+1} ≥ 1`, i.e. `α = 0`). -/
theorem generalRate_meets_budget_iff {n m : ℕ} {α κ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) :
    ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) ≤ 1 + κ / (m : ℝ)
      ↔ 1 ≤ (1 + κ / (m : ℝ)) * ((1 : ℝ) - α ^ 2) ^ (n + 1) := by
  have hone : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hc : (0 : ℝ) < ((1 : ℝ) - α ^ 2) ^ (n + 1) := by positivity
  rw [inv_pow, ← one_div, div_le_iff₀ hc]

/-- **Necessity.** Any `(α, m)` meeting the budget satisfies `(n+1)α²m ≤ κ`.

Proof: `(1-α²)⁻¹ = 1 + a` with `a = α²/(1-α²) ≥ α²`, and Bernoulli
(`one_add_mul_le_pow`) gives `(1+a)^{n+1} ≥ 1 + (n+1)a ≥ 1 + (n+1)α²`.

This is the half that makes the phase count `Θ(nL²/κ)` *forced* rather than merely
achievable; see `generalPhaseCount_ge_of_budget`. -/
theorem generalRate_budget_necessary {n m : ℕ} (hm : 0 < m) {α κ : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (h : ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) ≤ 1 + κ / (m : ℝ)) :
    ((n : ℝ) + 1) * α ^ 2 * (m : ℝ) ≤ κ := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hone : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  set a : ℝ := α ^ 2 / (1 - α ^ 2) with hadef
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hinv : ((1 : ℝ) - α ^ 2)⁻¹ = 1 + a := by
    rw [hadef]; field_simp; ring
  have hbern : 1 + ((n : ℝ) + 1) * a ≤ (1 + a) ^ (n + 1) := by
    have := one_add_mul_le_pow (a := a) (by linarith) (n + 1)
    push_cast at this
    linarith
  have hsq : α ^ 2 ≤ a := by
    rw [hadef, le_div_iff₀ hone]
    nlinarith [sq_nonneg α]
  rw [hinv] at h
  have hkey : ((n : ℝ) + 1) * α ^ 2 ≤ κ / (m : ℝ) := by
    have hN : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    nlinarith
  exact (le_div_iff₀ hm').1 hkey

/-- **Sufficiency.** `4(n+1)α²m ≤ κ` implies the budget, given `α² ≤ 1/2` and `0 ≤ κ ≤ m`.

Proof: `(1-α²)^{-(n+1)} ≤ exp(phaseVarBudget n α)` (reused from `IndicatorVariance`, not
reproved), `phaseVarBudget n α = (n+1)α²/(1-α²) ≤ 2(n+1)α²` since `1-α² ≥ 1/2`, and
`exp(κ/(2m)) ≤ 1 + κ/m` by `exp_half_le_one_add`.

The gap to `generalRate_budget_necessary` is exactly the factor `4`, split as
`2` (the `1-α² ≥ 1/2` slack) times `2` (the `e^{t/2} ≤ 1 + t` slack). -/
theorem generalRate_budget_sufficient {n m : ℕ} (hm : 0 < m) {α κ : ℝ}
    (hα0 : 0 ≤ α) (hα2 : α ^ 2 ≤ 1 / 2) (hκ0 : 0 ≤ κ) (hκm : κ ≤ (m : ℝ))
    (h : 4 * ((n : ℝ) + 1) * α ^ 2 * (m : ℝ) ≤ κ) :
    ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) ≤ 1 + κ / (m : ℝ) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hα1 : α < 1 := by nlinarith
  have hone : (1 : ℝ) / 2 ≤ 1 - α ^ 2 := by linarith
  have hN : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  -- `phaseVarBudget n α ≤ 2(n+1)α² ≤ κ/(2m)`
  have hbud : phaseVarBudget n α ≤ κ / (2 * (m : ℝ)) := by
    have hstep : phaseVarBudget n α ≤ 2 * (((n : ℝ) + 1) * α ^ 2) := by
      rw [phaseVarBudget, div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg hN (sq_nonneg α)]
    refine hstep.trans ?_
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  -- `e^{κ/(2m)} ≤ 1 + κ/m`
  have ht0 : (0 : ℝ) ≤ κ / (m : ℝ) := by positivity
  have ht1 : κ / (m : ℝ) ≤ 1 := by rw [div_le_one hm']; exact hκm
  have hexp : Real.exp (κ / (2 * (m : ℝ))) ≤ 1 + κ / (m : ℝ) := by
    have heq : κ / (2 * (m : ℝ)) = (κ / (m : ℝ)) / 2 := by ring
    rw [heq]
    exact exp_half_le_one_add ht0 ht1
  calc ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)
      ≤ Real.exp (phaseVarBudget n α) := inv_one_sub_sq_pow_le_exp_phaseVarBudget hα0 hα1
    _ ≤ Real.exp (κ / (2 * (m : ℝ))) := Real.exp_le_exp.2 hbud
    _ ≤ 1 + κ / (m : ℝ) := hexp

/-! ## Deliverable 2: how large can the total cooling `(1 + α)^m` be?

**Arbitrarily large** — this is the crux, and the point at which the general rate departs
from the fixed rate. `geomSchedule_total_cooling_lt` caps the fixed rate's total cooling at
`11/10`; `exists_admissible` below exceeds any prescribed `T`.

The exact price is `generalPhaseCount_ge_of_budget`: cooling by `T` costs at least
`(n+1)(log T)²/κ` phases. -/

/-- **The converse bound on total cooling.** If `(α, m)` meets the budget and cools by at
least `T ≥ 1`, then `(n+1)·(log T)² ≤ κ·m`.

Equivalently `m ≥ (n+1)(log T)²/κ`: a schedule that cools by `T` under the budget
`1 + κ/m` **must** use `Ω(n·log²T/κ)` phases. Combined with `generalPhaseCount_le`, which achieves
`32(n+1)(log T)²/κ + 1`, this pins the phase count to `Θ(n·log²T/κ)`.

Proof: `log T ≤ m·log(1+α) ≤ mα`, so `(n+1)(log T)² ≤ (n+1)m²α² = m·((n+1)α²m) ≤ mκ` by
`generalRate_budget_necessary`. -/
theorem generalPhaseCount_ge_of_budget {n m : ℕ} (hm : 0 < m) {α κ T : ℝ}
    (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hbud : ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) ≤ 1 + κ / (m : ℝ))
    (hT1 : 1 ≤ T) (hT : T ≤ (1 + α) ^ m) :
    ((n : ℝ) + 1) * (Real.log T) ^ 2 ≤ κ * (m : ℝ) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnec := generalRate_budget_necessary hm hα0 hα1 hbud
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  -- `log T ≤ m α`
  have hlog : Real.log T ≤ (m : ℝ) * α := by
    have h1 : Real.log T ≤ Real.log ((1 + α) ^ m) :=
      Real.log_le_log (by linarith) hT
    rw [Real.log_pow] at h1
    have h2 : Real.log (1 + α) ≤ α := by
      have := Real.log_le_sub_one_of_pos (x := 1 + α) (by linarith)
      linarith
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := hm'.le
    nlinarith
  have hN : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hma : 0 ≤ (m : ℝ) * α := by positivity
  have hsq : (Real.log T) ^ 2 ≤ ((m : ℝ) * α) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hnec hm'.le]

/-! ## Deliverable 3: an explicit admissible `(α, m)`

Given a per-phase variance budget `κ` and a target *log*-cooling `L` (so the schedule must
multiply `σ²` by at least `e^L`), take

  `α = κ/(16(n+1)L)`,   `m = ⌈32(n+1)L²/κ⌉₊`.

Then `mα ≥ 2L`, so `(1+α)^m ≥ e^{mα/2} ≥ e^L`, while `4(n+1)α²m ≤ κ`. -/

/-- **The admissible cooling rate** at budget `κ` and target log-cooling `L` in dimension
`n`: `generalCoolRate n κ L = κ/(16(n+1)L)`.

A *closed-form abbreviation and nothing more* — it asserts no property. What is claimed of
it is proved: `generalCoolRate_pos`, `generalCoolRate_le_sixteenth`, `generalCoolRate_meets_budget`,
`generalCoolRate_total_cooling`, `generalCoolRate_lt_fixedRate`. -/
noncomputable def generalCoolRate (n : ℕ) (κ L : ℝ) : ℝ := κ / (16 * ((n : ℝ) + 1) * L)

/-- **The admissible phase count** at budget `κ` and target log-cooling `L` in dimension
`n`: `generalPhaseCount n κ L = ⌈32(n+1)L²/κ⌉₊`.

A *closed-form abbreviation and nothing more*. See `generalPhaseCount_pos`, `generalPhaseCount_ge`,
`generalPhaseCount_le`, and the matching lower bound `generalPhaseCount_ge_of_budget`. -/
noncomputable def generalPhaseCount (n : ℕ) (κ L : ℝ) : ℕ := ⌈32 * ((n : ℝ) + 1) * L ^ 2 / κ⌉₊

section Explicit

variable {κ L : ℝ}

theorem generalCoolRate_pos (hκ0 : 0 < κ) (hL : 0 < L) : 0 < generalCoolRate n κ L := by
  rw [generalCoolRate]; positivity

/-- The admissible rate is tiny: `α ≤ 1/16` whenever `κ ≤ 1 ≤ L`. -/
theorem generalCoolRate_le_sixteenth (_hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hL : 1 ≤ L) :
    generalCoolRate n κ L ≤ 1 / 16 := by
  have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  rw [generalCoolRate, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- **How far below the fixed rate the admissible rate sits.** `generalCoolRate n κ L < 1/n` for
`n ≥ 1`, `0 < κ ≤ 1`, `1 ≤ L` — the fixed rate `α = 1/n` of
`geomSchedule_total_cooling_lt` is *never* admissible in this regime, and the gap is the
factor `16L/κ`. -/
theorem generalCoolRate_lt_fixedRate (hn : 0 < n) (_hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hL : 1 ≤ L) :
    generalCoolRate n κ L < 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [generalCoolRate, div_lt_div_iff₀ (by positivity) hn']
  nlinarith

theorem generalPhaseCount_ge (_hκ0 : 0 < κ) :
    32 * ((n : ℝ) + 1) * L ^ 2 / κ ≤ (generalPhaseCount n κ L : ℝ) :=
  Nat.le_ceil _

theorem generalPhaseCount_le (hκ0 : 0 < κ) :
    (generalPhaseCount n κ L : ℝ) ≤ 32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1 := by
  rw [generalPhaseCount]
  exact (Nat.ceil_lt_add_one (by positivity)).le

/-- The phase count is at least `32`, hence positive: the construction never degenerates. -/
theorem generalPhaseCount_ge_32 (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hL : 1 ≤ L) :
    (32 : ℝ) ≤ (generalPhaseCount n κ L : ℝ) := by
  refine le_trans ?_ (generalPhaseCount_ge (n := n) (L := L) hκ0)
  rw [le_div_iff₀ hκ0]
  have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  nlinarith

theorem generalPhaseCount_pos (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hL : 1 ≤ L) : 0 < generalPhaseCount n κ L := by
  have h := generalPhaseCount_ge_32 (n := n) hκ0 hκ1 hL
  have : (0 : ℝ) < (generalPhaseCount n κ L : ℝ) := by linarith
  exact_mod_cast this

/-- **The explicit choice meets the budget.** For `0 < κ ≤ 1` and `1 ≤ L`,

  `(1 - α²)^{-(n+1)} ≤ 1 + κ/m`  with  `α = generalCoolRate n κ L`, `m = generalPhaseCount n κ L`.

The whole content is `κ·m ≤ 64(n+1)L²`, which follows from `generalPhaseCount_le` and
`κ ≤ 32(n+1)L²`. -/
theorem generalCoolRate_meets_budget (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hL : 1 ≤ L) :
    ((1 : ℝ) - (generalCoolRate n κ L) ^ 2)⁻¹ ^ (n + 1)
      ≤ 1 + κ / (generalPhaseCount n κ L : ℝ) := by
  have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hN0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hm := generalPhaseCount_pos (n := n) hκ0 hκ1 hL
  have h32 := generalPhaseCount_ge_32 (n := n) (L := L) hκ0 hκ1 hL
  have hmle := generalPhaseCount_le (n := n) (L := L) hκ0
  set m : ℕ := generalPhaseCount n κ L with hmdef
  set α : ℝ := generalCoolRate n κ L with hαdef
  have hα0 : 0 ≤ α := (generalCoolRate_pos hκ0 hL0).le
  have hα16 : α ≤ 1 / 16 := generalCoolRate_le_sixteenth hκ0 hκ1 hL
  refine generalRate_budget_sufficient hm hα0 (by nlinarith) hκ0.le (by linarith) ?_
  -- `κ·m ≤ 64(n+1)L²`
  have hkm : κ * (m : ℝ) ≤ 64 * ((n : ℝ) + 1) * L ^ 2 := by
    have hstep : κ * (m : ℝ) ≤ κ * (32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1) :=
      mul_le_mul_of_nonneg_left hmle hκ0.le
    have hcancel : κ * (32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1)
        = 32 * ((n : ℝ) + 1) * L ^ 2 + κ := by field_simp
    rw [hcancel] at hstep
    nlinarith
  have hrw : 4 * ((n : ℝ) + 1) * α ^ 2 * (m : ℝ)
      = κ ^ 2 * (m : ℝ) / (64 * ((n : ℝ) + 1) * L ^ 2) := by
    rw [hαdef, generalCoolRate, div_pow]
    field_simp
    ring
  rw [hrw, div_le_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hkm hκ0.le]

/-- **The explicit choice cools by `e^L`.** For `0 < κ ≤ 1` and `1 ≤ L`,

  `e^L ≤ (1 + α)^m`  with  `α = generalCoolRate n κ L`, `m = generalPhaseCount n κ L`.

The whole content is `mα ≥ 2L`, then `totalCooling_ge_exp`. -/
theorem generalCoolRate_total_cooling (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hL : 1 ≤ L) :
    Real.exp L ≤ (1 + generalCoolRate n κ L) ^ (generalPhaseCount n κ L) := by
  have hN1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hN0 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have hmge := generalPhaseCount_ge (n := n) (L := L) hκ0
  set m : ℕ := generalPhaseCount n κ L with hmdef
  set α : ℝ := generalCoolRate n κ L with hαdef
  have hα0 : 0 ≤ α := (generalCoolRate_pos hκ0 hL0).le
  have hα1 : α ≤ 1 := le_trans (generalCoolRate_le_sixteenth hκ0 hκ1 hL) (by norm_num)
  -- `m·α ≥ 2L`
  have hmα : 2 * L ≤ (m : ℝ) * α := by
    have hlow : 32 * ((n : ℝ) + 1) * L ^ 2 / κ ≤ (m : ℝ) := hmge
    rw [div_le_iff₀ hκ0] at hlow
    have hαval : α = κ / (16 * ((n : ℝ) + 1) * L) := by rw [hαdef, generalCoolRate]
    have hexp : (m : ℝ) * α = (m : ℝ) * κ / (16 * ((n : ℝ) + 1) * L) := by
      rw [hαval]; ring
    rw [hexp, le_div_iff₀ (by positivity : (0 : ℝ) < 16 * ((n : ℝ) + 1) * L)]
    nlinarith
  refine le_trans (Real.exp_le_exp.2 ?_) (totalCooling_ge_exp hα0 hα1)
  linarith

end Explicit

/-! ## The crux, stated as an existence theorem

`geomSchedule_total_cooling_lt`: at the fixed rate, budget-meeting schedules cool by less
than `11/10`. Here: at a general rate, budget-meeting schedules cool by **more than any
prescribed `T`**. The obstruction is resolved. -/

/-- **The obstruction is removed.** For every dimension `n`, every per-phase variance budget
`0 < κ ≤ 1`, and every target total cooling factor `T ≥ e`, there is a cooling rate `α` and
a phase count `m` such that

* `0 < m`, `0 ≤ α < 1`;
* the per-phase constant meets the budget: `(1-α²)^{-(n+1)} ≤ 1 + κ/m`;
* the schedule cools by at least `T`: `T ≤ (1+α)^m`.

Since `T` is arbitrary it may be taken far above the `11/10` ceiling of
`geomSchedule_total_cooling_lt` — in particular `T = nR²`, which is what the Gaussian
cooling schedule needs.

The witnesses are explicit: `α = generalCoolRate n κ (log T)`, `m = generalPhaseCount n κ (log T)`. -/
theorem exists_admissible (n : ℕ) {κ T : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hT : Real.exp 1 ≤ T) :
    ∃ (α : ℝ) (m : ℕ), 0 < m ∧ 0 ≤ α ∧ α < 1 ∧
      ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) ≤ 1 + κ / (m : ℝ) ∧ T ≤ (1 + α) ^ m := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hL : (1 : ℝ) ≤ Real.log T := (Real.le_log_iff_exp_le hT0).2 hT
  have hL0 : (0 : ℝ) < Real.log T := by linarith
  refine ⟨generalCoolRate n κ (Real.log T), generalPhaseCount n κ (Real.log T),
    generalPhaseCount_pos hκ0 hκ1 hL, (generalCoolRate_pos hκ0 hL0).le, ?_,
    generalCoolRate_meets_budget hκ0 hκ1 hL, ?_⟩
  · exact lt_of_le_of_lt (generalCoolRate_le_sixteenth hκ0 hκ1 hL) (by norm_num)
  · have h := generalCoolRate_total_cooling (n := n) hκ0 hκ1 hL
    rwa [Real.exp_log hT0] at h

/-! ## Instantiation at the volume algorithm's parameters

`κ := varBudget ε = log(1 + ε²/5)`, `L := log(nR²)`, target cooling `nR²`. -/

/-- The volume algorithm's budget is in range for `exists_admissible`: `0 < varBudget ε ≤ 1`
for `0 < ε ≤ 1`. (In fact `varBudget ε ≤ ε²/5 ≤ 1/5`.) -/
theorem varBudget_pos_le_one {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < varBudget ε ∧ varBudget ε ≤ 1 := by
  refine ⟨varBudget_pos hε0, ?_⟩
  have h := Real.log_le_sub_one_of_pos (x := 1 + ε ^ 2 / 5) (by positivity)
  rw [← varBudget] at h
  nlinarith

/-- **The admissible schedule for the volume algorithm.** For `0 < ε ≤ 1` and a target
cooling factor `nR² ≥ e` — the factor a Gaussian-cooling schedule needs in order to raise
`σ²` from `≈ 1/n` to `≈ R²` — the rate

  `α = varBudget ε / (16(n+1)·log(nR²))`

and the phase count

  `m = ⌈32(n+1)·log(nR²)² / varBudget ε⌉₊`

meet the per-phase budget `1 + varBudget ε / m` *and* cool by at least `nR²`.

Since `varBudget ε = log(1 + ε²/5) = Θ(ε²)`, this is
`α = Θ(ε²/(n·log(nR²)))` and `m = Θ(n·log²(nR²)/ε²)` phases — and by
`generalPhaseCount_ge_of_budget` that phase count is optimal up to an absolute constant. Contrast
`geomSchedule_total_cooling_lt`, where the fixed rate caps the total cooling at `11/10`. -/
theorem exists_admissible_volume (n : ℕ) {ε R : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hR : Real.exp 1 ≤ (n : ℝ) * R ^ 2) :
    ((1 : ℝ) - (generalCoolRate n (varBudget ε) (Real.log ((n : ℝ) * R ^ 2))) ^ 2)⁻¹ ^ (n + 1)
        ≤ 1 + varBudget ε
            / (generalPhaseCount n (varBudget ε) (Real.log ((n : ℝ) * R ^ 2)) : ℝ)
      ∧ (n : ℝ) * R ^ 2
        ≤ (1 + generalCoolRate n (varBudget ε) (Real.log ((n : ℝ) * R ^ 2)))
            ^ (generalPhaseCount n (varBudget ε) (Real.log ((n : ℝ) * R ^ 2)))
      ∧ 0 < generalPhaseCount n (varBudget ε) (Real.log ((n : ℝ) * R ^ 2)) := by
  obtain ⟨hκ0, hκ1⟩ := varBudget_pos_le_one hε0 hε1
  have hT0 : (0 : ℝ) < (n : ℝ) * R ^ 2 := lt_of_lt_of_le (Real.exp_pos 1) hR
  have hL : (1 : ℝ) ≤ Real.log ((n : ℝ) * R ^ 2) := (Real.le_log_iff_exp_le hT0).2 hR
  refine ⟨generalCoolRate_meets_budget hκ0 hκ1 hL, ?_, generalPhaseCount_pos hκ0 hκ1 hL⟩
  have h := generalCoolRate_total_cooling (n := n) hκ0 hκ1 hL
  rwa [Real.exp_log hT0] at h

/-! ## Non-vacuity: a fully concrete instance

`CLAUDE.md` §11 — the hypotheses `0 < κ ≤ 1`, `1 ≤ L` are discharged numerically, so the
`∃` statements above are not empty. -/

/-- **Non-vacuity witness.** At `n = 3`, `ε = 1`, `R = 2` — so `nR² = 12 ≥ e` — an
admissible `(α, m)` exists. Every hypothesis is discharged by computation. -/
theorem admissible_witness :
    ∃ (α : ℝ) (m : ℕ), 0 < m ∧ 0 ≤ α ∧ α < 1 ∧
      ((1 : ℝ) - α ^ 2)⁻¹ ^ (3 + 1) ≤ 1 + varBudget 1 / (m : ℝ)
      ∧ (12 : ℝ) ≤ (1 + α) ^ m := by
  obtain ⟨hκ0, hκ1⟩ := varBudget_pos_le_one (ε := 1) one_pos le_rfl
  have hT : Real.exp 1 ≤ (12 : ℝ) := by
    have := Real.exp_one_lt_d9
    linarith
  exact exists_admissible 3 hκ0 hκ1 hT

/-! ## The payoff for a convex body

The admissible `(α, m)` fed back into the general-`α` transport step, with its
`ZLogconcaveHypothesis` already discharged for the indicator of a convex body by
`G_mul_G_le_indicator`. Nothing is reproved: these are one-line compositions. -/

section Body

variable {K : Set (EuclSpace n)} {σ κ L : ℝ}

/-- **The per-phase `G`-bound at the algorithm's budget**, unconditional for a convex body.
For `K` convex and measurable, `σ > 0`, `0 < κ ≤ 1`, `1 ≤ L`, and
`α = generalCoolRate n κ L`, `m = generalPhaseCount n κ L`,

  `G 1_K (σ²/(1-α)) · G 1_K (σ²/(1+α)) ≤ (1 + κ/m) · G 1_K (σ²)²`.

The constant is now the algorithm's `1 + κ/m` — no `1 + 2/n`, no `ZLogconcaveHypothesis`,
no roundness, no boundedness. -/
theorem G_mul_G_le_budget_indicator (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hσ : 0 < σ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hL : 1 ≤ L) :
    G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 - generalCoolRate n κ L))
        * G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + generalCoolRate n κ L))
      ≤ (1 + κ / (generalPhaseCount n κ L : ℝ))
        * (G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2)) ^ 2 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hα0 : 0 ≤ generalCoolRate n κ L := (generalCoolRate_pos hκ0 hL0).le
  have hα1 : generalCoolRate n κ L < 1 :=
    lt_of_le_of_lt (generalCoolRate_le_sixteenth hκ0 hκ1 hL) (by norm_num)
  refine (G_mul_G_le_indicator hK hKm hσ hα0 hα1).trans ?_
  exact mul_le_mul_of_nonneg_right (generalCoolRate_meets_budget hκ0 hκ1 hL) (sq_nonneg _)

/-- **`E(Y²) ≤ (1 + κ/m)·E(Y)²` at the admissible rate**, for the indicator of a convex body
of positive volume — the exact shape the volume algorithm's `hphase_var` asks for, at an
exact sample from the phase law, with the *algorithm's own* constant `1 + κ/m`.

This is what `PhaseVar.lean`'s `coolLaw_sq_moment_le` could not deliver at the fixed rate:
there the constant is `1 + 2/n`, and `geomSchedule_total_cooling_lt` shows no useful
schedule reconciles it with `1 + κ/m`. Here the reconciliation is unconditional, and
`generalCoolRate_total_cooling` certifies that the schedule still cools by `e^L`. -/
theorem second_moment_le_budget_indicator (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hvol : 0 < volume K) (hσ : 0 < σ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hL : 1 ≤ L) :
    (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
          / gW (Set.indicator K (1 : EuclSpace n → ℝ))
              (σ ^ 2 / (1 + generalCoolRate n κ L)) x) ^ 2
        * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + generalCoolRate n κ L)) x
          / G (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + generalCoolRate n κ L))))
      ≤ (1 + κ / (generalPhaseCount n κ L : ℝ))
        * (∫ x, (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2) x
              / gW (Set.indicator K (1 : EuclSpace n → ℝ))
                  (σ ^ 2 / (1 + generalCoolRate n κ L)) x)
            * (gW (Set.indicator K (1 : EuclSpace n → ℝ)) (σ ^ 2 / (1 + generalCoolRate n κ L)) x
              / G (Set.indicator K (1 : EuclSpace n → ℝ))
                  (σ ^ 2 / (1 + generalCoolRate n κ L)))) ^ 2 := by
  have hL0 : (0 : ℝ) < L := by linarith
  have hα0 : 0 ≤ generalCoolRate n κ L := (generalCoolRate_pos hκ0 hL0).le
  have hα1 : generalCoolRate n κ L < 1 :=
    lt_of_le_of_lt (generalCoolRate_le_sixteenth hκ0 hκ1 hL) (by norm_num)
  exact second_moment_le_of_G_bound hσ.ne' (by linarith) (by intro h; linarith)
    (G_indicator_pos hKm hvol (by positivity))
    (G_mul_G_le_budget_indicator hK hKm hσ hκ0 hκ1 hL)

end Body

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms exp_half_le_one_add
#print axioms totalCooling_ge_exp
#print axioms totalCooling_le_exp
#print axioms generalRate_meets_budget_iff
#print axioms generalRate_budget_necessary
#print axioms generalRate_budget_sufficient
#print axioms generalPhaseCount_ge_of_budget
#print axioms generalCoolRate_pos
#print axioms generalCoolRate_le_sixteenth
#print axioms generalCoolRate_lt_fixedRate
#print axioms generalPhaseCount_ge
#print axioms generalPhaseCount_le
#print axioms generalPhaseCount_ge_32
#print axioms generalPhaseCount_pos
#print axioms generalCoolRate_meets_budget
#print axioms generalCoolRate_total_cooling
#print axioms exists_admissible
#print axioms varBudget_pos_le_one
#print axioms exists_admissible_volume
#print axioms admissible_witness
#print axioms G_mul_G_le_budget_indicator
#print axioms second_moment_le_budget_indicator

end Arlib.GaussianCooling
