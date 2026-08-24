/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.IndicatorVariance
import Arlib.Convexity.GaussianCooling.PhaseVar

/-!
# A cooling schedule that meets the variance budget *and* anneals

`Arlib.Convexity.GaussianCooling.PhaseVar` proves a negative result about the **fixed**
cooling rate `α = 1/n`, the rate at which `ZLogconcave.lean` supplies the per-phase
second-moment constant `1 + 2/n`:

* `fixedRate_meets_budget_iff` — `1 + 2/n ≤ 1 + κ/m ↔ 2m ≤ nκ`;
* `geomSchedule_total_cooling_lt` — `2m ≤ n·varBudget ε` and `ε ≤ 1` force
  `(1 + 1/n)^m < 11/10`.

Since `σ_m²/σ_0² = (1+1/n)^m`, a fixed-rate schedule that fits the algorithm's variance
budget **cannot cool at all**, while Gaussian cooling needs a total factor of order `n·R²`.
That obstruction is machine-checked and is not a matter of constants.

This file builds the escape: a schedule with a *free* rate `α`, consuming the general-`α`
input `G_mul_G_le_indicator` (`IndicatorVariance.lean:200`, the transport step with its
`ZLogconcaveHypothesis` already discharged for the indicator of a convex body) whose
per-phase constant is `(1-α²)^{-(n+1)}` rather than the pinned `1 + 2/n`.

## The schedule, and what `m` and `α` actually are

Write `L` for the **logarithm** of the required total cooling factor (`σ_m²/σ_0² ≥ e^L`;
for Cousins–Vempala `e^L ≈ n·R²`, i.e. `L ≈ log n + 2 log R`) and `κ` for the algorithm's
total relative-variance budget (`κ = varBudget ε = log(1 + ε²/5) ≈ ε²/5`).  Then

  `coolPhases n L κ = ⌈8(n+1)L²/κ⌉`,   `coolRate n L κ = √(κ / (2·m·(n+1)))`,

so, substituting `m`,

  `m = Θ(n·L²/κ)`   and   `α = Θ(κ / (n·L))`.

The derivation is forced, not chosen.  `(1-α²)^{-(n+1)} ≤ 1 + κ/m` needs (Bernoulli)
`(n+1)α²(1 + κ/m) ≤ κ/m`, i.e. `α ≲ √(κ/(m(n+1)))`; a total cooling of `e^L` needs
`m·log(1+α) ≥ L`, i.e. `m·α ≳ L`.  Multiplying, `L ≲ mα ≲ √(mκ/(n+1))`, whence
`m ≳ (n+1)L²/κ`.  `phases_ge_of_budget_of_cooling` proves that lower bound outright, so the
constant `8` above is within a factor `8` of optimal for these two constraints.

**In Cousins–Vempala's parameters** (`e^L ≈ nR²`, `κ ≈ ε²/5`):

  `m = Θ(n·log²(nR²)/ε²)`,   `α = Θ(ε² / (n·log(nR²)))`.

So the **phase count is polynomial** in `n`, `1/ε` and `log R`.

## ⚠ A polynomial phase count is *not* a polynomial algorithm

The phase count is only the outer loop.  The per-phase cost — drawing a sample from the
phase density to within total variation `ε` — is where this repo's constants are
exponential, and nothing here improves them:

* `Arlib/Convexity/GaussianCooling/Unblock.lean` (≈ line 591) states outright that the
  isoperimetric constant it produces is `e^{-R²/s}·2⁻ⁿ/(2R)`, "doubly exponentially bad in
  `n` in the worst case.  This is not a polynomial-time result."
* `Arlib/MarkovChains/Continuous/MetropolisConductance.lean` carries the same exponential
  conductance constants into the mixing time.
* Even the TV transport in `PhaseVar.lean` pays exponentially: its smallness condition is
  `ε ≲ s·E(W)²·e^{−R²/σᵢ²}`, and that `e^{−R²/σᵢ²}` is inherited verbatim by
  `sampled_phase_sq_moment_le_coolRate` below.

**Nothing in this file claims, implies, or is a step towards a polynomial mixing time.**
It removes exactly one obstruction — the schedule-level one — and leaves the exponential
per-phase sampling cost exactly where it was.

## Main results

* `Arlib.GaussianCooling.coolPhases`, `Arlib.GaussianCooling.coolRate` — the schedule
  (closed-form `def`s; they assert nothing on their own).
* `Arlib.GaussianCooling.coolRate_meets_budget` — **the budget-meeting statement**, the
  general-`α` analogue of `fixedRate_meets_budget_iff`:
  `(1 - α²)^{-(n+1)} ≤ 1 + κ/m` at `α = coolRate n L κ`, `m = coolPhases n L κ`.
* `Arlib.GaussianCooling.coolSchedule_total_cooling` — **the positive counterpart of
  `geomSchedule_total_cooling_lt`**: `e^L ≤ (1+α)^m`.  Also
  `coolSchedule_total_cooling_factor` (in terms of a factor `T ≥ e` instead of `L`) and
  `geomSchedule_coolRate_total_cooling` (on the schedule object of `Chain.lean`).
* `Arlib.GaussianCooling.phases_ge_of_budget_of_cooling` — the matching lower bound
  `m ≥ (n+1)L²/κ` for *any* schedule meeting both constraints.
* `Arlib.GaussianCooling.coolLaw_sq_moment_le_rate` — `coolLaw_sq_moment_le` at a general
  rate: `E_π(W²) ≤ (1-α²)^{-(n+1)}·E_π(W)²` for the indicator of a convex body, with no
  `ZLogconcaveHypothesis`.
* `Arlib.GaussianCooling.coolLaw_sq_moment_le_budget` — the same with the constant written
  as the algorithm writes it, `1 + κ/m`.
* `Arlib.GaussianCooling.sampled_phase_sq_moment_le_coolRate` — `hphase_var`'s shape for a
  TV-approximate sample, i.e. `sampled_phase_sq_moment_le_budget` **with its `2m ≤ nκ`
  hypothesis deleted**, because the budget is now met by construction.

## Non-vacuity

Everything is guarded by `1 ≤ L`, `0 < κ`, `κ ≤ 1`.  These hold together at the algorithm's
own parameters: `varBudget_le_one` proves `varBudget ε ≤ 1` for `0 < ε ≤ 1`, and
`coolSchedule_nonvacuous` exhibits `κ = varBudget ε`, `L = 1` satisfying both headline
conclusions at once.  `sampled_phase_sq_moment_le_coolRate_witness` instantiates the whole
sampled-phase capstone — closed unit ball, `geomSchedule 1 α`, exact sample (`ε = 0`), no
slack (`s = 0`) — so no hypothesis of it is unsatisfiable.

## Scope

This file changes the *schedule* only.  It does not produce a TV bound, does not remove the
radius hypothesis `K ⊆ R·Bₙ` that `PhaseVar.lean` documents, and edits nothing under `Ttc/`.
It is not imported by `Arlib/Convexity.lean`; adding that import is a separate edit.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open scoped ENNReal

/-! ## The elementary inequality behind the budget -/

/-- **Bernoulli, in the form the variance budget needs.**  For `0 ≤ α < 1`, `0 ≤ c` and

  `(n+1)·α²·(1+c) ≤ c`,

the algebraic factor produced by the transport step satisfies `(1-α²)^{-(n+1)} ≤ 1 + c`.

Proof: `(1-α²)^{n+1} ≥ 1 - (n+1)α²` (Bernoulli), so
`(1+c)(1-α²)^{n+1} ≥ (1+c)(1-(n+1)α²) = 1 + c - (1+c)(n+1)α² ≥ 1`. -/
theorem inv_one_sub_sq_pow_le_one_add {n : ℕ} {α c : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hc : 0 ≤ c) (h : ((n : ℝ) + 1) * α ^ 2 * (1 + c) ≤ c) :
    ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) ≤ 1 + c := by
  have hpos : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hbern := one_add_mul_le_pow (a := -(α ^ 2)) (by nlinarith) (n + 1)
  have hb' : 1 - ((n : ℝ) + 1) * α ^ 2 ≤ (1 - α ^ 2) ^ (n + 1) := by
    have hrw : (1 : ℝ) + -(α ^ 2) = 1 - α ^ 2 := by ring
    rw [hrw] at hbern
    push_cast at hbern
    linarith
  have hkey : (1 : ℝ) ≤ (1 + c) * (1 - α ^ 2) ^ (n + 1) := by
    have hmul := mul_le_mul_of_nonneg_left hb' (show (0 : ℝ) ≤ 1 + c by linarith)
    nlinarith
  rw [inv_pow, inv_eq_one_div, div_le_iff₀ (by positivity)]
  linarith

/-! ## The schedule -/

/-- **The phase count.**  `L` is the *logarithm* of the total cooling factor the schedule
must achieve (`σ_m²/σ_0² ≥ e^L`; for Cousins–Vempala `e^L ≈ n·R²`, so `L ≈ log n + 2 log R`),
and `κ` is the algorithm's total relative-variance budget (`κ = varBudget ε`).

`coolPhases n L κ = ⌈8(n+1)L²/κ⌉`.

This is a closed-form abbreviation and asserts nothing; `coolRate_meets_budget` and
`coolSchedule_total_cooling` prove the two properties it is chosen for. -/
noncomputable def coolPhases (n : ℕ) (L κ : ℝ) : ℕ := ⌈8 * ((n : ℝ) + 1) * L ^ 2 / κ⌉₊

/-- **The per-phase cooling rate.**  With `m = coolPhases n L κ`,

  `coolRate n L κ = √(κ / (2·m·(n+1)))`,

i.e. `α ≈ κ/(4(n+1)L)` once `m` is substituted.  The schedule itself is
`geomSchedule σ₀sq (coolRate n L κ)`, i.e. `σᵢ₊₁² = σᵢ²(1 + α)`.

A closed-form abbreviation; the two theorems below prove what it is for. -/
noncomputable def coolRate (n : ℕ) (L κ : ℝ) : ℝ :=
  Real.sqrt (κ / (2 * (coolPhases n L κ : ℝ) * ((n : ℝ) + 1)))

/-- The rate, unfolded. -/
theorem coolRate_def (n : ℕ) (L κ : ℝ) :
    coolRate n L κ = Real.sqrt (κ / (2 * (coolPhases n L κ : ℝ) * ((n : ℝ) + 1))) := rfl

/-- `8(n+1)L²/κ ≤ m`: the defining property of the phase count. -/
theorem le_coolPhases (n : ℕ) (L κ : ℝ) :
    8 * ((n : ℝ) + 1) * L ^ 2 / κ ≤ (coolPhases n L κ : ℝ) :=
  Nat.le_ceil _

/-- The phase count is positive as soon as the cooling requirement is. -/
theorem coolPhases_pos {n : ℕ} {L κ : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ) :
    0 < coolPhases n L κ := by
  refine Nat.ceil_pos.2 ?_
  have hL0 : (0 : ℝ) < L ^ 2 := by nlinarith
  positivity

theorem one_le_coolPhases {n : ℕ} {L κ : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ) :
    (1 : ℝ) ≤ (coolPhases n L κ : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.2 (coolPhases_pos (n := n) hL hκ0).ne'

theorem coolRate_nonneg (n : ℕ) (L κ : ℝ) : 0 ≤ coolRate n L κ := Real.sqrt_nonneg _

/-- The square of the rate, in closed form. -/
theorem coolRate_sq {n : ℕ} {L κ : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ) :
    coolRate n L κ ^ 2 = κ / (2 * (coolPhases n L κ : ℝ) * ((n : ℝ) + 1)) := by
  have hm := one_le_coolPhases (n := n) hL hκ0
  have hd : (0 : ℝ) ≤ 2 * (coolPhases n L κ : ℝ) * ((n : ℝ) + 1) := by positivity
  have harg : (0 : ℝ) ≤ κ / (2 * (coolPhases n L κ : ℝ) * ((n : ℝ) + 1)) :=
    div_nonneg hκ0.le hd
  rw [coolRate]
  exact Real.sq_sqrt harg

/-- `α² ≤ 1/2`, hence in particular `α < 1`: the rate is a legitimate cooling rate. -/
theorem coolRate_sq_le_half {n : ℕ} {L κ : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    coolRate n L κ ^ 2 ≤ 1 / 2 := by
  have hm := one_le_coolPhases (n := n) hL hκ0
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hprod : (1 : ℝ) ≤ (coolPhases n L κ : ℝ) * ((n : ℝ) + 1) := by nlinarith
  have hden : (0 : ℝ) < 2 * (coolPhases n L κ : ℝ) * ((n : ℝ) + 1) := by nlinarith
  rw [coolRate_sq hL hκ0, div_le_div_iff₀ hden (by norm_num)]
  nlinarith

theorem coolRate_lt_one {n : ℕ} {L κ : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    coolRate n L κ < 1 := by
  have h := coolRate_sq_le_half (n := n) hL hκ0 hκ1
  nlinarith [coolRate_nonneg n L κ]

theorem coolRate_le_one {n : ℕ} {L κ : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    coolRate n L κ ≤ 1 := (coolRate_lt_one hL hκ0 hκ1).le

/-! ## Step 1: the schedule meets the per-phase variance budget -/

/-- **The budget-meeting statement: the general-`α` analogue of `fixedRate_meets_budget_iff`.**

At the rate `α = coolRate n L κ` and with `m = coolPhases n L κ` phases, the per-phase factor
`(1-α²)^{-(n+1)}` coming out of `G_mul_G_le_indicator` really is below the algorithm's
per-phase allowance `1 + κ/m`:

  `(1 - (coolRate n L κ)²)^{-(n+1)} ≤ 1 + κ / coolPhases n L κ`.

Hypotheses: `1 ≤ L`, `0 < κ ≤ 1` — all three simultaneously satisfiable, see
`coolSchedule_nonvacuous`.

Unlike the fixed rate `α = 1/n`, this costs nothing in total cooling: see
`coolSchedule_total_cooling`. -/
theorem coolRate_meets_budget {n : ℕ} {L κ : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    ((1 : ℝ) - coolRate n L κ ^ 2)⁻¹ ^ (n + 1) ≤ 1 + κ / (coolPhases n L κ : ℝ) := by
  have hm := one_le_coolPhases (n := n) hL hκ0
  have hm0 : (0 : ℝ) < (coolPhases n L κ : ℝ) := by linarith
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set c : ℝ := κ / (coolPhases n L κ : ℝ) with hcdef
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hc1 : c ≤ 1 := by
    rw [hcdef, div_le_one hm0]; linarith
  refine inv_one_sub_sq_pow_le_one_add (coolRate_nonneg n L κ)
    (coolRate_lt_one hL hκ0 hκ1) hc0 ?_
  -- `(n+1)·α² = κ/(2m) = c/2`, so the requirement is `(c/2)(1+c) ≤ c`, i.e. `c ≤ 1`.
  have hsq : ((n : ℝ) + 1) * coolRate n L κ ^ 2 = c / 2 := by
    rw [coolRate_sq hL hκ0, hcdef]
    field_simp
  calc ((n : ℝ) + 1) * coolRate n L κ ^ 2 * (1 + c) = c / 2 * (1 + c) := by rw [hsq]
    _ ≤ c := by nlinarith

/-! ## Step 2: the schedule actually anneals

This is the positive counterpart of `geomSchedule_total_cooling_lt`: the total cooling
factor `σ_m²/σ_0² = (1+α)^m` reaches `e^L`, for the `L` the schedule was built from — with
no upper bound of the `< 11/10` kind in sight. -/

/-- `α/2 ≤ log(1+α)` for `0 ≤ α ≤ 1`.  From `log x ≤ x − 1` at `x = 1/(1+α)`, which gives
`log(1+α) ≥ α/(1+α)`, and `1 + α ≤ 2`. -/
theorem half_le_log_one_add {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    α / 2 ≤ Real.log (1 + α) := by
  have hp : (0 : ℝ) < 1 + α := by linarith
  have hinv : (0 : ℝ) < 1 / (1 + α) := by positivity
  have h := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_div one_ne_zero hp.ne', Real.log_one] at h
  have h2 : (1 : ℝ) / (1 + α) - 1 = -(α / (1 + α)) := by
    field_simp
    ring
  rw [h2] at h
  have h3 : α / 2 ≤ α / (1 + α) := by
    rw [div_le_div_iff₀ (by norm_num) hp]
    nlinarith
  linarith

/-- **The schedule reaches the required total cooling.**

With `m = coolPhases n L κ` phases at rate `α = coolRate n L κ`, the geometric schedule's
total cooling factor satisfies

  `e^L ≤ (1 + α)^m`.

Contrast `geomSchedule_total_cooling_lt`, which shows that at the *fixed* rate `α = 1/n` a
budget-meeting schedule has `(1+1/n)^m < 11/10`: here the total factor is `e^L`, as large as
required, and `coolRate_meets_budget` says the budget is met at the same time.

The proof is `log(1+α) ≥ α/2` together with `m·α = √(mκ/(2(n+1))) ≥ 2L`, which is exactly
what `m ≥ 8(n+1)L²/κ` buys. -/
theorem coolSchedule_total_cooling {n : ℕ} {L κ : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) :
    Real.exp L ≤ (1 + coolRate n L κ) ^ coolPhases n L κ := by
  have hm1 : (1 : ℝ) ≤ (coolPhases n L κ : ℝ) := one_le_coolPhases hL hκ0
  have hm0 : (0 : ℝ) < (coolPhases n L κ : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hα0 : 0 ≤ coolRate n L κ := coolRate_nonneg n L κ
  have hα1 : coolRate n L κ ≤ 1 := coolRate_le_one hL hκ0 hκ1
  have hp : (0 : ℝ) < 1 + coolRate n L κ := by linarith
  have hden : (0 : ℝ) < 2 * (coolPhases n L κ : ℝ) * ((n : ℝ) + 1) := by nlinarith
  have hmk : 8 * ((n : ℝ) + 1) * L ^ 2 ≤ (coolPhases n L κ : ℝ) * κ :=
    (div_le_iff₀ hκ0).1 (le_coolPhases n L κ)
  have hnn : (0 : ℝ) ≤ 2 * L / (coolPhases n L κ : ℝ) := by
    apply div_nonneg <;> linarith
  have hm2 : (0 : ℝ) < (coolPhases n L κ : ℝ) ^ 2 := pow_pos hm0 2
  have hsq : (2 * L / (coolPhases n L κ : ℝ)) ^ 2
      ≤ κ / (2 * (coolPhases n L κ : ℝ) * ((n : ℝ) + 1)) := by
    rw [div_pow, div_le_div_iff₀ hm2 hden]
    nlinarith [mul_le_mul_of_nonneg_right hmk hm0.le]
  have hrate : 2 * L / (coolPhases n L κ : ℝ) ≤ coolRate n L κ := by
    have h1 := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hnn, ← coolRate_def] at h1
  have hmα : 2 * L ≤ (coolPhases n L κ : ℝ) * coolRate n L κ := by
    rw [div_le_iff₀ hm0] at hrate
    linarith
  have hlog : L ≤ (coolPhases n L κ : ℝ) * Real.log (1 + coolRate n L κ) := by
    have h3 := mul_le_mul_of_nonneg_left (half_le_log_one_add hα0 hα1) hm0.le
    linarith
  calc Real.exp L
      ≤ Real.exp ((coolPhases n L κ : ℝ) * Real.log (1 + coolRate n L κ)) :=
        Real.exp_le_exp.2 hlog
    _ = Real.exp (Real.log (1 + coolRate n L κ)) ^ coolPhases n L κ := Real.exp_nat_mul _ _
    _ = (1 + coolRate n L κ) ^ coolPhases n L κ := by rw [Real.exp_log hp]

/-- **The same in terms of a required cooling *factor* `T`** (rather than its logarithm):
for `T ≥ e`, the schedule built from `L = log T` cools by a factor at least `T`.  For
Cousins–Vempala `T ≈ n·R²`. -/
theorem coolSchedule_total_cooling_factor {n : ℕ} {T κ : ℝ} (hT : Real.exp 1 ≤ T)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    T ≤ (1 + coolRate n (Real.log T) κ) ^ coolPhases n (Real.log T) κ := by
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (Real.exp_pos 1) hT
  have hL : 1 ≤ Real.log T := (Real.le_log_iff_exp_le hT0).2 hT
  have h := coolSchedule_total_cooling (n := n) (L := Real.log T) hL hκ0 hκ1
  rwa [Real.exp_log hT0] at h

/-- **The total cooling, stated on the schedule itself.**  `geomSchedule σ₀sq α` is the
variance schedule `σᵢ² = σ₀²(1+α)ⁱ` of `Chain.lean`, i.e. `σᵢ₊₁² = σᵢ²(1+α)`; at
`α = coolRate n L κ` its final variance is at least `e^L·σ₀²`. -/
theorem geomSchedule_coolRate_total_cooling {n : ℕ} {L κ σ₀sq : ℝ} (hL : 1 ≤ L)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (h0 : 0 < σ₀sq) :
    Real.exp L * σ₀sq
      ≤ geomSchedule σ₀sq (coolRate n L κ) (coolPhases n L κ) := by
  have h := coolSchedule_total_cooling (n := n) hL hκ0 hκ1
  rw [geomSchedule]
  nlinarith

/-- **The phase count is essentially forced.**  *Any* rate `α ≥ 0` and phase count `m > 0`
that both (i) fit the per-phase allowance, `(n+1)α² ≤ κ/m`, and (ii) cool by `e^L` in total,
`e^L ≤ (1+α)^m`, must have `(n+1)L² ≤ m·κ`, i.e. `m ≥ (n+1)L²/κ`.

So `coolPhases n L κ = ⌈8(n+1)L²/κ⌉` is within a factor `8` of optimal for this pair of
constraints, and in particular the `Θ(n L²/κ)` growth quoted in the module docstring is not
an artefact of the construction.  Proof: `(1+α)^m ≤ e^{mα}` gives `L ≤ mα`, and then
`(n+1)L² ≤ m²·((n+1)α²) ≤ m²·κ/m`. -/
theorem phases_ge_of_budget_of_cooling {n m : ℕ} {α L κ : ℝ} (hα0 : 0 ≤ α) (hL0 : 0 ≤ L)
    (hm : 0 < m) (hbudget : ((n : ℝ) + 1) * α ^ 2 ≤ κ / (m : ℝ))
    (hcool : Real.exp L ≤ (1 + α) ^ m) :
    ((n : ℝ) + 1) * L ^ 2 ≤ (m : ℝ) * κ := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h1 : (1 + α) ^ m ≤ Real.exp ((m : ℝ) * α) := by
    calc (1 + α) ^ m ≤ (Real.exp α) ^ m :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp α]) m
      _ = Real.exp ((m : ℝ) * α) := (Real.exp_nat_mul _ _).symm
  have hLm : L ≤ (m : ℝ) * α := Real.exp_le_exp.1 (hcool.trans h1)
  have hsq : L ^ 2 ≤ ((m : ℝ) * α) ^ 2 := by nlinarith
  have hkey : ((m : ℝ)) ^ 2 * (((n : ℝ) + 1) * α ^ 2) ≤ ((m : ℝ)) ^ 2 * (κ / (m : ℝ)) :=
    mul_le_mul_of_nonneg_left hbudget (sq_nonneg _)
  have heq : ((m : ℝ)) ^ 2 * (κ / (m : ℝ)) = (m : ℝ) * κ := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hsq hnn]

/-! ## Step 3: the per-phase second-moment bound at a general rate

`coolLaw_sq_moment_le` (`PhaseVar.lean`) is the exact-law second-moment bound at the *fixed*
rate `α = 1/n`, with constant `1 + 2/n`.  This is the same statement at an arbitrary rate
`0 ≤ α < 1`, with the constant `(1-α²)^{-(n+1)}` that `G_mul_G_le_indicator` supplies.  The
proof is `coolLaw_sq_moment_le`'s, with `fixed_var_bound_indicator` replaced by
`G_mul_G_le_indicator`; as there, **no `ZLogconcaveHypothesis` is assumed** — it is
discharged for the indicator of a convex body. -/

/-- **The exact-law per-phase second-moment bound at cooling rate `α`.**

For `K` convex and measurable with `ball 0 1 ⊆ K` and finite volume, at an interior phase
(`i + 1 < m`) of a schedule with `σᵢ₊₁² = σᵢ²(1 + α)` and `0 ≤ α < 1`,

  `E_π(W²) ≤ (1-α²)^{-(n+1)} · E_π(W)²`,

with `π = coolLaw m σsq K i` the exact phase law and `W = phaseScore m σsq K i`. -/
theorem coolLaw_sq_moment_le_rate {n m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤) {i : ℕ} (hi : i + 1 < m)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hrate : σsq (i + 1) = σsq i * (1 + α)) :
    ∫ x, phaseScore m σsq K i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)
        * (∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i)) ^ 2 := by
  have hαp : (0 : ℝ) < 1 + α := by linarith
  have hαm : (0 : ℝ) < 1 - α := by linarith
  have ha0 := hσ i
  have hb0 := hσ (i + 1)
  have hab : 2 * σsq i - σsq (i + 1) ≠ 0 := by rw [hrate]; nlinarith
  set a : ℝ := σsq i with hadef
  set b : ℝ := σsq (i + 1) with hbdef
  set c : ℝ := a * b / (2 * a - b) with hcdef
  set F : EuclSpace n → ℝ := Set.indicator K (1 : EuclSpace n → ℝ) with hFdef
  have hchain := chain_pos (m := m) hσ hball hfin i
  have hGa : G F a = chain m σsq K i := (chain_eq_G (Nat.lt_of_succ_lt hi) hKm).symm
  have hGb : G F b = chain m σsq K (i + 1) := (chain_eq_G hi hKm).symm
  have hσb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have hcore := G_mul_G_le_indicator (K := K) hK hKm (σ := Real.sqrt b)
    (Real.sqrt_pos.2 hb0) hα0 hα1
  rw [hσb] at hcore
  have h2ab : 2 * a - b = a * (1 - α) := by rw [hrate]; ring
  have hba : b / (1 + α) = a := by
    rw [hrate, mul_div_assoc, div_self hαp.ne', mul_one]
  have hbc : b / (1 - α) = c := by
    rw [hcdef, h2ab, div_eq_div_iff hαm.ne' (mul_pos ha0 hαm).ne']
    ring
  rw [hbc, hba, ← hFdef] at hcore
  have hGApos : (0 : ℝ) < G F a := by rw [hGa]; exact hchain
  rw [integral_phaseScore_sq_coolLaw hKm hchain hi ha0.ne' hb0.ne' hab,
    integral_phaseScore_coolLaw hKm hchain, ← hcdef, ← hFdef, ← hGa, ← hGb]
  rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ hGApos (pow_pos hGApos 2)]
  nlinarith [mul_le_mul_of_nonneg_right hcore hGApos.le]

/-- **The per-phase bound in the algorithm's own shape, `1 + κ/m`.**  This is the statement
`PhaseVar.lean` could not reach at the fixed rate: `coolLaw_sq_moment_le` has constant
`1 + 2/n`, and `fixedRate_meets_budget_iff` + `geomSchedule_total_cooling_lt` show that
reconciling `1 + 2/n` with `1 + κ/m` costs all the cooling.  At the rate `coolRate n L κ`
the constant is `1 + κ/m` outright, with `m = coolPhases n L κ` the schedule's own phase
count, and `coolSchedule_total_cooling` says the schedule still cools by `e^L`. -/
theorem coolLaw_sq_moment_le_budget {n : ℕ} {L κ : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ)
    (hκ1 : κ ≤ 1) {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤) {i : ℕ}
    (hi : i + 1 < coolPhases n L κ)
    (hrate : σsq (i + 1) = σsq i * (1 + coolRate n L κ)) :
    ∫ x, phaseScore (coolPhases n L κ) σsq K i x ^ 2
        ∂(coolLaw (coolPhases n L κ) σsq K i)
      ≤ (1 + κ / (coolPhases n L κ : ℝ))
        * (∫ x, phaseScore (coolPhases n L κ) σsq K i x
            ∂(coolLaw (coolPhases n L κ) σsq K i)) ^ 2 :=
  (coolLaw_sq_moment_le_rate hσ hK hKm hball hfin hi (coolRate_nonneg n L κ)
      (coolRate_lt_one hL hκ0 hκ1) hrate).trans
    (mul_le_mul_of_nonneg_right (coolRate_meets_budget hL hκ0 hκ1) (sq_nonneg _))

/-! ## Step 4: the sampled phase, in `hphase_var`'s shape

`sampled_phase_sq_moment_le_budget` (`PhaseVar.lean`) reaches the constant `1 + κ/m` only by
assuming `2m ≤ nκ`, which `geomSchedule_total_cooling_lt` shows is incompatible with
annealing.  This is the same conclusion with that hypothesis **deleted**: the budget is met
by construction (`coolRate_meets_budget`) rather than assumed. -/

/-- **`hphase_var` for a TV-approximate sample, at the annealing schedule.**

Identical to `sampled_phase_sq_moment_le_budget` except that the rate is `coolRate n L κ`
instead of `1/n`, the phase count is `coolPhases n L κ`, and there is **no `2m ≤ nκ`
hypothesis** — the exact-law constant is already `1 + κ/m`
(`coolLaw_sq_moment_le_budget`).

The remaining hypotheses are the ones `PhaseVar.lean` documents: the body (`hK`, `hKm`,
`hball`, `hfin`), the radius `hKR` that makes the score bounded, the sampler's TV guarantee
`hTV`, and the slack `s` with its smallness condition `hslack`.  All of them are
simultaneously satisfiable — see `sampled_phase_sq_moment_le_coolRate_witness`. -/
theorem sampled_phase_sq_moment_le_coolRate {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n : ℕ} {L κ : ℝ}
    (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R)
    {i : ℕ} (hi : i + 1 < coolPhases n L κ)
    (hrate : σsq (i + 1) = σsq i * (1 + coolRate n L κ))
    {X : Ω → EuclSpace n} (hX : Measurable X) {ε : ℝ≥0∞}
    (hTV : TVLe (μ.map X) (coolLaw (coolPhases n L κ) σsq K i) ε) (hεtop : ε ≠ ⊤)
    {s : ℝ} (hs : 0 ≤ s)
    (hslack : ε.toReal * (Real.exp (R ^ 2 / (2 * σsq i)) ^ 2
          * (1 + 2 * (1 + κ / (coolPhases n L κ : ℝ) + s)))
        ≤ s * (chain (coolPhases n L κ) σsq K (i + 1)
            / chain (coolPhases n L κ) σsq K i) ^ 2) :
    ∫ ω, phaseScore (coolPhases n L κ) σsq K i (X ω) ^ 2 ∂μ
      ≤ (1 + κ / (coolPhases n L κ : ℝ) + s)
        * (∫ ω, phaseScore (coolPhases n L κ) σsq K i (X ω) ∂μ) ^ 2 := by
  haveI := coolLaw_isProbabilityMeasure (m := coolPhases n L κ) hσ hball hfin i
  have hchain := chain_pos (m := coolPhases n L κ) hσ hball hfin i
  have hm0 : (0 : ℝ) < (coolPhases n L κ : ℝ) := by
    have := one_le_coolPhases (n := n) hL hκ0; linarith
  have hC : (0 : ℝ) ≤ 1 + κ / (coolPhases n L κ : ℝ) := by positivity
  have hmean := integral_phaseScore_coolLaw (m := coolPhases n L κ) (σsq := σsq) hKm hchain
  rw [← hmean] at hslack
  exact sq_moment_le_of_tvLe_map hX hTV hεtop (Real.exp_pos _)
    (measurable_phaseScore hKm i) (phaseScore_nonneg _ σsq K i)
    (phaseScore_le hσ hKR i) hC hs
    (coolLaw_sq_moment_le_budget hL hκ0 hκ1 hσ hK hKm hball hfin hi hrate) hslack

/-! ## Non-vacuity

`CLAUDE.md` §11: a green, axiom-clean theorem whose hypotheses cannot all hold at once
certifies nothing.  Everything above is guarded by `1 ≤ L`, `0 < κ` and `κ ≤ 1`; this
section shows those are satisfied at the parameters the algorithm actually uses, and
exhibits a concrete instance of the sampled-phase capstone. -/

/-- **The algorithm's own budget satisfies `κ ≤ 1`.**  `varBudget ε = log(1 + ε²/5) ≤ ε²/5`,
so `varBudget ε ≤ 1/5` for `0 ≤ ε ≤ 1`.  Together with `varBudget_pos` this discharges
`0 < κ ≤ 1` at every target accuracy the algorithm is run at. -/
theorem varBudget_le_one {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : varBudget ε ≤ 1 := by
  have hx : (0 : ℝ) < 1 + ε ^ 2 / 5 := by positivity
  have h := Real.log_le_sub_one_of_pos hx
  rw [varBudget]
  nlinarith

/-- The schedule always has at least `8` phases, since `m ≥ 8(n+1)L²/κ ≥ 8`. -/
theorem eight_le_coolPhases {n : ℕ} {L κ : ℝ} (hL : 1 ≤ L) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    8 ≤ coolPhases n L κ := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n; linarith
  have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  have hprod : (1 : ℝ) ≤ ((n : ℝ) + 1) * L ^ 2 := by nlinarith
  have hge : (8 : ℝ) ≤ 8 * ((n : ℝ) + 1) * L ^ 2 / κ := by
    rw [le_div_iff₀ hκ0]; nlinarith
  have h8 : (8 : ℝ) ≤ (coolPhases n L κ : ℝ) := hge.trans (le_coolPhases n L κ)
  exact_mod_cast h8

/-- **Non-vacuity of the schedule's hypotheses.**  `1 ≤ L`, `0 < κ`, `κ ≤ 1` hold together
at parameters the algorithm actually uses — `κ = varBudget ε` for any target accuracy
`0 < ε ≤ 1`, and `L = 1` (a required total cooling factor of `e`) — and at those parameters
*both* headline conclusions hold simultaneously: the per-phase factor is inside the budget
**and** the schedule cools by the required factor.  Larger `L` is equally admissible; `L = 1`
is chosen only to make the witness closed-form. -/
theorem coolSchedule_nonvacuous (n : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < varBudget ε ∧ varBudget ε ≤ 1 ∧
      ((1 : ℝ) - coolRate n 1 (varBudget ε) ^ 2)⁻¹ ^ (n + 1)
        ≤ 1 + varBudget ε / (coolPhases n 1 (varBudget ε) : ℝ) ∧
      Real.exp 1 ≤ (1 + coolRate n 1 (varBudget ε)) ^ coolPhases n 1 (varBudget ε) :=
  ⟨varBudget_pos hε0, varBudget_le_one hε0.le hε1,
    coolRate_meets_budget le_rfl (varBudget_pos hε0) (varBudget_le_one hε0.le hε1),
    coolSchedule_total_cooling le_rfl (varBudget_pos hε0) (varBudget_le_one hε0.le hε1)⟩

/-- **Non-vacuity of the sampled-phase capstone.**  Every hypothesis of
`sampled_phase_sq_moment_le_coolRate` is satisfiable at once: `K` the closed unit ball
(convex, measurable, contains `ball 0 1`, finite volume, radius `R = 1`), the schedule
`geomSchedule 1 (coolRate n L κ)` (which satisfies `hrate` by `geomSchedule_succ`), phase
`i = 0` (legitimate because the schedule has at least `8` phases), and an *exact* sample —
`X = id` against the phase law itself, so `ε = 0` and the slack `s = 0` makes the smallness
condition `0 ≤ 0`. -/
theorem sampled_phase_sq_moment_le_coolRate_witness {n : ℕ} {L κ : ℝ} (hL : 1 ≤ L)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    ∫ ω, phaseScore (coolPhases n L κ) (geomSchedule 1 (coolRate n L κ))
          (closedBall (0 : EuclSpace n) 1) 0 (id ω) ^ 2
        ∂(coolLaw (coolPhases n L κ) (geomSchedule 1 (coolRate n L κ))
          (closedBall (0 : EuclSpace n) 1) 0)
      ≤ (1 + κ / (coolPhases n L κ : ℝ) + 0)
        * (∫ ω, phaseScore (coolPhases n L κ) (geomSchedule 1 (coolRate n L κ))
              (closedBall (0 : EuclSpace n) 1) 0 (id ω)
            ∂(coolLaw (coolPhases n L κ) (geomSchedule 1 (coolRate n L κ))
              (closedBall (0 : EuclSpace n) 1) 0)) ^ 2 := by
  have hα := coolRate_nonneg n L κ
  have hσ : ∀ j, 0 < geomSchedule 1 (coolRate n L κ) j := fun j =>
    geomSchedule_pos one_pos (by linarith) j
  have hK : Convex ℝ (closedBall (0 : EuclSpace n) 1) := convex_closedBall 0 1
  have hKm : MeasurableSet (closedBall (0 : EuclSpace n) 1) :=
    Metric.isClosed_closedBall.measurableSet
  have hball : ball (0 : EuclSpace n) 1 ⊆ closedBall (0 : EuclSpace n) 1 :=
    ball_subset_closedBall
  have hfin : volume (closedBall (0 : EuclSpace n) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hi : 0 + 1 < coolPhases n L κ := by
    have := eight_le_coolPhases (n := n) hL hκ0 hκ1; omega
  haveI := coolLaw_isProbabilityMeasure (m := coolPhases n L κ) hσ hball hfin 0
  refine sampled_phase_sq_moment_le_coolRate (R := 1) (X := id) (ε := 0) (s := 0)
    hL hκ0 hκ1 hσ hK hKm hball hfin Subset.rfl hi
    (geomSchedule_succ 1 (coolRate n L κ) 0) measurable_id ?_ (by simp) le_rfl (by simp)
  rw [Measure.map_id]
  exact TVLe.refl _

/-! ### Axiom audit

Every result above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms inv_one_sub_sq_pow_le_one_add
#print axioms coolPhases
#print axioms coolRate
#print axioms coolRate_def
#print axioms le_coolPhases
#print axioms coolPhases_pos
#print axioms one_le_coolPhases
#print axioms coolRate_nonneg
#print axioms coolRate_sq
#print axioms coolRate_sq_le_half
#print axioms coolRate_lt_one
#print axioms coolRate_le_one
#print axioms coolRate_meets_budget
#print axioms half_le_log_one_add
#print axioms coolSchedule_total_cooling
#print axioms coolSchedule_total_cooling_factor
#print axioms geomSchedule_coolRate_total_cooling
#print axioms phases_ge_of_budget_of_cooling
#print axioms coolLaw_sq_moment_le_rate
#print axioms coolLaw_sq_moment_le_budget
#print axioms sampled_phase_sq_moment_le_coolRate
#print axioms varBudget_le_one
#print axioms eight_le_coolPhases
#print axioms coolSchedule_nonvacuous
#print axioms sampled_phase_sq_moment_le_coolRate_witness

end Arlib.GaussianCooling
