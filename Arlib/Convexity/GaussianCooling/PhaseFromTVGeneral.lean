/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.TerminalMoment
import Arlib.Convexity.GaussianCooling.GeneralRate

/-!
# `hphase_var` at a **general** cooling rate: the fixed-rate contradiction removed

## The problem this file fixes

`Arlib/Convexity/GaussianCooling/TerminalMoment.lean`'s `hphase_var_of_tvLe_of_flat` proves
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`'s `hphase_var` binder from one
total-variation hypothesis, but it carries two binders that are **jointly contradictory in
the annealing regime**:

* `hrate` — the *fixed* cooling rate `σ²ᵢ₊₁ = σ²ᵢ·(1 + 1/n)`;
* `hbudget` — `2·m ≤ n·varBudget (ε/2)`.

`PhaseVar.lean:620`'s `geomSchedule_total_cooling_lt` proves that a fixed-rate schedule
meeting that budget cools by a total factor **`< 11/10`**.  A Gaussian-cooling schedule has
to raise `σ²` from `≈ 1/n` to `≈ R²`, a factor of order `nR²`, so the pair is satisfiable
only by schedules that **do not anneal**: everything downstream — including
`Ttc/Volume/CVAmended.lean`'s `cousinsVempalaOfRunsApproxMeanAmended` — was instantiable
only in that degenerate regime.

`Arlib/Convexity/GaussianCooling/GeneralRate.lean` diagnoses the obstruction as an artefact
of `α = 1/n` being far too large and removes it: at a general rate the per-phase constant is
`(1 − α²)^{−(n+1)}` rather than `1 + 2/n`, and `exists_admissible_volume` exhibits an
explicit `(α, m)` meeting the budget **and** cooling by `nR²` simultaneously.

## What is produced here

`hphase_var_of_tvLe_of_flat_general` (§4) — `hphase_var_of_tvLe_of_flat`'s conclusion
**character for character**, with

* `hrate` at a caller-supplied rate: `σ²ᵢ₊₁ = σ²ᵢ·(1 + α K ε p)`, with `0 ≤ α < 1`;
* `hbudget` the general-rate admissibility condition of `GeneralRate.lean`,
  `(1 − α²)^{−(n+1)} ≤ 1 + varBudget (ε/2)/m` — the exact hypothesis
  `generalRate_budget_sufficient` establishes and `generalCoolRate_meets_budget` discharges
  for the explicit choice;
* `hflat` at the general-rate constant, `R² ≤ 2σᵢ²·log((1 − α²)^{−(n+1)})`;
* `hslack` with its one coefficient moved from `κ/m − 2/n` to `1 + κ/m − (1 − α²)^{−(n+1)}`
  (the slack between the per-phase constant and the algorithm's budget).

**And §5 demonstrates that the new pair is satisfiable at an annealing schedule**:
`general_rate_annealing_witness` exhibits, from `exists_admissible_volume`, a rate `α > 0`,
a phase count `m > 0` and a positive geometric schedule satisfying `hrate`, `hbudget` and
`hflat` *simultaneously* while cooling by `σ²ₘ/σ²₀ ≥ nR²`.  That is the whole point: the
same three facts are unsatisfiable together at the fixed rate.

## How the port is made (`CLAUDE.md` §3, §6)

`TerminalMoment.lean` proves its result by *applying* `PhaseFromTV.lean`'s
`hphase_var_of_tvLe` with `hterm` supplied.  That is not available here, because
`hphase_var_of_tvLe` hard-codes the fixed rate three separate ways (its `hrate` binder, its
`hbudget` binder, and internally `coolLaw_interior_sq_moment_le` +
`fixedRate_meets_budget_iff`).  The port is therefore made one layer lower, at
`PhaseFromTV.lean:198`'s workhorse `phaseScore_interior_sq_moment_le_of_tvLe`, which is
already general in the exact-law constant `C` and the slack `s`; **the TV transport is not
re-proved**, only fed a different exact-law input:

* interior phases (`i + 1 < m`) — §1's `coolLaw_sq_moment_le_general`, which is
  `PhaseVar.lean:513`'s `coolLaw_sq_moment_le` with `fixed_var_bound_indicator` replaced by
  `IndicatorVariance.lean:200`'s `G_mul_G_le_indicator`.  This is the only genuinely new
  mathematics in the file and it is a mechanical substitution: at `σᵢ₊₁² = σᵢ²(1+α)` the
  three variance parameters satisfy `σᵢ² = σᵢ₊₁²/(1+α)` and
  `σᵢ²σᵢ₊₁²/(2σᵢ² − σᵢ₊₁²) = σᵢ₊₁²/(1−α)`, exactly the two arguments `G_mul_G_le_indicator`
  bounds;
* terminal phases (`i + 1 = m`) — `TerminalMoment.lean:193`'s
  `coolLaw_interior_sq_moment_le_terminal`, which is **rate-free** (its constant is
  `e^{R²/(2σᵢ²)}`), plus `hflat` to bring `e^{R²/(2σᵢ²)}` under `(1 − α²)^{−(n+1)}`.

## The terminal binder `hflat` survives the port, and must

`TerminalMoment.lean`'s `hterm_not_dischargeable` shows the terminal second-moment bound at
the uniform constant `1 + 2/n` is **false** for some variance, at `K = B₁`, on a schedule
satisfying `hrate` — and its proof (`terminal_sq_moment_unbounded`) refutes *every* constant,
so no change of rate rescues it.  `hflat` is therefore kept, restated at the general-rate
constant.  Two honest consequences:

* at `α = 0` the constant is `1` and `hflat` reads `R² ≤ 0`, which contradicts
  `ball 0 1 ⊆ K ⊆ closedBall 0 R`.  The terminal phase is usable only at `α > 0` — which
  the §5 witness has;
* `hflat` is a *lower* bound on the terminal variance (`σᵢ² ≳ R²/(2(n+1)α²)`), so meeting it
  together with the annealing requirement, which constrains only the *ratio* `σ²ₘ/σ²₀`,
  forces a large `σ²₀`.  §5 says exactly which one, and says so plainly rather than
  pretending the paper's `σ²₀ ≈ 1/n` start is covered.

## `n ≥ 3` is a fixed-rate artefact

`hphase_var_of_tvLe_of_flat` needs `hn : 3 ≤ n` because `fixed_var_bound_indicator` does.
`G_mul_G_le_indicator` has no dimension condition, so `hn` is **not used** on this route.
The binder is kept (as `_hn`) so that the theorem stays a drop-in replacement of the same
arity; that it is dischargeable-but-unused is a finding, not an oversight.

## What is reused verbatim (nothing below re-proves it)

* `Arlib.GaussianCooling.G_mul_G_le_indicator` — `IndicatorVariance.lean:200`.
* `Arlib.GaussianCooling.phaseScore_interior_sq_moment_le_of_tvLe` — `PhaseFromTV.lean:198`.
* `Arlib.GaussianCooling.coolLaw_interior`, `chain_interior`, `ball_subset_interior`,
  `volume_interior_ne_top` — `PhaseFromTV.lean:133-155`, the interior bridge (the score is
  `interior K` because `MeasurableSet K` is **not** available from the binders; see that
  file's own finding, which is inherited unchanged).
* `Arlib.GaussianCooling.coolLaw_interior_sq_moment_le_terminal` — `TerminalMoment.lean:193`.
* `Arlib.GaussianCooling.integral_phaseScore_sq_coolLaw`, `integral_phaseScore_coolLaw`,
  `chain_eq_G`, `chain_pos` — the exact-law computations.
* `Arlib.GaussianCooling.exists_admissible_volume`, `generalCoolRate`, `generalPhaseCount`,
  `varBudget_pos_le_one` — `GeneralRate.lean`.

## Hypotheses still carried unproved by `hphase_var_of_tvLe_of_flat_general`

* `hTV` — the sampler's guarantee.  Conductance/mixing; not touched here.
* `hKR` — a radius `K ⊆ closedBall 0 (R K ε p)`.  `cousinsVempala` exposes none.
* `hσ`, `hX`, `htop`, `hslack` — positivity of the schedule, measurability of the sample,
  finiteness and smallness of the TV error.
* `hα0`, `hα1` — `0 ≤ α K ε p < 1`.  **Not** implied by `hbudget`: at `α = 1` the constant
  `(1 − α²)⁻¹^(n+1)` is `0^(n+1) = 0` and `hbudget` holds vacuously.
* `hrate` — the general cooling rate.  Together with `hbudget` and `hflat` this is what §5
  shows satisfiable at an annealing schedule.
* `hbudget` — the general-rate admissibility condition.  **This is the binder the file
  exists to change**; `geomSchedule_total_cooling_lt`'s obstruction does not apply to it.
* `hflat` — the terminal flatness condition, at the general-rate constant.

## Scope

Nothing here produces a TV bound, a conductance bound, a phase count for the *sampler*, or a
running time.  Nothing under `Ttc/` is edited, and no file other than this one is touched.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open scoped ENNReal

variable {n : ℕ}

/-! ## 1.  The exact-law interior bound at a general rate

`PhaseVar.lean:513`'s `coolLaw_sq_moment_le` with the fixed-rate transport step replaced by
the general-`α` one.  The three variance parameters of the second-moment computation are
`a = σᵢ²`, `b = σᵢ₊₁²` and the harmonic partner `c = ab/(2a − b)`; under
`b = a(1 + α)` they are exactly `b/(1+α)`, `b` and `b/(1−α)`, which is the triple
`G_mul_G_le_indicator` bounds. -/

/-- **The exact-sample second-moment bound at a general cooling rate.**  For `K` convex and
measurable with `ball 0 1 ⊆ K` and finite volume, at an interior phase (`i + 1 < m`) of a
schedule with `σᵢ₊₁² = σᵢ²(1 + α)`, `0 ≤ α < 1`:

    `E_π(W²) ≤ (1 − α²)^{−(n+1)} · E_π(W)²`,

with `π = coolLaw m σsq K i` and `W = phaseScore m σsq K i`.  **No assumed input** and **no
`n ≥ 3`**: the `ZLogconcaveHypothesis` of `G_mul_G_le_of_zLogconcave` is discharged for the
indicator of a convex set by `zLogconcaveHypothesis_indicator`, and the general-`α` transport
step carries no dimension condition.  At `α = 1/n` and `n ≥ 3` this is weaker than
`coolLaw_sq_moment_le` (`(1 − 1/n²)^{−(n+1)}` versus `1 + 2/n`); the point is that it holds
for *every* `α < 1`, in particular for the small ones that can actually anneal. -/
theorem coolLaw_sq_moment_le_general {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
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
  have hchain1 := chain_pos (m := m) hσ hball hfin (i + 1)
  have hGa : G F a = chain m σsq K i := (chain_eq_G (Nat.lt_of_succ_lt hi) hKm).symm
  have hGb : G F b = chain m σsq K (i + 1) := (chain_eq_G hi hKm).symm
  have hσb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0.le
  have hcore := G_mul_G_le_indicator (K := K) hK hKm (σ := Real.sqrt b)
    (Real.sqrt_pos.2 hb0) hα0 hα1
  rw [hσb] at hcore
  have h2ab : 2 * a - b = a * (1 - α) := by rw [hrate]; ring
  have hba : b / (1 + α) = a := by rw [hrate, mul_div_assoc, div_self hαp.ne', mul_one]
  have hbc : b / (1 - α) = c := by
    rw [hcdef, h2ab, div_eq_div_iff hαm.ne' (mul_pos ha0 hαm).ne']
    ring
  rw [hba, hbc, ← hFdef] at hcore
  have hGApos : (0 : ℝ) < G F a := by rw [hGa]; exact hchain
  rw [integral_phaseScore_sq_coolLaw hKm hchain hi ha0.ne' hb0.ne' hab,
    integral_phaseScore_coolLaw hKm hchain, ← hcdef, ← hFdef, ← hGa, ← hGb]
  rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ hGApos (pow_pos hGApos 2)]
  nlinarith [mul_le_mul_of_nonneg_right hcore hGApos.le]

/-! ## 2.  The two exact-law inputs across the interior bridge

`MeasurableSet K` is not available from the algorithm's binders (`PhaseFromTV.lean`'s
finding), so the score is `interior K` while the law and the chain ratios stay at `K`.  Both
halves are moved across `coolLaw_interior` exactly as `coolLaw_interior_sq_moment_le` moves
the fixed-rate bound. -/

section Interior

variable {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}

/-- **The interior-phase exact-law input at a general rate**, for the interior score under
the law at `K`.  §1 across `PhaseFromTV.lean`'s bridge. -/
theorem coolLaw_interior_sq_moment_le_general (hσ : ∀ j, 0 < σsq j) (hK : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤) (hi : i + 1 < m)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hrate : σsq (i + 1) = σsq i * (1 + α)) :
    ∫ x, phaseScore m σsq (interior K) i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)
        * (∫ x, phaseScore m σsq (interior K) i x ∂(coolLaw m σsq K i)) ^ 2 := by
  rw [← coolLaw_interior hK i]
  exact coolLaw_sq_moment_le_general hσ hK.interior isOpen_interior.measurableSet
    (ball_subset_interior hball) (volume_interior_ne_top hfin) hi hα0 hα1 hrate

/-- **The terminal-phase exact-law input at the general-rate constant.**

`TerminalMoment.lean`'s `coolLaw_interior_sq_moment_le_terminal` is rate-free: its constant
is `e^{R²/(2σᵢ²)}`, the oscillation of the terminal Gaussian over the body.  `hflat`,

    `R² ≤ 2σᵢ²·log((1 − α²)^{−(n+1)})`,   i.e.   `e^{R²/(2σᵢ²)} ≤ (1 − α²)^{−(n+1)}`,

is exactly what brings it under the interior phases' own allowance.  It cannot be dropped:
`TerminalMoment.lean`'s `terminal_sq_moment_unbounded` refutes *every* constant at some
variance.  Note it forces `α > 0` whenever `R > 0`. -/
theorem coolLaw_interior_sq_moment_le_terminal_flat_general (hσ : ∀ j, 0 < σsq j)
    (hK : Convex ℝ K) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R) (hterm : m ≤ i + 1)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hflat : R ^ 2 ≤ 2 * σsq i * Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1))) :
    ∫ x, phaseScore m σsq (interior K) i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)
        * (∫ x, phaseScore m σsq (interior K) i x ∂(coolLaw m σsq K i)) ^ 2 := by
  have hone : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hCpos : (0 : ℝ) < ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) := by positivity
  have hσi := hσ i
  have harg : R ^ 2 / (2 * σsq i) ≤ Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * σsq i)]
    linarith
  have hexp : Real.exp (R ^ 2 / (2 * σsq i)) ≤ ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) := by
    calc Real.exp (R ^ 2 / (2 * σsq i))
        ≤ Real.exp (Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1))) := Real.exp_le_exp.2 harg
      _ = ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) := Real.exp_log hCpos
  refine (coolLaw_interior_sq_moment_le_terminal hσ hK hball hfin hKR hterm).trans ?_
  exact mul_le_mul_of_nonneg_right hexp (sq_nonneg _)

/-- **Every phase at once, at the general rate.**  Interior phases are §1 (radius-free);
terminal phases are the flat bound.  Both land on the same constant `(1 − α²)^{−(n+1)}`. -/
theorem coolLaw_interior_sq_moment_le_all_general (hσ : ∀ j, 0 < σsq j) (hK : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + α))
    (hflat : ∀ j, m ≤ j + 1 →
      R ^ 2 ≤ 2 * σsq j * Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1))) (i : ℕ) :
    ∫ x, phaseScore m σsq (interior K) i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)
        * (∫ x, phaseScore m σsq (interior K) i x ∂(coolLaw m σsq K i)) ^ 2 := by
  rcases lt_or_ge (i + 1) m with h | h
  · exact coolLaw_interior_sq_moment_le_general hσ hK hball hfin h hα0 hα1 (hrate i)
  · exact coolLaw_interior_sq_moment_le_terminal_flat_general hσ hK hball hfin hKR h hα0 hα1
      (hflat i h)

end Interior

/-! ## 3.  The per-phase transported bound, at the algorithm's constant

`PhaseFromTV.lean:198`'s workhorse `phaseScore_interior_sq_moment_le_of_tvLe` is already
general in the exact-law constant `C` and the slack `s`; nothing about the TV transport is
re-proved.  Here `C = (1 − α²)^{−(n+1)}` and `s = 1 + κ/m − C`, so that `C + s = 1 + κ/m` and
`hs : 0 ≤ s` **is** the general-rate admissibility condition — no `iff` conversion, and no
`0 < m` needed (contrast `phaseScore_interior_sq_moment_le_budget`, which routes through
`fixedRate_meets_budget_iff`). -/

section PerPhase

/-- **The second-moment consequence at the constant the algorithm writes**, `1 + κ/m`, from
the general-rate exact-law input.  `PhaseFromTV.lean`'s
`phaseScore_interior_sq_moment_le_budget` with `1 + 2/n` replaced by `(1 − α²)^{−(n+1)}` and
`fixedRate_meets_budget_iff` replaced by the hypothesis `hbudget` that
`GeneralRate.lean`'s `generalRate_budget_sufficient` establishes. -/
theorem phaseScore_interior_sq_moment_le_budget_general
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} {K : Set (EuclSpace n)} {X : Ω → EuclSpace n} {e : ℝ≥0∞}
    (hσ : ∀ j, 0 < σsq j) (hK : Convex ℝ K) (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    (hfin : volume K ≠ ⊤) {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R)
    (hX : Measurable X) (hTV : TVLe (μ.map X) (coolLaw m σsq K i) e) (he : e ≠ ⊤)
    {α κ : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hbudget : ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) ≤ 1 + κ / (m : ℝ))
    (hexact : ∫ x, phaseScore m σsq (interior K) i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)
        * (∫ x, phaseScore m σsq (interior K) i x ∂(coolLaw m σsq K i)) ^ 2)
    (hslack : e.toReal * (Real.exp (R ^ 2 / (2 * σsq i)) ^ 2 * (1 + 2 * (1 + κ / (m : ℝ))))
      ≤ (1 + κ / (m : ℝ) - ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1))
          * (chain m σsq K (i + 1) / chain m σsq K i) ^ 2) :
    ∫ ω, phaseScore m σsq (interior K) i (X ω) ^ 2 ∂μ
      ≤ (1 + κ / (m : ℝ)) * (∫ ω, phaseScore m σsq (interior K) i (X ω) ∂μ) ^ 2 := by
  have hone : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hC : (0 : ℝ) ≤ ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) := by positivity
  have hs : (0 : ℝ) ≤ 1 + κ / (m : ℝ) - ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) := by linarith
  have heq : ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)
      + (1 + κ / (m : ℝ) - ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)) = 1 + κ / (m : ℝ) := by ring
  have hmain := phaseScore_interior_sq_moment_le_of_tvLe hσ hK hball hfin hKR hX hTV he
    hC hs hexact (by rw [heq]; exact hslack)
  rwa [heq] at hmain

end PerPhase

/-! ## 4.  `hphase_var`, at a general rate -/

section Family

/-- **`cousinsVempalaOfRunsApproxMean`'s `hphase_var`, at a general cooling rate.**

The conclusion is `TerminalMoment.lean`'s `hphase_var_of_tvLe_of_flat` character for
character.  What changed:

* `hrate` reads `σᵢ₊₁² = σᵢ²·(1 + α K ε p)` for a caller-supplied rate function `α`
  (it must depend on `K, ε, p` exactly as `R` does: the admissible rate of
  `exists_admissible_volume` is `varBudget (ε/2)/(16(n+1)·log(nR²))`);
* `hbudget` reads `(1 − α²)^{−(n+1)} ≤ 1 + varBudget (ε/2)/m`, the general-rate
  admissibility condition of `GeneralRate.lean` — **not** `2m ≤ n·varBudget (ε/2)`, which
  `geomSchedule_total_cooling_lt` shows is incompatible with annealing;
* `hflat` and `hslack` are restated at the general-rate constant;
* `hα0`, `hα1` are new: `0 ≤ α < 1`.  They are *not* implied by `hbudget` (at `α = 1` the
  constant is `0` and `hbudget` is vacuous), and the interior bound genuinely needs them.

`_hn : 3 ≤ n` is kept for arity but is **unused**: the general-`α` transport step has no
dimension condition.

§5 shows `hrate`, `hbudget` and `hflat` are jointly satisfiable at a schedule that cools by
`nR²` — which is precisely what the fixed-rate pair could not do. -/
theorem hphase_var_of_tvLe_of_flat_general (E : Type) [MeasurableSpace E] (_hn : 3 ≤ n)
    (phases : Set (EuclSpace n) → ℝ → ℝ → ℕ)
    (σsq : Set (EuclSpace n) → ℝ → ℝ → ℕ → ℝ)
    (ν : ℕ → ℕ → Measure E) [∀ j i, IsProbabilityMeasure (ν j i)]
    (X : Set (EuclSpace n) → ℝ → ℝ → ℕ → ℕ → E → EuclSpace n)
    (R : Set (EuclSpace n) → ℝ → ℝ → ℝ)
    (α : Set (EuclSpace n) → ℝ → ℝ → ℝ)
    (tvErr : Set (EuclSpace n) → ℝ → ℝ → ℕ → ℕ → ℝ≥0∞)
    (hσ : ∀ K ε p j, 0 < σsq K ε p j)
    (hX : ∀ K ε p j i, Measurable (X K ε p j i))
    (hα0 : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 ≤ α K ε p)
    (hα1 : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), α K ε p < 1)
    (hKR : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)),
      K ⊆ Metric.closedBall (0 : EuclSpace n) (R K ε p))
    (htop : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      tvErr K ε p j (i : ℕ) ≠ ⊤)
    (hTV : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      TVLe ((ν j (i : ℕ)).map (X K ε p j (i : ℕ)))
        (coolLaw (phases K ε p) (σsq K ε p) K (i : ℕ)) (tvErr K ε p j (i : ℕ)))
    (hrate : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (i : Fin (phases K ε p)),
      σsq K ε p ((i : ℕ) + 1) = σsq K ε p (i : ℕ) * (1 + α K ε p))
    (hbudget : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)),
      ((1 : ℝ) - α K ε p ^ 2)⁻¹ ^ (n + 1)
        ≤ 1 + varBudget (ε / 2) / (phases K ε p : ℝ))
    (hflat : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (i : Fin (phases K ε p)),
      (i : ℕ) + 1 = phases K ε p →
      R K ε p ^ 2
        ≤ 2 * σsq K ε p (i : ℕ) * Real.log (((1 : ℝ) - α K ε p ^ 2)⁻¹ ^ (n + 1)))
    (hslack : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      (tvErr K ε p j (i : ℕ)).toReal
          * (Real.exp (R K ε p ^ 2 / (2 * σsq K ε p (i : ℕ))) ^ 2
              * (1 + 2 * (1 + varBudget (ε / 2) / (phases K ε p : ℝ))))
        ≤ (1 + varBudget (ε / 2) / (phases K ε p : ℝ)
              - ((1 : ℝ) - α K ε p ^ 2)⁻¹ ^ (n + 1))
            * (chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1)
                / chain (phases K ε p) (σsq K ε p) K (i : ℕ)) ^ 2) :
    ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      ∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
            (X K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ))
        ≤ (1 + varBudget (ε / 2) / (phases K ε p : ℝ))
            * (∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
                (X K ε p j (i : ℕ) x) ∂(ν j (i : ℕ))) ^ 2 := by
  intro K ε p hε hp hp1 hconv hball hfin j i
  have hexact : ∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ) x ^ 2
        ∂(coolLaw (phases K ε p) (σsq K ε p) K (i : ℕ))
      ≤ ((1 : ℝ) - α K ε p ^ 2)⁻¹ ^ (n + 1)
          * (∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ) x
              ∂(coolLaw (phases K ε p) (σsq K ε p) K (i : ℕ))) ^ 2 := by
    rcases Nat.lt_or_ge ((i : ℕ) + 1) (phases K ε p) with hlt | hge
    · exact coolLaw_interior_sq_moment_le_general (hσ K ε p) hconv hball hfin hlt
        (hα0 K ε p) (hα1 K ε p) (hrate K ε p hε hp hp1 hconv hball hfin j i)
    · have heq : (i : ℕ) + 1 = phases K ε p := by have := i.isLt; omega
      exact coolLaw_interior_sq_moment_le_terminal_flat_general (hσ K ε p) hconv hball hfin
        (hKR K ε p hε hp hp1 hconv hball hfin j i) (le_of_eq heq.symm)
        (hα0 K ε p) (hα1 K ε p) (hflat K ε p hε hp hp1 hconv hball hfin j i heq)
  exact phaseScore_interior_sq_moment_le_budget_general (hσ K ε p) hconv hball hfin
    (hKR K ε p hε hp hp1 hconv hball hfin j i) (hX K ε p j (i : ℕ))
    (hTV K ε p hε hp hp1 hconv hball hfin j i)
    (htop K ε p hε hp hp1 hconv hball hfin j i) (hα0 K ε p) (hα1 K ε p)
    (hbudget K ε p hε hp hp1 hconv hball hfin j i) hexact
    (hslack K ε p hε hp hp1 hconv hball hfin j i)

end Family

/-! ## 5.  The point of the exercise: the new pair is satisfiable while **annealing**

`geomSchedule_total_cooling_lt` (`PhaseVar.lean:620`) says a fixed-rate schedule meeting the
old `hbudget` cools by a factor `< 11/10`, so `hrate` and `hbudget` are jointly satisfiable
only by schedules that do not anneal.  `general_rate_annealing_witness` below is the
contradiction's removal, in one statement: it produces a rate, a phase count and a schedule
satisfying **`hrate`, `hbudget` and `hflat` at once** while cooling by `σ²ₘ/σ²₀ ≥ nR²`,
which is the factor a Gaussian-cooling schedule needs.

The witnesses are `GeneralRate.lean`'s explicit ones, `α = generalCoolRate n κ L` and
`m = generalPhaseCount n κ L` with `κ = varBudget (ε/2)` and `L = log(nR²)`, so the phase
count is `Θ(n·log²(nR²)/ε²)` and is genuine — `generalPhaseCount_ge_32` puts it at `≥ 32`,
not `0`.

**Stated honestly:** the starting variance the witness uses is
`σ²₀ = R²/(2·log((1 − α²)^{−(n+1)}))`, which is of order `(n+1)L²R²/κ²` — far above the
`σ²₀ ≈ 1/n` a Cousins–Vempala schedule starts at.  That is forced by `hflat`, which is a
*lower* bound on the terminal variance, while the annealing requirement constrains only the
*ratio* `σ²ₘ/σ²₀`; the two are compatible, and the way they are made compatible is by
starting warm.  The `hflat` price is the terminal-phase price `TerminalMoment.lean` already
records (`σᵢ² ≳ nR²/4` there, `σᵢ² ≳ R²/(2(n+1)α²)` here); it is not created by this file
and not removed by it. -/

section AnnealingWitness

/-- `1 < (1 − α²)^{−(n+1)}` for `0 < α < 1` — the general-rate constant is a genuine
allowance, so its logarithm is positive and `hflat` is a finite condition on `σᵢ²`. -/
theorem one_lt_generalRate_const {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) :
    1 < ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) := by
  have hone : (0 : ℝ) < 1 - α ^ 2 := by nlinarith
  have hinvpos : (0 : ℝ) < ((1 : ℝ) - α ^ 2)⁻¹ := inv_pos.2 hone
  have hcancel : ((1 : ℝ) - α ^ 2) * ((1 : ℝ) - α ^ 2)⁻¹ = 1 := mul_inv_cancel₀ hone.ne'
  have hbase : (1 : ℝ) < ((1 : ℝ) - α ^ 2)⁻¹ := by nlinarith [mul_pos hα0 hα0]
  exact one_lt_pow₀ hbase (Nat.succ_ne_zero n)

/-- **The demonstration this file exists to deliver.**

For every dimension `n`, every accuracy `0 < ε ≤ 2` and every radius `R` with
`nR² ≥ e`, there are a cooling rate `α > 0`, a phase count `m > 0` and a schedule `σsq` such
that **all of the following hold simultaneously**:

* `∀ j, 0 < σsq j` — the positivity `hσ` asks for;
* `∀ j, σsq (j+1) = σsq j · (1 + α)` — `hphase_var_of_tvLe_of_flat_general`'s `hrate`;
* `(1 − α²)^{−(n+1)} ≤ 1 + varBudget (ε/2)/m` — its `hbudget`;
* `∀ j, R² ≤ 2·σsq j·log((1 − α²)^{−(n+1)})` — its `hflat`, at *every* index, hence in
  particular at the terminal one;
* `nR² ≤ σsq m / σsq 0` — **the schedule anneals**: its total cooling factor is at least
  `nR²`, the factor needed to raise `σ²` from `≈ 1/n` to `≈ R²`;
* `32 ≤ m` — and the witness is **not** the degenerate `phases = 0` one.

Contrast `geomSchedule_total_cooling_lt`: at the fixed rate `α = 1/n`, the last two are
incompatible — a budget-meeting fixed-rate schedule has `σ²ₘ/σ²₀ < 11/10`.  So the
replacement of `hrate` and `hbudget` is not cosmetic: it is what makes the hypothesis pair
satisfiable in the regime the algorithm runs in.

The witnesses are `GeneralRate.lean`'s explicit `generalCoolRate`/`generalPhaseCount` at
`κ = varBudget (ε/2)`, `L = log(nR²)`, and the geometric schedule started at
`σ²₀ = R²/(2·log((1 − α²)^{−(n+1)}))`. -/
theorem general_rate_annealing_witness (n : ℕ) {ε R : ℝ} (hε0 : 0 < ε) (hε2 : ε ≤ 2)
    (hR : Real.exp 1 ≤ (n : ℝ) * R ^ 2) :
    ∃ (α : ℝ) (m : ℕ) (σsq : ℕ → ℝ),
      0 < m ∧ (32 : ℝ) ≤ (m : ℝ) ∧ 0 < α ∧ α < 1 ∧
      (∀ j, 0 < σsq j) ∧
      (∀ j, σsq (j + 1) = σsq j * (1 + α)) ∧
      ((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1) ≤ 1 + varBudget (ε / 2) / (m : ℝ) ∧
      (∀ j, R ^ 2 ≤ 2 * σsq j * Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1))) ∧
      (n : ℝ) * R ^ 2 ≤ σsq m / σsq 0 := by
  obtain ⟨hκ0, hκ1⟩ := varBudget_pos_le_one (ε := ε / 2) (by linarith) (by linarith)
  have hT0 : (0 : ℝ) < (n : ℝ) * R ^ 2 := lt_of_lt_of_le (Real.exp_pos 1) hR
  have hL : (1 : ℝ) ≤ Real.log ((n : ℝ) * R ^ 2) := (Real.le_log_iff_exp_le hT0).2 hR
  have hL0 : (0 : ℝ) < Real.log ((n : ℝ) * R ^ 2) := by linarith
  obtain ⟨hbud, hcool, hmpos⟩ :=
    exists_admissible_volume n (ε := ε / 2) (R := R) (by linarith) (by linarith) hR
  set κ : ℝ := varBudget (ε / 2) with hκdef
  set L : ℝ := Real.log ((n : ℝ) * R ^ 2) with hLdef
  set α : ℝ := generalCoolRate n κ L with hαdef
  set m : ℕ := generalPhaseCount n κ L with hmdef
  have hα0 : 0 < α := generalCoolRate_pos hκ0 hL0
  have hα1 : α < 1 :=
    lt_of_le_of_lt (generalCoolRate_le_sixteenth hκ0 hκ1 hL) (by norm_num)
  -- the general-rate allowance and its logarithm
  have hClt := one_lt_generalRate_const hα0 hα1 n
  set Λ : ℝ := Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (n + 1)) with hΛdef
  have hlog0 : 0 < Λ := Real.log_pos hClt
  -- `R > 0`, so the starting variance is positive
  have hRsq : (0 : ℝ) < R ^ 2 := by
    rcases (mul_pos_iff.1 hT0) with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · nlinarith [sq_nonneg R]
  set σ₀ : ℝ := R ^ 2 / (2 * Λ) with hσ₀def
  have hσ₀ : 0 < σ₀ := by rw [hσ₀def]; positivity
  have hbase : 2 * σ₀ * Λ = R ^ 2 := by
    rw [hσ₀def]
    field_simp
  refine ⟨α, m, geomSchedule σ₀ α, hmpos, generalPhaseCount_ge_32 hκ0 hκ1 hL, hα0, hα1,
    fun j => geomSchedule_pos hσ₀ (by linarith) j, fun j => geomSchedule_succ σ₀ α j,
    hbud, fun j => ?_, ?_⟩
  · -- `hflat` at every index: the schedule only grows, and `σ₀` was chosen to meet it
    have hpow : (1 : ℝ) ≤ (1 + α) ^ j := one_le_pow₀ (by linarith)
    have hge : σ₀ ≤ geomSchedule σ₀ α j := by
      rw [geomSchedule]
      nlinarith
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * Λ)
      (by linarith : (0 : ℝ) ≤ geomSchedule σ₀ α j - σ₀)]
  · -- the schedule anneals: total cooling `(1 + α)^m ≥ nR²`
    rw [geomSchedule_div_zero hσ₀.ne' m]
    exact hcool

/-- **A fully concrete instance** of the annealing witness: `n = 3`, `ε = 1`, `R = 2`, so
`nR² = 12 ≥ e`.  Every hypothesis is discharged by computation, mirroring
`GeneralRate.lean`'s `admissible_witness`. -/
theorem general_rate_annealing_witness_concrete :
    ∃ (α : ℝ) (m : ℕ) (σsq : ℕ → ℝ),
      0 < m ∧ (32 : ℝ) ≤ (m : ℝ) ∧ 0 < α ∧ α < 1 ∧
      (∀ j, 0 < σsq j) ∧
      (∀ j, σsq (j + 1) = σsq j * (1 + α)) ∧
      ((1 : ℝ) - α ^ 2)⁻¹ ^ (3 + 1) ≤ 1 + varBudget (1 / 2) / (m : ℝ) ∧
      (∀ j, (4 : ℝ) ≤ 2 * σsq j * Real.log (((1 : ℝ) - α ^ 2)⁻¹ ^ (3 + 1))) ∧
      (12 : ℝ) ≤ σsq m / σsq 0 := by
  have h12 : ((3 : ℕ) : ℝ) * (2 : ℝ) ^ 2 = 12 := by norm_num
  have hR : Real.exp 1 ≤ ((3 : ℕ) : ℝ) * (2 : ℝ) ^ 2 := by
    rw [h12]; linarith [Real.exp_one_lt_d9]
  obtain ⟨α, m, σsq, hm, hm32, hα0, hα1, hpos, hrate, hbud, hflat, hcool⟩ :=
    general_rate_annealing_witness 3 (ε := 1) (R := 2) one_pos (by norm_num) hR
  refine ⟨α, m, σsq, hm, hm32, hα0, hα1, hpos, hrate, hbud, fun j => ?_, ?_⟩
  · linarith [hflat j]
  · rw [h12] at hcool; exact hcool

end AnnealingWitness

/-! ## 6.  Non-vacuity of the family bundle (`CLAUDE.md` §11)

Degenerate on purpose (zero phases), exactly as `PhaseFromTV.lean`'s
`hphase_var_of_tvLe_witness` and `TerminalMoment.lean`'s `hphase_var_of_tvLe_of_flat_witness`
are, and for the reason recorded there: `ν` is a fixed family of laws chosen before `K` is
seen, while `hTV` asks each `ν j i` to be TV-close to `coolLaw … K i` for **every** admissible
`K`.  That is the `Ttc` interface's own obstruction, untouched here.

The witness that carries content is §5's `general_rate_annealing_witness`, which is
**genuine**: its phase count is `≥ 32` (`generalPhaseCount_ge_32`), not `0`. -/

section Witness

/-- Non-vacuity of the `hphase_var_of_tvLe_of_flat_general` bundle — **degenerate on purpose**
(zero phases); see the section docstring, and §5 for the witness that carries content. -/
theorem hphase_var_of_tvLe_of_flat_general_witness (hn : 3 ≤ n) :
    ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (_j : ℕ) (i : Fin 0),
      ∫ x, phaseScore 0 (fun _ => (1 : ℝ)) (interior K) (i : ℕ) (id x) ^ 2
          ∂(Measure.dirac (0 : EuclSpace n))
        ≤ (1 + varBudget (ε / 2) / ((0 : ℕ) : ℝ))
            * (∫ x, phaseScore 0 (fun _ => (1 : ℝ)) (interior K) (i : ℕ) (id x)
                ∂(Measure.dirac (0 : EuclSpace n))) ^ 2 :=
  hphase_var_of_tvLe_of_flat_general (EuclSpace n) hn (fun _ _ _ => 0) (fun _ _ _ _ => 1)
    (fun _ _ => Measure.dirac 0) (fun _ _ _ _ _ => id) (fun _ _ _ => 1) (fun _ _ _ => 0)
    (fun _ _ _ _ _ => 0)
    (fun _ _ _ _ => one_pos) (fun _ _ _ _ _ => measurable_id)
    (fun _ _ _ => le_rfl) (fun _ _ _ => by norm_num)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)

end Witness

end Arlib.GaussianCooling

/-! ## Axiom audit (`CLAUDE.md` §4)

Every declaration above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms Arlib.GaussianCooling.coolLaw_sq_moment_le_general
#print axioms Arlib.GaussianCooling.coolLaw_interior_sq_moment_le_general
#print axioms Arlib.GaussianCooling.coolLaw_interior_sq_moment_le_terminal_flat_general
#print axioms Arlib.GaussianCooling.coolLaw_interior_sq_moment_le_all_general
#print axioms Arlib.GaussianCooling.phaseScore_interior_sq_moment_le_budget_general
#print axioms Arlib.GaussianCooling.hphase_var_of_tvLe_of_flat_general
#print axioms Arlib.GaussianCooling.one_lt_generalRate_const
#print axioms Arlib.GaussianCooling.general_rate_annealing_witness
#print axioms Arlib.GaussianCooling.general_rate_annealing_witness_concrete
#print axioms Arlib.GaussianCooling.hphase_var_of_tvLe_of_flat_general_witness
