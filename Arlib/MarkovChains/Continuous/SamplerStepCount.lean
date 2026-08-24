/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.SpeedyGaussianMixing
import Arlib.Convexity.GaussianCooling.ColdStart
import Arlib.Convexity.GaussianCooling.WarmChain
import Arlib.MarkovChains.Continuous.WastedSteps
import Arlib.MarkovChains.Continuous.KLS97Shell

/-!
# The sampler's step count, at the regime `δ = 1/(2n)`

## Scope — read this first

`Ttc.VolumeAlgorithm` has **no complexity field**.  No running time can therefore be *stated*
inside that interface, and nothing in this file changes that.  What is proved here is an
**arithmetic/accounting result about step counts that are already proved elsewhere**:

* how many *speedy* steps the mixing theorem
  `Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit` demands per annealing
  phase once the step size is fixed at `δ = 1/(2n)`;
* what that becomes when multiplied by an annealing phase count;
* what `Arlib.MarkovChains.sum_lintegral_inv_ell_iterate_speedyWalk_le` then says about the
  summed *ball-walk* cost of that many speedy steps.

**This is not a claim that any volume algorithm runs in polynomial time.**  There is no cost
model, no machine model, no arithmetic-operation count, and no statement about `Ttc`'s
algorithm anywhere below.  A step count is not a running time, and the products formed here
are products of *proved bounds on counters*, nothing more.  Nothing under `Ttc/` is edited,
imported or referred to.

## The regime, and the arithmetic

`Arlib/MarkovChains/Continuous/KLS97Shell.lean` isolates the step-size regime `δ ≤ 1 − c =
1/(2n)`, at which the two Kannan–Lovász–Simonovits inputs to `lem:map-speedy-to-ball` become
provable outright (`ell_eq_one_on_shrunken`, `half_le_speedy_shrunken`).  Substituting
`δ = 1/(2n)` into the mixing deadline

    `4·640²·σ²·n·(log M + 2·log(1/ε)) / (δ·log 2)² + 1`

replaces `1/δ²` by `4n²`, so `4·640² = 1638400` becomes `4·4·640² = 6553600` and the
dimension exponent rises from `n` to `n³`:

    `6553600·σ²·n³·(log M + 2·log(1/ε)) / (log 2)² + 1`.

This is the `O(σ²n³·log(M/ε))` shape that `KLS97Shell.lean`'s module docstring already
predicts, in place of the `O(σ²n²·log(M/ε))` available at Cousins–Vempala's larger step.
No constant and no regime is changed silently: `6553600` is `4·640²·4` and nothing else.

### The side condition the substitution forces (a binder, and a finding)

The mixing theorem carries `hδσ : δ ≤ σ/(8√n)`.  At `δ = 1/(2n)` this is *exactly*

    `hσn : 4 ≤ σ·√n`,   i.e.   `σ² ≥ 16/n`,

which is **not** implied by the other hypotheses, so it appears as a binder on every theorem
below.  It is worth stating plainly what it costs: `ColdStart.lean`'s schedule starts at
`σ²₀ = 1/n` exactly (`geomSchedule (1/n) α`), where `σ₀·√n = 1 < 4`.  **The earliest
cold-start phases therefore fall outside the `δ = 1/(2n)` regime**: at `σ² = 1/n` the mixing
theorem needs `δ ≤ 1/(8n)`, a different constant, and the per-phase count below does not
apply to them.  Nothing here repairs that; it is recorded as a genuine gap between the two
ingredients, in the spirit of `CLAUDE.md` §5.

## What each section delivers

1. **Per phase** — `mixesWithin_lazy_speedyMetropolisGaussian_kls`: the mixing theorem at
   `δ = 1/(2n)` with the constant `6553600` explicit.
2. **All phases at one budget** — `mixesWithin_all_phases_kls`: a family of phases sharing the
   body `K`, each with its own variance `σⱼ²` and its own start `μⱼ`, all mixing within the
   single budget `t = ⌈D(σmax)⌉₊` computed at a dominating `σmax`.
3. **Total speedy steps** — `total_speedy_steps_le`: `m·t ≤ (32(n+1)L²/κ + 1)·(D + 1)`, where
   `32(n+1)L²/κ + 1` is `GeneralRate.lean`'s bound `generalPhaseCount_le` on the phase count
   `ColdStart.lean` uses.
4. **Polynomial shape** — `total_speedy_steps_poly`, `total_speedy_steps_poly_varBudget`, and
   `total_speedy_steps_poly_sqrt_exp` (the same at `WarmChain.lean`'s `n`-free `M = √e`).
5. **Total ball-walk cost** — `sum_ballWalk_cost_phases_le`.
6. **Non-vacuity** — `sampler_step_count_witness`.

## Which closed form was chosen for the polynomial shape

An **explicit product of factors**, not a single closed form in `n, R, 1/ε` alone:

    `m·t ≤ 5·10⁸ · (n+1) · n³ · σmax² · L² · (1 + log M + 2·log(1/ε)) / κ`

and, at `κ = varBudget (ε/2)`,

    `m·t ≤ 2·10¹⁰ · (n+1) · n³ · σmax² · L² · (1 + log M + 2·log(1/ε)) / ε²`.

So the **exponents achieved** are `n⁴` (as `(n+1)·n³`), `σmax²`, `ε⁻²`, `L²` and one power of
`log M`.  The reason a closed form in `R` is *not* offered is structural, and is itself a
finding: `cold_start_annealing_witness` is an existential over `(α, m, σsq)` that exposes only
a *lower* bound on the phase count (`32 ≤ m`) and only a *lower* bound on the total cooling
(`nR² ≤ σsq m / σsq 0`).  Neither `m` nor `max_j σⱼ` is pinned from above by that statement, so
neither can be eliminated here.  Both therefore enter as hypotheses: `hm`, which
`generalPhaseCount_le` discharges for `ColdStart.lean`'s *stated* choice
`m = generalPhaseCount n κ L'`, and `hsigmax`.  Since `hflat` forces
`σ²_{m−1} ≥ R²/(2Λ)` with `Λ` small, a binder `σmax² ≤ R²` would be **false** for the intended
schedule — which is why `σmax²` is carried as a factor rather than converted into `R²`.
`L` is likewise a parameter; `ColdStart.lean` runs at `L' = 3·log(nR²) + 4·log(256(n+1)/κ²)`.

## Hypotheses carried unproved

* **`hlam : lam ≤ avgLocalConductance K δ`** — Cousins–Vempala's `lem:lambda-bound`
  (`vol3_journal.tex:855`).  Nothing in this repository proves it and nothing here attempts
  to; §5's theorem carries it as a binder exactly as `WastedSteps.lean` does.  (At
  `δ ≤ 1/(2n)`, `KLS97Shell.ell_eq_one_on_shrunken` gives `ℓ ≡ 1` on the shrunken body, which
  *suggests* a route to a lower bound on `λ` in this regime; **that route is not taken and no
  such bound is proved here**.)
* **`hwarm : IsWarm (ofReal M) μⱼ (ellGaussianProb K δ σⱼ²)`** — the per-phase warm start.
  `WarmChain.lean` proves the `n`-free constants `√e` (`isWarm_coolLaw_succ_sqrt_exp`) and
  `e` (`isWarm_coolLaw_succ_exp`), but those are warmness of `coolLaw i` **for `coolLaw (i+1)`**
  — the Gaussian-weighted *uniform* phase laws.  The speedy chain's stationary law
  `ellGaussianProb` carries an extra factor `ℓ`, and the reweighting bridge between the two is
  **not proved in this repository**.  It is worse than merely unproved:
  `Arlib/Convexity/GaussianCooling/PhaseSamplerTV.lean` (which carries the *same* residual
  binder, for the same reason) records that `Arlib/MarkovChains/Continuous/EllFloor.lean`
  rules out the obvious route — there is **no uniform pointwise floor on `ell`** on the
  relevant class (`ell ≤ 2⁻ⁿ` at a cube corner, at every `δ`), so the sup-ratio
  `coolLaw / ellGaussianProb` cannot be bounded that way.  `M` therefore stays a hypothesis,
  with `hM : 1 ≤ M`; `total_speedy_steps_poly_sqrt_exp` substitutes `M = √e` as *arithmetic in
  a proved bound* and says so.
* **`hm`** — the identification of `ColdStart.lean`'s existentially-bound phase count with
  `generalPhaseCount n κ L'`.  True by construction (the docstring of
  `cold_start_annealing_witness` states the witness), but the theorem's `∃` hides it.
* **`hsigmax`** — that `σmax` dominates every phase's `σⱼ`; see above.
* **`hσn : 4 ≤ σ·√n`** — the regime side condition, with the cold-phase failure recorded above.

## The chain mismatch in §5, stated honestly

`WastedSteps.lean` converts speedy steps to ball-walk steps for the **uniform** speedy walk
(`speedyWalk K δ`, stationary law `ellProb K δ`).  The step count of §§1–4 is for the
**Gaussian** speedy chain (`speedyMetropolisGaussian K δ σ²`, stationary law
`ellGaussianProb K δ σ²`).  A Gaussian analogue of `WastedSteps.lean` **now exists** —
`Arlib/MarkovChains/Continuous/WastedStepsGaussian.lean`, which proves the exact one-step
identity `E_x[exit time] = (ℓ(x)·a(x))⁻¹` for `metropolisGaussian` and the averaged bound
`3·∑ ≤ 10·t·M` with both `λ ≥ 1/2` and the acceptance floor `a ≥ 3/5` discharged.  **§5 below
has not been restated over it**: §5 is still stated verbatim over the uniform chain, with the
total step count
`m·t` supplied as a plain natural number; reading it as "the ball-walk cost of the Gaussian
sampler" is **not** licensed by anything proved here.

`WastedSteps.lean`'s own caveat is preserved and must be quoted with §5: the left-hand side is
`∑_{i<T} E_{Qᵢ}[mean holding time]`, a sum of **per-step conditional expectations** — the
quantity Cousins–Vempala bound by linearity of expectation — and **not** the path-level number
of ball-walk steps a single trajectory takes.  The path-level time change is
`TrajTransfer.lean`'s unproved item.

## Audit surface (`CLAUDE.md` §11)

* **Capstones**: `mixesWithin_lazy_speedyMetropolisGaussian_kls` (§1),
  `total_speedy_steps_poly_varBudget` (§4), `sum_ballWalk_cost_phases_le` (§5).  Read the
  types only.
* **Hypotheses carried unproved**: the five listed above, each an inline binder.
* **Non-vacuity**: `sampler_step_count_witness`, which discharges every binder of §§1–5
  simultaneously at `n = 21`, `K = B(0,1)`, `σ = 100`, `R = 1`, `M = 1`, `ε = 1/2`,
  `m = 10⁸`, and exhibits the numeric total `m·t ≤ 2·10²³`.
* **Semantic `def`s**: none.  This file introduces no `def`, no `structure`, no `class`, no
  `axiom` and no named `Prop`; every step count is written out in the statement that uses it,
  so no name stands in for a proof.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory Metric
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. One phase, at `δ = 1/(2n)`

The mixing theorem `Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit` with the
step size fixed at the `KLS97Shell.lean` regime.  Only two things happen: the deadline is
rewritten (`4·640²/(1/(2n))² = 6553600·n²` extra), and `hδσ` is re-expressed as `4 ≤ σ·√n`. -/

/-- **The per-phase speedy step count at `δ = 1/(2n)`.**

The lazy speedy Metropolis–Gaussian chain at step size `δ = 1/(2n)` mixes to within `ε` of its
own stationary law `ellGaussianProb K δ σ²` from an `M`-warm start after

    `t ≥ 6553600·σ²·n³·(log M + 2·log(1/ε)) / (log 2)² + 1`

steps, where `6553600 = 4·4·640²`.

Every binder is `Arlib.mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit`'s, with one
replacement: that theorem's `hδ : 0 < δ` is discharged from `hn`, and its `hδσ : δ ≤ σ/(8√n)`
becomes the binder `hσn : 4 ≤ σ·√n`, which is *equivalent* to it at `δ = 1/(2n)` — see the
module docstring for what that costs at the cold end of the annealing schedule.

This is a step-count statement about a Markov chain.  It is not a running-time statement; see
the module docstring's scope paragraph. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_kls (hn : 21 ≤ n) {σ R : ℝ}
    (hσ : 0 < σ) (hσn : 4 ≤ σ * Real.sqrt n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    (hRσ : R ≤ 2 * σ * Real.sqrt n)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellGaussianProb K (1 / (2 * (n : ℝ))) (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 6553600 * σ ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin (lazy (speedyMetropolisGaussian K (1 / (2 * (n : ℝ))) (σ ^ 2)))
      (ellGaussianProb K (1 / (2 * (n : ℝ))) (σ ^ 2)) mu0 t (ENNReal.ofReal eps) := by
  have hnR : (21 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hδ : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by positivity
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
  have hsn : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hspos : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
  have hδσ : 1 / (2 * (n : ℝ)) ≤ σ / (8 * Real.sqrt (n : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.2 hσn) hsn]
  refine mixesWithin_lazy_speedyMetropolisGaussian_uncond_explicit hn hσ hδ hδσ hK hKc hK0
    hR hKR hRσ hM hwarm heps0 heps1 ?_
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have heq : 4 * 640 ^ 2 * σ ^ 2 * (n : ℝ) * (Real.log M + 2 * Real.log (1 / eps))
        / (1 / (2 * (n : ℝ)) * Real.log 2) ^ 2
      = 6553600 * σ ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
        / Real.log 2 ^ 2 := by
    field_simp
    ring
  rw [heq]
  exact ht

/-! ## 2. Every phase, at one budget

The annealing schedule keeps the body `K` fixed and raises the variance.  Phase `j` runs the
chain at variance `σⱼ²` from a start `μⱼ`, and the deadline of §1 is increasing in `σ`, so a
single budget computed at a dominating `σmax` serves every phase at once. -/

/-- **All `m` phases mix within the same budget.**

For a family of variances `σ : ℕ → ℝ` and starts `μ : ℕ → Measure _` sharing the body `K`,
every phase `j < m` mixes to within `ε` after

    `t = ⌈6553600·σmax²·n³·(log M + 2·log(1/ε))/(log 2)² + 1⌉₊`

speedy steps, where `σmax` dominates every `σⱼ`.  The per-phase hypotheses are §1's, imposed
for `j < m` only; `hσmax` is the domination.

`M` is one warmness constant serving every phase — the shape `WarmChain.lean` supplies for the
*cooling laws*.  See the module docstring: the bridge from `coolLaw` warmness to warmness for
`ellGaussianProb` is not proved in this repository, so `hwarm` is a binder here. -/
theorem mixesWithin_all_phases_kls (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hK0 : volume K ≠ 0) {R : ℝ} (hR : 0 ≤ R) (hKR : ∀ x ∈ K, ‖x‖ ≤ R)
    {m : ℕ} {sig : ℕ → ℝ} {mu : ℕ → Measure (EuclideanSpace ℝ (Fin n))}
    (hmu : ∀ j, IsProbabilityMeasure (mu j))
    (hsig0 : ∀ j < m, 0 < sig j) (hsign : ∀ j < m, 4 ≤ sig j * Real.sqrt n)
    (hRsig : ∀ j < m, R ≤ 2 * sig j * Real.sqrt n)
    {M eps sigmax : ℝ} (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hwarm : ∀ j < m, IsWarm (ENNReal.ofReal M) (mu j)
      (ellGaussianProb K (1 / (2 * (n : ℝ))) (sig j ^ 2)))
    (hsigmax : ∀ j < m, sig j ≤ sigmax) :
    ∀ j < m, MixesWithin (lazy (speedyMetropolisGaussian K (1 / (2 * (n : ℝ))) (sig j ^ 2)))
      (ellGaussianProb K (1 / (2 * (n : ℝ))) (sig j ^ 2)) (mu j)
      ⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
        / Real.log 2 ^ 2 + 1⌉₊ (ENNReal.ofReal eps) := by
  have hX : 0 ≤ Real.log M + 2 * Real.log (1 / eps) := by
    have h1 : 0 ≤ Real.log M := Real.log_nonneg hM
    have h2 : 0 ≤ Real.log (1 / eps) :=
      Real.log_nonneg (by rw [le_div_iff₀ heps0]; linarith)
    linarith
  have hlog2 : (0 : ℝ) < Real.log 2 ^ 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  intro j hj
  haveI := hmu j
  refine mixesWithin_lazy_speedyMetropolisGaussian_kls hn (hsig0 j hj) (hsign j hj) hK hKc hK0
    hR hKR (hRsig j hj) hM (hwarm j hj) heps0 heps1 ?_
  have hsq : sig j ^ 2 ≤ sigmax ^ 2 := by
    nlinarith [hsig0 j hj, hsigmax j hj]
  have hn3 : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
  have hmono : 6553600 * sig j ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
        / Real.log 2 ^ 2
      ≤ 6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
        / Real.log 2 ^ 2 := by
    rw [div_le_div_iff₀ hlog2 hlog2]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.2 hsq) hn3) hX) hlog2.le]
  have hceil := Nat.le_ceil (6553600 * sigmax ^ 2 * (n : ℝ) ^ 3
    * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1)
  linarith

/-! ## 3. The total number of speedy steps

The phase count.  `ColdStart.lean` runs `GeneralRate.lean`'s explicit construction at the
raised log-target `L' = 3·log(nR²) + 4·log(256(n+1)/κ²)`, i.e. at
`m = generalPhaseCount n κ L' = ⌈32(n+1)L'²/κ⌉₊`, for which `generalPhaseCount_le` gives

    `m ≤ 32(n+1)L'²/κ + 1`.

`cold_start_annealing_witness` states only `∃ m, 32 ≤ m ∧ …`, so that upper bound is *not*
recoverable from its type; it enters below as the binder `hm`, and
`total_speedy_steps_le_generalPhaseCount` discharges `hm` for the stated choice. -/

/-- **Total speedy steps: phase count times per-phase budget.**

Pure accounting: `m·t ≤ (32(n+1)L²/κ + 1)·(D + 1)` where `D` is §2's per-phase deadline and
`t = ⌈D⌉₊` is §2's budget.  The `+1` on the right is `⌈D⌉₊ < D + 1`.

`m` is a number of phases and `t` a number of speedy steps; the product is a number of speedy
steps and nothing else — no cost model is involved. -/
theorem total_speedy_steps_le (hn : 21 ≤ n) {m : ℕ} {sigmax M eps κ L : ℝ}
    (hκ0 : 0 < κ) (hL : 1 ≤ L) (_hsigmax : 0 ≤ sigmax) (hM : 1 ≤ M)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hm : (m : ℝ) ≤ 32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1) :
    ((m * ⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
          / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      ≤ (32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1)
        * (6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
            / Real.log 2 ^ 2 + 2) := by
  have hX : 0 ≤ Real.log M + 2 * Real.log (1 / eps) := by
    have h1 : 0 ≤ Real.log M := Real.log_nonneg hM
    have h2 : 0 ≤ Real.log (1 / eps) :=
      Real.log_nonneg (by rw [le_div_iff₀ heps0]; linarith)
    linarith
  have hlog2 : (0 : ℝ) < Real.log 2 ^ 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hD0 : (0 : ℝ) ≤ 6553600 * sigmax ^ 2 * (n : ℝ) ^ 3
      * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1 := by positivity
  have hceil : ((⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3
        * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      ≤ 6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
          / Real.log 2 ^ 2 + 2 := by
    have := Nat.ceil_lt_add_one hD0
    linarith
  have hAnn : (0 : ℝ) ≤ 32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1 := by positivity
  have hcast : ((m * ⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3
        * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      = (m : ℝ) * ((⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3
        * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ) := by
    push_cast; ring
  rw [hcast]
  exact mul_le_mul hm hceil (Nat.cast_nonneg _) hAnn

/-- **The same bound with `hm` discharged at `ColdStart.lean`'s stated phase count.**

`m = generalPhaseCount n κ L = ⌈32(n+1)L²/κ⌉₊` is the witness `cold_start_annealing_witness`
constructs (at `κ = varBudget (ε/2)` and `L` the raised log-target `L'`); `generalPhaseCount_le`
is the bound.  What is *not* proved is that the `m` bound by that theorem's `∃` is this one —
its type does not say so. -/
theorem total_speedy_steps_le_generalPhaseCount (hn : 21 ≤ n) {sigmax M eps κ L : ℝ}
    (hκ0 : 0 < κ) (hL : 1 ≤ L) (hsigmax : 0 ≤ sigmax) (hM : 1 ≤ M)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    ((GaussianCooling.generalPhaseCount n κ L
        * ⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
          / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      ≤ (32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1)
        * (6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
            / Real.log 2 ^ 2 + 2) :=
  total_speedy_steps_le hn hκ0 hL hsigmax hM heps0 heps1
    (GaussianCooling.generalPhaseCount_le hκ0)

/-! ## 4. The polynomial shape

An explicit product of factors, with the exponents visible.  See the module docstring for why
a closed form in `R` is not offered. -/

/-- **`x/2 ≤ log(1 + x)` for `0 ≤ x ≤ 1`.**  From `1 − x/2 ≤ e^{−x/2}`, which gives
`e^{x/2} ≤ 1/(1 − x/2) ≤ 1 + x`, the last step being `x² ≤ x`. -/
theorem half_le_log_one_add {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ Real.log (1 + x) := by
  have hd : (0 : ℝ) < 1 - x / 2 := by linarith
  have hpos : (0 : ℝ) < Real.exp (x / 2) := Real.exp_pos _
  have h1 : 1 - x / 2 ≤ Real.exp (-(x / 2)) := by
    have := Real.add_one_le_exp (-(x / 2)); linarith
  have h2 : (1 - x / 2) * Real.exp (x / 2) ≤ 1 := by
    calc (1 - x / 2) * Real.exp (x / 2)
        ≤ Real.exp (-(x / 2)) * Real.exp (x / 2) := mul_le_mul_of_nonneg_right h1 hpos.le
      _ = 1 := by rw [← Real.exp_add]; simp
  have h3 : Real.exp (x / 2) ≤ 1 / (1 - x / 2) := by
    rw [le_div_iff₀ hd, mul_comm]; exact h2
  have h4 : 1 / (1 - x / 2) ≤ 1 + x := by
    rw [div_le_iff₀ hd]; nlinarith
  have hexp : Real.exp (x / 2) ≤ 1 + x := le_trans h3 h4
  calc x / 2 = Real.log (Real.exp (x / 2)) := (Real.log_exp _).symm
    _ ≤ Real.log (1 + x) := Real.log_le_log hpos hexp

/-- **`ε²/40 ≤ varBudget (ε/2) ≤ 1` for `0 < ε ≤ 1`.**

`varBudget (ε/2) = log(1 + ε²/20)`; the lower bound is `half_le_log_one_add`, the upper bound
is `log y ≤ y − 1`.  This is what turns the `1/κ` factor of `total_speedy_steps_poly` into the
`ε⁻²` of `total_speedy_steps_poly_varBudget`. -/
theorem sq_div_forty_le_varBudget_le_one {eps : ℝ} (heps0 : 0 < eps) (heps1 : eps ≤ 1) :
    eps ^ 2 / 40 ≤ GaussianCooling.varBudget (eps / 2)
      ∧ GaussianCooling.varBudget (eps / 2) ≤ 1 := by
  have hx : (eps / 2) ^ 2 / 5 = eps ^ 2 / 20 := by ring
  have hxle : eps ^ 2 / 20 ≤ 1 := by nlinarith
  have hx0 : (0 : ℝ) ≤ eps ^ 2 / 20 := by positivity
  constructor
  · have := half_le_log_one_add hx0 hxle
    rw [GaussianCooling.varBudget, hx]
    linarith
  · rw [GaussianCooling.varBudget, hx]
    have := Real.log_le_sub_one_of_pos (x := 1 + eps ^ 2 / 20) (by positivity)
    linarith

/-- **The total speedy step count is bounded by an explicit product of factors.**

    `m·t ≤ 5·10⁸ · (n+1) · n³ · σmax² · L² · (1 + log M + 2·log(1/ε)) / κ`.

Exponents: `n⁴` (as `(n+1)·n³`), `σmax²`, `L²`, `κ⁻¹`, and one power of `log M`.  The constant
is `33 · 13653334 = 450560022 ≤ 5·10⁸`, where `33/32` absorbs the `+1` of the phase-count bound
(legitimate because `(n+1)L²/κ ≥ 22`) and `13653334 ≥ 6553600/(log 2)²` absorbs both the
`(log 2)²` and the `+2` of the per-phase bound (legitimate because `hσn` forces
`σmax²·n³ ≥ 16n² ≥ 7056`).  Every one of those side facts is proved below; nothing is
assumed. -/
theorem total_speedy_steps_poly (hn : 21 ≤ n) {m : ℕ} {sigmax M eps κ L : ℝ}
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hL : 1 ≤ L) (hsig0 : 0 < sigmax)
    (hσn : 4 ≤ sigmax * Real.sqrt n) (hM : 1 ≤ M) (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hm : (m : ℝ) ≤ 32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1) :
    ((m * ⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
          / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      ≤ 5 * 10 ^ 8 * ((n : ℝ) + 1) * (n : ℝ) ^ 3 * sigmax ^ 2 * L ^ 2
          * (1 + (Real.log M + 2 * Real.log (1 / eps))) / κ := by
  have hnR : (21 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hX : 0 ≤ Real.log M + 2 * Real.log (1 / eps) := by
    have h1 : 0 ≤ Real.log M := Real.log_nonneg hM
    have h2 : 0 ≤ Real.log (1 / eps) :=
      Real.log_nonneg (by rw [le_div_iff₀ heps0]; linarith)
    linarith
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2 : (0 : ℝ) < Real.log 2 ^ 2 := by positivity
  have hlog048 : (0.48 : ℝ) ≤ Real.log 2 ^ 2 := by
    nlinarith [Real.log_two_gt_d9]
  -- `hσn` forces `σmax²·n ≥ 16`, hence `σmax²·n³ ≥ 16n² ≥ 7056`
  have hsn : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
  have hs16 : (16 : ℝ) ≤ sigmax ^ 2 * (n : ℝ) := by
    nlinarith [hσn, hsq, hsn]
  have hbig : (7056 : ℝ) ≤ sigmax ^ 2 * (n : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg ((n : ℝ))) (sub_nonneg.2 hs16)]
  refine le_trans (total_speedy_steps_le hn hκ0 hL hsig0.le hM heps0 heps1 hm) ?_
  set X := Real.log M + 2 * Real.log (1 / eps) with hXdef
  have hnum : (0 : ℝ) ≤ 6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * X :=
    mul_nonneg (by positivity) hX
  have hQ : 6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * X / Real.log 2 ^ 2 + 2
      ≤ 13653334 * (sigmax ^ 2 * (n : ℝ) ^ 3) * (1 + X) := by
    have ha : 6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * X / Real.log 2 ^ 2
        ≤ 13653334 * (sigmax ^ 2 * (n : ℝ) ^ 3) * X := by
      rw [div_le_iff₀ hlog2]
      nlinarith [mul_nonneg hnum (sub_nonneg.2 hlog048)]
    have hb : (2 : ℝ) ≤ 13653334 * (sigmax ^ 2 * (n : ℝ) ^ 3) := by linarith
    linarith
  have hQ0 : (0 : ℝ) ≤ 6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * X / Real.log 2 ^ 2 + 2 := by
    have := div_nonneg hnum hlog2.le
    linarith
  have hP : 32 * ((n : ℝ) + 1) * L ^ 2 + κ ≤ 33 * ((n : ℝ) + 1) * L ^ 2 := by
    nlinarith [sq_nonneg (L - 1)]
  have h1X : (0 : ℝ) ≤ 1 + X := by linarith
  rw [le_div_iff₀ hκ0]
  have hrw : (32 * ((n : ℝ) + 1) * L ^ 2 / κ + 1)
        * (6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * X / Real.log 2 ^ 2 + 2) * κ
      = (32 * ((n : ℝ) + 1) * L ^ 2 + κ)
        * (6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * X / Real.log 2 ^ 2 + 2) := by
    field_simp
  rw [hrw]
  calc (32 * ((n : ℝ) + 1) * L ^ 2 + κ)
        * (6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * X / Real.log 2 ^ 2 + 2)
      ≤ (33 * ((n : ℝ) + 1) * L ^ 2) * (13653334 * (sigmax ^ 2 * (n : ℝ) ^ 3) * (1 + X)) :=
        mul_le_mul hP hQ hQ0 (by positivity)
    _ = 450560022 * (((n : ℝ) + 1) * (n : ℝ) ^ 3 * sigmax ^ 2 * L ^ 2 * (1 + X)) := by ring
    _ ≤ 5 * 10 ^ 8 * (((n : ℝ) + 1) * (n : ℝ) ^ 3 * sigmax ^ 2 * L ^ 2 * (1 + X)) := by
        refine mul_le_mul_of_nonneg_right (by norm_num) ?_
        have : (0 : ℝ) ≤ ((n : ℝ) + 1) * (n : ℝ) ^ 3 * sigmax ^ 2 * L ^ 2 := by positivity
        exact mul_nonneg this h1X
    _ = 5 * 10 ^ 8 * ((n : ℝ) + 1) * (n : ℝ) ^ 3 * sigmax ^ 2 * L ^ 2 * (1 + X) := by ring

/-- **The same bound at the volume algorithm's own variance budget `κ = varBudget (ε/2)`.**

    `m·t ≤ 2·10¹⁰ · (n+1) · n³ · σmax² · L² · (1 + log M + 2·log(1/ε)) / ε²`.

The only new input is `sq_div_forty_le_varBudget_le_one`, which prices `1/κ ≤ 40/ε²`; the
constant is `40 · 5·10⁸ = 2·10¹⁰`.  So the exponents in the four named quantities are

    `n⁴`,  `σmax²`,  `ε⁻²`,  `L²`,  and `log M` linearly,

with `L` the annealing log-target (`ColdStart.lean`: `L' = 3·log(nR²) + 4·log(256(n+1)/κ²)`,
hence `O(log(nR²) + log(n/ε))`) and `σmax` the largest phase standard deviation.  Neither `L`
nor `σmax` is eliminated in favour of `R`: see the module docstring. -/
theorem total_speedy_steps_poly_varBudget (hn : 21 ≤ n) {m : ℕ} {sigmax M eps L : ℝ}
    (hL : 1 ≤ L) (hsig0 : 0 < sigmax) (hσn : 4 ≤ sigmax * Real.sqrt n) (hM : 1 ≤ M)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hm : (m : ℝ) ≤ 32 * ((n : ℝ) + 1) * L ^ 2 / GaussianCooling.varBudget (eps / 2) + 1) :
    ((m * ⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (Real.log M + 2 * Real.log (1 / eps))
          / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      ≤ 2 * 10 ^ 10 * ((n : ℝ) + 1) * (n : ℝ) ^ 3 * sigmax ^ 2 * L ^ 2
          * (1 + (Real.log M + 2 * Real.log (1 / eps))) / eps ^ 2 := by
  obtain ⟨hlow, hhigh⟩ := sq_div_forty_le_varBudget_le_one heps0 heps1
  have hκ0 : 0 < GaussianCooling.varBudget (eps / 2) :=
    GaussianCooling.varBudget_pos (by linarith)
  refine le_trans (total_speedy_steps_poly hn hκ0 hhigh hL hsig0 hσn hM heps0 heps1 hm) ?_
  have hX : 0 ≤ Real.log M + 2 * Real.log (1 / eps) := by
    have h1 : 0 ≤ Real.log M := Real.log_nonneg hM
    have h2 : 0 ≤ Real.log (1 / eps) :=
      Real.log_nonneg (by rw [le_div_iff₀ heps0]; linarith)
    linarith
  have hZ : (0 : ℝ) ≤ ((n : ℝ) + 1) * (n : ℝ) ^ 3 * sigmax ^ 2 * L ^ 2
      * (1 + (Real.log M + 2 * Real.log (1 / eps))) := by
    have h1 : (0 : ℝ) ≤ ((n : ℝ) + 1) * (n : ℝ) ^ 3 * sigmax ^ 2 * L ^ 2 := by positivity
    exact mul_nonneg h1 (by linarith)
  rw [div_le_div_iff₀ hκ0 (by positivity)]
  nlinarith [mul_nonneg hZ (sub_nonneg.2 hlow)]

/-- **The same at `WarmChain.lean`'s `n`-free per-phase warm start `M = √e`.**

`isWarm_coolLaw_succ_sqrt_exp` supplies the constant `√e` — free of `n`, of `K`, of the
variance and of the phase index — at Cousins–Vempala's own schedule `σ²ᵢ₊₁ = (1 + 1/n)σ²ᵢ`.
Substituting `M = e^{1/2}`, so that `log M = 1/2`, collapses the log factor:

    `m·t ≤ 2·10¹⁰ · (n+1) · n³ · σmax² · L² · (3/2 + 2·log(1/ε)) / ε²`,

with the per-phase budget `⌈6553600·σmax²·n³·(1/2 + 2·log(1/ε))/(log 2)² + 1⌉₊`.

**This is substitution into a proved bound, not a proof that the chain can be started
`√e`-warm.**  `WarmChain.lean`'s constant warms `coolLaw i` against `coolLaw (i+1)`; §§1–2 need
warmness against `ellGaussianProb K δ σ²`, which carries the extra factor `ell K δ`, and
`EllFloor.lean` rules out bounding the sup-ratio by a pointwise floor on `ell` (there is none:
`ell ≤ 2⁻ⁿ` at a cube corner, at every `δ`).  See the module docstring; the same residual
binder is carried, for the same reason, by `PhaseSamplerTV.lean`. -/
theorem total_speedy_steps_poly_sqrt_exp (hn : 21 ≤ n) {m : ℕ} {sigmax eps L : ℝ}
    (hL : 1 ≤ L) (hsig0 : 0 < sigmax) (hσn : 4 ≤ sigmax * Real.sqrt n)
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    (hm : (m : ℝ) ≤ 32 * ((n : ℝ) + 1) * L ^ 2 / GaussianCooling.varBudget (eps / 2) + 1) :
    ((m * ⌈6553600 * sigmax ^ 2 * (n : ℝ) ^ 3 * (1 / 2 + 2 * Real.log (1 / eps))
          / Real.log 2 ^ 2 + 1⌉₊ : ℕ) : ℝ)
      ≤ 2 * 10 ^ 10 * ((n : ℝ) + 1) * (n : ℝ) ^ 3 * sigmax ^ 2 * L ^ 2
          * (3 / 2 + 2 * Real.log (1 / eps)) / eps ^ 2 := by
  have hM : (1 : ℝ) ≤ Real.exp (1 / 2) := by
    linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
  have h := total_speedy_steps_poly_varBudget hn (M := Real.exp (1 / 2)) hL hsig0 hσn hM
    heps0 heps1 hm
  rw [Real.log_exp] at h
  refine le_trans h (le_of_eq ?_)
  ring

/-! ## 5. The ball-walk cost of that many speedy steps

`WastedSteps.lean`'s `sum_lintegral_inv_ell_iterate_speedyWalk_le`, at `δ = 1/(2n)` and at a
step count presented as a product `m·t`.

**Two caveats travel with this statement and must be quoted with it.**

1. *Per-step conditional expectations, not a path.*  The left-hand side is
   `∑_{i<m·t} E_{Qᵢ}[1/ℓ]`, where each summand is the proved mean ball-walk holding time from
   the current speedy state — exactly the quantity Cousins–Vempala bound by linearity of
   expectation.  It is **not** the number of ball-walk steps a single trajectory takes; that
   identification needs the path-level time change, which `TrajTransfer.lean` leaves unproved.
2. *Uniform chain, Gaussian step count.*  `speedyWalk`/`ellProb` is the **uniform** speedy
   walk; §§1–4 count steps of the **Gaussian** chain `speedyMetropolisGaussian`.  No Gaussian
   analogue of `WastedSteps.lean` exists in this repository, so the two are combined only as
   *numbers*.  `m` and `t` are plain naturals here and are given no other meaning.

`hlam` is Cousins–Vempala's `lem:lambda-bound` and is carried unproved, as in `WastedSteps`. -/

/-- **Total ball-walk cost of `m·t` speedy steps, at `δ = 1/(2n)`.**

    `∑_{i<m·t} ∫ (ℓ)⁻¹ d(iterateᵢ) ≤ m·t·M/λ`.

Read the two caveats in the section docstring before quoting this. -/
theorem sum_ballWalk_cost_phases_le (hn : 21 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤)
    {lam Mw : ℝ≥0∞} (hlam : lam ≤ avgLocalConductance K (1 / (2 * (n : ℝ))))
    (hlam0 : lam ≠ 0) (hlamtop : lam ≠ ⊤)
    {Q₀ : Measure (EuclideanSpace ℝ (Fin n))}
    (hwarm : IsWarm Mw Q₀ (ellProb K (1 / (2 * (n : ℝ))))) (m t : ℕ) :
    ∑ i ∈ Finset.range (m * t), ∫⁻ x, (ell K (1 / (2 * (n : ℝ))) x)⁻¹
        ∂(iterate (speedyWalk K (1 / (2 * (n : ℝ)))) Q₀ i)
      ≤ (m : ℝ≥0∞) * (t : ℝ≥0∞) * Mw / lam := by
  have hnR : (21 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hδ : (0 : ℝ) < 1 / (2 * (n : ℝ)) := by
    have : (0 : ℝ) < (n : ℝ) := by linarith
    positivity
  have h := sum_lintegral_inv_ell_iterate_speedyWalk_le hK hδ hK0 hKtop hlam hlam0 hlamtop
    hwarm (m * t)
  rwa [Nat.cast_mul] at h

/-! ## 6. Non-vacuity (`CLAUDE.md` §11)

Every binder of §§1–5 discharged simultaneously at concrete data, with the conclusions of
§§2, 4 and 5 carried and a numeric total exhibited. -/

/-- **Non-vacuity: the whole bundle at concrete `n, R, ε`.**

    `n = 21`,  `K = B(0,1) ⊆ ℝ²¹`,  `R = 1`,  `σⱼ ≡ 100`,  `σmax = 100`,
    `μⱼ = ellGaussianProb K δ σ²`,  `M = 1`,  `ε = 1/2`,  `L = 84`,  `m = 10⁸`,
    `δ = 1/42`,  `Q₀ = ellProb K δ`,  `λ = avgLocalConductance K δ`,  `Mw = 1`,
    `t = ⌈6553600·100²·21³·2·log 2/(log 2)² + 1⌉₊`.

Nothing is a placeholder.  The warm starts are the *stationary* ones (`M = Mw = 1`, the best
possible), the accuracy is `ε = 1/2 < 1` so the `MixesWithin` conclusion is a genuine bound and
not the trivial `ε = 1`, and `λ` is the **exact** average local conductance, so no concession is
made on `hlam`.  The phase-count binder is met with room: `κ = varBudget (1/4) = log(81/80) ≤
1/80`, so `32·22·84²/κ + 1 ≥ 397393920 ≥ 10⁸`.

The exhibited numeric total is `m·t ≤ 2·10²³`, from `t ≤ 2·10¹⁵` — which holds because
`6553600·10⁴·21³·2/log 2 = 1213857792000000/log 2 < 1.76·10¹⁵` by `Real.log_two_gt_d9`.

Note what this witness does **not** claim: it is a witness that the *hypotheses are
satisfiable*, not that `10⁸` phases at `σ ≡ 100` are the schedule any algorithm would run. -/
theorem sampler_step_count_witness :
    ∃ (m0 : ℕ) (K : Set (EuclideanSpace ℝ (Fin 21))) (R sigmax M eps L : ℝ)
      (sig : ℕ → ℝ) (mu : ℕ → Measure (EuclideanSpace ℝ (Fin 21)))
      (Q₀ : Measure (EuclideanSpace ℝ (Fin 21))) (lam Mw : ℝ≥0∞) (t : ℕ),
      MeasurableSet K ∧ Convex ℝ K ∧ volume K ≠ 0 ∧ volume K ≠ ⊤ ∧
      0 ≤ R ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧
      (∀ j, IsProbabilityMeasure (mu j)) ∧
      (∀ j < m0, 0 < sig j) ∧
      (∀ j < m0, 4 ≤ sig j * Real.sqrt ((21 : ℕ) : ℝ)) ∧
      (∀ j < m0, R ≤ 2 * sig j * Real.sqrt ((21 : ℕ) : ℝ)) ∧
      1 ≤ M ∧ 0 < eps ∧ eps < 1 ∧ eps ≤ 1 ∧
      (∀ j < m0, IsWarm (ENNReal.ofReal M) (mu j)
        (ellGaussianProb K (1 / (2 * ((21 : ℕ) : ℝ))) (sig j ^ 2))) ∧
      (∀ j < m0, sig j ≤ sigmax) ∧ 0 < sigmax ∧
      4 ≤ sigmax * Real.sqrt ((21 : ℕ) : ℝ) ∧ 1 ≤ L ∧
      (m0 : ℝ) ≤ 32 * (((21 : ℕ) : ℝ) + 1) * L ^ 2
        / GaussianCooling.varBudget (eps / 2) + 1 ∧
      lam ≤ avgLocalConductance K (1 / (2 * ((21 : ℕ) : ℝ))) ∧ lam ≠ 0 ∧ lam ≠ ⊤ ∧
      IsWarm Mw Q₀ (ellProb K (1 / (2 * ((21 : ℕ) : ℝ)))) ∧
      t = ⌈6553600 * sigmax ^ 2 * (((21 : ℕ) : ℝ)) ^ 3
        * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1⌉₊ ∧
      (∀ j < m0, MixesWithin
        (lazy (speedyMetropolisGaussian K (1 / (2 * ((21 : ℕ) : ℝ))) (sig j ^ 2)))
        (ellGaussianProb K (1 / (2 * ((21 : ℕ) : ℝ))) (sig j ^ 2)) (mu j) t
        (ENNReal.ofReal eps)) ∧
      ((m0 * t : ℕ) : ℝ) ≤ 2 * 10 ^ 10 * (((21 : ℕ) : ℝ) + 1) * (((21 : ℕ) : ℝ)) ^ 3
        * sigmax ^ 2 * L ^ 2 * (1 + (Real.log M + 2 * Real.log (1 / eps))) / eps ^ 2 ∧
      ((m0 * t : ℕ) : ℝ) ≤ 2 * 10 ^ 23 ∧
      ∑ i ∈ Finset.range (m0 * t), ∫⁻ x, (ell K (1 / (2 * ((21 : ℕ) : ℝ))) x)⁻¹
          ∂(iterate (speedyWalk K (1 / (2 * ((21 : ℕ) : ℝ)))) Q₀ i)
        ≤ (m0 : ℝ≥0∞) * (t : ℝ≥0∞) * Mw / lam := by
  classical
  have hcast : ((21 : ℕ) : ℝ) = (21 : ℝ) := by norm_num
  have hδ : (0 : ℝ) < 1 / (2 * ((21 : ℕ) : ℝ)) := by rw [hcast]; norm_num
  have hsqrt21 : Real.sqrt ((21 : ℕ) : ℝ) ^ 2 = ((21 : ℕ) : ℝ) :=
    Real.sq_sqrt (by positivity)
  have h4 : (4 : ℝ) ≤ Real.sqrt ((21 : ℕ) : ℝ) := by
    nlinarith [hsqrt21, Real.sqrt_nonneg ((21 : ℕ) : ℝ), hcast]
  have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog9 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  -- the body
  set K : Set (EuclideanSpace ℝ (Fin 21)) := Metric.ball 0 1 with hKdef
  have hKm : MeasurableSet K := measurableSet_ball
  have hKc : Convex ℝ K := convex_ball _ _
  have hKb : Bornology.IsBounded K := Metric.isBounded_ball
  have hK0 : volume K ≠ 0 := volume_unitBall_ne_zero
  have hKtop : volume K ≠ ⊤ := volume_unitBall_ne_top
  have hKR : ∀ x ∈ K, ‖x‖ ≤ (1 : ℝ) := by
    intro x hx
    rw [hKdef, Metric.mem_ball, dist_zero_right] at hx
    exact hx.le
  -- the Gaussian speedy law is a probability measure
  have hs : (0 : ℝ) < (100 : ℝ) ^ 2 := by norm_num
  haveI hprobG : IsProbabilityMeasure
      (ellGaussianProb K (1 / (2 * ((21 : ℕ) : ℝ))) ((100 : ℝ) ^ 2)) :=
    isProbabilityMeasure_ellGaussianProb
      (ellGaussianMeasure_univ_ne_zero hKm hKc hKb hK0 hδ ((100 : ℝ) ^ 2))
      (ne_top_of_le_ne_top hKtop (ellGaussianMeasure_univ_le hs K _))
  have hwarmG : IsWarm (ENNReal.ofReal (1 : ℝ))
      (ellGaussianProb K (1 / (2 * ((21 : ℕ) : ℝ))) ((100 : ℝ) ^ 2))
      (ellGaussianProb K (1 / (2 * ((21 : ℕ) : ℝ))) ((100 : ℝ) ^ 2)) := by
    intro S _
    exact le_of_eq (by rw [ENNReal.ofReal_one, one_mul])
  -- the uniform speedy law, for the ball-walk half
  have hL0 : ellMeasure K (1 / (2 * ((21 : ℕ) : ℝ))) Set.univ ≠ 0 :=
    ellMeasure_univ_ne_zero hKm hK0 hδ
  have hLtop : ellMeasure K (1 / (2 * ((21 : ℕ) : ℝ))) Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top hKtop (ellMeasure_univ_le K _)
  have hlam0 : avgLocalConductance K (1 / (2 * ((21 : ℕ) : ℝ))) ≠ 0 := by
    rw [avgLocalConductance, ← ellMeasure_univ]
    intro hcon
    rcases ENNReal.div_eq_zero_iff.1 hcon with h | h
    · exact hL0 h
    · exact hKtop h
  have hlamtop : avgLocalConductance K (1 / (2 * ((21 : ℕ) : ℝ))) ≠ ⊤ := by
    rw [avgLocalConductance, ← ellMeasure_univ]
    intro hcon
    rcases ENNReal.div_eq_top.1 hcon with ⟨-, h⟩ | ⟨h, -⟩
    · exact hK0 h
    · exact hLtop h
  -- the variance budget at `ε = 1/2`
  have hκ0 : 0 < GaussianCooling.varBudget ((1 / 2 : ℝ) / 2) :=
    GaussianCooling.varBudget_pos (by norm_num)
  have hκub : GaussianCooling.varBudget ((1 / 2 : ℝ) / 2) ≤ 1 / 80 := by
    rw [GaussianCooling.varBudget]
    have h := Real.log_le_sub_one_of_pos
      (x := 1 + ((1 / 2 : ℝ) / 2) ^ 2 / 5) (by norm_num)
    norm_num at h ⊢
    linarith
  have hm : ((100000000 : ℕ) : ℝ) ≤ 32 * (((21 : ℕ) : ℝ) + 1) * (84 : ℝ) ^ 2
      / GaussianCooling.varBudget ((1 / 2 : ℝ) / 2) + 1 := by
    have hinv : (397393920 : ℝ) ≤ 4967424 / GaussianCooling.varBudget ((1 / 2 : ℝ) / 2) := by
      rw [le_div_iff₀ hκ0]
      nlinarith [hκub]
    have heq : 32 * (((21 : ℕ) : ℝ) + 1) * (84 : ℝ) ^ 2 = 4967424 := by
      rw [hcast]; norm_num
    rw [heq]
    push_cast
    linarith
  -- the per-phase deadline, evaluated
  have hone : (1 : ℝ) / (1 / 2 : ℝ) = 2 := by norm_num
  have hDval : 6553600 * (100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ)) ^ 3
        * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / Real.log 2 ^ 2 + 1
      = 1213857792000000 / Real.log 2 + 1 := by
    rw [Real.log_one, hone, hcast]
    field_simp
    ring
  have hDle : 6553600 * (100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ)) ^ 3
        * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / Real.log 2 ^ 2 + 1
      ≤ ((2000000000000000 : ℕ) : ℝ) := by
    rw [hDval]
    have : (1213857792000000 : ℝ) / Real.log 2 ≤ 1999999999999999 := by
      rw [div_le_iff₀ hlogpos]
      nlinarith [hlog9]
    push_cast
    linarith
  set t : ℕ := ⌈6553600 * (100 : ℝ) ^ 2 * (((21 : ℕ) : ℝ)) ^ 3
      * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / Real.log 2 ^ 2 + 1⌉₊ with htdef
  have htle : (t : ℝ) ≤ 2000000000000000 := by
    have := Nat.ceil_le.2 hDle
    rw [htdef]
    exact_mod_cast this
  -- the three conclusions
  have hmix := mixesWithin_all_phases_kls (n := 21) (m := 100000000)
    (sig := fun _ => (100 : ℝ)) (mu := fun _ => ellGaussianProb K
      (1 / (2 * ((21 : ℕ) : ℝ))) ((100 : ℝ) ^ 2))
    (sigmax := 100) (M := 1) (eps := 1 / 2) (R := 1)
    le_rfl hKm hKc hK0 (by norm_num) hKR (fun _ => hprobG)
    (fun _ _ => by norm_num) (fun _ _ => by nlinarith)
    (fun _ _ => by nlinarith) le_rfl (by norm_num) (by norm_num)
    (fun _ _ => hwarmG) (fun _ _ => le_rfl)
  have hpoly := total_speedy_steps_poly_varBudget (n := 21) (m := 100000000)
    (sigmax := 100) (M := 1) (eps := 1 / 2) (L := 84)
    le_rfl (by norm_num) (by norm_num) (by nlinarith) le_rfl (by norm_num) (by norm_num) hm
  have hball := sum_ballWalk_cost_phases_le (n := 21) le_rfl hKm hK0 hKtop
    (lam := avgLocalConductance K (1 / (2 * ((21 : ℕ) : ℝ)))) (Mw := 1) le_rfl hlam0 hlamtop
    (Q₀ := ellProb K (1 / (2 * ((21 : ℕ) : ℝ)))) (IsWarm.refl _) 100000000 t
  have hnum : ((100000000 * t : ℕ) : ℝ) ≤ 2 * 10 ^ 23 := by
    push_cast
    nlinarith [htle, Nat.cast_nonneg (α := ℝ) t]
  refine ⟨100000000, K, 1, 100, 1, 1 / 2, 84, fun _ => (100 : ℝ),
    fun _ => ellGaussianProb K (1 / (2 * ((21 : ℕ) : ℝ))) ((100 : ℝ) ^ 2),
    ellProb K (1 / (2 * ((21 : ℕ) : ℝ))),
    avgLocalConductance K (1 / (2 * ((21 : ℕ) : ℝ))), 1, t,
    hKm, hKc, hK0, hKtop, by norm_num, hKR, fun _ => hprobG,
    fun _ _ => by norm_num, fun _ _ => by nlinarith, fun _ _ => by nlinarith,
    le_rfl, by norm_num, by norm_num, by norm_num, fun _ _ => hwarmG, fun _ _ => le_rfl,
    by norm_num, by nlinarith, by norm_num, hm, le_rfl, hlam0, hlamtop, IsWarm.refl _,
    htdef, hmix, hpoly, hnum, hball⟩

/-! ### Axiom audit (`CLAUDE.md` §4)

Every theorem of this file, re-checked at elaboration time.  Each must print exactly
`[propext, Classical.choice, Quot.sound]`; anything else — in particular `sorryAx` — means
the file is not finished. -/

section AxiomCheck

#print axioms mixesWithin_lazy_speedyMetropolisGaussian_kls
#print axioms mixesWithin_all_phases_kls
#print axioms total_speedy_steps_le
#print axioms total_speedy_steps_le_generalPhaseCount
#print axioms half_le_log_one_add
#print axioms sq_div_forty_le_varBudget_le_one
#print axioms total_speedy_steps_poly
#print axioms total_speedy_steps_poly_varBudget
#print axioms total_speedy_steps_poly_sqrt_exp
#print axioms sum_ballWalk_cost_phases_le
#print axioms sampler_step_count_witness

end AxiomCheck

end Arlib.MarkovChains
