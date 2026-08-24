/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.GaussianCooling.CouplingRoute
import Arlib.Convexity.OneDimSharp

/-!
# The coupling route for the Gaussian-cooling estimator — with no `hiso` binder

`Arlib/Convexity/GaussianCooling/CouplingRoute.lean` composes the per-sample mixing bound, the
union bound over the `r·m` samples and the total-variation transfer into a statement about the
**success probability** of the Gaussian-cooling volume estimator when its samples come from a
finitely-run Markov chain.  Its two chain-level theorems (file sections 3 and 4 there) were
written before `hiso` was discharged, so each carries the isoperimetric inequality as an
**unproved binder**, quantified over the phase index.

That binder is now proved for convex bodies:
`Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo` (`Arlib/Convexity/OneDimSharp.lean:1040`)
supplies it from `hn hσ hK hKc hKR hKtop hK0` plus the single extra hypothesis
`hRσ : √3·R ≤ 2σ√n`.

This file is the propagation of that discharge to the two chain-level theorems, and nothing
else.  Every declaration is a `theorem`; there is no `def`, `structure`, `class`, `axiom`,
`sorry` or `native_decide` here.  It is the exact analogue, for `CouplingRoute.lean`, of what
`Arlib/MarkovChains/Continuous/MetropolisMixingUncond.lean` is for
`Arlib/MarkovChains/Continuous/MetropolisMixing.lean`.

## What is proved

* `le_measureReal_runMeasure_metropolisGaussian_of_convex` —
  `Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian` (`CouplingRoute.lean:248`)
  with `hiso` gone: the realised `r·m`-sample run of the lazy Metropolis–Gaussian chain succeeds
  with probability at least `q − (r·m)·eps`.
* `le_measureReal_runMeasure_metropolisGaussian_budget_of_convex` —
  `Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian_budget`
  (`CouplingRoute.lean:324`) with `hiso` gone: the same with the step count written from the
  total failure budget `ρ`, exhibiting `log(r·m/ρ)`.
* `exists_couplingRoute_chain_witness` — non-vacuity (`CLAUDE.md` §11) for the **chain layer**,
  which `CouplingRoute.lean` §5 flagged as missing.  See below.

## The conclusions are unchanged

Each theorem below has, character for character, the conclusion of the `hiso`-carrying theorem
it replaces, and the same binders **except**:

* `hiso` is **removed**;
* `hRσ : ∀ i, √3·R ≤ 2·σ i·√n` is **added**, in `hiso`'s binder slot.  It is the `∀ i`-form of
  the one hypothesis `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo` needs beyond those
  already present — a compatibility between the bounding radius of `K` and the Gaussian scale
  of each phase.  It is implied by the usual normalisation `R ≤ σ i·√n`.

Nothing else moves: not the step counts, not `hell`/`hfloor`, not the warm start, not the
schedule hypotheses `hσsch`/`hball`/`hs`, not the estimator binders `hV`/`hgood`.

## What is still carried

`hwarm : ∀ j i, IsWarm (ENNReal.ofReal M) (mu0 j i) …` — a warm start for every one of the
`r·m` chains.  It is data a caller supplies and nothing here proves it in general.  `hgood` —
the exact-law success probability `q` — is likewise a binder; it is proved on the `Ttc` side by
`Ttc.CV.volume_accuracy_of_samples`, and `Arlib/**` may not import `Ttc.*`
(see `CouplingRoute.lean` §3).

## The chain-layer non-vacuity gap, closed

`CouplingRoute.lean` §5 (`:391–398`) certified only the *abstract* layer and said so honestly:
the chain layer additionally carries `hiso`, `hell`, `hfloor` and `hwarm`, and it recorded that
the existing mixing witness `Arlib.MarkovChains.exists_mixesWithin_lazy_metropolisGaussian_witness`
(`MetropolisMixing.lean:397`) uses `K = B(0,1/2) ⊆ ℝ²`, which does **not** contain the unit ball, so it cannot simultaneously
witness `hball : ball 0 1 ⊆ K` (needed by `coolLaw_isProbabilityMeasure` / `chain_pos`).

With `hiso` gone the gap closes, and the fix is a rescaling rather than a new idea.  The mixing
witness's mechanism is "take `δ` at least the diameter of `K`, so that `K ⊆ ball x δ` for every
`x ∈ K` and hence `ell K δ x = vol K / vol (ball x δ)` exactly".  That mechanism is scale
invariant.  Applying it at

    n = 2,  K = B(0,1) ⊆ ℝ²,  δ = 2,  σ = 16√2 (so σ² = 512),  R = 1,  θ = 1/4

gives `hball` by `subset_rfl`, `ell K 2 x = vol(B(0,1))/vol(B(x,2)) = 1/4` because
`vol(B(x,2)) = 4·vol(B(0,1))` in dimension `2`, the operative step `δ = σ/(8√2)` exactly, an
acceptance exponent `−(2·1·2 + 2²)/(2·512) = −1/128` — numerically the *same* exponent as the
`B(0,1/2)` witness — and `hRσ : √3 ≤ 2·16√2·√2 = 64`.  `exists_couplingRoute_chain_witness`
below packages this, and its final conjunct is the conclusion of
`le_measureReal_runMeasure_metropolisGaussian_budget_of_convex` itself.

(The stale caveat in `CouplingRoute.lean`'s own §5 docstring is left untouched: that file is
not edited here.)

## Scope: this is a success-probability statement, and nothing more

The conclusion bounds `μ.real {ω | (1 − acc)·vol ≤ V ω ≤ (1 + acc)·vol}` from below, where `μ`
is the law of the realised `r·m`-sample run.  **It is not a running-time statement.**  It says
nothing about TTC, about the charged cost model, or about any `O(m·n⁴)` bound; no count of
arithmetic operations, oracle calls or samples-per-second appears anywhere in it, and the step
count `t` is the mixing theorem's *hypothesis*, carried through verbatim.  Nothing here bounds
the cost of one Metropolis step, proves that any particular cooling schedule is admissible, or
proves the estimator `V` is the one the algorithm computes.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}
variable {r m : ℕ}

/-! ## 1.  The instantiation, unconditionally

`Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian` (`CouplingRoute.lean:248`)
with its `hiso` binder supplied, phase by phase, by
`Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo`. -/

/-- **Route B, end to end for the Gaussian-cooling estimator — no isoperimetric hypothesis.**

`Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian` with `hiso` discharged by
`Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo`.  The conclusion and every other binder are
unchanged; the single added hypothesis is `hRσ : ∀ i, √3·R ≤ 2·σ i·√n`, which the discharge
needs at each phase and which `R ≤ σ i·√n` implies.

Suppose the estimator `V` on the run space is `acc`-relatively accurate for `vol` with
probability at least `q` when every one of the `r·m` coordinates is drawn from the exact phase
law `coolLaw m σsq K i`.  Suppose each coordinate is instead produced by running the lazy
Metropolis–Gaussian chain for phase `i` from an `M`-warm start `mu0 j i` for `t` steps, with `t`
meeting the mixing theorem's bound at TV budget `eps`.  Then the **realised** run succeeds with
probability at least `q − (r·m)·eps`.

**This is not a running-time statement.**  See the module docstring. -/
theorem le_measureReal_runMeasure_metropolisGaussian_of_convex (hn : 2 ≤ n)
    {σ δ θ : Fin m → ℝ} {R M eps : ℝ}
    (hσpos : ∀ i, 0 < σ i) (hδop : ∀ i, δ i = σ i / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclSpace n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ i, ∀ x ∈ K, ENNReal.ofReal (θ i) ≤ MarkovChains.ell K (δ i) x)
    (hfloor : ∀ i, 1 ≤ 20 * Real.exp (-(2 * R * δ i + δ i ^ 2) / (2 * σ i ^ 2)) * (1 / 4) * θ i)
    (hRσ : ∀ i, Real.sqrt 3 * R ≤ 2 * σ i * Real.sqrt n)
    {mu0 : Fin r → Fin m → Measure (EuclSpace n)}
    [∀ j i, IsProbabilityMeasure (mu0 j i)] (hM : 1 ≤ M)
    (hwarm : ∀ j i, IsWarm (ENNReal.ofReal M) (mu0 j i)
      (Arlib.uniformOn ((volume : Measure (EuclSpace n)).withDensity
        (MarkovChains.gaussianWeight (σ i ^ 2))) K))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * (5120 ^ 2 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2) + 1 ≤ (t : ℝ))
    {σsq : ℕ → ℝ} (hσsch : ∀ j, 0 < σsq j) (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    (hs : ∀ i : Fin m, σ i ^ 2 = σsq (i : ℕ))
    {V : Arlib.Probability.RunSpace (EuclSpace n) r m → ℝ} (hV : Measurable V)
    {vol acc q : ℝ}
    (hgood : q ≤ (Arlib.Probability.runMeasure
        fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)).real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol}) :
    q - (r * m : ℕ) * eps ≤ (Arlib.Probability.runMeasure
        fun (j : Fin r) (i : Fin m) => MarkovChains.iterate
          (MarkovChains.lazy (MarkovChains.metropolisGaussian K (δ i) (σ i ^ 2)))
          (mu0 j i) t).real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol} :=
  le_measureReal_runMeasure_metropolisGaussian hn hσpos hδop hR hK hKc hKR hKtop hK0 hell hfloor
    (fun i => Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo (δ := δ i) hn (hσpos i) hK hKc hKR
      hKtop hK0 (hRσ i))
    hM hwarm heps0 heps1 ht hσsch hball hs hV hgood

/-! ## 2.  The step count from the total failure budget, unconditionally

`Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian_budget`
(`CouplingRoute.lean:324`), likewise. -/

/-- **Route B with the step count written from the failure budget — no isoperimetric
hypothesis.**

`Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian_budget` with `hiso`
discharged; `hRσ : ∀ i, √3·R ≤ 2·σ i·√n` is added and nothing else changes.  To lose at most
`ρ` of success probability across all `r·m` samples it suffices to run each chain for

    t ≥ 4·(5120²·n²·(log M + 2·log(r·m/ρ))/log²2) + 1

steps.  `log(r·m/ρ)` is logarithmic in the sample count and in `1/ρ`; compare Route A's
`R²/(2σᵢ²)`, which is polynomial in `n` (`CouplingRoute.lean` §0).

**Every binder of this theorem is discharged simultaneously by
`exists_couplingRoute_chain_witness` (§3)**, so the statement is not vacuous.

**This is not a running-time statement.**  See the module docstring. -/
theorem le_measureReal_runMeasure_metropolisGaussian_budget_of_convex (hn : 2 ≤ n)
    (hr : 0 < r) (hm : 0 < m)
    {σ δ θ : Fin m → ℝ} {R M ρ : ℝ}
    (hσpos : ∀ i, 0 < σ i) (hδop : ∀ i, δ i = σ i / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclSpace n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ i, ∀ x ∈ K, ENNReal.ofReal (θ i) ≤ MarkovChains.ell K (δ i) x)
    (hfloor : ∀ i, 1 ≤ 20 * Real.exp (-(2 * R * δ i + δ i ^ 2) / (2 * σ i ^ 2)) * (1 / 4) * θ i)
    (hRσ : ∀ i, Real.sqrt 3 * R ≤ 2 * σ i * Real.sqrt n)
    {mu0 : Fin r → Fin m → Measure (EuclSpace n)}
    [∀ j i, IsProbabilityMeasure (mu0 j i)] (hM : 1 ≤ M)
    (hwarm : ∀ j i, IsWarm (ENNReal.ofReal M) (mu0 j i)
      (Arlib.uniformOn ((volume : Measure (EuclSpace n)).withDensity
        (MarkovChains.gaussianWeight (σ i ^ 2))) K))
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ (r * m : ℕ))
    {t : ℕ} (ht : 4 * (5120 ^ 2 * (n : ℝ) ^ 2
        * (Real.log M + 2 * Real.log ((r * m : ℕ) / ρ)) / Real.log 2 ^ 2) + 1 ≤ (t : ℝ))
    {σsq : ℕ → ℝ} (hσsch : ∀ j, 0 < σsq j) (hball : ball (0 : EuclSpace n) 1 ⊆ K)
    (hs : ∀ i : Fin m, σ i ^ 2 = σsq (i : ℕ))
    {V : Arlib.Probability.RunSpace (EuclSpace n) r m → ℝ} (hV : Measurable V)
    {vol acc q : ℝ}
    (hgood : q ≤ (Arlib.Probability.runMeasure
        fun (_ : Fin r) (i : Fin m) => coolLaw m σsq K (i : ℕ)).real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol}) :
    q - ρ ≤ (Arlib.Probability.runMeasure
        fun (j : Fin r) (i : Fin m) => MarkovChains.iterate
          (MarkovChains.lazy (MarkovChains.metropolisGaussian K (δ i) (σ i ^ 2)))
          (mu0 j i) t).real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol} :=
  le_measureReal_runMeasure_metropolisGaussian_budget hn hr hm hσpos hδop hR hK hKc hKR hKtop
    hK0 hell hfloor
    (fun i => Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo (δ := δ i) hn (hσpos i) hK hKc hKR
      hKtop hK0 (hRσ i))
    hM hwarm hρ0 hρ1 ht hσsch hball hs hV hgood

/-! ## 3.  Non-vacuity of the chain layer (`CLAUDE.md` §11)

`CouplingRoute.lean` §5 certified the *abstract* layer (`exists_couplingRoute_witness`) and
flagged the chain layer as uncertified: §3/§4 there additionally carry `hiso`, `hell`, `hfloor`
and `hwarm`, and the existing mixing witness lives on `K = B(0,1/2) ⊆ ℝ²`, which does not
contain the unit ball and therefore cannot also serve `hball : ball 0 1 ⊆ K`.

`hiso` is gone from §1/§2 above, and the other three are met by rescaling the mixing witness:
its mechanism is "take `δ` at least the diameter of `K`, so `K ⊆ ball x δ` for every `x ∈ K`
and hence `ell K δ x = vol K / vol (ball x δ)` exactly", and that is scale invariant. -/

/-- **Non-vacuity of the chain-level coupling route.**

Every hypothesis of `le_measureReal_runMeasure_metropolisGaussian_budget_of_convex` is satisfied
at

    n = 2,  r = m = 1,  K = B(0,1) ⊆ ℝ²,  δ = 2,  σ = 16√2 (so σ² = 512),  R = 1,  θ = 1/4,
    μ₀ = π,  M = 1,  σsq ≡ 512,  ρ = 1/2,  V ≡ 1,  vol = 1,  acc = 0,  q = 1,

and the final conjunct is the conclusion itself, obtained by applying that theorem to the
exhibited data.  The success bound it certifies is `q − ρ = 1/2 > 0`, which the statement
records, so the conclusion is not the trivial `0 ≤ measure`.

*Why this body.*  `hball : ball 0 1 ⊆ K` is `subset_rfl`.  Since `δ = 2` exceeds the diameter of
`K`, `K ⊆ ball x 2` for every `x ∈ K`, so `ell K 2 x = vol K / vol (ball x 2) = 1/4` exactly,
`vol (ball x 2)` being `4·vol (ball 0 1)` in dimension `2`.  The acceptance exponent is
`−(2·1·2 + 2²)/(2·512) = −1/128`, so the floor test reads `20·e^{−1/128}·(1/4)·(1/4) ≥ 1.24 > 1`.
`δ = 2` **is** the operative step `σ/(8√2)` at `σ = 16√2`, not merely below it.  `hRσ` reads
`√3 ≤ 2·16√2·√2 = 64`.  The warm start is the stationary one, `μ₀ = π` with `M = 1`.

*Coverage.*  The conjuncts packaged here are the budget form's.  §1's eps form is covered too,
but only derivatively: `le_measureReal_runMeasure_metropolisGaussian_budget_of_convex` proves
itself by applying it at `eps = ρ/(r·m) = 1/2`, so the exhibited data is an instance of §1 as
well; that instantiation is not restated as a separate conjunct.

*Scope.*  This certifies that the chain-layer statements have a genuine instance.  It is not
evidence for any running-time claim — see the module docstring. -/
theorem exists_couplingRoute_chain_witness :
    ∃ (K : Set (EuclSpace 2)) (σ δ θ : Fin 1 → ℝ) (R M ρ : ℝ)
      (mu0 : Fin 1 → Fin 1 → Measure (EuclSpace 2)) (σsq : ℕ → ℝ) (t : ℕ)
      (V : Arlib.Probability.RunSpace (EuclSpace 2) 1 1 → ℝ) (vol acc q : ℝ),
      (∀ i, 0 < σ i) ∧ (∀ i, δ i = σ i / (8 * Real.sqrt ((2 : ℕ) : ℝ))) ∧ 0 ≤ R ∧
      MeasurableSet K ∧ Convex ℝ K ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧
      volume K ≠ ⊤ ∧ volume K ≠ 0 ∧
      (∀ i, ∀ x ∈ K, ENNReal.ofReal (θ i) ≤ MarkovChains.ell K (δ i) x) ∧
      (∀ i, 1 ≤ 20 * Real.exp (-(2 * R * δ i + δ i ^ 2) / (2 * σ i ^ 2)) * (1 / 4) * θ i) ∧
      (∀ i, Real.sqrt 3 * R ≤ 2 * σ i * Real.sqrt ((2 : ℕ) : ℝ)) ∧
      (∀ j i, IsProbabilityMeasure (mu0 j i)) ∧ 1 ≤ M ∧
      (∀ j i, IsWarm (ENNReal.ofReal M) (mu0 j i)
        (Arlib.uniformOn ((volume : Measure (EuclSpace 2)).withDensity
          (MarkovChains.gaussianWeight (σ i ^ 2))) K)) ∧
      0 < ρ ∧ ρ ≤ ((1 * 1 : ℕ) : ℝ) ∧
      4 * (5120 ^ 2 * (((2 : ℕ)) : ℝ) ^ 2
        * (Real.log M + 2 * Real.log (((1 * 1 : ℕ) : ℝ) / ρ)) / Real.log 2 ^ 2) + 1 ≤ (t : ℝ) ∧
      (∀ j, 0 < σsq j) ∧ ball (0 : EuclSpace 2) 1 ⊆ K ∧
      (∀ i : Fin 1, σ i ^ 2 = σsq (i : ℕ)) ∧ Measurable V ∧
      q ≤ (Arlib.Probability.runMeasure
          fun (_ : Fin 1) (i : Fin 1) => coolLaw 1 σsq K (i : ℕ)).real
        {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol} ∧
      0 < q - ρ ∧
      q - ρ ≤ (Arlib.Probability.runMeasure
          fun (j : Fin 1) (i : Fin 1) => MarkovChains.iterate
            (MarkovChains.lazy (MarkovChains.metropolisGaussian K (δ i) (σ i ^ 2)))
            (mu0 j i) t).real
        {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol} := by
  classical
  set K : Set (EuclSpace 2) := Metric.ball 0 1 with hKdef
  have hcast2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have hsqrt2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hσpos : (0 : ℝ) < 16 * Real.sqrt 2 := by linarith
  have hσsq : (16 * Real.sqrt 2 : ℝ) ^ 2 = 512 := by rw [mul_pow, hsq2]; norm_num
  have hspos : (0 : ℝ) < (16 * Real.sqrt 2 : ℝ) ^ 2 := by rw [hσsq]; norm_num
  -- `δ = 2` **is** the operative step at `σ = 16√2`
  have hδop : (2 : ℝ) = 16 * Real.sqrt 2 / (8 * Real.sqrt ((2 : ℕ) : ℝ)) := by
    rw [hcast2]
    field_simp
    norm_num
  -- geometry of `K = B(0,1)`
  have hK0 : volume K ≠ 0 := (Metric.measure_ball_pos volume 0 (by norm_num)).ne'
  have hKtop : volume K ≠ ⊤ := measure_ball_lt_top.ne
  have hKc : Convex ℝ K := convex_ball _ _
  have hKR : ∀ x ∈ K, ‖x‖ ≤ 1 := by
    intro x hx
    rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hx
    exact hx.le
  have hball : ball (0 : EuclSpace 2) 1 ⊆ K := by rw [hKdef]
  -- `vol (ball x 2) = 4 · vol K`, and hence `ell K 2 x = 1/4` on `K`
  have hb2 : volume (Metric.ball (0 : EuclSpace 2) 2)
      = ENNReal.ofReal 4 * volume K := by
    rw [hKdef, Measure.addHaar_ball_of_pos volume 0 (by norm_num : (0 : ℝ) < 2),
      finrank_euclideanSpace_fin]
    norm_num
  have hb2ne : ENNReal.ofReal 4 * volume K ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨by simp, hK0⟩
  have hb2top : ENNReal.ofReal 4 * volume K ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKtop
  have hell : ∀ x ∈ K, MarkovChains.ell K (2 : ℝ) x = ENNReal.ofReal (1 / 4) := by
    intro x hx
    have hxnorm : ‖x‖ < 1 := by
      rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hx; exact hx
    have hsub : K ⊆ Metric.ball x 2 := by
      intro y hy
      rw [hKdef, Metric.mem_ball, dist_eq_norm, sub_zero] at hy
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖y - x‖ ≤ ‖y‖ + ‖x‖ := norm_sub_le _ _
        _ < 2 := by linarith
    have hnum : volume K = ENNReal.ofReal (1 / 4) * (ENNReal.ofReal 4 * volume K) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      norm_num
    rw [MarkovChains.ell_apply, Set.inter_eq_self_of_subset_right hsub,
      MarkovChains.volume_ball_eq x 2, hb2]
    nth_rewrite 1 [hnum]
    exact ENNReal.mul_div_cancel_right hb2ne hb2top
  -- the acceptance floor at `σ² = 512`: `a = e^{-1/128} ≥ 127/128`, and `20·a/16 ≥ 1.24`
  have hexpge : (127 : ℝ) / 128
      ≤ Real.exp (-(2 * (1 : ℝ) * 2 + (2 : ℝ) ^ 2) / (2 * (16 * Real.sqrt 2 : ℝ) ^ 2)) := by
    have h := Real.add_one_le_exp (-(1 : ℝ) / 128)
    have heq : -(2 * (1 : ℝ) * 2 + (2 : ℝ) ^ 2) / (2 * (16 * Real.sqrt 2 : ℝ) ^ 2)
        = -(1 : ℝ) / 128 := by rw [hσsq]; norm_num
    rw [heq]; linarith
  have hfloor : (1 : ℝ) ≤ 20
      * Real.exp (-(2 * (1 : ℝ) * 2 + (2 : ℝ) ^ 2) / (2 * (16 * Real.sqrt 2 : ℝ) ^ 2))
      * (1 / 4) * (1 / 4) := by linarith
  -- `hRσ`: `√3 ≤ 2·(16√2)·√2 = 64`
  have hsqrt3 : Real.sqrt 3 ≤ 2 := by
    have h := Real.sqrt_le_sqrt (show (3 : ℝ) ≤ 4 by norm_num)
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hRσ : Real.sqrt 3 * (1 : ℝ)
      ≤ 2 * (16 * Real.sqrt 2 : ℝ) * Real.sqrt ((2 : ℕ) : ℝ) := by
    rw [hcast2]
    have hcalc : (2 : ℝ) * (16 * Real.sqrt 2) * Real.sqrt 2 = 64 := by
      have h : (2 : ℝ) * (16 * Real.sqrt 2) * Real.sqrt 2 = 32 * Real.sqrt 2 ^ 2 := by ring
      rw [h, hsq2]; norm_num
    rw [hcalc]; linarith
  -- the stationary start
  haveI hprob := MarkovChains.isProbabilityMeasure_uniformOn_gaussianWeight
    (K := K) measurableSet_ball hK0 hKtop hspos
  have hwarm : ∀ _j _i : Fin 1, IsWarm (ENNReal.ofReal 1) (Arlib.uniformOn
      ((volume : Measure (EuclSpace 2)).withDensity
        (MarkovChains.gaussianWeight ((16 * Real.sqrt 2 : ℝ) ^ 2))) K) (Arlib.uniformOn
      ((volume : Measure (EuclSpace 2)).withDensity
        (MarkovChains.gaussianWeight ((16 * Real.sqrt 2 : ℝ) ^ 2))) K) := by
    intro _ _ S _
    exact le_of_eq (by rw [ENNReal.ofReal_one, one_mul])
  -- the schedule, and the exact-law success probability at `V ≡ 1`, `vol = 1`, `acc = 0`
  have hσsch : ∀ _j : ℕ, (0 : ℝ) < 512 := fun _ => by norm_num
  have hcool : ∀ (_ : Fin 1) (i : Fin 1),
      IsProbabilityMeasure (coolLaw 1 (fun _ => (512 : ℝ)) K (i : ℕ)) :=
    fun _ i => coolLaw_isProbabilityMeasure hσsch hball hKtop _
  have hPM : IsProbabilityMeasure (Arlib.Probability.runMeasure
      fun (_ : Fin 1) (i : Fin 1) => coolLaw 1 (fun _ => (512 : ℝ)) K (i : ℕ)) :=
    @Arlib.Probability.isProbabilityMeasure_runMeasure 1 1 (EuclSpace 2) _
      (fun (_ : Fin 1) (i : Fin 1) => coolLaw 1 (fun _ => (512 : ℝ)) K (i : ℕ)) hcool
  have hsetuniv : {ω : Arlib.Probability.RunSpace (EuclSpace 2) 1 1 |
      (1 - (0 : ℝ)) * 1 ≤ (fun _ => (1 : ℝ)) ω ∧ (fun _ => (1 : ℝ)) ω ≤ (1 + (0 : ℝ)) * 1}
      = Set.univ := by
    ext ω; simp
  have hgood : (1 : ℝ) ≤ (Arlib.Probability.runMeasure
      fun (_ : Fin 1) (i : Fin 1) => coolLaw 1 (fun _ => (512 : ℝ)) K (i : ℕ)).real
      {ω | (1 - (0 : ℝ)) * 1 ≤ (fun _ => (1 : ℝ)) ω ∧ (fun _ => (1 : ℝ)) ω ≤ (1 + (0 : ℝ)) * 1} := by
    rw [hsetuniv, MeasureTheory.measureReal_def, hPM.measure_univ, ENNReal.toReal_one]
  obtain ⟨t, ht⟩ := exists_nat_ge (4 * (5120 ^ 2 * (((2 : ℕ)) : ℝ) ^ 2
    * (Real.log 1 + 2 * Real.log (((1 * 1 : ℕ) : ℝ) / (1 / 2 : ℝ))) / Real.log 2 ^ 2) + 1)
  -- with `hiso` gone, the exhibited data yields the conclusion itself
  have hmain := le_measureReal_runMeasure_metropolisGaussian_budget_of_convex
    (n := 2) (r := 1) (m := 1) (σ := fun _ => 16 * Real.sqrt 2) (δ := fun _ => (2 : ℝ))
    (θ := fun _ => (1 / 4 : ℝ)) (R := 1) (M := 1) (ρ := 1 / 2)
    (mu0 := fun _ _ => Arlib.uniformOn ((volume : Measure (EuclSpace 2)).withDensity
      (MarkovChains.gaussianWeight ((16 * Real.sqrt 2 : ℝ) ^ 2))) K)
    (σsq := fun _ => (512 : ℝ)) (t := t) (V := fun _ => (1 : ℝ)) (vol := 1) (acc := 0) (q := 1)
    le_rfl Nat.one_pos Nat.one_pos (fun _ => hσpos) (fun _ => hδop) (by norm_num)
    measurableSet_ball hKc hKR hKtop hK0 (fun _ x hx => (hell x hx).ge) (fun _ => hfloor)
    (fun _ => hRσ) le_rfl hwarm (by norm_num) (by norm_num) ht hσsch hball
    (fun _ => hσsq) measurable_const hgood
  exact ⟨K, fun _ => 16 * Real.sqrt 2, fun _ => (2 : ℝ), fun _ => (1 / 4 : ℝ), 1, 1, 1 / 2,
    fun _ _ => Arlib.uniformOn ((volume : Measure (EuclSpace 2)).withDensity
      (MarkovChains.gaussianWeight ((16 * Real.sqrt 2 : ℝ) ^ 2))) K,
    fun _ => (512 : ℝ), t, fun _ => (1 : ℝ), 1, 0, 1,
    fun _ => hσpos, fun _ => hδop, by norm_num, measurableSet_ball, hKc, hKR, hKtop, hK0,
    fun _ x hx => (hell x hx).ge, fun _ => hfloor, fun _ => hRσ, fun _ _ => hprob, le_rfl,
    hwarm, by norm_num, by norm_num, ht, hσsch, hball, fun _ => hσsq, measurable_const,
    hgood, by norm_num, hmain⟩

end Arlib.GaussianCooling

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian_of_convex
#print axioms Arlib.GaussianCooling.le_measureReal_runMeasure_metropolisGaussian_budget_of_convex
#print axioms Arlib.GaussianCooling.exists_couplingRoute_chain_witness
