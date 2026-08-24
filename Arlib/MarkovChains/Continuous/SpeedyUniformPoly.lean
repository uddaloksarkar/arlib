/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.SpeedyToUniform
import Arlib.MarkovChains.Continuous.EllFloor

/-!
# A polynomial-time uniform sampler on a general convex body, assembled

`Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn` (`SpeedyToUniform.lean:226`)
takes three inputs — an isoperimetric inequality `hiso` for `ellProb K δ`, a warm start
`hwarm`, and a smoothness certificate `hsmooth : IsSmooth K δ s` — and concludes that the
lazy speedy walk mixes to `Arlib.uniformOn volume K` within total variation
`ε + s/(1-s)` in `conductanceMixingTime M (min (1/32) (κδ/(256n))) ε` steps.

**This file discharges `hsmooth` for the whole class of convex bodies containing the unit
ball**, using `Arlib.MarkovChains.isSmooth_of_ball_subset` (`EllFloor.lean:549`), and then
tunes `δ` so that the resulting bias is a named number rather than an opaque `s/(1-s)`.
`hiso` and `hwarm` are carried verbatim as binders; nothing here attempts either.

## What is proved

* `smoothBias_le` — pure `ℝ≥0∞` arithmetic: `(1 - (1-δ)ⁿ)/(1-δ)ⁿ ≤ 2nδ` once `2nδ ≤ 1`.
* `mixesWithin_lazy_speedyWalk_uniformOn_of_ball_subset` — the composition with `hsmooth`
  discharged; tolerance `ofReal ε + (1 - ofReal((1-δ)ⁿ)) / ofReal((1-δ)ⁿ)`.
* `mixesWithin_lazy_speedyWalk_uniformOn_bias` — with `2nδ ≤ η ≤ 1`, tolerance
  `ofReal ε + ofReal η`.
* `mixesWithin_lazy_speedyWalk_uniformOn_poly` — **the honest final form**: a single
  tolerance `ofReal ρ`, at `δ = ρ/(4n)` and `ε = ρ/2`.
* `mixesWithin_lazy_speedyWalk_uniformOn_poly_unitBall` — the non-vacuity witness.

## The cost of discharging smoothness: `δ ≪ 1/n`, and why it is `n` and not `√n`

`isSmooth_of_ball_subset` certifies `IsSmooth K δ (1 - ofReal((1-δ)ⁿ))`, i.e.
`s = 1 - (1-δ)ⁿ`.  By Bernoulli (`one_sub_nsmul_le_pow_one_sub`) this is `≈ nδ` for small
`δ`, so the bias `s/(1-s)` is small **only when `δ ≪ 1/n`** — `smoothBias_le` makes this
exact: `s/(1-s) ≤ 2nδ` whenever `2nδ ≤ 1`.  Asking for bias `η` therefore forces
`δ ≈ η/(2n)`.

The step count of `mixesWithin_lazy_speedyWalk` is `O(φ⁻² log(M/ε))` with
`φ = min(1/32, κδ/(256n))`, i.e. `δ` enters as `δ⁻²`.  Substituting `δ = η/(2n)`:

    φ = min(1/32, κη/(512 n²)),      steps = O( n⁴ / (κ²η²) · log(M/ε) ).

And with `ε = η = ρ/2` (`..._poly`), `δ = ρ/(4n)`:

    φ = min(1/32, κρ/(1024 n²)),     steps = O( n⁴ / (κ²ρ²) · log(M/ρ) ).

Both errors are paid once; the bias is a property of the *stationary* law `ellProb K δ` and
does not decay with `t` (see `SpeedyToUniform.lean`'s module docstring).

### Comparison with the literature — the `n⁴` is two `√n`s worse than the book

Lee's optimization/sampling book (`ball_walk.tex`) obtains, from an `O(1)`-warm start, a
mixing rate of `O(n²/ψ²)` for a convex body containing the unit ball with isoperimetric
coefficient `ψ` (`thm:ballwalk_warmstart`), at step size `δ = s/(4√n)`.  Our `n⁴/(κ²ρ²)` is
worse by exactly two factors of `n`, and **both losses are inherited from upstream lemmas,
not created by this composition**:

1. *Smoothness.*  `ball_walk.tex`'s `lem:avg-local-conductance` says
   `vol{ℓ ≥ 3/4} ≥ (1 - 2δ√n)·vol K`: its smoothness-type input degrades as `δ√n`, where
   `isSmooth_of_ball_subset` degrades as `1 - (1-δ)ⁿ = Θ(δn)`.  So the book can work at
   `δ = Θ(1/√n)` where this file's bias route forces `δ = Θ(η/n)`: one factor `√n` in `δ`,
   hence `n` in `φ⁻²`.  (The comparison is of the *scaling of the two inputs*, not a claim
   that the book's lemma yields bias `η` through this file's route — it does not: its `3/4`
   floor leaves an `Θ(1)` bias, and the book removes that bias by `s`-conductance and the
   holding-time correspondence rather than by a sharper `IsSmooth`.)
2. *Conductance.*  `ball_walk.tex` states the conductance of the speedy walk is `Ω(1/(nD))`,
   i.e. `Ω(ψ/n)` with no `δ` in it, while
   `Arlib.MarkovChains.conductance_speedyWalk_ge` (`SpeedyWalk.lean:973`) certifies
   `min(1/16, κ·(δ/(2n))/64)` — linear in `δ`, and with the one-step-overlap scale taken as
   `δ/(2n)` rather than the book's `δ/√n`.  That is the second `√n`.

Sharpening either upstream lemma improves this file's exponent mechanically, with no change
to the statements below.  The exponent `4` is therefore an artefact of the two proved inputs,
and the *polynomiality* — the point of the exercise — is unaffected.

## Scope — read before quoting anything from this file

Every theorem here is a **Markov-chain mixing statement**: after `t` steps the law of the
lazy speedy walk is within total variation `ρ` of `Arlib.uniformOn volume K`.  It is
**not**:

* a running-time claim about any algorithm — no oracle-call count, no bit complexity, and
  in particular nothing of the form `O(m·n⁴)`; `t` counts abstract kernel applications;
* a statement about the TTC pipeline, volume computation, or lattice counting;
* unconditional — `hiso` (isoperimetry for `ellProb K δ`) and `hwarm` (an `M`-warm start
  for `ellProb K δ`) are hypotheses, supplied by the caller.

**No `def`, `structure`, `class`, `axiom` or named `Prop` is introduced in this file.**
Every declaration is a `theorem`, and every hypothesis is an inline binder.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. The arithmetic of the smoothness bias

`isSmooth_of_ball_subset` produces `s = 1 - ofReal((1-δ)ⁿ)`, hence `1 - s = ofReal((1-δ)ⁿ)`
and a bias `(1 - ofReal((1-δ)ⁿ))/ofReal((1-δ)ⁿ)`.  One lemma turns that into `2nδ`. -/

/-- **The smoothness bias of a convex body containing the unit ball is at most `2nδ`.**

For `0 < δ` with `2nδ ≤ 1`,

    (1 - (1-δ)ⁿ) / (1-δ)ⁿ  ≤  2nδ.

This is the `δ ≪ 1/n` tradeoff in one line: the numerator is `Θ(nδ)` by Bernoulli
(`one_sub_nsmul_le_pow_one_sub`), and the hypothesis `2nδ ≤ 1` keeps the denominator above
`1/2`.  It is pure `ℝ≥0∞` arithmetic — no measure theory, no geometry.

The unconditional companion `tvLe_ellProb_uniformOn_unitBall_le` (`SpeedyToUniform.lean:337`)
proves the same estimate inside a total-variation statement about the unit ball; this is the
statement about numbers, usable for any `K`. -/
theorem smoothBias_le (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδn : 2 * (n : ℝ) * δ ≤ 1) :
    (1 - ENNReal.ofReal ((1 - δ) ^ n)) / ENNReal.ofReal ((1 - δ) ^ n)
      ≤ ENNReal.ofReal (2 * (n : ℝ) * δ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hδ1 : δ ≤ 1 := by nlinarith
  have hber : 1 - (n : ℝ) * δ ≤ (1 - δ) ^ n := one_sub_nsmul_le_pow_one_sub hδ1 n
  have hhalf : (1 : ℝ) / 2 ≤ (1 - δ) ^ n := by nlinarith
  have hpow0 : (0 : ℝ) < (1 - δ) ^ n := by linarith
  have hc0 : ENNReal.ofReal ((1 - δ) ^ n) ≠ 0 := by
    simpa using (ENNReal.ofReal_pos.2 hpow0).ne'
  rw [ENNReal.div_le_iff hc0 ENNReal.ofReal_ne_top]
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal ((1 - δ) ^ n)
      = ENNReal.ofReal (1 - (1 - δ) ^ n) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ hpow0.le]
  rw [hsub, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (n : ℝ)) hδ.le)
    (by linarith : (0:ℝ) ≤ 2 * (1 - δ) ^ n - 1)]

/-! ## 2. The composition, with smoothness discharged

`isSmooth_of_ball_subset` is the only new input; `hiso` and `hwarm` are passed through. -/

/-- **The lazy speedy walk on ANY convex body containing the unit ball mixes to the uniform
measure**, with the smoothness hypothesis of `mixesWithin_lazy_speedyWalk_uniformOn`
discharged internally.

For convex, bounded, measurable `K ⊇ B(0,1)` and `0 < δ < 1`, in

    conductanceMixingTime M (min (1/32) (κ·δ/(256·n))) ε

steps from an `M`-warm start the law of the walk is within total variation

    ε + (1 - (1-δ)ⁿ)/(1-δ)ⁿ

of `Arlib.uniformOn volume K`.  The bias term is `isSmooth_of_ball_subset`'s
`s = 1 - (1-δ)ⁿ` fed through `s ↦ s/(1-s)`, already simplified: `1 - s = ofReal((1-δ)ⁿ)`
because `ofReal((1-δ)ⁿ) ≤ 1`.

`volume K ≠ 0` comes from `B(0,1) ⊆ K` and `volume K ≠ ⊤` from `hbdd`, so neither is a
binder.  What remains open is exactly `hiso` and `hwarm`.  See the module docstring for the
`δ ≪ 1/n` reading of the bias and its `δ⁻²` price. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_of_ball_subset (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    (hbdd : Bornology.IsBounded K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d * ellProb K δ A * ellProb K δ B
        ≤ ellProb K δ ((K \ A) \ B))
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellProb K δ))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M (min (1 / 32) (kappa * δ / (256 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (speedyWalk K δ)) (Arlib.uniformOn volume K) mu0 t
      (ENNReal.ofReal eps
        + (1 - ENNReal.ofReal ((1 - δ) ^ n)) / ENNReal.ofReal ((1 - δ) ^ n)) := by
  have hK0 : volume K ≠ 0 := fun h => volume_unitBall_ne_zero (measure_mono_null hball h)
  have hKtop : volume K ≠ ⊤ := hbdd.measure_lt_top.ne
  have hle : ENNReal.ofReal ((1 - δ) ^ n) ≤ 1 :=
    ENNReal.ofReal_le_one.2 (pow_le_one₀ (by linarith) (by linarith))
  have h := mixesWithin_lazy_speedyWalk_uniformOn hn hK hconv hK0 hKtop hδ hkappa hiso
    (isSmooth_of_ball_subset hK hconv hball hδ hδ1) hM hwarm heps ht
  rwa [ENNReal.sub_sub_cancel ENNReal.one_ne_top hle] at h

/-! ## 3. Fixing `δ` to make the bias a named number -/

/-- **The same, with the bias named `η`.**  Choosing `δ` small enough that `2nδ ≤ η ≤ 1`
turns the conclusion into a clean two-term total-variation bound

    ε + η

with the step count `conductanceMixingTime M (min (1/32) (κδ/(256n))) ε` unchanged.  The
canonical choice is `δ = η/(2n)`, giving `φ = min(1/32, κη/(512 n²))` and

    O( n⁴ / (κ² η²) · log(M/ε) )   steps

— see the module docstring for why the `n⁴` (rather than the book's `n²`) is inherited from
`isSmooth_of_ball_subset` and `conductance_speedyWalk_ge`, not produced here.

`hδeta` is the whole content of the `δ ≪ 1/n` tradeoff: shrinking the bias by a factor `c`
shrinks `δ` by `c` and multiplies the step count by `c²`. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_bias (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    (hbdd : Bornology.IsBounded K) {δ eta : ℝ} (hδ : 0 < δ) (heta1 : eta ≤ 1)
    (hδeta : 2 * (n : ℝ) * δ ≤ eta)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d * ellProb K δ A * ellProb K δ B
        ≤ ellProb K δ ((K \ A) \ B))
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellProb K δ))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M (min (1 / 32) (kappa * δ / (256 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (speedyWalk K δ)) (Arlib.uniformOn volume K) mu0 t
      (ENNReal.ofReal eps + ENNReal.ofReal eta) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hδn : 2 * (n : ℝ) * δ ≤ 1 := le_trans hδeta heta1
  have hδ1 : δ < 1 := by nlinarith
  refine (mixesWithin_lazy_speedyWalk_uniformOn_of_ball_subset hn hK hconv hball hbdd hδ hδ1
    hkappa hiso hM hwarm heps ht).mono_err ?_
  exact add_le_add le_rfl ((smoothBias_le hn hδ hδn).trans
    (ENNReal.ofReal_le_ofReal hδeta))

/-! ## 4. The honest final theorem: one tolerance `ρ` -/

/-- **A polynomial-time uniform sampler on a general convex body — the honest final form.**

Let `K ⊆ ℝⁿ` be measurable, convex, bounded, with `B(0,1) ⊆ K`, let `0 < ρ ≤ 1`, and set

    δ = ρ/(4n),        φ = min(1/32, κ·(ρ/(4n))/(256·n)) = min(1/32, κρ/(1024 n²)).

Then from any `M`-warm start for `ellProb K δ`, after

    t ≥ conductanceMixingTime M φ (ρ/2)      =  O( φ⁻² log(M/ρ) )
                                             =  O( n⁴/(κ²ρ²) · log(M/ρ) )

steps, the law of the lazy speedy walk is within total variation `ρ` of
`Arlib.uniformOn volume K`.  Polynomial in `n`, `1/κ`, `1/ρ` and `log M`.

The tolerance is split evenly: `ρ/2` of mixing error (costing `log(1/ρ)`) and `ρ/2` of
smoothness bias (costing `(1/ρ)²`, via `δ = ρ/(4n)`).  The two halves have completely
different prices; the `δ⁻²` half dominates.

**Remaining binders.**  Exactly two hypotheses are unproved here and supplied by the caller:

* `hiso` — the isoperimetric inequality for `ellProb K (ρ/(4n))` at coefficient `κ`;
* `hwarm` — an `M`-warm start for `ellProb K (ρ/(4n))`.

Everything else (measurability, convexity, `B(0,1) ⊆ K`, boundedness, positivity of `ρ`)
is a geometric fact about `K` or a numeric side condition.  In particular `IsSmooth` is
**discharged**, by `isSmooth_of_ball_subset`.

**Scope.**  This is a mixing statement about a Markov kernel, not a running-time claim; see
the module docstring. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_poly (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    (hbdd : Bornology.IsBounded K) {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d
          * ellProb K (rho / (4 * (n : ℝ))) A * ellProb K (rho / (4 * (n : ℝ))) B
        ≤ ellProb K (rho / (4 * (n : ℝ))) ((K \ A) \ B))
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellProb K (rho / (4 * (n : ℝ))))) {t : ℕ}
    (ht : conductanceMixingTime M
        (min (1 / 32) (kappa * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) (rho / 2) ≤ t) :
    MixesWithin (lazy (speedyWalk K (rho / (4 * (n : ℝ)))))
      (Arlib.uniformOn volume K) mu0 t (ENNReal.ofReal rho) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hδ : 0 < rho / (4 * (n : ℝ)) := by positivity
  have hnne : (n : ℝ) ≠ 0 := hn0.ne'
  have hδeta : 2 * (n : ℝ) * (rho / (4 * (n : ℝ))) ≤ rho / 2 := by
    have heq : 2 * (n : ℝ) * (rho / (4 * (n : ℝ))) = rho / 2 := by
      field_simp
      ring
    exact heq.le
  have h := mixesWithin_lazy_speedyWalk_uniformOn_bias hn hK hconv hball hbdd hδ
    (eta := rho / 2) (by linarith) hδeta hkappa hiso hM hwarm (by linarith) ht
  refine h.mono_err ?_
  rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ## 5. Non-vacuity (`CLAUDE.md` §11)

The theorems of §§2–4 quantify over convex bodies together with two unproved hypotheses.
If no `K` met the geometric binders the statements would be empty.  The unit ball meets all
of them, and additionally lets `hwarm` be discharged at `M = 1` by starting the chain at its
own stationary law (`IsWarm.refl`), so the witness below leaves **only `hiso`** open. -/

/-- **Non-vacuity witness: the unit ball.**

Every binder of `mixesWithin_lazy_speedyWalk_uniformOn_poly` except `hiso` is discharged
here, concretely:

| binder | discharged by |
| --- | --- |
| `hK : MeasurableSet K` | `measurableSet_ball` |
| `hconv : Convex ℝ K` | `convex_ball` |
| `hball : B(0,1) ⊆ K` | `subset_rfl` |
| `hbdd : Bornology.IsBounded K` | `Metric.isBounded_ball` |
| `hM : 1 ≤ M` | `le_rfl` at `M = 1` |
| `hwarm` | `IsWarm.refl` — the start *is* `ellProb K δ` |
| `hsmooth` (already internal) | `isSmooth_of_ball_subset` |

**What it does not cover.**  `hiso` — the isoperimetric inequality for
`ellProb (B(0,1)) (ρ/(4n))` — remains a hypothesis of this witness too.  It is the one
input of the whole chain that is proved nowhere in this file, and this witness makes no
claim that it holds; it certifies only that the *other* hypotheses are jointly satisfiable
on a genuine convex body, so that `..._poly` is not vacuously composed.  A warm start with
`M > 1` (the interesting case for an algorithm, where `mu0` is something one can actually
sample) is likewise not exhibited: `M = 1` here is the degenerate end.

This mirrors `mixesWithin_lazy_speedyWalk_unitBall` (`SpeedyWalk.lean:1320`), which does the
same job one level down, for the target measure `ellProb` rather than `uniformOn`. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn_poly_unitBall (hn : 1 ≤ n)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B →
      A ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
      B ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d
          * ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) (rho / (4 * (n : ℝ))) A
          * ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) (rho / (4 * (n : ℝ))) B
        ≤ ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) (rho / (4 * (n : ℝ)))
            ((Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 \ A) \ B))
    {t : ℕ}
    (ht : conductanceMixingTime 1
        (min (1 / 32) (kappa * (rho / (4 * (n : ℝ))) / (256 * (n : ℝ)))) (rho / 2) ≤ t) :
    MixesWithin
      (lazy (speedyWalk (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
        (rho / (4 * (n : ℝ)))))
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) (rho / (4 * (n : ℝ)))) t
      (ENNReal.ofReal rho) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hδ : 0 < rho / (4 * (n : ℝ)) := by positivity
  haveI : IsProbabilityMeasure
      (ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) (rho / (4 * (n : ℝ)))) :=
    isProbabilityMeasure_ellProb_of_volume measurableSet_ball volume_unitBall_ne_zero
      volume_unitBall_ne_top hδ
  refine mixesWithin_lazy_speedyWalk_uniformOn_poly hn measurableSet_ball (convex_ball _ _)
    subset_rfl Metric.isBounded_ball hrho hrho1 hkappa hiso le_rfl ?_ ht
  simp

/-! ## Axiom check -/

#print axioms smoothBias_le
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_of_ball_subset
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_bias
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_poly
#print axioms mixesWithin_lazy_speedyWalk_uniformOn_poly_unitBall

end Arlib.MarkovChains
