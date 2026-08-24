/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.SpeedyWalk
import Arlib.MarkovChains.Continuous.PointwiseRoute

/-!
# From the speedy walk's stationary measure to the uniform measure on `K`

`Arlib/MarkovChains/Continuous/SpeedyWalk.lean` proves that the lazy speedy walk on a convex
body mixes in `O((n/(κδ))² log(M/ε))` steps — **polynomially** in `n`, with no
local-conductance hypothesis — but to `Arlib.MarkovChains.ellProb K δ`, the law with density
proportional to the local conductance `ell` on `K`, not to `Arlib.uniformOn volume K`.  Its
module docstring records the consequence: nothing there composes with
`Arlib.PointwiseRoute.theorem2_of_mixesWithin`, which consumes a mixing bound to the
*uniform* measure.

This file closes that gap by the arithmetic route.  The whole content is one comparison:

    TVLe (ellProb K δ) (uniformOn volume K) (s / (1 - s))          under `IsSmooth K δ s`,

after which `Arlib.TVLe.trans` gives a mixing bound to the uniform measure at tolerance
`ε + s/(1-s)`, which is exactly the shape Kannan–Vempala Theorem 2 consumes.

## The arithmetic, in one line

Write `V = vol(K)`, `L = ∫_K ell`, and for a measurable `S`, `a = ∫_{S∩K} ell` and
`b = vol(S ∩ K)`.  Then `ellProb K δ S = a/L` and `uniformOn volume K S = b/V`, and

    a/L ≤ b/L ≤ b/((1-s)V) = (b/V)·(1-s)⁻¹ = (b/V)·(1 + s/(1-s)) ≤ b/V + s/(1-s),

using, in order: `ell ≤ 1` on `S ∩ K` (`ellMeasure_le_volume_inter`); `IsSmooth K δ s`, i.e.
`(1-s)·V ≤ L`; the identity `(1-s)⁻¹ = 1 + s·(1-s)⁻¹` valid for `s < 1`; and `b/V ≤ 1`.  The
reverse inequality is free for probability measures (`Arlib.tvLe_of_forall_le`).  The
argument is `inv_mul_le_div_add_div` below: a statement about five extended nonnegative
reals, with no measure theory in it and no side conditions on `V` at all.

Note what is **not** used: `Arlib.MarkovChains.ellMeasure_add_volume_le` (the local-deficit
≤ global-deficit lemma) is not needed.  The one-sided bound plus `tvLe_of_forall_le` already
gives both directions, and the one-sided bound needs only `ell ≤ 1` and `IsSmooth`.

## Main results

* `Arlib.MarkovChains.inv_mul_le_div_add_div` — the `ℝ≥0∞` arithmetic, standalone.
* `Arlib.MarkovChains.tvLe_ellProb_uniformOn` — **the bridge**:
  `TVLe (ellProb K δ) (uniformOn volume K) (s/(1-s))` for a `(δ,s)`-smooth `K` of positive
  finite volume.
* `Arlib.MarkovChains.mixesWithin_lazy_speedyWalk_uniformOn` — **the composed result**: the
  lazy speedy walk mixes *to the uniform measure on `K`* within `ε + s/(1-s)`, in the same
  polynomial step count `conductanceMixingTime M (min (1/32) (κδ/(256n))) ε`.
* `Arlib.MarkovChains.theorem2_of_lazy_speedyWalk` — the Kannan–Vempala Theorem 2 conclusion,
  produced by the speedy walk.  This is the composition `SpeedyWalk.lean` declined to write.
* `Arlib.MarkovChains.tvLe_ellProb_uniformOn_unitBall`,
  `Arlib.MarkovChains.tvLe_ellProb_uniformOn_unitBall_le` — the non-vacuity witness, and its
  quantitative form: for the unit ball and `δ ≤ 1/(2n)` the bridge costs at most `2nδ` in
  total variation.

## Honest accounting of what the bridge costs

`s` is not free.  `IsSmooth K δ s` says `(1-s)·vol(K) ≤ ∫_K ell`, and the only proved
witness is `isSmooth_unitBall`: `s = 1 - (1-δ)ⁿ` for the unit ball.  So the bridge is
informative exactly when `δ = O(1/n)` — `tvLe_ellProb_uniformOn_unitBall_le` makes this
precise, `TV ≤ 2nδ` for `δ ≤ 1/(2n)` — and it is vacuous (`s ≥ 1`, bound `⊤`) for large `δ`.
That is the same regime `vol3_journal.tex:904` works in, and it is *not* an extra assumption
beyond what the conductance bound already needs: `conductance_speedyWalk_ge` certifies
`min(1/16, κδ/(128n))`, which is itself only useful for small `δ`.

### The bias does not decay with time — read this before quoting a step count

`ellProb K δ` is a *fixed* law, at total-variation distance `≈ s` from uniform whatever the
chain does.  Running longer shrinks the `ε` of `mixesWithin_lazy_speedyWalk` — logarithmically
cheaply, `O(φ⁻² log(M/ε))` — but leaves `s/(1-s)` untouched.  The only way to shrink the bias
is to shrink `δ`, and `δ` sits in `φ = min(1/32, κδ/(256n))`, i.e. in the step count as `δ⁻²`.
So the two error terms of `mixesWithin_lazy_speedyWalk_uniformOn` have **completely different
prices**:

| tolerance asked of … | cost in steps |
| --- | --- |
| the mixing term `ε` | `log(1/ε)` |
| the bias term `s/(1-s)` | `(1/s)²`, via `δ ≈ s/(2n)` (`tvLe_ellProb_uniformOn_unitBall_le`) |

The consequence for `theorem2_of_lazy_speedyWalk` is concrete and unfavourable.  Its `htol`
forces `s/(1-s) ≤ θ/V` with `V = vol(K)`, so on the unit ball one needs `δ ≲ θ/(2nV)` and the
step count is `Θ((n/(κδ))²) = Θ((n²V/(κθ))²)` — **polynomial in `V`, hence exponential in the
bit-length of `V`.**  Contrast `Arlib.PointwiseRoute.conductanceMixingTime_inv_volume_le`,
whose point is that the *mixing* half of the same tolerance costs only `log V`.

So: Route A closes the composition, and the polynomial-in-`n` step count of
`mixesWithin_lazy_speedyWalk` survives verbatim into
`mixesWithin_lazy_speedyWalk_uniformOn` **at a fixed tolerance** — which is what a plain
uniform sampler on `K` wants.  It does *not* survive into a KV97 lattice-counting tolerance
`θ/vol(K)`, where the `δ⁻²` defeats it.  That is precisely why Cousins–Vempala do not use
this route but the holding-time correspondence (`Geom(ell(x))` holding times, mean `1/ell`,
whose product with the density `∝ ell` is *exactly* uniform, with **no** `s` at all).  Route
B is therefore still worth formalising; what this file establishes is that Route A is not a
substitute for it at small tolerances, only at constant ones.

What is genuinely assumed, and by whom:

* `IsSmooth K δ s` is a **hypothesis** of `tvLe_ellProb_uniformOn`, supplied by the caller.
  It is a pre-existing predicate of `BallWalk.lean` with a proved non-degenerate witness
  (`isSmooth_unitBall`); this file adds no predicate of its own.
* the isoperimetric inequality `hiso` for `ellProb K δ` remains the one unproved input of
  `mixesWithin_lazy_speedyWalk`, and is passed through verbatim.

## Scope

**No `def`, `structure`, `class` or named `Prop` is introduced anywhere in this file.**  Every
declaration below is a `theorem`.  In particular there is no predicate asserting a
total-variation bound, an isoperimetric inequality, a conductance bound, or the smallness of
`vol(K) - ∫_K ell`: the first is *proved* from `IsSmooth`, the second is an inline `∀`
hypothesis, the third is imported from `SpeedyWalk.lean`, and the fourth is `IsSmooth`
itself, consumed and not restated.
-/

namespace Arlib.MarkovChains

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## 1. The arithmetic

One lemma about five extended nonnegative reals.  It is the whole of Route A. -/

/-- **The comparison of two normalised measures, as pure `ℝ≥0∞` arithmetic.**

If `a ≤ b ≤ V` and `(1 - s)·V ≤ L`, then

    L⁻¹ · a  ≤  b/V + s/(1 - s).

Read `a = ∫_{S∩K} ell`, `b = vol(S∩K)`, `L = ∫_K ell`, `V = vol(K)`: the hypotheses are
`ell ≤ 1` and `IsSmooth K δ s`, and the conclusion is
`ellProb K δ S ≤ uniformOn volume K S + s/(1-s)`.

**No side conditions on `V` or `L`.**  If `s ≥ 1` the right-hand side is `⊤` (the truncated
`1 - s` is `0`, and `s/0 = ⊤` since `s ≠ 0`) and the claim is trivial; otherwise `1 - s` is
invertible and the chain in the module docstring applies.  At `V = 0` we get `b = 0` and
`b/V = 0`, and at `V = ⊤` we get `b/V = 0`; both are absorbed by `ENNReal.div_le_of_le_mul`,
which needs nothing. -/
theorem inv_mul_le_div_add_div {a b L V s : ℝ≥0∞} (hab : a ≤ b) (hbV : b ≤ V)
    (hsm : (1 - s) * V ≤ L) : L⁻¹ * a ≤ b / V + s / (1 - s) := by
  rcases le_or_gt 1 s with hs1 | hs1
  · -- `1 - s = 0` and `s ≠ 0`, so the slack is `⊤`.
    have hc : (1 : ℝ≥0∞) - s = 0 := tsub_eq_zero_of_le hs1
    have hs0 : s ≠ 0 := (lt_of_lt_of_le zero_lt_one hs1).ne'
    rw [hc, ENNReal.div_zero hs0, add_top]
    exact le_top
  · -- `1 - s` is a genuine unit.
    have hcs : (1 : ℝ≥0∞) - s + s = 1 := tsub_add_cancel_of_le hs1.le
    have hc0 : (1 : ℝ≥0∞) - s ≠ 0 := (tsub_pos_of_lt hs1).ne'
    have hctop : (1 : ℝ≥0∞) - s ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
    have hcinv : ((1 : ℝ≥0∞) - s)⁻¹ = 1 + s * ((1 : ℝ≥0∞) - s)⁻¹ := by
      calc ((1 : ℝ≥0∞) - s)⁻¹ = ((1 - s) + s) * ((1 : ℝ≥0∞) - s)⁻¹ := by rw [hcs, one_mul]
        _ = (1 - s) * (1 - s)⁻¹ + s * (1 - s)⁻¹ := by rw [add_mul]
        _ = 1 + s * ((1 : ℝ≥0∞) - s)⁻¹ := by rw [ENNReal.mul_inv_cancel hc0 hctop]
    have hbV1 : b / V ≤ 1 := ENNReal.div_le_of_le_mul (by rwa [one_mul])
    rw [div_eq_mul_inv s (1 - s)]
    calc L⁻¹ * a ≤ ((1 - s) * V)⁻¹ * b :=
          mul_le_mul' (ENNReal.inv_le_inv.mpr hsm) hab
      _ = ((1 : ℝ≥0∞) - s)⁻¹ * (b / V) := by
          rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hctop), div_eq_mul_inv]
          ring
      _ = (1 + s * ((1 : ℝ≥0∞) - s)⁻¹) * (b / V) := by rw [← hcinv]
      _ = b / V + (s * ((1 : ℝ≥0∞) - s)⁻¹) * (b / V) := by rw [add_mul, one_mul]
      _ ≤ b / V + (s * ((1 : ℝ≥0∞) - s)⁻¹) * 1 := by gcongr
      _ = b / V + s * ((1 : ℝ≥0∞) - s)⁻¹ := by rw [mul_one]

/-! ## 2. The bridge -/

/-- **The stationary measure of the speedy walk is within `s/(1-s)` of the uniform measure**,
for a `(δ, s)`-smooth body of positive finite volume:

    TVLe (ellProb K δ) (uniformOn volume K) (s / (1 - s)).

This is the statement `SpeedyWalk.lean`'s §12 says follows "by arithmetic alone" from
`ellMeasure_le_volume_inter` and `Arlib.MarkovChains.IsSmooth`, and declines to prove.  Here
it is.  The proof is `inv_mul_le_div_add_div` applied setwise, plus `Arlib.tvLe_of_forall_le`
for the reverse direction.

`IsSmooth K δ s` is consumed, never asserted; `isSmooth_unitBall` is its proved witness, and
`tvLe_ellProb_uniformOn_unitBall_le` below turns that witness into a concrete bound. -/
theorem tvLe_ellProb_uniformOn {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {δ : ℝ} (hδ : 0 < δ) {s : ℝ≥0∞}
    (hs : IsSmooth K δ s) :
    TVLe (ellProb K δ) (Arlib.uniformOn volume K) (s / (1 - s)) := by
  haveI : IsProbabilityMeasure (ellProb K δ) :=
    isProbabilityMeasure_ellProb_of_volume hK hK0 hKtop hδ
  haveI : IsProbabilityMeasure (Arlib.uniformOn volume K) :=
    Arlib.isProbabilityMeasure_uniformOn volume hK0 hKtop
  refine Arlib.tvLe_of_forall_le fun S hS => ?_
  rw [ellProb, Measure.smul_apply, smul_eq_mul, Arlib.uniformOn_apply volume hK hS]
  refine inv_mul_le_div_add_div (ellMeasure_le_volume_inter K δ hS)
    (measure_mono Set.inter_subset_right) ?_
  rw [ellMeasure_univ]
  exact hs

/-! ## 3. The composed mixing statement

`SpeedyWalk.lean`'s `mixesWithin_lazy_speedyWalk` plus §2, through `Arlib.TVLe.trans`. -/

/-- **The lazy speedy walk on a convex, `(δ, s)`-smooth body mixes to the UNIFORM measure on
`K`**, within total variation `ε + s/(1-s)`, in

    conductanceMixingTime M (min (1/32) (κ·δ/(256·n))) ε

steps — `O((n/(κδ))² log(M/ε))`, polynomial in `n`.

This is `mixesWithin_lazy_speedyWalk` with its target measure moved from `ellProb K δ` to
`Arlib.uniformOn volume K` at a cost of `s/(1-s)` in the tolerance and **no cost at all in
the step count**.  The chain from a geometric hypothesis to a uniform sampler is closed:

* `hiso` (isoperimetry for `ellProb K δ`) → `conductance_speedyWalk_ge` → the step count;
* `hsmooth` (`IsSmooth K δ s`) → `tvLe_ellProb_uniformOn` → the change of target.

The bias `s/(1-s)` is **not** reduced by taking `t` larger; only `δ` reduces it, and `δ`
costs `δ⁻²` steps.  See the module docstring.

Both inputs are hypotheses of *this* theorem, written out inline; neither is asserted
anywhere.  `hwarm` is warmness relative to `ellProb K δ`, the measure the chain is actually
reversible for — it is not restated for the uniform measure, which would be a different and
unproved assumption. -/
theorem mixesWithin_lazy_speedyWalk_uniformOn (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {δ : ℝ} (hδ : 0 < δ)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d * ellProb K δ A * ellProb K δ B
        ≤ ellProb K δ ((K \ A) \ B))
    {s : ℝ≥0∞} (hsmooth : IsSmooth K δ s)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellProb K δ))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M (min (1 / 32) (kappa * δ / (256 * (n : ℝ)))) eps ≤ t) :
    MixesWithin (lazy (speedyWalk K δ)) (Arlib.uniformOn volume K) mu0 t
      (ENNReal.ofReal eps + s / (1 - s)) :=
  TVLe.trans
    (mixesWithin_lazy_speedyWalk hn hK hconv hK0 hKtop hδ hkappa hiso hM hwarm heps ht)
    (tvLe_ellProb_uniformOn hK hK0 hKtop hδ hsmooth)

/-! ## 4. Kannan–Vempala Theorem 2, from the speedy walk

The composition `SpeedyWalk.lean` deliberately did not write, now that its missing input —
a total-variation bound between `ellProb K δ` and `Arlib.uniformOn volume K` — exists. -/

open Arlib.Lattice.Rounding in
/-- **Kannan–Vempala Theorem 2's conclusion, delivered by the lazy speedy walk.**

For every lattice point `x`, with `V = vol(K)` and `E` the escape mass,

    (1 - (E + θ))/V  ≤  Pr[rnd p = x]  ≤  (1 + θ)/V,

where `p` is the state of the lazy speedy walk after
`conductanceMixingTime M (min (1/32) (κδ/(256n))) ε` steps from an `M`-warm start.

The tolerance hypothesis `htol : ofReal ε + s/(1-s) ≤ ofReal (θ/V)` is the sampler contract
of `Arlib.PointwiseRoute.theorem2_of_mixesWithin`: **ask the walk for total variation
`θ/vol(K)`**, which costs only `log V` extra steps
(`Arlib.PointwiseRoute.conductanceMixingTime_inv_volume_le`).  Note that it forces
`s/(1-s) ≤ θ/V`, i.e. the smoothness parameter must itself be at the sampler's tolerance —
the bridge of §2 is a real constraint on `δ`, not a free lunch.

This is the end of the chain: geometric hypotheses (`hconv`, `hiso`, `hsmooth`) in, the KV97
Theorem 2 window out.  **But read the "bias does not decay with time" section of the module
docstring before quoting a cost.**  The step count is polynomial in `n` for fixed `δ`, and
`htol` forces `δ ≲ θ/(nV)`, so the count is polynomial in `V = vol(K)` and therefore
exponential in the bit-length of `V`.  This theorem is the honest composition, not a
polynomial-time sampler for the lattice-counting tolerance. -/
theorem theorem2_of_lazy_speedyWalk (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hconv : Convex ℝ K)
    (hK0 : volume K ≠ 0) (hKtop : volume K ≠ ⊤) {δ : ℝ} (hδ : 0 < δ)
    {kappa : ℝ} (hkappa : 0 < kappa)
    (hiso : ∀ d : ℝ, 0 < d → ∀ A B : Set (EuclideanSpace ℝ (Fin n)),
      MeasurableSet A → MeasurableSet B → A ⊆ K → B ⊆ K →
      (∀ u ∈ A, ∀ v ∈ B, d ≤ dist u v) →
      ENNReal.ofReal kappa * ENNReal.ofReal d * ellProb K δ A * ellProb K δ B
        ≤ ellProb K δ ((K \ A) \ B))
    {s : ℝ≥0∞} (hsmooth : IsSmooth K δ s)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (ellProb K δ))
    {eps : ℝ} (heps : 0 < eps) {t : ℕ}
    (ht : conductanceMixingTime M (min (1 / 32) (kappa * δ / (256 * (n : ℝ)))) eps ≤ t)
    {V E theta : ℝ} (hVK : (volume K).toReal = V) (htheta : 0 ≤ theta)
    (htol : ENNReal.ofReal eps + s / (1 - s) ≤ ENNReal.ofReal (theta / V))
    {x : EuclideanSpace ℝ (Fin n)} (hesc : ∫ p in Kᶜ, prodTent x p ≤ E) :
    (1 - (E + theta)) / V
        ≤ ∫ p, prodTent x p ∂(iterate (lazy (speedyWalk K δ)) mu0 t) ∧
      ∫ p, prodTent x p ∂(iterate (lazy (speedyWalk K δ)) mu0 t) ≤ (1 + theta) / V :=
  Arlib.PointwiseRoute.theorem2_of_mixesWithin hK hK0 hKtop hVK htheta
    ((mixesWithin_lazy_speedyWalk_uniformOn hn hK hconv hK0 hKtop hδ hkappa hiso hsmooth hM
      hwarm heps ht).mono_err htol)
    hesc

/-! ## 5. Non-vacuity: the bridge on the unit ball

`CLAUDE.md` §11.  A `TVLe … (s/(1-s))` whose only instances have `s ≥ 1` would be the
statement `TVLe … ⊤`, which `Arlib.tvLe_top` already gives for free.  The unit ball,
`(δ, 1-(1-δ)ⁿ)`-smooth by `isSmooth_unitBall`, shows the bound is finite and — for
`δ ≤ 1/(2n)` — small. -/

/-- **The bridge, instantiated on the unit ball.**  `isSmooth_unitBall` gives
`s = 1 - (1-δ)ⁿ`, hence `1 - s = (1-δ)ⁿ` and the total-variation bound
`(1 - (1-δ)ⁿ)/(1-δ)ⁿ`. -/
theorem tvLe_ellProb_uniformOn_unitBall [NeZero n] {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    TVLe (ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ)
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      ((1 - ENNReal.ofReal ((1 - δ) ^ n)) / ENNReal.ofReal ((1 - δ) ^ n)) := by
  have hle : ENNReal.ofReal ((1 - δ) ^ n) ≤ 1 :=
    ENNReal.ofReal_le_one.2 (pow_le_one₀ (by linarith) (by linarith))
  have h := tvLe_ellProb_uniformOn (K := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
    measurableSet_ball volume_unitBall_ne_zero volume_unitBall_ne_top hδ
    (isSmooth_unitBall hδ hδ1)
  rwa [ENNReal.sub_sub_cancel ENNReal.one_ne_top hle] at h

/-- **Bernoulli's inequality in the form the bound needs**: `1 - n·δ ≤ (1-δ)ⁿ` for
`δ ≤ 1`. -/
theorem one_sub_nsmul_le_pow_one_sub {δ : ℝ} (hδ1 : δ ≤ 1) (m : ℕ) :
    1 - (m : ℝ) * δ ≤ (1 - δ) ^ m := by
  have h := one_add_mul_le_pow (a := -δ) (by linarith) m
  calc 1 - (m : ℝ) * δ = 1 + (m : ℝ) * (-δ) := by ring
    _ ≤ (1 + -δ) ^ m := h
    _ = (1 - δ) ^ m := by ring_nf

/-- **The bridge is quantitatively useful on the unit ball**: for `0 < δ` with
`2·n·δ ≤ 1`, the stationary measure of the speedy walk is within total variation `2·n·δ` of
the uniform measure on the ball.

So the bound of `tvLe_ellProb_uniformOn` is not merely finite: choosing `δ = θ/(2nV)` makes
it as small as the sampler contract of `theorem2_of_lazy_speedyWalk` demands, at the price of
the `δ⁻²` already present in the step count.  The regime `δ = O(1/n)` is exactly the one
`vol3_journal.tex:904` works in. -/
theorem tvLe_ellProb_uniformOn_unitBall_le [NeZero n] {δ : ℝ} (hδ : 0 < δ)
    (hδn : 2 * (n : ℝ) * δ ≤ 1) :
    TVLe (ellProb (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) δ)
      (Arlib.uniformOn volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1))
      (ENNReal.ofReal (2 * (n : ℝ) * δ)) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne n)
  have hδ1 : δ ≤ 1 := by nlinarith
  -- `(1-δ)ⁿ ≥ 1 - nδ ≥ 1/2`
  have hber : 1 - (n : ℝ) * δ ≤ (1 - δ) ^ n := one_sub_nsmul_le_pow_one_sub hδ1 n
  have hhalf : (1 : ℝ) / 2 ≤ (1 - δ) ^ n := by nlinarith
  have hpow0 : (0 : ℝ) < (1 - δ) ^ n := by linarith
  refine (tvLe_ellProb_uniformOn_unitBall hδ hδ1).mono ?_
  -- `(1 - c)/c ≤ 2nδ` where `c = ofReal ((1-δ)ⁿ)`
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

/-! ## Axiom check -/

#print axioms inv_mul_le_div_add_div
#print axioms tvLe_ellProb_uniformOn
#print axioms mixesWithin_lazy_speedyWalk_uniformOn
#print axioms theorem2_of_lazy_speedyWalk
#print axioms tvLe_ellProb_uniformOn_unitBall
#print axioms one_sub_nsmul_le_pow_one_sub
#print axioms tvLe_ellProb_uniformOn_unitBall_le

end Arlib.MarkovChains
