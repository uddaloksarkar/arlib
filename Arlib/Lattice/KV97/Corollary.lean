/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Lattice.KV97.Theorem2
import Arlib.Probability.Rejection

/-!
# Kannan–Vempala, *Sampling Lattice Points*: the rejection-sampling corollary

> Draw `p` from an almost-uniform distribution on the inflated polytope `P'`,
> round it, and repeat until the rounded point lands in `P`. The point that comes
> out is almost uniform on `P ∩ ℤⁿ`:
> `(1 − δ)/N ≤ Pr[output = x] ≤ (1 + δ)/N` for every `x ∈ P ∩ ℤⁿ`, `N = |P ∩ ℤⁿ|`.

This is `cor:linf` (`sections/proof-appendix.tex:159`), the statement that lets
`GenerateSamples` be realised: it is exactly the shape `eq:almostuniform`
(`sections/related.tex:21`) assumes. `Arlib.KV97.cor_linf` and
`Arlib.KV97.cor_linf_tuned` are the theorems.

## What the rejection step does, arithmetically

`Arlib.KV97.theorem2` pins each unnormalised weight
`w x = Pr[rnd p = x] = ∫_{P'} f p · prodTent x p dp` into a window,

```
(1 − ε)(1 − E) / V  ≤  w x  ≤  (1 + ε) / V,        V = Vol(P'),
```

where `ε` is the sampler's pointwise deviation from uniform and `E` bounds the
escape mass. Conditioning on acceptance replaces `w x` by `w x / ∑_y w y`, and
`Arlib.Rejection.ratio_bounds_of_window` turns the window into

```
(1 − ε)(1 − E) / ((1 + ε)·N)  ≤  w x / ∑ w  ≤  (1 + ε) / ((1 − ε)(1 − E)·N).
```

`V` has cancelled — that is the whole point of rejecting, and it is why the
enormous and unknown volume of `P'` never has to be estimated. Everything below
is the job of putting that window into the `(1 ± δ)/N` shape the caller wants.

## The honest `δ`, and where the paper is optimistic

**Step 1** (`Arlib.KV97.ratio_bounds_of_loss`). For `0 ≤ ε`, `0 ≤ E` and
`ε + E ≤ 1/2`,

```
δ = 4·(ε + E).
```

Both halves are proved from scratch as scalar facts
(`Arlib.KV97.one_sub_four_le_window`, `Arlib.KV97.window_le_one_add_four`); the
upper one is *tight at the boundary*, `(1+ε)/((1−ε)(1−E)) = 1 + 4(ε+E)` exactly
at `ε = 1/2, E = 0`. So `4` cannot be lowered without shrinking the admissible
range of `ε + E`.

**Step 2** (`Arlib.KV97.ratio_bounds_tuned`). The paper's tuning takes the
sampler's deviation to be `ε/4` and the escape to be
`exp(−(cOf ε)²/2) = ε/4` (`Arlib.KV97.exp_cOf`), so the total loss is
`lossOf (cOf ε) (ε/4) = ε/2` (`Arlib.KV97.lossOf_cOf`). Step 1 applied verbatim
gives `δ = 4·(ε/4 + ε/4) = 2ε` on both sides; going back to the raw window and
computing at the tuned point sharpens the *lower* half and leaves the upper half
where it was, so the truth is asymmetric:

```
lower bound:  (1 − ε)/N          — the paper's constant, valid for all 0 < ε ≤ 1
upper bound:  (1 + 2ε)/N         — twice the paper's constant
```

The lower side is unconditionally as good as advertised: `(1−ε/4)²/(1+ε/4) ≥ 1−ε`
for every `ε ≥ 0` (`Arlib.KV97.tuned_lower`), with room to spare. The upper side
is where the paper is optimistic. The exact requirement for the paper's
`(1 + ε)/N` is

```
(1 + ε/4)/(1 − ε/4)²  ≤  1 + ε   ⟺   ε² − 7ε + 4 ≥ 0   ⟺   ε ≤ (7 − √33)/2 ≈ 0.6277,
```

so `Arlib.KV97.ratio_bounds_tuned_sharp` recovers `(1 ± ε)/N` verbatim under the
extra hypothesis `ε ≤ 5/8`, and **`ε > (7−√33)/2` genuinely breaks it**: at
`ε = 1` the true upper bound is `1.25/0.5625 = 2.22…/N`, not `2/N`.

This is a consequence of the correction recorded in
`Arlib/Lattice/KV97/Theorem2.lean`, not a new error. The printed proof of
`cor:linf` divides by an upper bound of `1/V`; with the honest two-sided window
the numerator carries a `(1 + ε/4)` as well, and that extra factor is exactly the
gap. Recorded in `AUDIT-KV97.md`.

## Non-vacuity (`CLAUDE.md` §11)

Two witnesses, both proved here.

* `Arlib.KV97.exists_uniform_weights`: at `ε = E = 0` the window collapses to
  `w j = 1/V` for every `j`, which satisfies both hypotheses, and its normalised
  value is **exactly** `1/N`. So the conclusion at `δ = 0` is the genuine uniform
  distribution and not an empty statement.
* `Arlib.KV97.exists_pointwiseAlmostUniform`: the density hypothesis of step 3 is
  inhabited at `ε = 0` by the exactly-uniform density
  (`Arlib.KV97.PointwiseAlmostUniform.uniform`).

**`E ≥ 1` is excluded, and must be.** If the escape mass could be `≥ 1` the lower
bound `(1−ε)(1−E)/V` would be `≤ 0`, the weights would no longer be pinned away
from `0`, the acceptance probability could vanish and the ratio bound would
degenerate. Every statement here therefore forces `E < 1`: the raw window
(`Arlib.KV97.ratio_window_of_loss`) assumes it outright, and the headline's
`0 ≤ ε`, `ε + E ≤ 1/2` give `E ≤ 1/2 < 1` (`Arlib.KV97.escape_lt_one`). At the
tuned point `E = ε/4 ≤ 1/4`.

## Scope

What is *not* proved here: that the rejection loop terminates as a stochastic
process, and that the conditional law of the output is the normalised weight
vector. The first is `Arlib.Rejection.sum_pos` in spirit — positivity of the
acceptance mass follows from the window, since `∑ w ≥ N(1−ε)(1−E)/V > 0` — and
the second is the definitional content of `Arlib.condOn`. Neither is packaged
against the concrete measure here; the corollary is stated about the normalised
weights, which is what the downstream interface consumes.
-/

namespace Arlib.KV97

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-! ## Step 1a: the two scalar inequalities -/

/-- **Lower half of `δ = 4(ε+E)`:** `1 − 4(ε+E) ≤ (1−ε)(1−E)/(1+ε)`.

Cross-multiplying leaves `0 ≤ 2ε + 3E + 4ε² + 5εE`, so this half needs only
`ε, E ≥ 0` — no upper bound on `ε + E` at all, and there is a lot of slack. The
true lower constant is nearer `2(ε+E)`; `4` is carried only so that both halves
of the headline quote the same `δ`. -/
theorem one_sub_four_le_window {ε E : ℝ} (hε : 0 ≤ ε) (hE : 0 ≤ E) :
    1 - 4 * (ε + E) ≤ (1 - ε) * (1 - E) / (1 + ε) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg hε hE, sq_nonneg ε]

/-- **Upper half of `δ = 4(ε+E)`:** `(1+ε)/((1−ε)(1−E)) ≤ 1 + 4(ε+E)` when
`ε + E ≤ 1/2`.

This is the half that fixes the constant. Cross-multiplied it reads
`0 ≤ 2ε + 3E − 4ε² − 7εE − 4E² + 4ε²E + 4εE²`, which is driven by
`4(ε+E)² ≤ 2(ε+E)` — precisely the hypothesis `ε + E ≤ 1/2` — and it is an
**equality** at `ε = 1/2, E = 0`, where both sides are `3`. So `4` is the
smallest constant that works over the whole range `ε + E ≤ 1/2`. -/
theorem window_le_one_add_four {ε E : ℝ} (hε : 0 ≤ ε) (hE : 0 ≤ E)
    (hθ : ε + E ≤ 1 / 2) :
    (1 + ε) / ((1 - ε) * (1 - E)) ≤ 1 + 4 * (ε + E) := by
  have hpos : (0:ℝ) < (1 - ε) * (1 - E) := by nlinarith
  rw [div_le_iff₀ hpos]
  nlinarith [mul_nonneg hε hE,
    mul_nonneg (add_nonneg hε hE) (show (0:ℝ) ≤ 1 / 2 - (ε + E) by linarith),
    mul_nonneg (mul_nonneg hε hE) (add_nonneg hε hE)]

/-! ## Step 1b: the raw window -/

/-- **The normalised-weight window, unsimplified.**

Weights pinned to `[(1−ε)(1−E)/V, (1+ε)/V]` — the exact window
`Arlib.KV97.theorem2` delivers — normalise into

```
(1−ε)(1−E)/((1+ε)·N)  ≤  w i / ∑ w  ≤  (1+ε)/((1−ε)(1−E)·N).
```

`V` cancels. This is `Arlib.Rejection.ratio_bounds_of_window` at
`a = 1 − (1−ε)(1−E)` and `b = ε`, and it is the last statement in this file that
loses nothing; every later bound is a readability trade against it.

`E < 1` is a hypothesis and cannot be dropped: at `E ≥ 1` the lower end of the
window is `≤ 0`, the weights are no longer bounded away from `0`, and `∑ w` may
be `0` — see the module docstring. -/
theorem ratio_window_of_loss [Nonempty ι] (w : ι → ℝ) {V ε E : ℝ} (hV : 0 < V)
    (hε : ε < 1) (hE : E < 1)
    (hlow : ∀ i, (1 - ε) * (1 - E) / V ≤ w i)
    (hhigh : ∀ i, w i ≤ (1 + ε) / V) (i : ι) :
    (1 - ε) * (1 - E) / ((1 + ε) * (Fintype.card ι : ℝ)) ≤ w i / (∑ j, w j) ∧
      w i / (∑ j, w j) ≤ (1 + ε) / ((1 - ε) * (1 - E) * (Fintype.card ι : ℝ)) := by
  have hprod : (0:ℝ) < (1 - ε) * (1 - E) := mul_pos (by linarith) (by linarith)
  have ha : 1 - (1 - ε) * (1 - E) < 1 := by linarith
  have hlow' : ∀ i, (1 - (1 - (1 - ε) * (1 - E))) / V ≤ w i := by
    intro i; simpa only [sub_sub_cancel] using hlow i
  have := Rejection.ratio_bounds_of_window w hV ha hlow' hhigh i
  simpa only [sub_sub_cancel] using this

/-! ## Step 1c: the headline, `δ = 4(ε+E)` -/

/-- **Step 1 headline: the abstract rejection corollary.**

Let `w : ι → ℝ` be nonnegative weights on a nonempty finite index type with
`N = Fintype.card ι`, and suppose that for every `i`

```
(1 − ε)(1 − E)/V  ≤  w i  ≤  (1 + ε)/V,
```

with `V > 0`, `0 ≤ ε`, `0 ≤ E` and `ε + E ≤ 1/2`. Then every normalised weight is
within a multiplicative `1 ± δ` of uniform on `ι`, at

```
δ = 4·(ε + E).
```

**This is not the paper's `δ = ε`,** and the discrepancy is real rather than an
artefact of a lossy proof: the upper half is attained (see
`Arlib.KV97.window_le_one_add_four`). The paper reaches `ε` only by tuning `ε`
and `E` down to `ε/4` each first — that is step 2,
`Arlib.KV97.ratio_bounds_tuned`, where the honest answer is `(1−ε, 1+2ε)`.

`ε + E ≤ 1/2` is the standing hypothesis; it is what makes `1/(1−ε−E)`
controllable, and it forces `E ≤ 1/2 < 1` (`Arlib.KV97.escape_lt_one`), without
which the statement degenerates. -/
theorem ratio_bounds_of_loss [Nonempty ι] (w : ι → ℝ) {V ε E : ℝ} (hV : 0 < V)
    (hε : 0 ≤ ε) (hE : 0 ≤ E) (hθ : ε + E ≤ 1 / 2)
    (hlow : ∀ i, (1 - ε) * (1 - E) / V ≤ w i)
    (hhigh : ∀ i, w i ≤ (1 + ε) / V) (i : ι) :
    (1 - 4 * (ε + E)) / (Fintype.card ι : ℝ) ≤ w i / (∑ j, w j) ∧
      w i / (∑ j, w j) ≤ (1 + 4 * (ε + E)) / (Fintype.card ι : ℝ) := by
  have hN : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨hlo, hhi⟩ :=
    ratio_window_of_loss w hV (by linarith) (by linarith) hlow hhigh i
  rw [← div_div] at hlo hhi
  refine ⟨le_trans ?_ hlo, le_trans hhi ?_⟩
  · gcongr
    exact one_sub_four_le_window hε hE
  · gcongr
    exact window_le_one_add_four hε hE hθ

/-! ## Step 2a: the tuned scalar inequalities -/

/-- **The tuned lower bound is the paper's, for every `ε ≥ 0`:**
`1 − ε ≤ (1−ε/4)²/(1+ε/4)`.

Cross-multiplied this is `0 ≤ ε/4 + 5ε²/16`, so it holds with no upper
restriction on `ε` whatsoever, and with slack: the left side is really
`1 − 3ε/4 + O(ε²)`. -/
theorem tuned_lower {ε : ℝ} (hε : 0 ≤ ε) :
    1 - ε ≤ (1 - ε / 4) * (1 - ε / 4) / (1 + ε / 4) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith [sq_nonneg ε]

/-- **The tuned upper bound, at the constant that survives all of `(0,1]`:**
`(1+ε/4)/(1−ε/4)² ≤ 1 + 2ε` for `0 ≤ ε ≤ 1`.

Cross-multiplied and cleared of denominators this is `0 ≤ ε(20 − 15ε + 2ε²)`,
comfortable on `[0,1]` where the bracket is at least `7`. Compare
`Arlib.KV97.tuned_upper_sharp`, which gets the paper's `1 + ε` but only up to
`ε ≈ 0.6277`. -/
theorem tuned_upper {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 + ε / 4) / ((1 - ε / 4) * (1 - ε / 4)) ≤ 1 + 2 * ε := by
  have hpos : (0:ℝ) < (1 - ε / 4) * (1 - ε / 4) := by nlinarith
  rw [div_le_iff₀ hpos]
  nlinarith [mul_nonneg hε (show (0:ℝ) ≤ 1 - ε by linarith), sq_nonneg ε,
    mul_nonneg hε (sq_nonneg ε)]

/-- **The paper's constant, and the exact range in which it is true:**
`(1+ε/4)/(1−ε/4)² ≤ 1 + ε` for `0 ≤ ε ≤ 5/8`.

Cross-multiplying and clearing denominators reduces this to `0 ≤ ε(4 − 7ε + ε²)`,
i.e. to `ε² − 7ε + 4 ≥ 0`, whose relevant root is `(7 − √33)/2 ≈ 0.62771`. So the
claim is **false** for `ε` above that threshold and the hypothesis is not an
artefact of the proof. `5/8 = 0.625` is the convenient rational just underneath;
at `ε = 5/8` the polynomial is `(5/8)·(1/64) > 0`, only barely. -/
theorem tuned_upper_sharp {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 5 / 8) :
    (1 + ε / 4) / ((1 - ε / 4) * (1 - ε / 4)) ≤ 1 + ε := by
  have hpos : (0:ℝ) < (1 - ε / 4) * (1 - ε / 4) := by nlinarith
  rw [div_le_iff₀ hpos]
  nlinarith [mul_nonneg hε (mul_nonneg (show (0:ℝ) ≤ 5 / 8 - ε by linarith)
    (show (0:ℝ) ≤ 51 / 8 - ε by linarith))]

/-! ## Step 2b: the tuned headline -/

/-- **Step 2 headline: the tuned instance.**

The paper's parameter choice, in weight form. The sampler deviates pointwise from
uniform by `ε/4`, and the escape mass is `exp(−(cOf ε)²/2)`, which the choice
`c = cOf ε = √(2 log(4/ε))` makes exactly `ε/4` (`Arlib.KV97.exp_cOf`) — total
loss `lossOf (cOf ε) (ε/4) = ε/2`. The conclusion is

```
(1 − ε)/N  ≤  w i / ∑ w  ≤  (1 + 2ε)/N        for  0 < ε ≤ 1.
```

**The lower constant is the paper's `ε`; the upper is `2ε`, twice the paper's.**
The asymmetry is genuine: see `Arlib.KV97.tuned_upper_sharp` and the module
docstring for the exact threshold `(7 − √33)/2 ≈ 0.6277` below which `1 + ε` is
recoverable, and `Arlib.KV97.ratio_bounds_tuned_sharp` for that version.

Note this is *better* than step 1 applied blindly, which would give `1 − 2ε` on
the left. -/
theorem ratio_bounds_tuned [Nonempty ι] (w : ι → ℝ) {V ε : ℝ} (hV : 0 < V)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hlow : ∀ i, (1 - ε / 4) * (1 - Real.exp (-(cOf ε) ^ 2 / 2)) / V ≤ w i)
    (hhigh : ∀ i, w i ≤ (1 + ε / 4) / V) (i : ι) :
    (1 - ε) / (Fintype.card ι : ℝ) ≤ w i / (∑ j, w j) ∧
      w i / (∑ j, w j) ≤ (1 + 2 * ε) / (Fintype.card ι : ℝ) := by
  have hN : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [exp_cOf hε0 hε1] at hlow
  obtain ⟨hlo, hhi⟩ :=
    ratio_window_of_loss w hV (by linarith) (by linarith) hlow hhigh i
  rw [← div_div] at hlo hhi
  refine ⟨le_trans ?_ hlo, le_trans hhi ?_⟩
  · gcongr
    exact tuned_lower hε0.le
  · gcongr
    exact tuned_upper hε0.le hε1

/-- **Step 2 headline at the paper's constant, in the range where it holds.**

Identical to `Arlib.KV97.ratio_bounds_tuned` except that `ε ≤ 1` is strengthened
to `ε ≤ 5/8`, which buys the symmetric `(1 ± ε)/N` the paper states — exactly
`eq:almostuniform` (`sections/related.tex:21`). The restriction is not
cosmetic: `1 + ε` fails for `ε > (7 − √33)/2 ≈ 0.6277`
(`Arlib.KV97.tuned_upper_sharp`). Since the caller always wants a *small* error
budget, `ε ≤ 5/8` costs nothing in practice. -/
theorem ratio_bounds_tuned_sharp [Nonempty ι] (w : ι → ℝ) {V ε : ℝ} (hV : 0 < V)
    (hε0 : 0 < ε) (hε1 : ε ≤ 5 / 8)
    (hlow : ∀ i, (1 - ε / 4) * (1 - Real.exp (-(cOf ε) ^ 2 / 2)) / V ≤ w i)
    (hhigh : ∀ i, w i ≤ (1 + ε / 4) / V) (i : ι) :
    (1 - ε) / (Fintype.card ι : ℝ) ≤ w i / (∑ j, w j) ∧
      w i / (∑ j, w j) ≤ (1 + ε) / (Fintype.card ι : ℝ) := by
  have hN : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [exp_cOf hε0 (by linarith)] at hlow
  obtain ⟨hlo, hhi⟩ :=
    ratio_window_of_loss w hV (by linarith) (by linarith) hlow hhigh i
  rw [← div_div] at hlo hhi
  refine ⟨le_trans ?_ hlo, le_trans hhi ?_⟩
  · gcongr
    exact tuned_lower hε0.le
  · gcongr
    exact tuned_upper_sharp hε0.le hε1

/-! ## Step 3: over the real objects -/

section Concrete

open MeasureTheory Arlib.Lattice.Rounding

variable {n : ℕ} {J : Type*}

/-- **`cor:linf`, general form** (`sections/proof-appendix.tex:159`).

Over the real objects. `pt : ι → EuclideanSpace ℝ (Fin n)` enumerates the lattice
points of `P ∩ ℤⁿ`; `ι` is assumed finite and nonempty rather than derived, so
this theorem is about *any* finite nonempty set of target points and carries no
geometric side conditions. `f` is the continuous sampler's density on the
inflated polytope, and

```
w x = ∫_{P'} f p · prodTent x p dp = Pr[rnd p = x]
```

is the probability that randomized rounding of a draw hits `x`
(`Arlib/Lattice/Rounding/ProdKernel.lean`). The conclusion is that after
rejection — i.e. after normalising `w` over `ι` — every lattice point is hit with
probability within `1 ± 4(ε+E)` of `1/N`.

The two `∀ i` hypotheses are exactly `Arlib.KV97.theorem2`'s: integrability of
the integrand, and a bound `E` on the escape mass
`∫_{P'ᶜ} prodTent x p dp`, at every target point.

Note `pt` is **not** required injective. It need not be: the statement is about
the normalised weight of the index `i`, and a repeated point would simply be a
different index type. Injectivity matters only when reading `Fintype.card ι` as
`|P ∩ ℤⁿ|`, which is the caller's obligation. -/
theorem cor_linf [Nonempty ι] {A : J → EuclideanSpace ℝ (Fin n)} {b : J → ℝ}
    {c r : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {V ε E : ℝ}
    (pt : ι → EuclideanSpace ℝ (Fin n)) (hV : 0 < V) (hε : 0 ≤ ε) (hE : 0 ≤ E)
    (hθ : ε + E ≤ 1 / 2)
    (hf : PointwiseAlmostUniform f (inflated A b c r) V ε)
    (hint : ∀ i, IntegrableOn (fun p => f p * prodTent (pt i) p) (inflated A b c r))
    (hesc : ∀ i, ∫ p in (inflated A b c r)ᶜ, prodTent (pt i) p ≤ E) (i : ι) :
    (1 - 4 * (ε + E)) / (Fintype.card ι : ℝ) ≤
        (∫ p in inflated A b c r, f p * prodTent (pt i) p) /
          (∑ j, ∫ p in inflated A b c r, f p * prodTent (pt j) p) ∧
      (∫ p in inflated A b c r, f p * prodTent (pt i) p) /
          (∑ j, ∫ p in inflated A b c r, f p * prodTent (pt j) p) ≤
        (1 + 4 * (ε + E)) / (Fintype.card ι : ℝ) := by
  have hε1 : ε ≤ 1 := by linarith
  exact ratio_bounds_of_loss
    (fun j => ∫ p in inflated A b c r, f p * prodTent (pt j) p) hV hε hE hθ
    (fun j => (theorem2 hV (by linarith) hε1 hf (hint j) (hesc j)).1)
    (fun j => (theorem2 hV (by linarith) hε1 hf (hint j) (hesc j)).2) i

/-- **`cor:linf`, tuned form.**

`Arlib.KV97.cor_linf` at the paper's parameter choice: inflation constant
`c = cOf ε = √(2 log(4/ε))`, sampler deviation `ε/4`, escape mass
`exp(−(cOf ε)²/2)` — which is `ε/4` by `Arlib.KV97.exp_cOf`, so the total loss is
`lossOf (cOf ε) (ε/4) = ε/2`. The conclusion is

```
(1 − ε)/N  ≤  Pr[rnd p = x ∣ rnd p ∈ P]  ≤  (1 + 2ε)/N.
```

**The honest upper constant is `2ε`, not the paper's `ε`.** For `ε ≤ 5/8` the
symmetric `(1 ± ε)/N` is recoverable — `Arlib.KV97.ratio_bounds_tuned_sharp` is
the weight-level statement; instantiating it here is the same one-liner. See the
module docstring for why the extra factor appears (it is the `(1+ε/4)` in the
corrected upper half of Theorem 2, which the printed proof takes to be `1`). -/
theorem cor_linf_tuned [Nonempty ι] {A : J → EuclideanSpace ℝ (Fin n)} {b : J → ℝ}
    {r : ℝ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {V ε : ℝ}
    (pt : ι → EuclideanSpace ℝ (Fin n)) (hV : 0 < V) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hf : PointwiseAlmostUniform f (inflated A b (cOf ε) r) V (ε / 4))
    (hint : ∀ i, IntegrableOn (fun p => f p * prodTent (pt i) p)
      (inflated A b (cOf ε) r))
    (hesc : ∀ i, ∫ p in (inflated A b (cOf ε) r)ᶜ, prodTent (pt i) p ≤
      Real.exp (-(cOf ε) ^ 2 / 2)) (i : ι) :
    (1 - ε) / (Fintype.card ι : ℝ) ≤
        (∫ p in inflated A b (cOf ε) r, f p * prodTent (pt i) p) /
          (∑ j, ∫ p in inflated A b (cOf ε) r, f p * prodTent (pt j) p) ∧
      (∫ p in inflated A b (cOf ε) r, f p * prodTent (pt i) p) /
          (∑ j, ∫ p in inflated A b (cOf ε) r, f p * prodTent (pt j) p) ≤
        (1 + 2 * ε) / (Fintype.card ι : ℝ) :=
  ratio_bounds_tuned
    (fun j => ∫ p in inflated A b (cOf ε) r, f p * prodTent (pt j) p) hV hε0 hε1
    (fun j => (theorem2 hV (by linarith) (by linarith) hf (hint j) (hesc j)).1)
    (fun j => (theorem2 hV (by linarith) (by linarith) hf (hint j) (hesc j)).2) i

/-! ## Step 4: non-vacuity -/

/-- **The hypotheses force `E < 1`** — the degeneracy check.

`Arlib.KV97.ratio_bounds_of_loss` assumes `0 ≤ ε` and `ε + E ≤ 1/2`, hence
`E ≤ 1/2`. This matters: at `E ≥ 1` the lower end of the weight window,
`(1−ε)(1−E)/V`, is `≤ 0`, so the hypothesis `(1−ε)(1−E)/V ≤ w i` says nothing,
`∑ w` need not be positive, and the ratio bound is worthless (indeed `w i / 0 = 0`
by Mathlib's convention, so the *lower* conclusion would be outright false for
positive `δ < 1`). The statement is therefore not vacuously true through that
route. -/
theorem escape_lt_one {ε E : ℝ} (hε : 0 ≤ ε) (hθ : ε + E ≤ 1 / 2) : E < 1 := by
  linarith

/-- **Non-vacuity witness for steps 1–2** (`CLAUDE.md` §11).

At `ε = E = 0` the hypotheses of `Arlib.KV97.ratio_bounds_of_loss` are
simultaneously satisfiable — the constant weight `w = fun _ => 1/V` meets both,
with equality — and the quantity the theorem bounds is then **exactly** `1/N`,
the genuine uniform distribution on `ι`. So at `δ = 0` the conclusion
`1/N ≤ w i / ∑ w ≤ 1/N` is a true, non-trivial, attained statement rather than an
empty one.

`hV : 0 < V` is needed for the final equality: at `V = 0` Mathlib's `1/0 = 0`
makes every weight `0` and the ratio `0/0 = 0 ≠ 1/N`. -/
theorem exists_uniform_weights [Nonempty ι] {V : ℝ} (hV : 0 < V) (i : ι) :
    ∃ w : ι → ℝ, (∀ j, (1 - 0) * (1 - 0) / V ≤ w j) ∧ (∀ j, w j ≤ (1 + 0) / V) ∧
      w i / (∑ j, w j) = 1 / (Fintype.card ι : ℝ) := by
  have hN : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨fun _ => 1 / V, fun j => by norm_num, fun j => by norm_num, ?_⟩
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **Non-vacuity witness for step 3, density side.**

`Arlib.KV97.cor_linf` quantifies over a `PointwiseAlmostUniform` density, which
would make it vacuous if no such density existed. It does: the exactly-uniform
density `fun _ => 1/V` satisfies it at `ε = 0` on any inflated polytope
(`Arlib.KV97.PointwiseAlmostUniform.uniform`). Combined with `E = 0` — the escape
hypothesis `∫_{P'ᶜ} prodTent x p ≤ 0` is the statement that no mass escapes — the
whole hypothesis bundle of `cor_linf` is inhabited at `ε = E = 0`, where it
returns the exact `1/N` of `Arlib.KV97.exists_uniform_weights`. -/
theorem exists_pointwiseAlmostUniform {n : ℕ} {J : Type*}
    (A : J → EuclideanSpace ℝ (Fin n)) (b : J → ℝ) (c r : ℝ) {V : ℝ} (hV : 0 < V) :
    PointwiseAlmostUniform (fun _ => 1 / V) (inflated A b c r) V 0 :=
  PointwiseAlmostUniform.uniform _ hV le_rfl

end Concrete

end Arlib.KV97
