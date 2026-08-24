/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.NeedleLimit

/-!
# Positional control for the localisation bisection, and what it can and cannot buy

This file answers the question left open by `Arlib.Convexity.NeedleLimit`:

> `Arlib.le_diam_of_sign_separated` shows that no cutting scheme can shrink the **diameter**
> of the bodies of the localisation bisection chain, because the invariant `0 < ∫_C g`,
> `0 < ∫_C h` alone bounds `diam C` from below.  It does **not** forbid shrinking the `n-1`
> directions *transverse* to a spanning chord.  Is there a cut rule that simultaneously
> (a) preserves `0 < ∫ g` and `0 < ∫ h` on the retained side and (b) halves the width in some
> direction?

The answer is **yes**, and the file both proves the general mechanism and exhibits it running
to completion on the very configuration that defeats the diameter argument.

## 1. Positional control is free — it never had to be extracted

The obstacle was stated as "the existential cut API never reveals where the cut lands, so the
retained side can be nearly all of the current body in every direction simultaneously".  The
first half of that is true and the second half is false, for a reason that needs no information
about the cut position at all:

`Arlib.exists_side_extent_halved` — if `L x ∈ [p, q]` for all `x ∈ C`, then for **every** real
`s` one of the two sides `C ∩ {L ≤ s}`, `C ∩ {s < L}` has its `L`-image inside an interval of
length **exactly** `(q - p)/2`.

The proof is one line of arithmetic: compare `s` with the midpoint `(p+q)/2`; if `s` is below it
the closed side lies in `[p, (p+q)/2]`, otherwise the open side lies in `[(p+q)/2, q]`.  No
continuity, no measure, no convexity — and, crucially, *no knowledge of where `s` is*.  The two
sides' `L`-extents always sum to at most the whole, so the smaller one is at most half.  So the
"missing bisection lemma with positional control" is not missing; it is trivial, and it is
`Arlib.exists_side_extent_halved`.

## 2. …but the *choice of side* is the whole difficulty

`Arlib.exists_side_extent_halved` names a side, and it is generally **not** the side that the
mass condition forces `Arlib.exists_halfSpace_cut_pos` to keep.  To use it one must be free to
keep either side, i.e. one needs both sides to satisfy the invariant:

`Arlib.exists_side_extent_halved_pos` — if **both** sides of the cut at level `s` have positive
`g`-mass and positive `h`-mass, then the side with the halved `L`-extent also has them.

`Arlib.exists_cut_chain_extent_halved` iterates this: given that every admissible subset of `K`
admits a *two-sided* cut orthogonal to a fixed `L`, the chain's `L`-extent is exactly
`(q-p)/2^N` at depth `N`, with the invariant intact at every stage.  The two-sidedness is an
explicit hypothesis on concrete integrals, not a named predicate, and it is **not** assumed to
hold in general — §3 shows it is exactly what fails in the bad direction.  It is satisfiable:
`Arlib.exists_cut_chain_extent_halved_volume` discharges it unconditionally for `g = h = 1`
(volume-bisecting cuts are two-sided), so the reduction is not vacuous.

## 3. Two-sidedness fails **exactly** in the separating direction — with positional control

`Arlib.le_of_setIntegral_halfSpace_true_pos`, `Arlib.lt_of_setIntegral_halfSpace_false_pos`:
if `g ≤ 0` on `{a < L}` and `h ≤ 0` on `{L < b}` (the sign-separated configuration of
`Arlib.le_diam_of_sign_separated`), then keeping the closed side forces `b ≤ s` and keeping the
open side forces `s < a`.  **This is genuine positional control**: the invariant *dictates* that
the cut level lies outside the slab `[a, b)`, and hence that the retained side contains the whole
slab.

`Arlib.not_two_sided_of_sign_separated`: consequently, for `a < b`, **no** cut orthogonal to `L`
is two-sided — one of the two sides always violates the invariant.  So in the separating
direction the side is forced, the forced side is the fat one, and
`Arlib.sub_le_extent_of_sign_separated` records the price: every admissible body has
`L`-extent at least `b - a`, forever.

So the direction responsible for the diameter bound is also, and for the same reason, the one
direction in which width-halving is impossible: it is the direction along which the needle runs.
(The converse implication — *if* no level in direction `L` is two-sided *then* `g` and `h` are
sign-separated orthogonally to `L` — is **not** proved here; see "What is not proved" below.)

## 4. The dichotomy, executed: a needle from the diameter-obstructed configuration

`Arlib.transverse_thin_chain_gapBox` takes the planar witness of
`Arlib.Convexity.NeedleLimit` — `Arlib.gapG`, `Arlib.gapH` on `Arlib.gapBox = [0,3] × [0,1]`,
for which `Arlib.one_le_diam_bisection_chain` proves every bisection body has diameter `≥ 1`
regardless of the directions chosen — and runs the bisection in the **transverse** direction
`snd`.  The result is the explicit chain `Arlib.thinBox k = [0,3] × [0, 2^{-k}]`, in which:

* `thinBox (k+1)` is *literally* the closed side of a halfspace cut of `thinBox k` orthogonal to
  `snd` (`Arlib.thinBox_succ`);
* the invariant survives at every depth, with both masses exactly `2^{-k}/2`
  (`Arlib.integral_gapG_thinBox`, `Arlib.integral_gapH_thinBox`) — so this *is* a mass-bisecting
  cut, of both `g` and `h` at once;
* **both** sides of every cut satisfy the invariant (`Arlib.two_sided_thinBox`), so the choice of
  side is genuinely free — the situation §3 proves impossible in the direction `fst`;
* the transverse width is exactly `2^{-k} → 0`, while the diameter stays `≥ 1` and a spanning
  chord persists at every depth;
* the bodies converge in Hausdorff distance to the honest **needle** `[0,3] × {0}`
  (`Arlib.tendsto_hausdorffDist_thinBox`).

And `Arlib.not_two_sided_fst_gapBox` is the other half on the same data: **no** cut orthogonal to
`fst` is ever two-sided, for any measurable set whatsoever.

So on the configuration that kills the diameter argument, transverse thinning is achievable, the
longitudinal direction is provably frozen, and the limit is a segment of length `3`.  This
settles the question in the affirmative and identifies the real remaining obstacle: not
positional control, but producing a two-sided (i.e. simultaneously `g`- and `h`-bisecting) cut in
a transverse direction for a *general* configuration — the two-measure ham-sandwich, gap (G1) of
`Arlib.Convexity.LocalizationLemma`, which Mathlib `v4.32` cannot supply.

## What is not proved here, stated exactly

Two things, and neither is hidden in a hypothesis-bundle.

**(P1) The existence of a two-sided cut in a transverse direction, for a general configuration.**
`Arlib.exists_cut_chain_extent_halved` reduces transverse thinness to it;
`Arlib.two_sided_thinBox` verifies it along one explicit chain;
`Arlib.exists_cut_chain_extent_halved_volume` discharges it for `g = h = 1`.  In general it is
exactly the two-measure ham-sandwich — a hyperplane bisecting `∫ g` and `∫ h` at once, whose two
sides are then both admissible — i.e. gap **(G1)** of `Arlib.Convexity.LocalizationLemma`, which
needs Borsuk–Ulam and is absent from Mathlib `v4.32`.  Note the *weaker* statement suffices here:
one does not need exact bisection of both, only positivity of both masses on both sides.

**(P2) A converse to §3.**  It is not proved that failure of two-sidedness at *every* level in
direction `L` forces `g` and `h` to be sign-separated orthogonally to `L`.  For nonnegative `g`
and `h` this is a routine monotone-rearrangement argument (the two-sided levels form the open
interval between the endpoints of the mass profile, and two disjoint such intervals separate the
masses); for the *signed* integrands the localisation argument actually uses, the profiles are
not monotone and the statement is open here.  Nothing below depends on it.

Thinning all `n-1` transverse directions of a general body — as opposed to one fixed direction,
which is what `Arlib.exists_cut_chain_extent_halved` delivers — is a matter of interleaving the
directions and is not attempted here either; the per-direction rate `(q-p)/2^N` is uniform, so
nothing new is needed beyond (P1) holding for each of them in turn.

## Honesty note

This file contains **no** `def`/`structure`/`class`/`Prop` asserting the Localization Lemma, the
isoperimetric inequality or Dyer–Frieze, and no theorem below takes any of them as a hypothesis.
The single `def` (`Arlib.thinBox`) is an explicit box, and every property attributed to it is
proved.  The two-sidedness hypothesis of `Arlib.exists_cut_chain_extent_halved` is an ordinary
∀-hypothesis about concrete set integrals appearing in that theorem's own statement; it is
discharged unconditionally in `Arlib.exists_cut_chain_extent_halved_volume` and it is *refuted*
in the separating direction by `Arlib.not_two_sided_of_sign_separated`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Metric Bornology
open scoped ENNReal Topology

namespace Arlib

/-! ### Positional control, for free: one side of every cut has half the extent -/

section Extent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed side of a cut has `L`-image inside `[p, min q s]`. -/
theorem apply_mem_Icc_of_mem_halfSpace_true {L : E →L[ℝ] ℝ} {C : Set E} {p q : ℝ}
    (hC : ∀ x ∈ C, L x ∈ Icc p q) (s : ℝ) :
    ∀ x ∈ C ∩ halfSpace L s true, L x ∈ Icc p (min q s) := by
  rintro x ⟨hxC, hxs⟩
  exact ⟨(hC x hxC).1, le_min (hC x hxC).2 hxs⟩

/-- The open side of a cut has `L`-image inside `[max p s, q]`. -/
theorem apply_mem_Icc_of_mem_halfSpace_false {L : E →L[ℝ] ℝ} {C : Set E} {p q : ℝ}
    (hC : ∀ x ∈ C, L x ∈ Icc p q) (s : ℝ) :
    ∀ x ∈ C ∩ halfSpace L s false, L x ∈ Icc (max p s) q := by
  rintro x ⟨hxC, hxs⟩
  exact ⟨max_le (hC x hxC).1 (le_of_lt hxs), (hC x hxC).2⟩

/-- **Positional control, for free.**

If the `L`-values on `C` lie in `[p, q]`, then for **every** cut level `s` — in particular for
the one that `Arlib.exists_halfSpace_bisecting` produces and never reveals — one of the two
sides of the cut has all its `L`-values inside an interval of length exactly `(q - p)/2`, itself
contained in `[p, q]`.

No measure, no continuity, no convexity, and no information about `s` is used: the two sides'
`L`-extents are `[p, s]` and `[s, q]`, which sum to `[p, q]`, so the smaller is at most half.
This is the "bisection lemma with positional control" whose absence was recorded as the blocker
for transverse thinness in `Arlib.Convexity.NeedleLimit`; it is a two-case comparison of `s`
with the midpoint `(p+q)/2`.

What it does *not* do is choose the side for you — see
`Arlib.exists_side_extent_halved_pos` and `Arlib.not_two_sided_of_sign_separated`. -/
theorem exists_side_extent_halved {L : E →L[ℝ] ℝ} {C : Set E} {p q : ℝ} (hpq : p ≤ q)
    (hC : ∀ x ∈ C, L x ∈ Icc p q) (s : ℝ) :
    ∃ (side : Bool) (p' q' : ℝ), p ≤ p' ∧ q' ≤ q ∧ q' - p' = (q - p) / 2 ∧
      ∀ x ∈ C ∩ halfSpace L s side, L x ∈ Icc p' q' := by
  rcases le_or_gt s ((p + q) / 2) with hs | hs
  · refine ⟨true, p, (p + q) / 2, le_rfl, by linarith, by ring, ?_⟩
    rintro x ⟨hxC, hxs⟩
    exact ⟨(hC x hxC).1, le_trans hxs hs⟩
  · refine ⟨false, (p + q) / 2, q, by linarith, le_rfl, by ring, ?_⟩
    rintro x ⟨hxC, hxs⟩
    exact ⟨le_of_lt (lt_trans hs hxs), (hC x hxC).2⟩

end Extent

/-! ### Halving the extent while keeping the invariant -/

section ExtentPos

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  {μ : Measure E}

/-- **The extent halves and the invariant survives — provided the cut is two-sided.**

If *both* sides of the cut at level `s` carry positive `g`-mass and positive `h`-mass, then the
side singled out by `Arlib.exists_side_extent_halved` (whose `L`-extent is exactly half) also
carries both.

The hypothesis is the entire difficulty: the `g`-bisecting cut of
`Arlib.exists_halfSpace_cut_pos` guarantees only that *some* side keeps the invariant, and
`Arlib.not_two_sided_of_sign_separated` shows the hypothesis is unsatisfiable in the direction
that separates the supports of `g` and `h`. -/
theorem exists_side_extent_halved_pos {g h : E → ℝ} {L : E →L[ℝ] ℝ} {C : Set E} {p q : ℝ}
    (hpq : p ≤ q) (hC : ∀ x ∈ C, L x ∈ Icc p q) {s : ℝ}
    (hpos : ∀ side : Bool, 0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ ∧
      0 < ∫ x in C ∩ halfSpace L s side, h x ∂μ) :
    ∃ (side : Bool) (p' q' : ℝ), p ≤ p' ∧ q' ≤ q ∧ q' - p' = (q - p) / 2 ∧
      (∀ x ∈ C ∩ halfSpace L s side, L x ∈ Icc p' q') ∧
      0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ ∧
      0 < ∫ x in C ∩ halfSpace L s side, h x ∂μ := by
  obtain ⟨side, p', q', h1, h2, h3, h4⟩ := exists_side_extent_halved hpq hC s
  exact ⟨side, p', q', h1, h2, h3, h4, (hpos side).1, (hpos side).2⟩

end ExtentPos

/-! ### The obstruction: two-sidedness fails in a separating direction -/

section Obstruction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E}

/-- **Positional control from the invariant, one.**

If `h ≤ 0` on the open halfspace `{L < b}`, then a cut whose **closed** side keeps positive
`h`-mass must land at level `b` or beyond.  So the invariant itself tells you where the cut is —
and tells you that the retained side contains everything below `b`. -/
theorem le_of_setIntegral_halfSpace_true_pos {h : E → ℝ} {C : Set E} (hC : MeasurableSet C)
    {L : E →L[ℝ] ℝ} {b s : ℝ} (hh : ∀ x, L x < b → h x ≤ 0)
    (hpos : 0 < ∫ x in C ∩ halfSpace L s true, h x ∂μ) : b ≤ s := by
  rcases le_or_gt b s with hbs | hbs
  · exact hbs
  · exfalso
    have hnp : ∫ x in C ∩ halfSpace L s true, h x ∂μ ≤ 0 :=
      setIntegral_nonpos (hC.inter (measurableSet_halfSpace L s true)) fun x hx =>
        hh x (lt_of_le_of_lt hx.2 hbs)
    linarith

/-- **Positional control from the invariant, two.**

If `g ≤ 0` on the open halfspace `{a < L}`, then a cut whose **open** side keeps positive
`g`-mass must land strictly below `a`.  So the retained side contains everything above `a`. -/
theorem lt_of_setIntegral_halfSpace_false_pos {g : E → ℝ} {C : Set E} (hC : MeasurableSet C)
    {L : E →L[ℝ] ℝ} {a s : ℝ} (hg : ∀ x, a < L x → g x ≤ 0)
    (hpos : 0 < ∫ x in C ∩ halfSpace L s false, g x ∂μ) : s < a := by
  rcases le_or_gt a s with hsa | hsa
  · exfalso
    have hnp : ∫ x in C ∩ halfSpace L s false, g x ∂μ ≤ 0 :=
      setIntegral_nonpos (hC.inter (measurableSet_halfSpace L s false)) fun x hx =>
        hg x (lt_of_le_of_lt hsa hx.2)
    linarith
  · exact hsa

/-- **The cut level of an admissible cut is forced out of the separating slab.**

In the sign-separated configuration, whichever side is retained, the cut level is either `< a`
(open side retained) or `≥ b` (closed side retained).  It can never land inside `[a, b)`. -/
theorem cut_level_lt_or_le_of_sign_separated {g h : E → ℝ} {C : Set E} (hC : MeasurableSet C)
    {L : E →L[ℝ] ℝ} {a b s : ℝ} (hg : ∀ x, a < L x → g x ≤ 0) (hh : ∀ x, L x < b → h x ≤ 0)
    (side : Bool) (hgpos : 0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ)
    (hhpos : 0 < ∫ x in C ∩ halfSpace L s side, h x ∂μ) : s < a ∨ b ≤ s := by
  cases side
  · exact Or.inl (lt_of_setIntegral_halfSpace_false_pos hC hg hgpos)
  · exact Or.inr (le_of_setIntegral_halfSpace_true_pos hC hh hhpos)

/-- **No cut orthogonal to a separating direction is two-sided.**

If `g ≤ 0` on `{a < L}` and `h ≤ 0` on `{L < b}` with `a < b`, then for every level `s` at least
one of the two sides of the cut violates the invariant: the closed side loses the `h`-mass
(unless `b ≤ s`) and the open side loses the `g`-mass (unless `s < a`), and `a < b` makes those
two escapes mutually exclusive.

This is the exact obstruction to `Arlib.exists_side_extent_halved_pos` in the direction `L`.
Combined with `Arlib.sub_le_extent_of_sign_separated`, it says that the `L`-width can never be
halved and never falls below `b - a` — which is what `Arlib.le_diam_of_sign_separated` predicts,
now localised to the single direction responsible for it. -/
theorem not_two_sided_of_sign_separated {g h : E → ℝ} {C : Set E} (hC : MeasurableSet C)
    {L : E →L[ℝ] ℝ} {a b : ℝ} (hab : a < b) (hg : ∀ x, a < L x → g x ≤ 0)
    (hh : ∀ x, L x < b → h x ≤ 0) (s : ℝ) :
    ¬ (∀ side : Bool, 0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ ∧
        0 < ∫ x in C ∩ halfSpace L s side, h x ∂μ) := by
  intro hcon
  have h1 : b ≤ s := le_of_setIntegral_halfSpace_true_pos hC hh (hcon true).2
  have h2 : s < a := lt_of_setIntegral_halfSpace_false_pos hC hg (hcon false).1
  linarith

/-- **The separating direction's extent is bounded below on every admissible body.**

The extent form of `Arlib.le_diam_of_sign_separated`: if all `L`-values on `C` lie in `[p, q]`
and `C` carries positive `g`- and `h`-mass, then `b - a ≤ q - p`.  So no cutting scheme, adaptive
or not, can reduce the `L`-width below the gap. -/
theorem sub_le_extent_of_sign_separated {g h : E → ℝ} {C : Set E} (hC : MeasurableSet C)
    {L : E →L[ℝ] ℝ} {a b p q : ℝ} (hg : ∀ x, a < L x → g x ≤ 0) (hh : ∀ x, L x < b → h x ≤ 0)
    (hgC : 0 < ∫ x in C, g x ∂μ) (hhC : 0 < ∫ x in C, h x ∂μ)
    (hCpq : ∀ x ∈ C, L x ∈ Icc p q) : b - a ≤ q - p := by
  obtain ⟨x, hxC, y, hyC, hxy⟩ :=
    exists_pair_apply_sub_ge_of_sign_separated hC hg hh hgC hhC
  have hx := hCpq x hxC
  have hy := hCpq y hyC
  have hx1 : p ≤ L x := hx.1
  have hy2 : L y ≤ q := hy.2
  linarith

end Obstruction

/-! ### The chain: iterated two-sided cuts thin a fixed direction geometrically -/

section Iteration

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E}

/-- **Iterated two-sided cuts halve the extent in a fixed direction, geometrically.**

Suppose every admissible subset `C ⊆ K` (measurable, with `0 < ∫_C g` and `0 < ∫_C h`) admits a
cut orthogonal to `L` **both** of whose sides are still admissible.  Then for every depth `N`
there is a body `C ⊆ K`, obtained by `N` halfspace cuts orthogonal to `L`, still measurable,
still convex whenever `K` is, still admissible, whose `L`-values lie in an interval of length
exactly `(q - p)/2^N`.

The hypothesis `hstep` is an ordinary ∀-statement about the concrete set integrals in this
theorem's own statement — not a named predicate standing in for a hard lemma.  It is:

* **satisfiable**, unconditionally, for `g = h = 1` — see
  `Arlib.exists_cut_chain_extent_halved_volume`, which discharges it from
  `Arlib.exists_halfSpace_bisecting` alone;
* **false** whenever `g` and `h` are sign-separated by a slab orthogonal to `L` — see
  `Arlib.not_two_sided_of_sign_separated`;
* **satisfiable in a transverse direction even then** — see `Arlib.two_sided_thinBox`, which
  verifies it along the chain for the planar witness whose longitudinal direction is frozen.

So this theorem is the precise reduction: *transverse thinness follows from two-sided cuts*, and
two-sided cuts are what the two-measure ham-sandwich would supply. -/
theorem exists_cut_chain_extent_halved {g h : E → ℝ} {K : Set E} {L : E →L[ℝ] ℝ} {p q : ℝ}
    (hK : MeasurableSet K) (hKpq : ∀ x ∈ K, L x ∈ Icc p q) (hpq : p ≤ q)
    (hgK : 0 < ∫ x in K, g x ∂μ) (hhK : 0 < ∫ x in K, h x ∂μ)
    (hstep : ∀ C : Set E, MeasurableSet C → C ⊆ K →
      0 < ∫ x in C, g x ∂μ → 0 < ∫ x in C, h x ∂μ →
      ∃ s : ℝ, ∀ side : Bool, 0 < ∫ x in C ∩ halfSpace L s side, g x ∂μ ∧
        0 < ∫ x in C ∩ halfSpace L s side, h x ∂μ) :
    ∀ N : ℕ, ∃ (C : Set E) (p' q' : ℝ), C ⊆ K ∧ MeasurableSet C ∧
      (Convex ℝ K → Convex ℝ C) ∧ 0 < ∫ x in C, g x ∂μ ∧ 0 < ∫ x in C, h x ∂μ ∧
      p ≤ p' ∧ q' ≤ q ∧ q' - p' = (q - p) / 2 ^ N ∧ ∀ x ∈ C, L x ∈ Icc p' q' := by
  intro N
  induction N with
  | zero =>
    exact ⟨K, p, q, Subset.rfl, hK, fun hc => hc, hgK, hhK, le_rfl, le_rfl, by simp, hKpq⟩
  | succ N ih =>
    obtain ⟨C, p', q', hCK, hCm, hCc, hCg, hCh, hp', hq', hlen, hCpq⟩ := ih
    have hpq' : p' ≤ q' := by
      have hnn : (0:ℝ) ≤ (q - p) / 2 ^ N := by
        apply div_nonneg (by linarith)
        positivity
      linarith
    obtain ⟨s, hs⟩ := hstep C hCm hCK hCg hCh
    obtain ⟨side, p'', q'', h1, h2, h3, h4⟩ := exists_side_extent_halved hpq' hCpq s
    refine ⟨C ∩ halfSpace L s side, p'', q'',
      Set.inter_subset_left.trans hCK, hCm.inter (measurableSet_halfSpace L s side),
      fun hc => (hCc hc).inter (convex_halfSpace L s side), (hs side).1, (hs side).2,
      le_trans hp' h1, le_trans h2 hq', ?_, h4⟩
    rw [h3, hlen, pow_succ]
    ring

/-- **The two-sidedness hypothesis is satisfiable: volume-bisecting cuts are two-sided.**

Taking `g = h = 1`, `Arlib.exists_halfSpace_bisecting` gives a cut with *both* sides of measure
exactly half, so both sides are admissible; the hypothesis of
`Arlib.exists_cut_chain_extent_halved` is then discharged unconditionally, and the conclusion is
an honest chain of nested bodies of positive volume whose `L`-extent is `(q-p)/2^N`.

This is the non-vacuity check for the reduction of `Arlib.exists_cut_chain_extent_halved`: the
hypothesis is not secretly contradictory. -/
theorem exists_cut_chain_extent_halved_volume [BorelSpace E] [FiniteDimensional ℝ E]
    [μ.IsAddHaarMeasure] {K : Set E} {L : E →L[ℝ] ℝ} (hL : L ≠ 0) {p q : ℝ}
    (hK : MeasurableSet K) (hKb : IsBounded K) (hKpq : ∀ x ∈ K, L x ∈ Icc p q) (hpq : p ≤ q)
    (hKpos : 0 < ∫ _x in K, (1:ℝ) ∂μ) :
    ∀ N : ℕ, ∃ (C : Set E) (p' q' : ℝ), C ⊆ K ∧ MeasurableSet C ∧
      (Convex ℝ K → Convex ℝ C) ∧ 0 < ∫ _x in C, (1:ℝ) ∂μ ∧
      p ≤ p' ∧ q' ≤ q ∧ q' - p' = (q - p) / 2 ^ N ∧ ∀ x ∈ C, L x ∈ Icc p' q' := by
  have hstep : ∀ C : Set E, MeasurableSet C → C ⊆ K →
      0 < ∫ _x in C, (1:ℝ) ∂μ → 0 < ∫ _x in C, (1:ℝ) ∂μ →
      ∃ s : ℝ, ∀ side : Bool, 0 < ∫ _x in C ∩ halfSpace L s side, (1:ℝ) ∂μ ∧
        0 < ∫ _x in C ∩ halfSpace L s side, (1:ℝ) ∂μ := by
    intro C hCm hCK hCpos _
    have hCb : IsBounded C := hKb.subset hCK
    obtain ⟨r, hr⟩ := hCb.subset_closedBall (0 : E)
    have hCtop : μ C ≠ ⊤ :=
      ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono hr)
    have hint : IntegrableOn (fun _ : E => (1:ℝ)) C μ := integrableOn_const hCtop
    obtain ⟨s, hs⟩ := exists_halfSpace_bisecting hint hCb hL
    have hsum := setIntegral_halfSpace_add hint hCm L s
    refine ⟨s, fun side => ?_⟩
    have hpos : ∀ side : Bool, 0 < ∫ _x in C ∩ halfSpace L s side, (1:ℝ) ∂μ := by
      intro side
      cases side
      · have : ∫ _x in C ∩ halfSpace L s false, (1:ℝ) ∂μ = (∫ _x in C, (1:ℝ) ∂μ) / 2 := by
          linarith [hsum, hs]
        rw [this]; linarith
      · rw [hs]; linarith
    exact ⟨hpos side, hpos side⟩
  intro N
  obtain ⟨C, p', q', h1, h2, h3, h4, -, h6, h7, h8, h9⟩ :=
    exists_cut_chain_extent_halved hK hKpq hpq hKpos hKpos hstep N
  exact ⟨C, p', q', h1, h2, h3, h4, h6, h7, h8, h9⟩

end Iteration

/-! ### The planar witness: transverse thinning of the diameter-obstructed configuration -/

section ThinChain

/-- `2 ^ k ≥ 1` over the reals. -/
theorem one_le_two_pow_real (k : ℕ) : (1:ℝ) ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; nlinarith

theorem one_div_two_pow_pos (k : ℕ) : (0:ℝ) < 1 / 2 ^ k := by positivity

theorem one_div_two_pow_le_one (k : ℕ) : (1:ℝ) / 2 ^ k ≤ 1 := by
  rw [div_le_one (by positivity)]
  exact one_le_two_pow_real k

theorem one_div_two_pow_succ_le (k : ℕ) : (1:ℝ) / 2 ^ (k + 1) ≤ 1 / 2 ^ k := by
  have h : (1:ℝ) / 2 ^ (k + 1) = (1 / 2 ^ k) / 2 := by rw [pow_succ]; ring
  have h0 : (0:ℝ) ≤ 1 / 2 ^ k := le_of_lt (one_div_two_pow_pos k)
  rw [h]; linarith

/-- The mass of the unit-height profile `1_{[0,1)}` over any set squeezed between `Ioo d c` and
`Icc d c`, for `0 ≤ d ≤ c ≤ 1`, is `c - d`.  Used for the closed sides `Icc 0 c` and the open
sides `Ioc d c` of the transverse cuts. -/
theorem integral_icoConst_unit {S : Set ℝ} {d c : ℝ} (hd : 0 ≤ d) (hdc : d ≤ c) (hc : c ≤ 1)
    (h1 : Ioo d c ⊆ S) (h2 : S ⊆ Icc d c) :
    ∫ y in S, icoConst 0 1 1 y = c - d := by
  have hmeas : volume (S ∩ Ico (0:ℝ) 1) = ENNReal.ofReal (c - d) := by
    refine le_antisymm ?_ ?_
    · calc volume (S ∩ Ico (0:ℝ) 1) ≤ volume (Icc d c) :=
            measure_mono fun x hx => h2 hx.1
        _ = ENNReal.ofReal (c - d) := Real.volume_Icc
    · calc ENNReal.ofReal (c - d) = volume (Ioo d c) := Real.volume_Ioo.symm
        _ ≤ volume (S ∩ Ico (0:ℝ) 1) :=
            measure_mono fun x hx =>
              ⟨h1 hx, ⟨le_trans hd (le_of_lt hx.1), lt_of_lt_of_le hx.2 hc⟩⟩
  rw [icoConst, setIntegral_indicator measurableSet_Ico, setIntegral_const, measureReal_def,
    hmeas, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]

/-- **The transverse chain**: `thinBox k = [0,3] × [0, 2^{-k}]`.

A plain explicit box.  `thinBox 0` is `Arlib.gapBox`, and `thinBox (k+1)` is literally one side
of a halfspace cut of `thinBox k` orthogonal to the second coordinate. -/
noncomputable def thinBox (k : ℕ) : Set (ℝ × ℝ) := Icc (0:ℝ) 3 ×ˢ Icc (0:ℝ) ((1:ℝ) / 2 ^ k)

theorem thinBox_zero : thinBox 0 = gapBox := by
  show Icc (0:ℝ) 3 ×ˢ Icc (0:ℝ) ((1:ℝ) / 2 ^ 0) = Icc (0:ℝ) 3 ×ˢ Icc (0:ℝ) 1
  norm_num

theorem measurableSet_thinBox (k : ℕ) : MeasurableSet (thinBox k) :=
  measurableSet_Icc.prod measurableSet_Icc

theorem convex_thinBox (k : ℕ) : Convex ℝ (thinBox k) :=
  (convex_Icc (0:ℝ) 3).prod (convex_Icc (0:ℝ) ((1:ℝ) / 2 ^ k))

theorem thinBox_subset_gapBox (k : ℕ) : thinBox k ⊆ gapBox :=
  Set.prod_mono Subset.rfl (Icc_subset_Icc le_rfl (one_div_two_pow_le_one k))

/-- **Each stage is literally a halfspace cut of the previous one**, orthogonal to the transverse
direction `snd`, at the midpoint of the current transverse extent. -/
theorem thinBox_succ (k : ℕ) :
    thinBox (k + 1)
      = thinBox k ∩ halfSpace (ContinuousLinearMap.snd ℝ ℝ ℝ) ((1:ℝ) / 2 ^ (k + 1)) true := by
  ext z
  constructor
  · rintro ⟨hx, hy⟩
    exact ⟨⟨hx, ⟨hy.1, le_trans hy.2 (one_div_two_pow_succ_le k)⟩⟩, hy.2⟩
  · rintro ⟨⟨hx, hy⟩, hle⟩
    exact ⟨hx, ⟨hy.1, hle⟩⟩

/-- The *other* side of the same cut is the slab `[0,3] × (2^{-(k+1)}, 2^{-k}]`. -/
theorem thinBox_inter_false (k : ℕ) :
    thinBox k ∩ halfSpace (ContinuousLinearMap.snd ℝ ℝ ℝ) ((1:ℝ) / 2 ^ (k + 1)) false
      = Icc (0:ℝ) 3 ×ˢ Ioc ((1:ℝ) / 2 ^ (k + 1)) ((1:ℝ) / 2 ^ k) := by
  ext z
  constructor
  · rintro ⟨⟨hx, hy⟩, hlt⟩
    exact ⟨hx, ⟨hlt, hy.2⟩⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨hx, ⟨le_trans (le_of_lt (one_div_two_pow_pos (k + 1))) (le_of_lt hy.1), hy.2⟩⟩, hy.1⟩

/-- The `gapG`-mass of `thinBox k` is `2^{-k}/2`: positive at every depth. -/
theorem integral_gapG_thinBox (k : ℕ) :
    ∫ z in thinBox k, gapG z = (1 / 2) * (1 / 2 ^ k) := by
  show ∫ z in Icc (0:ℝ) 3 ×ˢ Icc (0:ℝ) ((1:ℝ) / 2 ^ k),
      stepLeft z.1 * icoConst 0 1 1 z.2 = (1 / 2) * (1 / 2 ^ k)
  rw [Measure.volume_eq_prod, setIntegral_prod_mul, integral_stepLeft,
    integral_icoConst_unit (d := 0) (c := (1:ℝ) / 2 ^ k) le_rfl
      (le_of_lt (one_div_two_pow_pos k)) (one_div_two_pow_le_one k)
      Ioo_subset_Icc_self Subset.rfl]
  ring

/-- The `gapH`-mass of `thinBox k` is `2^{-k}/2`: positive at every depth. -/
theorem integral_gapH_thinBox (k : ℕ) :
    ∫ z in thinBox k, gapH z = (1 / 2) * (1 / 2 ^ k) := by
  show ∫ z in Icc (0:ℝ) 3 ×ˢ Icc (0:ℝ) ((1:ℝ) / 2 ^ k),
      stepRight z.1 * icoConst 0 1 1 z.2 = (1 / 2) * (1 / 2 ^ k)
  rw [Measure.volume_eq_prod, setIntegral_prod_mul, integral_stepRight,
    integral_icoConst_unit (d := 0) (c := (1:ℝ) / 2 ^ k) le_rfl
      (le_of_lt (one_div_two_pow_pos k)) (one_div_two_pow_le_one k)
      Ioo_subset_Icc_self Subset.rfl]
  ring

/-- The discarded side of the `k`-th cut also has positive `gapG`-mass. -/
theorem integral_gapG_thinBox_false (k : ℕ) :
    ∫ z in thinBox k ∩ halfSpace (ContinuousLinearMap.snd ℝ ℝ ℝ) ((1:ℝ) / 2 ^ (k + 1)) false,
      gapG z = (1 / 2) * (1 / 2 ^ (k + 1)) := by
  rw [thinBox_inter_false]
  show ∫ z in Icc (0:ℝ) 3 ×ˢ Ioc ((1:ℝ) / 2 ^ (k + 1)) ((1:ℝ) / 2 ^ k),
      stepLeft z.1 * icoConst 0 1 1 z.2 = (1 / 2) * (1 / 2 ^ (k + 1))
  rw [Measure.volume_eq_prod, setIntegral_prod_mul, integral_stepLeft,
    integral_icoConst_unit (d := (1:ℝ) / 2 ^ (k + 1)) (c := (1:ℝ) / 2 ^ k)
      (le_of_lt (one_div_two_pow_pos (k + 1))) (one_div_two_pow_succ_le k)
      (one_div_two_pow_le_one k) Ioo_subset_Ioc_self Ioc_subset_Icc_self]
  rw [pow_succ]
  ring

/-- The discarded side of the `k`-th cut also has positive `gapH`-mass. -/
theorem integral_gapH_thinBox_false (k : ℕ) :
    ∫ z in thinBox k ∩ halfSpace (ContinuousLinearMap.snd ℝ ℝ ℝ) ((1:ℝ) / 2 ^ (k + 1)) false,
      gapH z = (1 / 2) * (1 / 2 ^ (k + 1)) := by
  rw [thinBox_inter_false]
  show ∫ z in Icc (0:ℝ) 3 ×ˢ Ioc ((1:ℝ) / 2 ^ (k + 1)) ((1:ℝ) / 2 ^ k),
      stepRight z.1 * icoConst 0 1 1 z.2 = (1 / 2) * (1 / 2 ^ (k + 1))
  rw [Measure.volume_eq_prod, setIntegral_prod_mul, integral_stepRight,
    integral_icoConst_unit (d := (1:ℝ) / 2 ^ (k + 1)) (c := (1:ℝ) / 2 ^ k)
      (le_of_lt (one_div_two_pow_pos (k + 1))) (one_div_two_pow_succ_le k)
      (one_div_two_pow_le_one k) Ioo_subset_Ioc_self Ioc_subset_Icc_self]
  rw [pow_succ]
  ring

/-- **Both sides of every transverse cut are admissible.**

This is exactly the hypothesis `hstep` of `Arlib.exists_cut_chain_extent_halved`, verified along
the chain — and exactly what `Arlib.not_two_sided_of_sign_separated` forbids in the direction
`fst`.  So the choice of which side to keep is genuinely free in the transverse direction, and
genuinely forced in the longitudinal one. -/
theorem two_sided_thinBox (k : ℕ) :
    ∀ side : Bool,
      0 < ∫ z in thinBox k ∩
            halfSpace (ContinuousLinearMap.snd ℝ ℝ ℝ) ((1:ℝ) / 2 ^ (k + 1)) side, gapG z ∧
      0 < ∫ z in thinBox k ∩
            halfSpace (ContinuousLinearMap.snd ℝ ℝ ℝ) ((1:ℝ) / 2 ^ (k + 1)) side, gapH z := by
  intro side
  cases side
  · refine ⟨?_, ?_⟩
    · rw [integral_gapG_thinBox_false]; positivity
    · rw [integral_gapH_thinBox_false]; positivity
  · refine ⟨?_, ?_⟩
    · rw [← thinBox_succ, integral_gapG_thinBox]; positivity
    · rw [← thinBox_succ, integral_gapH_thinBox]; positivity

/-- The transverse extent of `thinBox k` is exactly `[0, 2^{-k}]`. -/
theorem snd_mem_Icc_thinBox (k : ℕ) :
    ∀ z ∈ thinBox k, (ContinuousLinearMap.snd ℝ ℝ ℝ) z ∈ Icc (0:ℝ) ((1:ℝ) / 2 ^ k) :=
  fun _ hz => hz.2

/-- The longitudinal extent of `thinBox k` is `[0, 3]` at every depth: it never shrinks. -/
theorem fst_mem_Icc_thinBox (k : ℕ) :
    ∀ z ∈ thinBox k, (ContinuousLinearMap.fst ℝ ℝ ℝ) z ∈ Icc (0:ℝ) 3 :=
  fun _ hz => hz.1

/-- The needle: the segment `[0,3] × {0}`, the Hausdorff limit of the chain. -/
theorem hausdorffDist_thinBox_le (k : ℕ) :
    hausdorffDist (thinBox k) (Icc (0:ℝ) 3 ×ˢ ({0} : Set ℝ)) ≤ 1 / 2 ^ k := by
  refine hausdorffDist_le_of_mem_dist (le_of_lt (one_div_two_pow_pos k)) ?_ ?_
  · rintro ⟨x, y⟩ hz
    refine ⟨(x, 0), ⟨hz.1, rfl⟩, ?_⟩
    rw [Prod.dist_eq]
    refine max_le (by simp) ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hz.2.1]
    exact hz.2.2
  · rintro ⟨x, y⟩ hz
    refine ⟨(x, 0), ⟨hz.1, ⟨le_rfl, le_of_lt (one_div_two_pow_pos k)⟩⟩, ?_⟩
    have hy : y = 0 := hz.2
    rw [Prod.dist_eq, hy]
    simp

theorem tendsto_one_div_two_pow : Tendsto (fun k : ℕ => (1:ℝ) / 2 ^ k) atTop (𝓝 0) := by
  have h : Tendsto (fun k : ℕ => ((1:ℝ) / 2) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine h.congr fun k => ?_
  rw [div_pow, one_pow]

/-- **The chain converges to an honest needle.** -/
theorem tendsto_hausdorffDist_thinBox :
    Tendsto (fun k => hausdorffDist (thinBox k) (Icc (0:ℝ) 3 ×ˢ ({0} : Set ℝ))) atTop (𝓝 0) :=
  squeeze_zero (fun _ => hausdorffDist_nonneg) hausdorffDist_thinBox_le tendsto_one_div_two_pow

/-- **No cut orthogonal to `fst` is ever two-sided, for any measurable set.**

The planar instance of `Arlib.not_two_sided_of_sign_separated` with `a = 1`, `b = 2`: the
positive parts of `Arlib.gapG` and `Arlib.gapH` are separated by the slab `1 ≤ x < 2`, so in the
longitudinal direction one side of every cut always loses the invariant, at every level, for
every measurable body.  The side is forced, and the forced side keeps the whole slab. -/
theorem not_two_sided_fst_gapBox {C : Set (ℝ × ℝ)} (hC : MeasurableSet C) (s : ℝ) :
    ¬ (∀ side : Bool,
        0 < ∫ z in C ∩ halfSpace (ContinuousLinearMap.fst ℝ ℝ ℝ) s side, gapG z ∧
        0 < ∫ z in C ∩ halfSpace (ContinuousLinearMap.fst ℝ ℝ ℝ) s side, gapH z) :=
  not_two_sided_of_sign_separated (μ := (volume : Measure (ℝ × ℝ))) hC (a := 1) (b := 2)
    (by norm_num) (fun z hz => gapG_nonpos (le_of_lt hz)) (fun z hz => gapH_nonpos hz) s

/-- **The longitudinal extent of every admissible body is at least `1`.**

The planar instance of `Arlib.sub_le_extent_of_sign_separated`. -/
theorem one_le_extent_fst_gapBox {C : Set (ℝ × ℝ)} (hC : MeasurableSet C)
    (hg : 0 < ∫ z in C, gapG z) (hh : 0 < ∫ z in C, gapH z) {p q : ℝ}
    (hCpq : ∀ z ∈ C, (ContinuousLinearMap.fst ℝ ℝ ℝ) z ∈ Icc p q) : 1 ≤ q - p := by
  have := sub_le_extent_of_sign_separated (μ := (volume : Measure (ℝ × ℝ))) hC
    (a := 1) (b := 2) (fun z hz => gapG_nonpos (le_of_lt hz)) (fun z hz => gapH_nonpos hz)
    hg hh hCpq
  linarith

/-- **The capstone: transverse thinness, on the configuration where the diameter cannot shrink.**

For the planar data `Arlib.gapG`, `Arlib.gapH` of `Arlib.Convexity.NeedleLimit` — for which
`Arlib.one_le_diam_bisection_chain` proves *every* bisection body has diameter `≥ 1`, for every
sequence of cut directions — the explicit chain `Arlib.thinBox` satisfies simultaneously:

* `C 0 = gapBox`, and every `C (k+1)` is **literally** the closed side of a halfspace cut of
  `C k` orthogonal to the transverse direction `snd`;
* every `C k` is measurable, convex and inside the box;
* the localisation invariant holds at every depth, with **both** masses exactly `2^{-k}/2` — so
  each cut bisects `∫ g` and `∫ h` simultaneously;
* **both** sides of every cut are admissible, so the retained side was a free choice;
* the transverse extent is exactly `[0, 2^{-k}]`, tending to `0`;
* the longitudinal extent is `[0,3]` at every depth, and every body still carries a chord of
  length at least `1` (the sign-separation obstruction, unbeaten);
* the bodies converge in Hausdorff distance to the segment `[0,3] × {0}` — a genuine needle.

Together with `Arlib.not_two_sided_fst_gapBox` (no cut orthogonal to `fst` is ever two-sided)
this settles the question: a cut rule can preserve the invariant *and* halve a width, in every
direction transverse to the separation, and provably in none along it. -/
theorem transverse_thin_chain_gapBox :
    ∃ C : ℕ → Set (ℝ × ℝ), C 0 = gapBox ∧
      (∀ k, C (k + 1) =
        C k ∩ halfSpace (ContinuousLinearMap.snd ℝ ℝ ℝ) ((1:ℝ) / 2 ^ (k + 1)) true) ∧
      (∀ k, MeasurableSet (C k) ∧ Convex ℝ (C k) ∧ C k ⊆ gapBox ∧
        (∫ z in C k, gapG z) = (1 / 2) * (1 / 2 ^ k) ∧
        (∫ z in C k, gapH z) = (1 / 2) * (1 / 2 ^ k) ∧
        0 < ∫ z in C k, gapG z ∧ 0 < ∫ z in C k, gapH z ∧
        (∀ side : Bool,
          0 < ∫ z in C k ∩
                halfSpace (ContinuousLinearMap.snd ℝ ℝ ℝ) ((1:ℝ) / 2 ^ (k + 1)) side, gapG z ∧
          0 < ∫ z in C k ∩
                halfSpace (ContinuousLinearMap.snd ℝ ℝ ℝ) ((1:ℝ) / 2 ^ (k + 1)) side, gapH z) ∧
        (∀ z ∈ C k, (ContinuousLinearMap.snd ℝ ℝ ℝ) z ∈ Icc (0:ℝ) ((1:ℝ) / 2 ^ k)) ∧
        (∀ z ∈ C k, (ContinuousLinearMap.fst ℝ ℝ ℝ) z ∈ Icc (0:ℝ) 3) ∧
        (∃ x ∈ C k, ∃ y ∈ C k, 1 ≤ dist x y)) ∧
      Tendsto (fun k => hausdorffDist (C k) (Icc (0:ℝ) 3 ×ˢ ({0} : Set ℝ))) atTop (𝓝 0) := by
  refine ⟨thinBox, thinBox_zero, thinBox_succ, fun k => ?_, tendsto_hausdorffDist_thinBox⟩
  have hg : (0:ℝ) < ∫ z in thinBox k, gapG z := by
    rw [integral_gapG_thinBox]; positivity
  have hh : (0:ℝ) < ∫ z in thinBox k, gapH z := by
    rw [integral_gapH_thinBox]; positivity
  exact ⟨measurableSet_thinBox k, convex_thinBox k, thinBox_subset_gapBox k,
    integral_gapG_thinBox k, integral_gapH_thinBox k, hg, hh, two_sided_thinBox k,
    snd_mem_Icc_thinBox k, fst_mem_Icc_thinBox k,
    exists_pair_one_le_dist_of_gap_pos (measurableSet_thinBox k) hg hh⟩

end ThinChain

/-! ### Axiom audit

Every result above must depend on exactly `[propext, Classical.choice, Quot.sound]`.  There are
no `axiom` declarations, no `sorry` and no `native_decide` anywhere in this file. -/

#print axioms apply_mem_Icc_of_mem_halfSpace_true
#print axioms apply_mem_Icc_of_mem_halfSpace_false
#print axioms exists_side_extent_halved
#print axioms exists_side_extent_halved_pos
#print axioms le_of_setIntegral_halfSpace_true_pos
#print axioms lt_of_setIntegral_halfSpace_false_pos
#print axioms cut_level_lt_or_le_of_sign_separated
#print axioms not_two_sided_of_sign_separated
#print axioms sub_le_extent_of_sign_separated
#print axioms exists_cut_chain_extent_halved
#print axioms exists_cut_chain_extent_halved_volume
#print axioms one_le_two_pow_real
#print axioms one_div_two_pow_pos
#print axioms one_div_two_pow_le_one
#print axioms one_div_two_pow_succ_le
#print axioms integral_icoConst_unit
#print axioms thinBox_zero
#print axioms measurableSet_thinBox
#print axioms convex_thinBox
#print axioms thinBox_subset_gapBox
#print axioms thinBox_succ
#print axioms thinBox_inter_false
#print axioms integral_gapG_thinBox
#print axioms integral_gapH_thinBox
#print axioms integral_gapG_thinBox_false
#print axioms integral_gapH_thinBox_false
#print axioms two_sided_thinBox
#print axioms snd_mem_Icc_thinBox
#print axioms fst_mem_Icc_thinBox
#print axioms hausdorffDist_thinBox_le
#print axioms tendsto_one_div_two_pow
#print axioms tendsto_hausdorffDist_thinBox
#print axioms not_two_sided_fst_gapBox
#print axioms one_le_extent_fst_gapBox
#print axioms transverse_thin_chain_gapBox

end Arlib
