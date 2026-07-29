/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Arlib.Approximation.RejectionCollect

/-!
# The conditional law of a failing draw, and `RejectionCollect` without its hypothesis

`Arlib.Approximation.RejectionCollect` states every one of its results against a
*given* pair `(s, ν)` with

  `d (some x) = s * ν x`   (`hs`)

— the oracle's success probability and its conditional law given success.  That
is the right shape for a caller who already knows what `ν` is, and it is what
makes `collectLaw_toOuterMeasure` an identity with no side condition at all.
It is the wrong shape for a caller who has only the oracle: producing `ν` from
`d` means dividing by the success probability, which needs that probability to be
nonzero and finite, and constructing a `PMF` out of the quotient.

This module does that once.

## Main definitions

* `succProb d = ∑' x, d (some x)` — the probability that one draw succeeds.
* `condDraw d hp` — `d` conditioned on success, as a `PMF Ω`.  The `PMF`
  obligation is where `succProb_ne_top` is needed: `∑' x, d (some x) / p = p / p`
  is `1` only because `p ≠ 0` *and* `p ≠ ⊤`, and the second is not automatic for
  an arbitrary `ℝ≥0∞`-valued family — it holds here because `d` is a `PMF`.

## Main results

* `succProb_mul_condDraw` — the factorisation
  `d (some x) = succProb d * condDraw d hp x`, i.e. exactly `RejectionCollect`'s
  hypothesis `hs`, discharged.  (`succProb_le_one'` carries a prime: the
  unprimed name is `RejectionCollect`'s lemma about a *supplied* `s`.)
* `condLaw_collectLaw_of_pos`, `collectLaw_full_of_pos` — `RejectionCollect`'s
  two headline results with the hypothesis replaced by `succProb d ≠ 0`.  So
  **the loop's survivors are i.i.d. `condDraw d`, conditioned on the loop
  collecting a full complement**, for every failing oracle whose success
  probability is positive, with nothing supplied by the caller.

## What is *not* here

**No repair of `RejectionCollect`'s shape.**  The hypothesis form is kept and
re-exported rather than replaced: a caller who knows `ν` on other grounds — for
instance because a separate theorem says the draw is *uniform* on some set —
wants to name that `ν` and not `condDraw`, and `condDraw d hp = ν` would then be
an extra obligation rather than a saving.

**Nothing about the multiset image.**  A loop that accumulates a *multiset*
rather than a list is the image of `collectLaw` under `List → Multiset`, and the
conditional law of its output is therefore the image of `iidList ν k` — which
assigns a multiset the sum of its orderings' probabilities, i.e. a multinomial
coefficient times `∏ ν`.  The identity `Pr[sketch = ↑L ∣ full] = ∏ x ∈ L, ν x`,
which is the shape in which the claim is natural to state for a sketch, is
therefore **false** as written: at `k = 2` and `x ≠ y` the multiset `{x, y}` is
reached along two orderings and its conditional probability is `2 · ν x · ν y`.
Only the list-level statement is correct, and a caller whose loop accumulates a
multiset must carry the coefficient.  `CQCount.Capstone.Repair.SketchIID` is such
a caller.

**No positivity for free.**  `succProb d ≠ 0` is a real hypothesis: an oracle
that always fails has `succProb = 0`, no conditional law, and a collection loop
that never completes.
-/

namespace Arlib.Approximation

open scoped ENNReal

universe u

variable {Ω : Type u}

/-- The probability that one draw from a failing oracle succeeds. -/
noncomputable def succProb (d : PMF (Option Ω)) : ℝ≥0∞ := ∑' x : Ω, d (some x)

/-- Failure and success exhaust the outcomes. -/
theorem none_add_succProb (d : PMF (Option Ω)) : d none + succProb d = 1 := by
  rw [succProb, ← tsum_option]
  exact d.tsum_coe

theorem succProb_le_one' (d : PMF (Option Ω)) : succProb d ≤ 1 :=
  (none_add_succProb d) ▸ le_add_self

theorem succProb_ne_top (d : PMF (Option Ω)) : succProb d ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (succProb_le_one' d)

/-- **The oracle conditioned on success.** -/
noncomputable def condDraw (d : PMF (Option Ω)) (hp : succProb d ≠ 0) : PMF Ω :=
  ⟨fun x => d (some x) / succProb d, by
    have h : ∑' x : Ω, d (some x) / succProb d = (1 : ℝ≥0∞) := by
      simp only [ENNReal.div_eq_inv_mul]
      rw [ENNReal.tsum_mul_left, ← succProb, ENNReal.inv_mul_cancel hp (succProb_ne_top d)]
    exact h ▸ ENNReal.summable.hasSum⟩

@[simp] theorem condDraw_apply (d : PMF (Option Ω)) (hp : succProb d ≠ 0) (x : Ω) :
    condDraw d hp x = d (some x) / succProb d := rfl

/-- **`RejectionCollect`'s hypothesis, discharged.** -/
theorem succProb_mul_condDraw (d : PMF (Option Ω)) (hp : succProb d ≠ 0) (x : Ω) :
    d (some x) = succProb d * condDraw d hp x := by
  rw [condDraw_apply, ENNReal.div_eq_inv_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel hp (succProb_ne_top d), one_mul]

/-- **The survivors of the rejection loop are i.i.d. from the conditioned law**,
with nothing assumed but that a draw can succeed.

`RejectionCollect.condLaw_collectLaw` with `ν := condDraw d hp` and `s :=
succProb d`.  Read with `collectLaw_full_of_pos`, which computes the left factor,
this says: conditioned on the loop having collected its full complement, the law
of what it collected is exactly `k` independent draws from `condDraw d hp`
appended to what it started with.  The adaptive stopping rule — the loop halts as
soon as the quota is met, so the number of oracle calls is a random variable
depending on the draws already made — biases nothing. -/
theorem condLaw_collectLaw_of_pos {d : PMF (Option Ω)} (hp : succProb d ≠ 0)
    (h c : ℕ) (acc : List Ω) (A : Set (List Ω)) :
    (collectLaw d h c acc).toOuterMeasure ({l : List Ω | h ≤ l.length} ∩ A)
      = (collectLaw d h c acc).toOuterMeasure {l : List Ω | h ≤ l.length}
          * (iidList (condDraw d hp) (h - acc.length)).toOuterMeasure ((acc ++ ·) ⁻¹' A) :=
  condLaw_collectLaw (succProb_mul_condDraw d hp) h c acc A

/-- The completion probability, likewise. -/
theorem collectLaw_full_of_pos {d : PMF (Option Ω)} (hp : succProb d ≠ 0)
    (h c : ℕ) (acc : List Ω) :
    (collectLaw d h c acc).toOuterMeasure {l : List Ω | h ≤ l.length}
      = binTail (d none) (succProb d) c (h - acc.length) :=
  collectLaw_full (ν := condDraw d hp) (succProb_mul_condDraw d hp) h c acc

end Arlib.Approximation
