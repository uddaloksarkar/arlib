/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.ChordContinuity
import Arlib.Convexity.LocalizationNeedleInBody

/-!
# Lovász–Vempala Theorem 4.2 with **no isoperimetry hypothesis**

`Arlib.MarkovChains.conductance_hitAndRun_ge`
(`Arlib/MarkovChains/Continuous/HitAndRunConductance.lean`) is Lovász–Vempala Theorem 4.2 —
the conductance of hit-and-run on a convex body containing the unit ball is `Ω(1/(nD))`.  As
stated there it carries two mathematical hypotheses: `hLem41` (the one-step overlap, Lovász
1999 Lemma 8) and `hIso` (the weighted cross-ratio isoperimetric inequality, the paper's
Theorem 2.1).

`hIso` was the deep one.  It has now been eliminated in three steps, each in its own file:

1. `Arlib.MarkovChains.conductance_hitAndRun_ge_of_transfer_of_localization`
   (`Arlib/Convexity/IsoConcaveWeight.lean`) replaces `hIso` by two ordinary obligations —
   `htrans` (the chord bound survives a small perturbation of the endpoints) and `hloc` (the
   Localization Lemma, one-equality-one-inequality form, needle inside the body).  The
   generality that made `hIso` unreachable — it quantifies over *arbitrary*, not even
   measurable, weights — is not used by the consumer, which passes the single concave weight
   `stepRadius K (63/64)/(48·D·√n)`.
2. `Arlib.htrans_of_compact` (`Arlib/Convexity/ChordContinuity.lean`) proves `htrans`, via
   the first continuity results for `chordLow`/`chordHigh` in this repository.
3. `Arlib.hloc_needle_in_body` (`Arlib/Convexity/LocalizationNeedleInBody.lean`) proves
   `hloc` — Kannan–Lovász–Simonovits 1995, Corollary 2.4 in substance.

This file is the composition, and contains no new mathematics.

## What is proved here

* `Arlib.conductance_hitAndRun_ge_isoFree` — Theorem 4.2 with **`hIso`, `htrans` and `hloc`
  all gone**.  The only mathematical hypothesis left is `hLem41`.

## Scope — read this before quoting the result

**`hLem41` is still a hypothesis here, and in the shape below it is UNSATISFIABLE.**  It
quantifies over all `u, v ∈ K`, and `Arlib.MarkovChains.tvLe_hitAndRun_lemma41_uncond`
(`Arlib/MarkovChains/Continuous/SphereCap.lean`) — which proves Lemma 4.1 outright, at
`1 - 1/8000` for `n ≥ 1100` — requires `chordLow K u v < 0`, which **fails at every boundary
point**: for `u ∈ frontier K` and `v ∈ interior K` the chord cannot extend past `u`, so
`chordLow K u v = 0`.  So no bundle asserting `hLem41` across all of `K` is inhabited, and a
theorem carrying it is vacuous until the binder is weakened to `interior K` — which is sound,
because `conductance_hitAndRun_ge_of_tv`'s proof cuts `S₁'`, `S₂'` to `interior K` and uses
`hLem41` only there (that file's own module docstring, §"Two places where the formalisation
is more careful than the paper").

**Therefore this theorem is stated, not celebrated.**  It records that the isoperimetry side
is finished; it is not yet a conductance bound anyone can use.  The remaining work is the
interior-isation of the `hLem41` binder, and it is in progress in
`Arlib/MarkovChains/Continuous/HitAndRunConductance.lean`.

Two further caveats, both inherited:

* **`2 ≤ n`**, not `1 ≤ n`, from `hloc_needle_in_body` — the pencil bisection of
  `exists_flat_cut_chain_collinear_compact_ge` needs a codimension-two flat.
* the constant `1 - 1/500` in `hLem41` is **not achievable** (`HitAndRunOverlap.lean`'s
  module docstring proves the paper's constant fails); the achievable value is `1 - 1/8000`,
  and `Arlib.MarkovChains.conductance_hitAndRun_ge_param`
  (`HitAndRunConductanceParam.lean`) is the version that accepts it, at
  `Φ ≥ c/(245760·n·D)`.
-/

namespace Arlib

open MeasureTheory Arlib.MarkovChains

variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}

/-- **Lovász–Vempala Theorem 4.2 with no isoperimetry hypothesis of any kind.**

`hIso`, and the `htrans`/`hloc` pair it was decomposed into, are all discharged.  The only
mathematical hypothesis left is `hLem41`, the one-step overlap.

⚠ **`hLem41` in this shape is unsatisfiable** — see the module docstring.  It quantifies over
all `u, v ∈ K`, and Lemma 4.1 needs `chordLow K u v < 0`, which fails on the frontier.  This
statement is therefore a record that the isoperimetry side is complete, **not** a usable
conductance bound.  Weakening the binder to `interior K` is what makes it usable, and is
sound because the underlying proof uses `hLem41` only on the interior. -/
theorem conductance_hitAndRun_ge_isoFree (hn : 2 ≤ n)
    (hKc : Convex ℝ K) (hKcl : IsClosed K) (hKm : MeasurableSet K)
    (hKb : Bornology.IsBounded K)
    {z : EuclideanSpace ℝ (Fin n)} (hball : Metric.closedBall z 1 ⊆ K)
    {D : ℝ} (hD : Metric.diam K ≤ D)
    (hLem41 : ∀ u ∈ K, ∀ v ∈ K, crossRatioDist K u v < 1 / 8 →
      dist u v < 2 / Real.sqrt n * max (medianStep K u) (medianStep K v) →
      Arlib.TVLe (hitAndRun K u) (hitAndRun K v) (ENNReal.ofReal (1 - 1 / 500))) :
    ENNReal.ofReal (1 / (2 ^ 27 * (n : ℝ) * D))
      ≤ conductance (hitAndRun K) (uniformOn volume K) :=
  conductance_hitAndRun_ge_of_localization (by omega) hKc hKcl hKm hKb hball hD hLem41
    (hloc_needle_in_body hn hKc hKcl hKb)

section AxiomCheck

#print axioms Arlib.conductance_hitAndRun_ge_isoFree

end AxiomCheck

end Arlib
