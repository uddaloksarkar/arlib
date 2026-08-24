/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.GaussianCooling.PhaseVar
import Mathlib.Analysis.Convex.Measure

/-!
# The phase law does not distinguish `K` from its interior

The volume algorithm's interface (`Ttc/Volume/CVAmended.lean`) deliberately carries **no**
`MeasurableSet K` binder, and must not: a convex set need not be Borel (an open ball together
with a non-Borel subset of its bounding sphere is convex and not Borel), so the hypothesis
`∀ K, Convex ℝ K → … → MeasurableSet K` would be *false* and any construction carrying it
would be vacuous.  `Ttc/Volume/CousinsVempala.lean:819` records this.

The sampler chain, on the other hand, needs measurability everywhere — `ellGaussianProb`,
`condOn`, `speedyWalk` and the whole of `Arlib/Convexity/GaussianCooling/WarmSpeedy.lean` all
take `MeasurableSet K`.

**This file is the bridge.**  The sampler runs on `interior K`, which is open (hence Borel),
convex, and contains the unit ball whenever `K` does; and the phase law it targets is
*literally equal* to the phase law on `K`:

    coolLaw m σsq (interior K) i  =  coolLaw m σsq K i.

Not close in total variation — equal.  The reason is that `Convex.addHaar_frontier` gives
`vol(frontier K) = 0`, hence `interior K =ᵐ K`, and both `Measure.restrict` and the
normaliser `chain` read the set only through `volume.restrict`, which
`MeasureTheory.Measure.restrict_congr_set` shows is insensitive to null differences —
for *arbitrary* sets, with no measurability hypothesis on `K` anywhere in this file.

## What is proved here

* `Arlib.GaussianCooling.interior_ae_eq` — `interior K =ᵐ[volume] K` for convex `K`.
* `Arlib.GaussianCooling.restrict_interior` — `volume.restrict (interior K) = volume.restrict K`.
* `Arlib.GaussianCooling.chain_interior` — the normaliser agrees.
* `Arlib.GaussianCooling.coolLaw_interior` — **the bridge**, an equality of measures.
* `Arlib.GaussianCooling.volume_interior` — `vol(interior K) = vol(K)`, so the quantity the
  algorithm reports is unchanged.
* `Arlib.GaussianCooling.interior_admissible` — `interior K` is convex, measurable, contains
  the unit ball, and has the same (finite, nonzero) volume: the hypothesis bundle the sampler
  chain wants, supplied from the bundle the interface offers.

## Scope

This removes the measurability mismatch at the *phase law*.  It says nothing about the score,
which `Ttc` already takes on `interior K` for the same reason
(`Arlib/Convexity/GaussianCooling/PhaseFromTVGeneral.lean:198`), and nothing about any other
binder of the interface.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set

variable {n : ℕ}

/-! ## 1. A convex set agrees with its interior up to a null set -/

/-- **`interior K =ᵐ K`** for convex `K`, because `K \ interior K ⊆ frontier K` and a convex
set has null frontier (`Convex.addHaar_frontier`).

No measurability hypothesis: `ae_eq_set` is a statement about two `volume`-measures of
differences, and both are bounded by sets that *are* measurable. -/
theorem interior_ae_eq {K : Set (EuclSpace n)} (hKc : Convex ℝ K) :
    interior K =ᵐ[(volume : Measure (EuclSpace n))] K := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · -- `interior K \ K = ∅`
    have : interior K \ K = ∅ := by
      rw [Set.diff_eq_empty]
      exact interior_subset
    rw [this, measure_empty]
  · -- `K \ interior K ⊆ frontier K`
    refine measure_mono_null (fun x hx => ?_) (Convex.addHaar_frontier volume hKc)
    exact ⟨subset_closure hx.1, hx.2⟩

/-- **The restricted measures coincide.**  `Measure.restrict_congr_set` needs only the
almost-everywhere equality, and holds for arbitrary sets. -/
theorem restrict_interior {K : Set (EuclSpace n)} (hKc : Convex ℝ K) :
    (volume : Measure (EuclSpace n)).restrict (interior K)
      = (volume : Measure (EuclSpace n)).restrict K :=
  Measure.restrict_congr_set (interior_ae_eq hKc)

/-- **The volume is unchanged**, so the number the algorithm reports is the same. -/
theorem volume_interior {K : Set (EuclSpace n)} (hKc : Convex ℝ K) :
    volume (interior K) = volume K := by
  have h := restrict_interior hKc
  have h1 : (volume : Measure (EuclSpace n)).restrict (interior K) univ = volume (interior K) := by
    rw [Measure.restrict_apply_univ]
  have h2 : (volume : Measure (EuclSpace n)).restrict K univ = volume K := by
    rw [Measure.restrict_apply_univ]
  rw [← h1, ← h2, h]

/-! ## 2. The normaliser and the phase law -/

/-- **The chain normaliser agrees on `K` and its interior.**  `chain` is a set integral, i.e.
an integral against `volume.restrict`, so this is `restrict_interior` transported. -/
theorem chain_interior (m : ℕ) (σsq : ℕ → ℝ) {K : Set (EuclSpace n)} (hKc : Convex ℝ K)
    (i : ℕ) : chain m σsq (interior K) i = chain m σsq K i := by
  rw [chain_def, chain_def, restrict_interior hKc]

/-- **The bridge: the phase law on `interior K` *is* the phase law on `K`.**

An equality of measures, not a total-variation estimate.  Both the base measure
(`volume.restrict`) and the density's normaliser (`chain`) are insensitive to the null
difference between `K` and `interior K`.

This is what lets the sampler chain — which needs `MeasurableSet` everywhere — run on
`interior K` while targeting the interface's `coolLaw … K i`. -/
theorem coolLaw_interior (m : ℕ) (σsq : ℕ → ℝ) {K : Set (EuclSpace n)} (hKc : Convex ℝ K)
    (i : ℕ) : coolLaw m σsq (interior K) i = coolLaw m σsq K i := by
  unfold coolLaw
  rw [restrict_interior hKc, chain_interior m σsq hKc i]

/-! ## 3. The admissibility bundle -/

/-- **`interior K` satisfies everything the sampler chain asks of a body**, given only what
the volume algorithm's interface offers about `K`: convexity, the unit ball, and finite
volume.  In particular `MeasurableSet (interior K)` holds because the interior is open —
this is the hypothesis that is *unavailable* for `K` itself.

`ball 0 1 ⊆ interior K` is immediate: the ball is open and contained in `K`, and the interior
is the largest open subset. -/
theorem interior_admissible {K : Set (EuclSpace n)} (hKc : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    MeasurableSet (interior K) ∧ Convex ℝ (interior K) ∧
      ball (0 : EuclSpace n) 1 ⊆ interior K ∧
      volume (interior K) ≠ 0 ∧ volume (interior K) ≠ ⊤ := by
  refine ⟨isOpen_interior.measurableSet, hKc.interior, ?_, ?_, ?_⟩
  · exact interior_maximal hball isOpen_ball
  · rw [volume_interior hKc]
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hball))
    exact Metric.measure_ball_pos volume (0 : EuclSpace n) one_pos
  · rw [volume_interior hKc]
    exact hfin

section AxiomCheck

#print axioms Arlib.GaussianCooling.interior_ae_eq
#print axioms Arlib.GaussianCooling.restrict_interior
#print axioms Arlib.GaussianCooling.volume_interior
#print axioms Arlib.GaussianCooling.chain_interior
#print axioms Arlib.GaussianCooling.coolLaw_interior
#print axioms Arlib.GaussianCooling.interior_admissible

end AxiomCheck

end Arlib.GaussianCooling
