/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.KLS97Shell
import Arlib.Probability.Rejection
import Arlib.MarkovChains.Continuous.SpeedyGaussian

/-!
# On the shrunken body the speedy law **is** the target

Cousins–Vempala's `lem:map-speedy-to-ball` (`1409.6011/vol3_journal.tex:942`) exists to correct
for the factor `ℓ` between the speedy walk's stationary law `∝ 1_K·ℓ·γ` and the target
`∝ 1_K·γ`.  `Arlib.MarkovChains.ell_eq_one_on_shrunken`
(`Arlib/MarkovChains/Continuous/KLS97Shell.lean`) shows that at the shrink factor
`c = 1 − 1/(2n)` and step `δ ≤ 1 − c`, the local conductance is **identically `1`** on `c·K`.

So on `c·K` there is nothing to correct: the two measures coincide there, exactly.  That is
what this file records, and it is the step that makes the rest of `lem:map-speedy-to-ball`
plumbing rather than estimation.

## What is proved here

* `Arlib.MarkovChains.ellGaussianMeasure_restrict_shrunken` — the two unnormalised measures
  agree as measures when restricted to `c·K`.
* `Arlib.MarkovChains.condOn_ellGaussianMeasure_shrunken` — hence conditioning either on
  `c·K` gives the *same* probability measure:

      condOn (speedy law) (c·K)  =  condOn (target) (c·K).

  No total variation, no `ε`: an equality.

## Scope

This is one step of `lem:map-speedy-to-ball`, and the file proves nothing else.  The rescaling
`v = u/c`, the acceptance test `f(v)/f(cv)`, the propagation of the sampler's own total
variation error, and the `10ε` conclusion are **not** here.  Nor is the regime restriction
lifted: `δ ≤ 1 − c` is required, which is stronger than Cousins–Vempala's step size — see
`KLS97Shell.lean`'s module docstring for what that costs.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric
open scoped ENNReal Pointwise

variable {n : ℕ}

/-- **The speedy law and the target agree on the shrunken body, as measures.**

`ellGaussianMeasure K δ s = (volume.restrict K).withDensity (ℓ·γ)` is the speedy walk's
stationary measure; `(volume.restrict K).withDensity γ` is the target.  Restricted to `c·K`
they are equal, because `ℓ ≡ 1` there (`Arlib.MarkovChains.ell_eq_one_on_shrunken`) and
`c·K ⊆ K`.

The hypotheses are exactly those of `ell_eq_one_on_shrunken` plus measurability of `K`. -/
theorem ellGaussianMeasure_restrict_shrunken {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {c δ s : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hδ : 0 < δ) (hδc : δ ≤ 1 - c) :
    (ellGaussianMeasure K δ s).restrict (c • K)
      = ((volume.restrict K).withDensity (gaussianWeight s)).restrict (c • K) := by
  have hcKm : MeasurableSet (c • K) := measurableSet_smul_set hK (ne_of_gt hc0)
  have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := hball (mem_ball_self one_pos)
  have hsub : c • K ⊆ K := smul_subset_of_convex hKc h0K hc0.le hc1.le
  rw [ellGaussianMeasure, restrict_withDensity hcKm,
    restrict_withDensity hcKm]
  refine withDensity_congr_ae ?_
  refine (ae_restrict_iff' ?_).2 ?_
  · exact hcKm
  refine Filter.Eventually.of_forall fun x hx => ?_
  simp only
  rw [ell_eq_one_on_shrunken hKc hball hc0 hc1 hδ hδc hx, one_mul]

/-- **Conditioning either law on the shrunken body gives the same probability measure.**

    condOn (speedy law) (c·K)  =  condOn (target) (c·K)

exactly — this is Cousins–Vempala's rejection correction becoming trivial in the regime
`δ ≤ 1 − c`.  Both sides are `Arlib.condOn`, and the proof is
`ellGaussianMeasure_restrict_shrunken` together with the fact that `condOn` reads its measure
only through `μ (c·K)` and `μ.restrict (c·K)`, both of which are determined by that
restriction. -/
theorem condOn_ellGaussianMeasure_shrunken {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {c δ s : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hδ : 0 < δ) (hδc : δ ≤ 1 - c) :
    Arlib.condOn (ellGaussianMeasure K δ s) (c • K)
      = Arlib.condOn ((volume.restrict K).withDensity (gaussianWeight s))
          (c • K) := by
  have hcKm : MeasurableSet (c • K) := measurableSet_smul_set hK (ne_of_gt hc0)
  have hres := ellGaussianMeasure_restrict_shrunken hK hKc hball hc0 hc1 hδ hδc (s := s)
  have hmass : ellGaussianMeasure K δ s (c • K)
      = ((volume.restrict K).withDensity (gaussianWeight s)) (c • K) := by
    have h1 : ellGaussianMeasure K δ s (c • K)
        = (ellGaussianMeasure K δ s).restrict (c • K) (c • K) := by
      rw [Measure.restrict_apply hcKm, Set.inter_self]
    have h2 : ((volume.restrict K).withDensity (gaussianWeight s)) (c • K)
        = (((volume.restrict K).withDensity (gaussianWeight s)).restrict (c • K)) (c • K) := by
      rw [Measure.restrict_apply hcKm, Set.inter_self]
    rw [h1, h2, hres]
  rw [Arlib.condOn_def, Arlib.condOn_def, hres, hmass]

section AxiomCheck

#print axioms Arlib.MarkovChains.ellGaussianMeasure_restrict_shrunken
#print axioms Arlib.MarkovChains.condOn_ellGaussianMeasure_shrunken

end AxiomCheck

end Arlib.MarkovChains
