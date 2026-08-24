/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.SpeedyToGaussian

/-!
# The level-set step of Cousins–Vempala's `lem:map-speedy-to-ball`

`1409.6011/vol3_journal.tex:942` maps the speedy walk's law `∝ ℓ·f` to the target `∝ f` by a
rejection routine at shrink factor `c = 1 − 1/(2n)`.  Its analysis has one step that is pure
measure theory and independent of everything else in the argument — the passage from a bound
that holds on **each level set of `f`** to a bound on the whole integral (`:963`–`:972`):

> `∫_{μ_L ∩ cK} (1 − ℓ(x)) dx ≤ ε·vol(μ_L ∩ cK)` for every level set `μ_L = {f ≥ L}`
>
> ⟹ `∫_{cK} (1 − ℓ(x))·f(x) dx ≤ ε·∫_{cK} f(x) dx`.

CV justify this with a two-line display that is exactly the layer-cake formula applied twice,
once to each side.  This file proves it, in a form with no `ℓ`, no `f` and no convexity in it:
**if one measure is uniformly `ε`-dominated by another on every superlevel set of a
nonnegative function, its integral of that function is `ε`-dominated too.**

## Why this is the piece worth isolating

The two inputs CV take from Kannan–Lovász–Simonovits 1995 — the per-level-set bound above and
`Q̂(cK) ≥ 1/2` — are **not** in this repository, and `AUDIT.md` §0k's companion note records
that the homothety route cannot supply them (`Arlib.MarkovChains.ell_eq_one_setOf_cube`
caps any argument that only uses the set `{ℓ = 1}`).  Isolating the layer-cake step means the
KLS95 input can be plugged in later as a hypothesis about level sets — its natural shape —
rather than having to be restated globally.

**Nothing here proves `lem:map-speedy-to-ball`.**  The rejection routine, the `10ε` bound and
the two KLS95 inputs are all absent.  This is one lemma of its proof.

## What is proved here

* `Arlib.MarkovChains.lintegral_le_of_superlevel_le` — the general statement.
* `Arlib.MarkovChains.setLIntegral_one_sub_ell_le` — its instance at
  `ν = (1 − ℓ)·1_A·volume` and `ρ = 1_A·volume`, which is CV's display verbatim.

Every declaration is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here.
-/

namespace Arlib.MarkovChains

open MeasureTheory Set
open scoped ENNReal

/-! ## 1. The general layer-cake comparison -/

/-- **If `ν` is `ε`-dominated by `ρ` on every superlevel set of `f`, it is `ε`-dominated on
`∫ f`.**

Both sides are rewritten by the layer-cake formula
(`MeasureTheory.lintegral_eq_lintegral_meas_le`) into integrals over the level parameter `t`,
after which the hypothesis applies pointwise in `t` and the constant comes out of the integral.

This is the step at `1409.6011/vol3_journal.tex:963`–`:972`, with everything specific to
Cousins–Vempala stripped out: no `ℓ`, no Gaussian, no convex body. -/
theorem lintegral_le_of_superlevel_le {E : Type*} [MeasurableSpace E]
    (ν ρ : Measure E) {f : E → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfm : Measurable f) {ε : ℝ≥0∞}
    (hε : ε ≠ ⊤) (h : ∀ t : ℝ, ν {x | t ≤ f x} ≤ ε * ρ {x | t ≤ f x}) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ε * ∫⁻ x, ENNReal.ofReal (f x) ∂ρ := by
  rw [lintegral_eq_lintegral_meas_le ν (Filter.Eventually.of_forall hf0) hfm.aemeasurable,
    lintegral_eq_lintegral_meas_le ρ (Filter.Eventually.of_forall hf0) hfm.aemeasurable,
    ← lintegral_const_mul' _ _ hε]
  exact lintegral_mono fun t => h t

/-! ## 2. Cousins–Vempala's display, verbatim -/

/-- **`∫_A (1 − ℓ)·f ≤ ε·∫_A f` from the per-level-set bound** — the step of
`lem:map-speedy-to-ball` at `1409.6011/vol3_journal.tex:963`.

`A` is CV's shrunken body `cK`; the hypothesis is their

    ∫_{μ_L ∩ cK} (1 − ℓ(x)) dx ≤ ε · vol(μ_L ∩ cK)

for every level set `μ_L = {x | L ≤ f x}`, written here with the deficit `1 − ℓ` carried as an
arbitrary nonnegative measurable `g` — nothing in the argument uses that `g` is a local
conductance deficit.

**The hypothesis is exactly what CV import from Kannan–Lovász–Simonovits 1995 and do not
prove; it is carried here, not established.** -/
theorem setLIntegral_one_sub_ell_le {E : Type*} [MeasurableSpace E] (μ : Measure E)
    {A : Set E} (hA : MeasurableSet A) {g : E → ℝ≥0∞} (hgm : Measurable g)
    {f : E → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hfm : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ ⊤)
    (hlevel : ∀ t : ℝ, ∫⁻ x in A ∩ {x | t ≤ f x}, g x ∂μ ≤ ε * μ (A ∩ {x | t ≤ f x})) :
    ∫⁻ x in A, g x * ENNReal.ofReal (f x) ∂μ ≤ ε * ∫⁻ x in A, ENNReal.ofReal (f x) ∂μ := by
  have hlev : ∀ t : ℝ, ((μ.restrict A).withDensity g) {x | t ≤ f x}
      ≤ ε * (μ.restrict A) {x | t ≤ f x} := by
    intro t
    have hmeas : MeasurableSet {x | t ≤ f x} := measurableSet_le measurable_const hfm
    rw [withDensity_apply _ hmeas, Measure.restrict_restrict hmeas,
      Measure.restrict_apply hmeas]
    simpa [Set.inter_comm] using hlevel t
  have hmain := lintegral_le_of_superlevel_le ((μ.restrict A).withDensity g) (μ.restrict A)
    hf0 hfm hε hlev
  rwa [lintegral_withDensity_eq_lintegral_mul _ hgm hfm.ennreal_ofReal] at hmain

section AxiomCheck

#print axioms Arlib.MarkovChains.lintegral_le_of_superlevel_le
#print axioms Arlib.MarkovChains.setLIntegral_one_sub_ell_le

end AxiomCheck

end Arlib.MarkovChains
