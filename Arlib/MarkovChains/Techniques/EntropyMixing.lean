/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# A mixing time in total variation from entropy contraction

`Techniques/EntropyDecay.lean` runs entropy contraction to a bound on the
relative entropy of the law of the chain, `D_KL(P^t(x, ·) ‖ μ) ≤ ε` once
`t ≥ ρ⁻¹ ln(ln(1/m)/ε)`.  `Techniques/Pinsker.lean` converts a bound on `D_KL`
into a bound on the total variation distance, with the sharp constant.  Neither
module imports the other, and this one is nothing but their composition.

## What Pinsker costs, and what it does not

`mixesWithin_of_klDiv_le_two_mul_sq` consumes `D_KL ≤ 2δ²`, so the composite is
the entropy bound at `ε = 2δ²`: the `ε` inside the logarithm becomes `2δ²`, and
**that substitution is the whole of Pinsker's cost**.  Two things follow, and
they point in opposite directions.

* The `μ_min` dependence is untouched.  It is `ln ln(1/m)` before and after,
  because Pinsker only ever sees the accuracy parameter.  This is the point of
  the entropy route and it survives intact.
* The `δ` dependence is halved in rate.  `klDiv` decays like `(1 − ρ)^t` and
  Pinsker takes a square root, so the *distance* decays like `(1 − ρ)^{t/2}`:
  the coefficient of `ln(1/δ)` is `2ρ⁻¹` here against `γ⁻¹` for the variance
  route (`MixingTime.mixesWithin_of_log_le`).  That factor two is a genuine
  loss, not an artefact of the bookkeeping.  The sharp constant `2` of Pinsker
  is the part of the exchange that is a *gain*: it contributes `−ρ⁻¹ ln 2`.

`Chains/OptimalMixingTV.lean` instantiates all of this for the Gibbs sampler of
a product measure and computes the exact crossover with the variance route.

## The composition must not be routed through χ²

`Techniques/Pinsker.lean` records that chaining Pinsker after
`EntropyVariational.klDiv_le_chiSq` gives `‖·‖_TV ≤ √(D_{χ²}/2)`, which is worse
than the direct `TotalVariation.tvDist_sq_le_chiSq` by a factor `√2`; Pinsker
earns its place only on divergence bounds of *entropy* origin.  The divergence
bound consumed below is of entropy origin, from `EntropyContraction` alone, and
`chiSq` occurs nowhere in the chain.

## Main declarations

* **`EntropyContraction.mixesWithin_of_log_le`** — a reversible chain with fully
  supported `μ ≥ m` that contracts entropy at rate `ρ ≤ 1` satisfies
  `MixesWithin P μ δ t` as soon as `t ≥ ρ⁻¹·ln(ln(1/m)/(2δ²))`.  This *verifies*
  the expression predicted by the closing section of `Techniques/Pinsker.lean`.
* `EntropyContraction.mixesWithin_of_klDiv_bound` — the same composition with the
  divergence bound supplied by hand, for callers who have one from another
  source.

Everything here is proved from first principles with no `sorry`; no eigenvalue,
and no spectral notion beyond the Dirichlet form, appears anywhere.
-/
import Arlib.MarkovChains.Techniques.EntropyDecay
import Arlib.MarkovChains.Techniques.Pinsker

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The generic composition

The shape of the composition is forced by the two interfaces.
`EntropyContraction.klDiv_iter_row_le_of_log_le` produces `D_KL ≤ ε` and
`mixesWithin_of_klDiv_le_two_mul_sq` consumes `D_KL ≤ 2δ²`, so the composite is
the first at `ε = 2δ²`, and the `ε` inside the logarithm becomes `2δ²`.  That
substitution is the whole of Pinsker's cost, and the module docstring accounts
for it. -/

section Generic

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- **Entropy contraction plus Pinsker is a mixing time in total variation.**

Let `P` be reversible with respect to a fully supported `μ` bounded below by `m`,
and let `P` contract entropy at rate `ρ ≤ 1`.  Then

  `‖P^t(x, ·) − μ‖_TV ≤ δ`  as soon as  `ln(ln(1/m)/(2δ²)) ≤ ρ·t`,

that is, after `t ≥ ρ⁻¹·ln(ln(1/m)/(2δ²))` steps, from every starting state.

This is the statement the closing section of `Techniques/Pinsker.lean` predicts,
and it holds exactly as predicted: `EntropyContraction.klDiv_iter_row_le_of_log_le`
at `ε = 2δ²` fed to `mixesWithin_of_klDiv_le_two_mul_sq`.  The hypotheses are the
union of the two, with `0 < ε` becoming `0 < δ` and nothing else added.

Two remarks on what the bound is and is not.

* The `μ_min` dependence is `ln ln(1/m)`, not `ln(1/m)`.  That is the point of
  the entropy route, and it survives Pinsker intact, because Pinsker touches only
  the accuracy parameter.
* Pinsker converts a divergence decaying at rate `ρ` into a distance decaying at
  rate `ρ/2`, so the coefficient of `ln(1/δ)` here is `2ρ⁻¹`, against `γ⁻¹` for
  the variance route (`MixingTime.mixesWithin_of_log_le`).  This is a genuine
  loss of a factor two in the `δ`-dependence, not an artefact.

The composition must not be routed through χ²: `EntropyVariational.klDiv_le_chiSq`
followed by Pinsker is worse than `tvDist_sq_le_chiSq` by `√2`.  It is not routed
through χ² — the divergence bound consumed here is of entropy origin, from
`EntropyContraction` alone. -/
theorem EntropyContraction.mixesWithin_of_log_le {μ : FinDist Ω} {P : FinChain Ω} {ρ : ℝ}
    (hrev : Reversible μ P) (hpos : ∀ x, 0 < μ x) (h : EntropyContraction μ P ρ)
    (hρ : ρ ≤ 1) {m δ : ℝ} (hm : 0 < m) (hmin : ∀ x, m ≤ μ x)
    (hL : 0 < Real.log (1 / m)) (hδ : 0 < δ) {t : ℕ}
    (ht : Real.log (Real.log (1 / m) / (2 * δ ^ 2)) ≤ ρ * t) :
    MixesWithin P μ δ t := by
  refine mixesWithin_of_klDiv_le_two_mul_sq hpos hδ.le fun x => ?_
  exact h.klDiv_iter_row_le_of_log_le hrev hpos hρ hm hmin hL (by positivity) ht x

/-- **A divergence bound of any provenance is a mixing statement**, provided the
provenance is not χ².

This is `mixesWithin_of_klDiv_le_two_mul_sq` under its intended name, recorded
here so that the composition above can be reused by a caller who obtains
`D_KL(P^t(x,·) ‖ μ) ≤ 2δ²` from something other than `EntropyContraction` — a
sharper tensorization statement, say.  The warning attached to it is the one in
`Techniques/Pinsker.lean`: a bound obtained as `klDiv ≤ chiSq` should be sent to
`tvDist_sq_le_chiSq` instead, which is better by `√2`. -/
theorem EntropyContraction.mixesWithin_of_klDiv_bound {μ : FinDist Ω} {P : FinChain Ω}
    {δ : ℝ} {t : ℕ} (hpos : ∀ x, 0 < μ x) (hδ : 0 ≤ δ)
    (h : ∀ x, klDiv ((P.iter t).row x) μ ≤ 2 * δ ^ 2) : MixesWithin P μ δ t :=
  mixesWithin_of_klDiv_le_two_mul_sq hpos hδ h

end Generic

end Arlib.MarkovChains
