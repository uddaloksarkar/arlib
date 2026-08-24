/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.PhaseVar
import Arlib.MarkovChains.Continuous.MetropolisMixing

/-!
# Does the new Metropolis–Gaussian mixing bound deliver `hphase_mean`?  Half of it does.

`Ttc/Volume/CVInstantiate.lean` leaves exactly two hypotheses of the Cousins–Vempala volume
assembly on the table, `hphase_mean` and `hphase_var`, and says of the first (`:80-83`):

> No mixing bound can deliver this: a Markov chain run for finitely many steps is at
> total-variation distance `> 0` from its stationary law, which makes the score's mean the
> ratio only up to an error, never on the nose.

That paragraph was written when no mixing bound existed for the relevant kernel.  One now
does — `Arlib.MarkovChains.mixesWithin_lazy_metropolisGaussian_at_operative_step`
(`MetropolisMixing.lean:161`).  This file settles, in Lean, what that changes.  Every
declaration below is a `theorem`; there is no `def`, `structure`, `class` or `axiom` here,
and nothing is assumed that is not a binder of a named statement.

**`Arlib` may not import `Ttc`** (`lakefile.toml`).  The two hypotheses are therefore
restated here in `Arlib`'s own vocabulary; the dictionary is spelled out in §0 below, and no
file under `Ttc/` is read from, edited, or depended on.

## §0.  What `hphase_mean` and `hphase_var` actually say

On the **live** instantiation path, `Ttc.VolumeAlgorithm.cousinsVempalaOfRuns`
(`Ttc/Volume/CVInstantiate.lean:265`), the two residual binders are, verbatim (`:277-286`):

    (hphase_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) =
        Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1) /
          Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ))

    (hphase_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
      ∫ x, (g K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ))
        ≤ (1 + Arlib.GaussianCooling.varBudget ε / (phases K ε p : ℝ)) *
            (∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ))) ^ 2)

Both are statements about `Arlib` objects only — `Arlib.GaussianCooling.chain` and
`Arlib.GaussianCooling.varBudget` — against `ν j i`, the law of one phase's randomness.
`hphase_mean` is an **equation**; `hphase_var` is an **inequality**.  That asymmetry is the
whole story of this file.

In `Arlib`'s vocabulary, with `m = phases K ε p` and `σsq = σsq K ε p`, the score whose mean
`hphase_mean` prescribes is `Arlib.GaussianCooling.phaseScore m σsq K i` (`PhaseVar.lean:360`),
the exact law it must be integrated against is `Arlib.GaussianCooling.coolLaw m σsq K i`
(`PhaseVar.lean:408`), and `Arlib.GaussianCooling.integral_phaseScore_coolLaw`
(`PhaseVar.lean:445`) already proves

    ∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i) = chain m σsq K (i+1) / chain m σsq K i,

i.e. `hphase_mean` **holds exactly at `coolLaw`**.  So the entire question is: what law does
the sampler actually have, and how close is it to `coolLaw`?

## §1.  The seam that is now closed: the mixing bound's target measure *is* `coolLaw`

`AUDIT.md:167-168` records the seam as: `HitAndRunTheorem11Input.at_steps` yields `TVLe` to
`Arlib.uniformOn` — the **uniform** measure on `K` — **not** to `coolLaw`, the Gaussian-tilted
one, and bridging the two is Cousins–Vempala §4.  That seam is about the *hit-and-run* route;
what follows **bypasses** it rather than resolving it, by taking a route whose stationary law
is already the Gaussian-tilted one.  The `AUDIT.md` line about hit-and-run still stands as
written.

`mixesWithin_lazy_metropolisGaussian_at_operative_step` names a different measure.  Its
stationary law is

    Arlib.uniformOn ((volume).withDensity (gaussianWeight (σ^2))) K,

the Lebesgue measure **reweighted by the Gaussian** `e^{-‖x‖²/(2σ²)}` and then restricted and
renormalised to `K`.  `coolLaw_eq_uniformOn_gaussianWeight` below proves these are *the same
measure*:

    coolLaw m σsq K i = Arlib.uniformOn ((volume).withDensity (gaussianWeight (σsq i))) K   (i < m).

This is not an approximation and carries no error term.  It holds for every `i < m`, and
`i < m` is *exactly* the range `hphase_mean` quantifies over (`i : Fin (phases K ε p)`), so
there is no terminal-phase remainder: for this route the **measure-target mismatch is
closed outright, not narrowed** — what remains is exactness alone (§3).
`mixesWithin_coolLaw_of_uniformOn` is the transport of an arbitrary `MixesWithin` statement
across that identity, and `mixesWithin_lazy_metropolisGaussian_coolLaw` is the composition
with the mixing theorem itself.

## §2.  What that buys: `hphase_mean` **up to `B·ε`**, and nothing sharper

`abs_integral_phaseScore_sub_ratio_le` transports the TV bound to the mean:

    |∫ phaseScore ∂ν − chain(i+1)/chain i| ≤ e^{R²/(2σᵢ²)} · ε,

for any `ν` within total variation `ε` of `coolLaw`, on a body `K ⊆ R·Bₙ`.  Composed with the
mixing theorem this is `abs_integral_phaseScore_sub_ratio_le_of_mixing`: an explicit,
quantitative, approximately-unbiased phase score for the *actual* chain the algorithm runs.
That statement did not exist before, and it is the strongest true form of `hphase_mean`
reachable from mixing.

## §3.  What it does **not** buy: the equation, at any positive `ε`

`hphase_mean` is an equation, and no total-variation bound implies it.
`exists_tvLe_coolLaw_integral_phaseScore_ne` is the machine-checked negative, with a rate: for
every `ε ∈ (0,1]` the mixture

    ν = ofReal(1−ε) • coolLaw m σsq K i + ofReal ε • dirac x₀        (x₀ ∉ K)

is a probability measure, satisfies `TVLe ν (coolLaw m σsq K i) (ofReal ε)` — every hypothesis
a mixing theorem could ever supply — and has

    ∫ phaseScore ∂ν = (1 − ε) · (chain(i+1)/chain i)  ≠  chain(i+1)/chain i,

a **relative error of exactly `ε`**.  So the conclusion of the `CVInstantiate` docstring stands:
mixing gives the ratio only up to an error, never on the nose, and the gap does not shrink
faster than the TV bound itself.  `hphase_mean` as written is reachable only from `ε = 0`.

## §4.  A §5 bug-oracle finding: the docstring's *reason* is false as stated

`Ttc/Volume/CVInstantiate.lean:81-82` justifies the conclusion of §3 by the claim

> a Markov chain run for finitely many steps is at total-variation distance `> 0` from its
> stationary law.

That is **not true**, and this repository already contains its refutation:
`Arlib.MarkovChains.mixesWithin_const` (`Warmness.lean:381`) proves `MixesWithin
(Kernel.const Ω pi) pi μ₀ 1 0` — total-variation distance exactly `0` after one step.
`exists_markovKernel_mixesWithin_coolLaw_exact` below instantiates that at `pi = coolLaw` and
reads off the *exact* `hphase_mean` equation from it.  The "perfect sampler" the docstring
offers as the alternative to mixing **is** a Markov kernel that mixes in finitely many steps;
the two are not opposites.

The correct statement of the obstruction is the one §3 proves: not "TV is always positive",
but "a bound of the form `TV ≤ ε` with `ε > 0` does not pin a mean, and cannot be strengthened
to do so".  Conclusion right, stated reason false.  See the agent report for the `file:line`
form of this finding.

## §5.  Scope, stated once and plainly

* Every composed statement here that mentions `metropolisGaussian` is **exactly as
  conditional as** `Arlib.MarkovChains.conductance_metropolisGaussian_sharp_sqrt_ge`: it
  carries `hiso` — Cousins–Vempala's isoperimetric inequality for the Gaussian-restricted
  density — as an unproved binder, and it carries a warm start `hwarm` as a hypothesis.
  Neither is proved anywhere in this repository.  `Arlib.Convexity.IsoOpenClosed`'s
  unconditional `thm:iso` does **not** discharge it: the live `hiso`'s `h` is
  `Set.indicator K (gaussianWeightReal (σ^2))`, which is discontinuous.
* §1 and §3 carry **no** such condition.  `coolLaw_eq_uniformOn_gaussianWeight` and the
  negative of §3 are unconditional theorems about the measures themselves.
* Nothing here is a running-time statement, and nothing here discharges `hphase_var`.  What
  changed for `hphase_var` is only that the TV input `Arlib.GaussianCooling.sq_moment_le_of_tvLe`
  (`PhaseVar.lean:191`) consumes now exists *to the right measure*.  Its own recorded
  obstructions are untouched: the fixed-rate budget failure
  (`geomSchedule_total_cooling_lt`) and the missing radius parameter in `cousinsVempala`
  (see `PhaseVar.lean`'s "Scope: what this does *not* give").

## Main results

* `coolWeight_eq_gaussianWeightReal` — the two weights are the same function for `i < m`.
* `coolLaw_eq_uniformOn_gaussianWeight` — **the crux**: the phase law *is* the mixing bound's
  stationary law.
* `mixesWithin_coolLaw_of_uniformOn` — any `MixesWithin` to that stationary law is a
  `MixesWithin` to `coolLaw`, for any kernel.
* `mixesWithin_lazy_metropolisGaussian_coolLaw` — the same for the actual chain, with the
  mixing theorem's binders passed through verbatim.
* `abs_integral_phaseScore_sub_ratio_le`,
  `abs_integral_phaseScore_sub_ratio_le_of_mixing` — approximate unbiasedness, with the rate.
* `tvLe_coolMix`, `integral_phaseScore_coolMix`,
  `exists_tvLe_coolLaw_integral_phaseScore_ne` — **the machine-checked negative**, with a rate.
* `exists_markovKernel_mixesWithin_coolLaw_exact` — the refutation of the docstring's stated
  reason (§4).
* `exists_coolLaw_uniformOn_witness`, `exists_phaseMean_negative_witness` — non-vacuity
  (`CLAUDE.md` §11): one concrete body satisfying every binder of §1 and §3 simultaneously.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## 1.  The weight, and then the law

`Arlib.MarkovChains.gaussianWeightReal s x = e^{-‖x‖²/(2s)}` (`MetropolisGaussian.lean:151`)
and `Arlib.GaussianCooling.coolWeight m σsq i x = e^{-‖x‖²/(2 σsq i)}` for `i < m`
(`Chain.lean`) are literally the same function.  Everything in §1 is downstream of that. -/

/-- **The cooling weight of an interior phase is the Metropolis chain's Gaussian weight.**
For `i < m` the two unnormalised densities coincide as functions, with `s = σsq i`.

The hypothesis `i < m` is not cosmetic: at `i ≥ m` the cooling weight is the constant `1`
(that is what makes `chain_end` exact) and the Gaussian weight is not.  But `i < m` is
exactly the range the volume algorithm's `hphase_mean` quantifies over. -/
theorem coolWeight_eq_gaussianWeightReal {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (h : i < m) :
    coolWeight (n := n) m σsq i = MarkovChains.gaussianWeightReal (σsq i) := by
  funext x
  simp only [coolWeight_of_lt h, MarkovChains.gaussianWeightReal]

/-- **The crux: the exact phase law is the Metropolis–Gaussian chain's stationary law.**

    `coolLaw m σsq K i = Arlib.uniformOn (volume.withDensity (gaussianWeight (σsq i))) K`

for every interior phase `i < m`, on a body containing the unit ball and of finite volume.

The left-hand side is the distribution the volume algorithm's `hphase_mean` is stated
against (`integral_phaseScore_coolLaw`).  The right-hand side is, verbatim, the stationary
measure of `Arlib.MarkovChains.mixesWithin_lazy_metropolisGaussian_at_operative_step`
(`MetropolisMixing.lean:161`).  They are the same measure — an equality, with no error term
and no side condition beyond positivity of the schedule and the two geometric guards that
`chain_pos` already needs.

This is what closes the seam recorded in `AUDIT.md:167-168`, where the only mixing bound in
the repository gave total variation to the *uniform* measure on `K` and a Cousins–Vempala §4
uniform-to-Gaussian bridge was missing.  The Metropolis-filtered chain does not need that
bridge: its stationary law is already the Gaussian-tilted one. -/
theorem coolLaw_eq_uniformOn_gaussianWeight {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤) {i : ℕ} (hi : i < m) :
    coolLaw m σsq K i
      = Arlib.uniformOn ((volume : Measure (EuclSpace n)).withDensity
          (MarkovChains.gaussianWeight (σsq i))) K := by
  have hc : 0 < chain m σsq K i := chain_pos hσ hball hfin i
  -- rewrite the target's density into cooling-weight terms
  have hden : (MarkovChains.gaussianWeight (σsq i) : EuclSpace n → ℝ≥0∞)
      = fun x => ENNReal.ofReal (coolWeight m σsq i x) := by
    funext x
    simp only [MarkovChains.gaussianWeight, coolWeight_eq_gaussianWeightReal (n := n) hi]
  rw [hden]
  have hdm : Measurable fun x : EuclSpace n => ENNReal.ofReal (coolWeight m σsq i x) :=
    (continuous_coolWeight m σsq i).measurable.ennreal_ofReal
  have hint : IntegrableOn (coolWeight (n := n) m σsq i) K volume :=
    integrableOn_coolWeight (hσ i) hfin
  have hnn : (0 : EuclSpace n → ℝ) ≤ᵐ[volume.restrict K] coolWeight m σsq i :=
    Filter.Eventually.of_forall fun x => (coolWeight_pos m σsq i x).le
  -- the normalising constant of the Gaussian-tilted measure is the chain entry
  have hmuK : ((volume : Measure (EuclSpace n)).withDensity
        (fun x => ENNReal.ofReal (coolWeight m σsq i x))) K
      = ENNReal.ofReal (chain m σsq K i) := by
    rw [withDensity_apply _ hKm, ← ofReal_integral_eq_lintegral_ofReal hint hnn, chain_def]
  -- and the phase density is that same density, rescaled by the constant
  have hstep : coolLaw m σsq K i
      = (volume.restrict K).withDensity ((ENNReal.ofReal (chain m σsq K i))⁻¹ •
          fun x : EuclSpace n => ENNReal.ofReal (coolWeight m σsq i x)) := by
    rw [coolLaw]
    congr 1
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [ENNReal.ofReal_div_of_pos hc, div_eq_mul_inv, mul_comm]
  rw [hstep, withDensity_smul _ hdm, Arlib.uniformOn_def, hmuK,
    restrict_withDensity hKm _]

/-! ## 2.  Transporting a mixing statement onto the phase law

`coolLaw_eq_uniformOn_gaussianWeight` is an equality of measures, so it moves *any*
`MixesWithin` statement about the Gaussian-tilted uniform measure onto `coolLaw` with no loss
at all.  The first theorem is stated for an arbitrary kernel — that is the honest content, and
it is what makes the non-vacuity witness below possible.  The second is the composition with
the actual Metropolis–Gaussian mixing theorem, binders passed through verbatim. -/

/-- **Any mixing bound to the Gaussian-tilted uniform measure is a mixing bound to the phase
law.**  Pure transport across `coolLaw_eq_uniformOn_gaussianWeight`; the error `ε`, the time
`t`, the start `mu0` and the kernel `P` are unchanged. -/
theorem mixesWithin_coolLaw_of_uniformOn {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤) {i : ℕ} (hi : i < m)
    {s : ℝ} (hs : s = σsq i)
    {P : Kernel (EuclSpace n) (EuclSpace n)} {mu0 : Measure (EuclSpace n)} {t : ℕ}
    {ε : ℝ≥0∞}
    (h : MarkovChains.MixesWithin P (Arlib.uniformOn
      ((volume : Measure (EuclSpace n)).withDensity (MarkovChains.gaussianWeight s)) K)
      mu0 t ε) :
    MarkovChains.MixesWithin P (coolLaw m σsq K i) mu0 t ε := by
  subst hs
  rwa [← coolLaw_eq_uniformOn_gaussianWeight hσ hKm hball hfin hi] at h

/-- **The Metropolis-filtered Gaussian ball walk mixes to the phase law.**

Every binder of `Arlib.MarkovChains.mixesWithin_lazy_metropolisGaussian_at_operative_step`
(`MetropolisMixing.lean:161`) is passed through unchanged; the three added ones are `hball`
(the inscribed unit ball, which `chain_pos` needs), `hi : i < m`, and the identification
`hs : σ^2 = σsq i` of the chain's Gaussian parameter with the phase-`i` schedule entry.

**This carries `hiso` as a binder** — see §5 of the module docstring.  It is a mixing
statement, not a running-time statement.

⚠ `hiso` is **no longer unproved**: `Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo`
(`Arlib/Convexity/OneDimSharp.lean`) discharges it for convex `K` given
`hRσ : √3·R ≤ 2σ√n`, and `Arlib.GaussianCooling.mixesWithin_lazy_metropolisGaussian_coolLaw_of_convex`
(`Arlib/MarkovChains/Continuous/MetropolisMixingUncond.lean`) is this theorem with `hiso`
replaced by `hRσ`.  Prefer that version. -/
theorem mixesWithin_lazy_metropolisGaussian_coolLaw (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσpos : 0 < σ) (hδop : δ = σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclSpace n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ MarkovChains.ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hiso : ∀ S₁ S₂ S₃ : Set (EuclSpace n),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (MarkovChains.gaussianWeightReal (σ ^ 2))) u v) →
      δ * Real.log 2 / Real.sqrt n / σ
          * ((∫ x in S₁, Set.indicator K (MarkovChains.gaussianWeightReal (σ ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (MarkovChains.gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (MarkovChains.gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (MarkovChains.gaussianWeightReal (σ ^ 2)) x)
    {mu0 : Measure (EuclSpace n)} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn
      ((volume : Measure (EuclSpace n)).withDensity
        (MarkovChains.gaussianWeight (σ ^ 2))) K))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * (5120 ^ 2 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2) + 1 ≤ (t : ℝ))
    -- the phase-law side
    {m : ℕ} {σsq : ℕ → ℝ} (hσsch : ∀ j, 0 < σsq j)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) {i : ℕ} (hi : i < m) (hs : σ ^ 2 = σsq i) :
    MarkovChains.MixesWithin
      (MarkovChains.lazy (MarkovChains.metropolisGaussian K δ (σ ^ 2)))
      (coolLaw m σsq K i) mu0 t (ENNReal.ofReal eps) :=
  mixesWithin_coolLaw_of_uniformOn hσsch hK hball hKtop hi hs
    (MarkovChains.mixesWithin_lazy_metropolisGaussian_at_operative_step hn hσpos hδop hR hK
      hKc hKR hKtop hK0 hell hfloor hiso hM hwarm heps0 heps1 ht)

/-! ## 3.  What total variation then buys: `hphase_mean` up to `B·ε`

`Arlib.GaussianCooling.abs_integral_sub_le_of_tvLe` (`PhaseVar.lean:141`) is the transport;
`integral_phaseScore_coolLaw` (`PhaseVar.lean:445`) says the exact-law mean *is* the chain
ratio.  Composing them turns a TV bound into an explicit approximate-unbiasedness statement.

The bound `B = e^{R²/(2σᵢ²)}` needs a radius: `coolRatio` is unbounded on an unbounded body
(`PhaseVar.lean`, "The three things the transport has to get right", point 1). -/

/-- **Approximate unbiasedness of the phase score.**  If the sampled law `ν` is within total
variation `ε` of the exact phase law, then the phase score's mean is the chain ratio up to
`e^{R²/(2σᵢ²)}·ε`:

    `|∫ phaseScore ∂ν − chain(i+1)/chain i| ≤ e^{R²/(2σᵢ²)} · ε`.

At `ε = 0` this is the exact `hphase_mean`; at `ε > 0` §4 below shows the bound cannot be
improved to an equation. -/
theorem abs_integral_phaseScore_sub_ratio_le {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ}
    (hσ : ∀ j, 0 < σsq j) {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R)
    {ν : Measure (EuclSpace n)} [IsProbabilityMeasure ν] {ε : ℝ≥0∞}
    (hTV : TVLe ν (coolLaw m σsq K i) ε) (hεtop : ε ≠ ⊤) :
    |∫ x, phaseScore m σsq K i x ∂ν - chain m σsq K (i + 1) / chain m σsq K i|
      ≤ Real.exp (R ^ 2 / (2 * σsq i)) * ε.toReal := by
  haveI := coolLaw_isProbabilityMeasure (m := m) hσ hball hfin i
  have hc : 0 < chain m σsq K i := chain_pos hσ hball hfin i
  have key := abs_integral_sub_le_of_tvLe hTV hεtop (Real.exp_pos (R ^ 2 / (2 * σsq i)))
    (measurable_phaseScore hKm i) (phaseScore_nonneg m σsq K i) (phaseScore_le hσ hKR i)
  rwa [integral_phaseScore_coolLaw hKm hc] at key

/-- **The headline positive: the chain the algorithm runs has an approximately unbiased phase
score, with an explicit rate.**

Composition of `mixesWithin_lazy_metropolisGaussian_coolLaw` (§2) with
`abs_integral_phaseScore_sub_ratio_le` (§3).  After the mixing theorem's step count, the law
of the lazy Metropolis-filtered Gaussian ball walk gives the phase-`i` chain ratio to within
`e^{R²/(2σᵢ²)}·ε`.

This is the strongest form of `hphase_mean` that any mixing bound can produce, and it did not
exist before the measure identification of §1.  It is **not** `hphase_mean`, which is an
equation; see §4.  It carries `hiso` and `hwarm` — module docstring §5.

⚠ `hiso` is **now proved** for convex `K`
(`Arlib.hiso_metropolisGaussian_sharp_sqrt_logTwo`, `Arlib/Convexity/OneDimSharp.lean`), so
`Arlib.GaussianCooling.abs_integral_phaseScore_sub_ratio_le_of_mixing_of_convex`
(`Arlib/MarkovChains/Continuous/MetropolisMixingUncond.lean`) is this statement with `hiso`
replaced by `hRσ : √3·R ≤ 2σ√n`.  `hwarm` remains a binder on both. -/
theorem abs_integral_phaseScore_sub_ratio_le_of_mixing (hn : 2 ≤ n)
    {σ δ R θ : ℝ} (hσpos : 0 < σ) (hδop : δ = σ / (8 * Real.sqrt n)) (hR : 0 ≤ R)
    {K : Set (EuclSpace n)} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hKR : ∀ x ∈ K, ‖x‖ ≤ R) (hKtop : volume K ≠ ⊤) (hK0 : volume K ≠ 0)
    (hell : ∀ x ∈ K, ENNReal.ofReal θ ≤ MarkovChains.ell K δ x)
    (hfloor : 1 ≤ 20 * Real.exp (-(2 * R * δ + δ ^ 2) / (2 * σ ^ 2)) * (1 / 4) * θ)
    (hiso : ∀ S₁ S₂ S₃ : Set (EuclSpace n),
      IsPartition3 Set.univ S₁ S₂ S₃ →
      MeasurableSet S₁ → MeasurableSet S₂ → MeasurableSet S₃ →
      (∀ u ∈ S₁, ∀ v ∈ S₂,
        δ * Real.log 2 / Real.sqrt n / Real.log 2 ≤ ‖u - v‖ ∨
          4 * (δ * Real.log 2 / Real.sqrt n / σ) * Real.sqrt n
            ≤ densDist (Set.indicator K (MarkovChains.gaussianWeightReal (σ ^ 2))) u v) →
      δ * Real.log 2 / Real.sqrt n / σ
          * ((∫ x in S₁, Set.indicator K (MarkovChains.gaussianWeightReal (σ ^ 2)) x)
            * ∫ x in S₂, Set.indicator K (MarkovChains.gaussianWeightReal (σ ^ 2)) x)
        ≤ (∫ x, Set.indicator K (MarkovChains.gaussianWeightReal (σ ^ 2)) x)
          * ∫ x in S₃, Set.indicator K (MarkovChains.gaussianWeightReal (σ ^ 2)) x)
    {mu0 : Measure (EuclSpace n)} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn
      ((volume : Measure (EuclSpace n)).withDensity
        (MarkovChains.gaussianWeight (σ ^ 2))) K))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 4 * (5120 ^ 2 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2) + 1 ≤ (t : ℝ))
    {m : ℕ} {σsq : ℕ → ℝ} (hσsch : ∀ j, 0 < σsq j)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) {i : ℕ} (hi : i < m) (hs : σ ^ 2 = σsq i) :
    |(∫ x, phaseScore m σsq K i x
        ∂(MarkovChains.iterate
            (MarkovChains.lazy (MarkovChains.metropolisGaussian K δ (σ ^ 2))) mu0 t))
        - chain m σsq K (i + 1) / chain m σsq K i|
      ≤ Real.exp (R ^ 2 / (2 * σsq i)) * eps := by
  have hmix := mixesWithin_lazy_metropolisGaussian_coolLaw hn hσpos hδop hR hK hKc hKR hKtop
    hK0 hell hfloor hiso hM hwarm heps0 heps1 ht hσsch hball hi hs
  have hKR' : K ⊆ closedBall (0 : EuclSpace n) R := fun x hx =>
    mem_closedBall_zero_iff.2 (hKR x hx)
  have key := abs_integral_phaseScore_sub_ratio_le (m := m) (σsq := σsq) (i := i) hσsch hK
    hball hKtop hKR' hmix ENNReal.ofReal_ne_top
  rwa [ENNReal.toReal_ofReal heps0.le] at key

/-! ## 4.  The negative: no total-variation bound implies the *equation*

The mixture `ν = (1−ε)·coolLaw + ε·δ_{x₀}` with `x₀` outside the body meets every hypothesis a
mixing theorem could ever supply — it is a probability measure and it is within total variation
`ε` of `coolLaw` — and its phase-score mean is `(1−ε)` times the required ratio.  Since the
ratio is strictly positive (`chain_pos`), the mean is *not* the ratio, for any `ε > 0`.

Note the rate: the relative error is exactly `ε`, so the discrepancy does not decay faster
than the TV bound.  This is the sense in which `abs_integral_phaseScore_sub_ratio_le` cannot
be improved to an equation, and the sense in which the conclusion of
`Ttc/Volume/CVInstantiate.lean:80-83` is correct. -/

/-- The mixture is a probability measure. -/
theorem isProbabilityMeasure_coolMix {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x₀ : EuclSpace n) :
    IsProbabilityMeasure (ENNReal.ofReal (1 - ε) • coolLaw m σsq K i
      + ENNReal.ofReal ε • Measure.dirac x₀) := by
  haveI := coolLaw_isProbabilityMeasure (m := m) hσ hball hfin i
  constructor
  simp only [Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) hε0]
  norm_num

/-- **The mixture is within total variation `ε` of the exact phase law.**  Every hypothesis a
mixing theorem could supply about the sampled law is therefore satisfied by it. -/
theorem tvLe_coolMix {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (x₀ : EuclSpace n) :
    TVLe (ENNReal.ofReal (1 - ε) • coolLaw m σsq K i + ENNReal.ofReal ε • Measure.dirac x₀)
      (coolLaw m σsq K i) (ENNReal.ofReal ε) := by
  haveI := coolLaw_isProbabilityMeasure (m := m) hσ hball hfin i
  have hsum : ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hε0]
    norm_num
  have hone : ENNReal.ofReal (1 - ε) ≤ 1 := ENNReal.ofReal_le_one.2 (by linarith)
  intro S hS
  have hπ : coolLaw m σsq K i S ≤ 1 := prob_le_one
  have hδ : Measure.dirac x₀ S ≤ 1 := prob_le_one
  simp only [Measure.coe_add, Pi.add_apply, Measure.coe_smul, Pi.smul_apply, smul_eq_mul]
  constructor
  · refine add_le_add ?_ ?_
    · calc ENNReal.ofReal (1 - ε) * coolLaw m σsq K i S
          ≤ 1 * coolLaw m σsq K i S := by gcongr
        _ = coolLaw m σsq K i S := one_mul _
    · calc ENNReal.ofReal ε * Measure.dirac x₀ S ≤ ENNReal.ofReal ε * 1 := by gcongr
        _ = ENNReal.ofReal ε := mul_one _
  · calc coolLaw m σsq K i S
        = (ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε) * coolLaw m σsq K i S := by
          rw [hsum, one_mul]
      _ = ENNReal.ofReal (1 - ε) * coolLaw m σsq K i S
            + ENNReal.ofReal ε * coolLaw m σsq K i S := add_mul _ _ _
      _ ≤ ENNReal.ofReal (1 - ε) * coolLaw m σsq K i S
            + (ENNReal.ofReal ε * Measure.dirac x₀ S + ENNReal.ofReal ε) := by
          refine add_le_add le_rfl ?_
          calc ENNReal.ofReal ε * coolLaw m σsq K i S ≤ ENNReal.ofReal ε * 1 := by gcongr
            _ = ENNReal.ofReal ε := mul_one _
            _ ≤ ENNReal.ofReal ε * Measure.dirac x₀ S + ENNReal.ofReal ε := by
                simp
      _ = ENNReal.ofReal (1 - ε) * coolLaw m σsq K i S
            + ENNReal.ofReal ε * Measure.dirac x₀ S + ENNReal.ofReal ε := by
          rw [add_assoc]

/-- **The mixture's phase-score mean is `(1−ε)` times the required ratio.**  The atom sits
outside the body, where `phaseScore` — the cut-off `coolRatio` — is `0`, so the mixture simply
loses a fraction `ε` of the mean. -/
theorem integral_phaseScore_coolMix {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {x₀ : EuclSpace n} (hx₀ : x₀ ∉ K) :
    ∫ x, phaseScore m σsq K i x
        ∂(ENNReal.ofReal (1 - ε) • coolLaw m σsq K i + ENNReal.ofReal ε • Measure.dirac x₀)
      = (1 - ε) * (chain m σsq K (i + 1) / chain m σsq K i) := by
  haveI := coolLaw_isProbabilityMeasure (m := m) hσ hball hfin i
  have hc : 0 < chain m σsq K i := chain_pos hσ hball hfin i
  have hmeas : Measurable (phaseScore (n := n) m σsq K i) := measurable_phaseScore hKm i
  have hint1 : Integrable (phaseScore m σsq K i) (coolLaw m σsq K i) :=
    integrable_of_bounded hmeas (phaseScore_nonneg m σsq K i) (phaseScore_le hσ hKR i)
  have hint2 : Integrable (phaseScore m σsq K i) (Measure.dirac x₀) :=
    integrable_of_bounded hmeas (phaseScore_nonneg m σsq K i) (phaseScore_le hσ hKR i)
  rw [integral_add_measure (hint1.smul_measure ENNReal.ofReal_ne_top)
      (hint2.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_phaseScore_coolLaw hKm hc,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - ε), ENNReal.toReal_ofReal hε0]
  simp only [phaseScore, Set.indicator_of_notMem hx₀, smul_eq_mul, mul_zero, add_zero]

/-- **The machine-checked negative, with a rate.**

For every `ε ∈ (0,1]` there is a probability measure `ν` that satisfies *every* hypothesis a
mixing theorem could deliver — `TVLe ν (coolLaw m σsq K i) (ofReal ε)` — and whose phase-score
mean is `(1−ε)·(chain(i+1)/chain i)`, hence **not** `chain(i+1)/chain i`.

So the volume algorithm's `hphase_mean`, which is an *equation*, is not implied by any
total-variation bound with `ε > 0`; and the relative error is exactly `ε`, so the shortfall
does not decay faster than the mixing error itself.  Only `ε = 0` — an exact sampler — closes
it, or a restatement of the assembly with an approximately-unbiased score.

Contrast `abs_integral_phaseScore_sub_ratio_le`: the *inequality* form is available, at
exactly this rate. -/
theorem exists_tvLe_coolLaw_integral_phaseScore_ne {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ}
    (hσ : ∀ j, 0 < σsq j) {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {x₀ : EuclSpace n} (hx₀ : x₀ ∉ K) :
    ∃ ν : Measure (EuclSpace n), IsProbabilityMeasure ν ∧
      TVLe ν (coolLaw m σsq K i) (ENNReal.ofReal ε) ∧
      ∫ x, phaseScore m σsq K i x ∂ν
        = (1 - ε) * (chain m σsq K (i + 1) / chain m σsq K i) ∧
      ∫ x, phaseScore m σsq K i x ∂ν ≠ chain m σsq K (i + 1) / chain m σsq K i := by
  have hratio : 0 < chain m σsq K (i + 1) / chain m σsq K i :=
    div_pos (chain_pos hσ hball hfin (i + 1)) (chain_pos hσ hball hfin i)
  refine ⟨ENNReal.ofReal (1 - ε) • coolLaw m σsq K i + ENNReal.ofReal ε • Measure.dirac x₀,
    isProbabilityMeasure_coolMix hσ hball hfin hε0.le hε1 x₀,
    tvLe_coolMix hσ hball hfin hε0.le hε1 x₀,
    integral_phaseScore_coolMix hσ hKm hball hfin hKR hε0.le hε1 hx₀, ?_⟩
  rw [integral_phaseScore_coolMix hσ hKm hball hfin hKR hε0.le hε1 hx₀]
  intro hcon
  nlinarith [hcon, hratio, hε0]

/-! ## 5.  The docstring's stated *reason* is false (`CLAUDE.md` §5 bug-oracle)

`Ttc/Volume/CVInstantiate.lean:80-82` argues that mixing cannot deliver `hphase_mean` because
"a Markov chain run for finitely many steps is at total-variation distance `> 0` from its
stationary law".  That premise is false, and this repository already refutes it
(`Arlib.MarkovChains.mixesWithin_const`, `Warmness.lean:381`).  Here is the refutation aimed
directly at the phase law, together with the exact `hphase_mean` equation it produces. -/

/-- **A Markov kernel that reaches the phase law exactly in one step — and gives the exact
`hphase_mean` equation.**

The constant kernel `x ↦ coolLaw m σsq K i` is a Markov kernel, has `coolLaw` as its
stationary law, and is at total-variation distance **exactly `0`** from it after one step.
Its phase-score mean is `chain(i+1)/chain i` on the nose.

This refutes the premise quoted at `Ttc/Volume/CVInstantiate.lean:81-82`.  It does **not**
refute the conclusion: this kernel is a perfect sampler wearing a kernel's clothes, and §4
shows that every chain at TV distance `ε > 0` fails the equation.  The two are the precise
statement of what is and is not blocked. -/
theorem exists_markovKernel_mixesWithin_coolLaw_exact {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ}
    (hσ : ∀ j, 0 < σsq j) {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (mu0 : Measure (EuclSpace n)) [IsProbabilityMeasure mu0] :
    ∃ P : Kernel (EuclSpace n) (EuclSpace n), IsMarkovKernel P ∧
      Kernel.Invariant P (coolLaw m σsq K i) ∧
      MarkovChains.MixesWithin P (coolLaw m σsq K i) mu0 1 0 ∧
      ∫ x, phaseScore m σsq K i x ∂(MarkovChains.iterate P mu0 1)
        = chain m σsq K (i + 1) / chain m σsq K i := by
  haveI := coolLaw_isProbabilityMeasure (m := m) hσ hball hfin i
  have hc : 0 < chain m σsq K i := chain_pos hσ hball hfin i
  refine ⟨Kernel.const (EuclSpace n) (coolLaw m σsq K i), inferInstance,
    MarkovChains.invariant_const _, MarkovChains.mixesWithin_const _ _, ?_⟩
  rw [MarkovChains.iterate_one, MarkovChains.step_const_eq,
    integral_phaseScore_coolLaw hKm hc]

/-! ## 6.  Non-vacuity (`CLAUDE.md` §11)

Both §1 and §4 quantify over a bundle — a positive schedule, a body containing the unit ball,
of finite volume, inside a radius `R`, and a point outside it.  A green build over an
unsatisfiable bundle certifies nothing.  Here is one body meeting all of it at once:

    n = 1,  K = closedBall 0 1 ⊆ ℝ¹,  σsq ≡ 1,  m = 1,  i = 0,  R = 1,
    x₀ = single 0 2  (norm 2, so outside K),  ε = 1/2.

Both the measure identification of §1 and the negative of §4 are exhibited at these
parameters, so neither is vacuous.

**What this does not certify.**  The composed theorems of §2 and §3 additionally carry `hiso`,
which is not proved anywhere in this repository, and a warm start.  No witness for those is
claimed here, and none is offered: see
`Arlib.MarkovChains.exists_mixesWithin_lazy_metropolisGaussian_witness`
(`MetropolisMixing.lean`), which satisfies every binder of the mixing theorem *except* `hiso`
— at a different body (`B(0,1/2) ⊆ ℝ²`, which does not contain the unit ball, so it is not
simultaneously a witness for `chain_pos`).  A joint witness would require redoing that
local-conductance computation for a body containing `B(0,1)`; it is flagged, not faked. -/

/-- **Non-vacuity of the measure identification (§1).**  One concrete body on which
`coolLaw_eq_uniformOn_gaussianWeight` applies and its conclusion holds, with every binder
satisfied simultaneously. -/
theorem exists_coolLaw_uniformOn_witness :
    ∃ (K : Set (EuclSpace 1)) (σsq : ℕ → ℝ),
      (∀ j, 0 < σsq j) ∧ MeasurableSet K ∧ Convex ℝ K ∧
      ball (0 : EuclSpace 1) 1 ⊆ K ∧ volume K ≠ ⊤ ∧
      K ⊆ closedBall (0 : EuclSpace 1) 1 ∧
      coolLaw 1 σsq K 0
        = Arlib.uniformOn ((volume : Measure (EuclSpace 1)).withDensity
            (MarkovChains.gaussianWeight (σsq 0))) K := by
  refine ⟨closedBall (0 : EuclSpace 1) 1, fun _ => 1, fun _ => one_pos, measurableSet_closedBall,
    convex_closedBall _ _, ball_subset_closedBall, measure_closedBall_lt_top.ne, subset_rfl, ?_⟩
  exact coolLaw_eq_uniformOn_gaussianWeight (fun _ => one_pos) measurableSet_closedBall
    ball_subset_closedBall measure_closedBall_lt_top.ne Nat.one_pos

/-- **Non-vacuity of the negative (§4).**  On the same body, with `ε = 1/2` and the atom at
`single 0 2`, there really is a probability measure within total variation `1/2` of the phase
law whose phase-score mean is not the chain ratio — so
`exists_tvLe_coolLaw_integral_phaseScore_ne` is not a statement about an empty bundle. -/
theorem exists_phaseMean_negative_witness :
    ∃ (K : Set (EuclSpace 1)) (σsq : ℕ → ℝ) (ν : Measure (EuclSpace 1)),
      (∀ j, 0 < σsq j) ∧ MeasurableSet K ∧ ball (0 : EuclSpace 1) 1 ⊆ K ∧
      volume K ≠ ⊤ ∧ IsProbabilityMeasure ν ∧
      TVLe ν (coolLaw 1 σsq K 0) (ENNReal.ofReal (1 / 2)) ∧
      ∫ x, phaseScore 1 σsq K 0 x ∂ν
        = (1 - 1 / 2) * (chain 1 σsq K 1 / chain 1 σsq K 0) ∧
      ∫ x, phaseScore 1 σsq K 0 x ∂ν ≠ chain 1 σsq K 1 / chain 1 σsq K 0 := by
  have hx₀ : (EuclideanSpace.single (0 : Fin 1) (2 : ℝ)) ∉ closedBall (0 : EuclSpace 1) 1 := by
    rw [mem_closedBall_zero_iff]
    simp only [PiLp.norm_single, Real.norm_eq_abs]
    norm_num
  obtain ⟨ν, hprob, hTV, hval, hne⟩ :=
    exists_tvLe_coolLaw_integral_phaseScore_ne (m := 1) (σsq := fun _ => 1) (i := 0)
      (fun _ => one_pos) (K := closedBall (0 : EuclSpace 1) 1) measurableSet_closedBall
      ball_subset_closedBall measure_closedBall_lt_top.ne (R := 1) subset_rfl
      (ε := 1 / 2) (by norm_num) (by norm_num) hx₀
  exact ⟨closedBall (0 : EuclSpace 1) 1, fun _ => 1, ν, fun _ => one_pos,
    measurableSet_closedBall, ball_subset_closedBall, measure_closedBall_lt_top.ne,
    hprob, hTV, hval, hne⟩

end Arlib.GaussianCooling

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms Arlib.GaussianCooling.coolWeight_eq_gaussianWeightReal
#print axioms Arlib.GaussianCooling.coolLaw_eq_uniformOn_gaussianWeight
#print axioms Arlib.GaussianCooling.mixesWithin_coolLaw_of_uniformOn
#print axioms Arlib.GaussianCooling.mixesWithin_lazy_metropolisGaussian_coolLaw
#print axioms Arlib.GaussianCooling.abs_integral_phaseScore_sub_ratio_le
#print axioms Arlib.GaussianCooling.abs_integral_phaseScore_sub_ratio_le_of_mixing
#print axioms Arlib.GaussianCooling.isProbabilityMeasure_coolMix
#print axioms Arlib.GaussianCooling.tvLe_coolMix
#print axioms Arlib.GaussianCooling.integral_phaseScore_coolMix
#print axioms Arlib.GaussianCooling.exists_tvLe_coolLaw_integral_phaseScore_ne
#print axioms Arlib.GaussianCooling.exists_markovKernel_mixesWithin_coolLaw_exact
#print axioms Arlib.GaussianCooling.exists_coolLaw_uniformOn_witness
#print axioms Arlib.GaussianCooling.exists_phaseMean_negative_witness
