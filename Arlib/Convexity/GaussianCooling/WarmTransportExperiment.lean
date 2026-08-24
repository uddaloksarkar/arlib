/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Probability.TV
import Arlib.MarkovChains.Continuous.Warmness

/-!
# Can the mixing conclusion be transported instead of the warmness?

A **decision experiment**.  The Gaussian-cooling phase chain currently consumes
`Ttc.CVIdealCombinedAccepted.map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw` as an
*equality of measures*.  That equality is available only because `ell ≡ 1` on the shrunken
body `c·K` (`Arlib.ell_eq_one_on_shrunken`), which forces `δ ≤ 1 − c` and hence — since
`cⁿ = Θ(1)` forces `1 − c = O(1/n)` — pins the ball-walk step at `δ = Θ(1/n)`.  At
`δ ~ 1/√n` the identity degrades to a *closeness* statement, so the question is which
consumers survive closeness.

This file settles that question with two theorems and one no-go.

## The positive half: transporting the *conclusion*

`Arlib.GaussianCooling.tvLe_bind_of_isWarm_source` — if the mixing bound is available from
**every** `M`-warm start, and the actual start `mu` is only within total variation `eps` of
some warm start `nu0`, then the chain started at `mu` still reaches `pi` within `eps + zeta`.
The whole content is data processing (`Arlib.MarkovChains.tvLe_step`, which assumes neither
`IsProbabilityMeasure` nor `eps ≠ ⊤`) plus the triangle inequality (`Arlib.TVLe.trans`).
`Arlib.GaussianCooling.tvLe_iterate_of_isWarm_source` is the same statement for `t` steps of
a fixed kernel, which is the shape the deadline argument uses; note that
`Ttc.CVSequentialPhaseSampler.sampleFromKernel Q rho` is *by definition* `rho.bind Q`, so the
`bind` form applies to it without any unfolding, and
`Ttc.CVSequentialPhaseSampler.iterate_eq_sampleFrom_iteratedKernel` converts the `iterate`
form to `sampleFromKernel (iteratedKernel P t) rho`.

So: a perturbation of the **source** of the mixing chain is free.

## The negative half: warmness against a perturbed *reference* is not transportable

The obstruction in the phase chain is not on the source side.  At
`Ttc/Exec/CVGaussianAdaptiveAcceptedWarm.lean:163` (and at `CVAdaptiveRadiusQAcceptedWarm.lean:146`,
`CVAdaptiveRadiusFourAcceptedWarm.lean:144`, `CVColdAcceptedWarm.lean:206`) the equality is
`rw`-consumed into the **second** argument of an `Arlib.IsWarm` — the *reference* measure,
the denominator of the density ratio.  No total-variation hypothesis can drive that
rewrite:

`Arlib.GaussianCooling.exists_isWarm_tvLe_reference_not_isWarm` — for **every** `eps ≠ 0`
there are probability measures `mu, nu, nu'` on `Bool` with `IsWarm eps⁻¹ mu nu` and
`TVLe nu nu' eps`, such that `mu` is `M`-warm against `nu'` for **no** `M : ℝ≥0∞`, `⊤`
included.  Consequently `Arlib.GaussianCooling.not_exists_isWarm_transport_of_tvLe_reference`:
there is no function `f` of the warmness constant and the TV error that could serve as a
transported warmness constant.

This is the exact mirror of `Arlib.GaussianCooling.exists_supported_on_shrunken_not_isWarm`
(`Arlib/Convexity/GaussianCooling/WarmSpeedy.lean:102`): there the numerator was a Dirac,
here the reference has a null set the numerator charges.  Both say the same thing —
`IsWarm` is an `L∞` statement and total variation is an `L¹` one.

`Arlib.GaussianCooling.measure_le_of_isWarm_of_tvLe_reference` records exactly what total
variation *does* buy on the reference side: the additive relaxation
`mu S ≤ M * pi S + M * eps`.  It is stated so that the report can point at the shape a
consumer would have to accept, and deliberately **not** developed further — turning that
relaxation back into a genuine warm start needs a Lebesgue-decomposition/truncation argument
that is downstream of this experiment's verdict.

## Main results

* `Arlib.GaussianCooling.tvLe_bind_of_isWarm_source`
* `Arlib.GaussianCooling.tvLe_iterate_of_isWarm_source`
* `Arlib.GaussianCooling.measure_le_of_isWarm_of_tvLe_reference`
* `Arlib.GaussianCooling.exists_isWarm_tvLe_reference_not_isWarm`
* `Arlib.GaussianCooling.not_exists_isWarm_transport_of_tvLe_reference`
-/

set_option maxHeartbeats 8000000

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Arlib.GaussianCooling

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## 1.  Transporting the conclusion through the kernel -/

/-- **The mixing conclusion transports across a total-variation gap in the start.**

If every `M`-warm probability start reaches `pi` within `zeta` after one application of the
Markov kernel `Q`, and the actual start `mu` is within total variation `eps` of *some*
`M`-warm start `nu0`, then `mu` reaches `pi` within `eps + zeta`.

Nothing about `mu` is assumed — in particular `mu` is **not** required to be warm.  The
proof is data processing (`Arlib.MarkovChains.tvLe_step`) followed by the triangle
inequality (`Arlib.TVLe.trans`); the kernel does not amplify `eps`, so the two errors merely
add.

`Q` is arbitrary, so instantiating it at `Ttc.CVSequentialPhaseSampler.iteratedKernel P t`
gives the `t`-step statement for the phase chain; and since
`Ttc.CVSequentialPhaseSampler.sampleFromKernel Q rho` is *definitionally* `rho.bind Q`, the
statement applies to `sampleFromKernel` verbatim. -/
theorem tvLe_bind_of_isWarm_source {mu nu0 pi : Measure Ω} {M zeta eps : ℝ≥0∞}
    (Q : Kernel Ω Ω) [IsMarkovKernel Q]
    (hmix : ∀ rho : Measure Ω, Arlib.IsWarm M rho pi → IsProbabilityMeasure rho →
      Arlib.TVLe (Measure.bind rho Q) pi zeta)
    [IsProbabilityMeasure nu0] (hwarm : Arlib.IsWarm M nu0 pi)
    (hclose : Arlib.TVLe mu nu0 eps) :
    Arlib.TVLe (Measure.bind mu Q) pi (eps + zeta) :=
  (Arlib.MarkovChains.tvLe_step Q hclose).trans (hmix nu0 hwarm inferInstance)

/-- The same statement with the error written `zeta + eps`, the order the per-phase budget
is bookkept in. -/
theorem tvLe_bind_of_isWarm_source' {mu nu0 pi : Measure Ω} {M zeta eps : ℝ≥0∞}
    (Q : Kernel Ω Ω) [IsMarkovKernel Q]
    (hmix : ∀ rho : Measure Ω, Arlib.IsWarm M rho pi → IsProbabilityMeasure rho →
      Arlib.TVLe (Measure.bind rho Q) pi zeta)
    [IsProbabilityMeasure nu0] (hwarm : Arlib.IsWarm M nu0 pi)
    (hclose : Arlib.TVLe mu nu0 eps) :
    Arlib.TVLe (Measure.bind mu Q) pi (zeta + eps) := by
  rw [add_comm]
  exact tvLe_bind_of_isWarm_source Q hmix hwarm hclose

/-- **The `t`-step form**, phrased with `Arlib.MarkovChains.iterate`: run the *same* number
of steps the deadline prescribes, from a start that is only `eps`-close to a warm one, and
pay `eps` once — not once per step. -/
theorem tvLe_iterate_of_isWarm_source {mu nu0 pi : Measure Ω} {M zeta eps : ℝ≥0∞}
    (P : Kernel Ω Ω) [IsMarkovKernel P] (t : ℕ)
    (hmix : ∀ rho : Measure Ω, Arlib.IsWarm M rho pi → IsProbabilityMeasure rho →
      Arlib.TVLe (Arlib.MarkovChains.iterate P rho t) pi zeta)
    [IsProbabilityMeasure nu0] (hwarm : Arlib.IsWarm M nu0 pi)
    (hclose : Arlib.TVLe mu nu0 eps) :
    Arlib.TVLe (Arlib.MarkovChains.iterate P mu t) pi (eps + zeta) :=
  (Arlib.MarkovChains.tvLe_iterate P hclose t).trans (hmix nu0 hwarm inferInstance)

/-! ## 2.  What total variation buys on the *reference* side -/

/-- **Warmness against a total-variation-perturbed reference, in its honest additive form.**

From `IsWarm M mu nu` and `TVLe nu pi eps` one gets `mu S ≤ M * pi S + M * eps`: an
*additive* relaxation of warmness, with the slack inflated by the warmness constant.  This
is the strongest conclusion available, and §3 shows it cannot be improved to an `IsWarm`
statement for any constant. -/
theorem measure_le_of_isWarm_of_tvLe_reference {mu nu pi : Measure Ω} {M eps : ℝ≥0∞}
    (h : Arlib.IsWarm M mu nu) (hnu : Arlib.TVLe nu pi eps)
    {S : Set Ω} (hS : MeasurableSet S) :
    mu S ≤ M * pi S + M * eps := by
  calc mu S ≤ M * nu S := h S hS
    _ ≤ M * (pi S + eps) := by gcongr; exact hnu.left hS
    _ = M * pi S + M * eps := by rw [mul_add]

/-! ## 3.  The no-go: warmness does not survive a perturbation of the reference -/

/-- **A total-variation perturbation of the reference measure destroys warmness outright.**

For every `eps ≠ 0` with `eps ≤ 1` there are probability measures `mu, nu, nu'` on `Bool`
with

* `mu` is `eps⁻¹`-warm against `nu`,
* `nu` and `nu'` are within total variation `eps`,
* `mu` is `M`-warm against `nu'` for **no** `M : ℝ≥0∞` — not even `M = ⊤`.

The construction: `mu = δ_true`, `nu = eps·δ_true + (1−eps)·δ_false`, `nu' = δ_false`.  The
event `{true}` has `mu`-mass `1`, `nu`-mass `eps`, and `nu'`-mass `0`; and `⊤ * 0 = 0` in
`ℝ≥0∞`.

Read against the phase chain: `nu` is the ideal post-processed law, `nu'` the phase target,
`mu` the sampler's actual output.  The perturbation is arbitrarily small and the warmness
constant it destroys is arbitrarily good — the failure is not quantitative. -/
theorem exists_isWarm_tvLe_reference_not_isWarm (eps : ℝ≥0∞) (heps0 : eps ≠ 0)
    (heps1 : eps ≤ 1) :
    ∃ mu nu nu' : Measure Bool,
      IsProbabilityMeasure mu ∧ IsProbabilityMeasure nu ∧ IsProbabilityMeasure nu' ∧
        Arlib.IsWarm eps⁻¹ mu nu ∧ Arlib.TVLe nu nu' eps ∧
        ∀ M : ℝ≥0∞, ¬ Arlib.IsWarm M mu nu' := by
  have hepstop : eps ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top heps1
  refine ⟨Measure.dirac true, eps • Measure.dirac true + (1 - eps) • Measure.dirac false,
    Measure.dirac false, Measure.dirac.isProbabilityMeasure, ⟨?_⟩,
    Measure.dirac.isProbabilityMeasure, ?_, ?_, ?_⟩
  · -- `nu` is a probability measure: `eps + (1 - eps) = 1`.
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, measure_univ, mul_one]
    exact add_tsub_cancel_of_le heps1
  · -- warmness of `mu` against `nu`, with constant `eps⁻¹`
    intro S hS
    have hmul : eps⁻¹ * (eps * Measure.dirac true S) = Measure.dirac true S := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel heps0 hepstop, one_mul]
    calc Measure.dirac true S = eps⁻¹ * (eps * Measure.dirac true S) := hmul.symm
      _ ≤ eps⁻¹ * ((eps • Measure.dirac true + (1 - eps) • Measure.dirac false) S) := by
          gcongr
          simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul]
          exact le_self_add
  · -- the two references are `eps`-close in total variation
    intro S hS
    set a : ℝ≥0∞ := Measure.dirac true S with ha
    set b : ℝ≥0∞ := Measure.dirac false S with hb
    have ha1 : a ≤ 1 := by rw [ha]; exact prob_le_one
    have hb1 : b ≤ 1 := by rw [hb]; exact prob_le_one
    have hval : (eps • Measure.dirac true + (1 - eps) • Measure.dirac false) S
        = eps * a + (1 - eps) * b := by
      simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, ha, hb]
    rw [hval]
    constructor
    · calc eps * a + (1 - eps) * b ≤ eps * 1 + 1 * b := by
            gcongr
            exact tsub_le_self
        _ = b + eps := by rw [mul_one, one_mul, add_comm]
    · have hsplit : (1 - eps) * b + eps * b = b := by
        rw [← add_mul, tsub_add_cancel_of_le heps1, one_mul]
      calc b = (1 - eps) * b + eps * b := hsplit.symm
        _ ≤ (1 - eps) * b + eps := by
            gcongr
            calc eps * b ≤ eps * 1 := by gcongr
              _ = eps := mul_one eps
        _ ≤ eps * a + (1 - eps) * b + eps := by
            gcongr
            exact le_add_self
  · -- but `mu` is warm against `nu'` for no constant whatsoever
    intro M hM
    have hle := hM ({true} : Set Bool) (measurableSet_singleton true)
    rw [Measure.dirac_apply_of_mem (Set.mem_singleton true),
      Measure.dirac_apply' _ (measurableSet_singleton true),
      Set.indicator_of_notMem (by simp), mul_zero] at hle
    exact absurd hle (by simp)

/-- **There is no transport rule at all.**  No function of the warmness constant and the
total-variation error can serve as a warmness constant against the perturbed reference —
so the `rw`-consumption of
`Ttc.CVIdealCombinedAccepted.map_combinedOutput_condOn_ellGaussianProb_eq_coolLaw` into the
reference argument of an `Arlib.IsWarm` cannot be replaced by a `TVLe` hypothesis, however
generous the bookkeeping. -/
theorem not_exists_isWarm_transport_of_tvLe_reference :
    ¬ ∃ f : ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞,
        ∀ (mu nu nu' : Measure Bool) (M eps : ℝ≥0∞),
          Arlib.IsWarm M mu nu → Arlib.TVLe nu nu' eps → Arlib.IsWarm (f M eps) mu nu' := by
  rintro ⟨f, hf⟩
  obtain ⟨mu, nu, nu', _, _, _, hwarm, hclose, hno⟩ :=
    exists_isWarm_tvLe_reference_not_isWarm (1 / 2 : ℝ≥0∞) (by norm_num) (by norm_num)
  exact hno _ (hf mu nu nu' _ _ hwarm hclose)

section AxiomCheck

#print axioms Arlib.GaussianCooling.tvLe_bind_of_isWarm_source
#print axioms Arlib.GaussianCooling.tvLe_bind_of_isWarm_source'
#print axioms Arlib.GaussianCooling.tvLe_iterate_of_isWarm_source
#print axioms Arlib.GaussianCooling.measure_le_of_isWarm_of_tvLe_reference
#print axioms Arlib.GaussianCooling.exists_isWarm_tvLe_reference_not_isWarm
#print axioms Arlib.GaussianCooling.not_exists_isWarm_transport_of_tvLe_reference

end AxiomCheck

end Arlib.GaussianCooling
