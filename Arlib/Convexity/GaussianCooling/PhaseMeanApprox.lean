/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.PhaseMean
import Arlib.Convexity.GaussianCooling.PhaseMeanRoute
import Arlib.Probability.RunPlumbing

/-!
# `hphase_mean` does not need the equation — and the price of the route that avoids it

`PhaseMeanRoute.lean` proved that the exact phase law `coolLaw` **is** the stationary law of
the Metropolis–Gaussian mixing bound (`coolLaw_eq_uniformOn_gaussianWeight`), and that no
total-variation bound with `ε > 0` implies the *equation*
`∫ phaseScore ∂ν = chain(i+1)/chain i` (`exists_tvLe_coolLaw_integral_phaseScore_ne`).
It left open the question this file answers:

> **Does the Cousins–Vempala analysis actually need that equation?**

**It does not**, and neither does Cousins–Vempala's own proof.  This file closes the loop
by composing the mixing bound with the approximate-mean bookkeeping that
`PhaseMean.lean` already proves, and it prices the composition honestly.

Every declaration below is a `theorem`; there is no `def`, `structure`, `class` or `axiom`
here.  `Arlib` may not import `Ttc` (`lakefile.toml`), so the `Ttc`-side hypothesis is
restated in `Arlib`'s own vocabulary, exactly as `PhaseMeanRoute.lean` §0 does.

## §0.  The answer, and where the repository already contained half of it

`PhaseMean.lean` proves, abstractly, that a **relative** per-phase bias suffices:

* `integral_prod_mem_relErr_of_budget` — if each of the `m` phase means lies in
  `(1 ± η)·(A(i+1)/A i)` and `2mη ≤ τ ≤ 1`, the telescoped product's mean lies in
  `(1 ± τ)·(A m / A 0)`.
* `integral_mem_Icc_of_tvLe` — a `TVLe ρ ν e` bound on a score valued in `[0, B]` with
  target mean `r` delivers exactly that interval, as soon as `B·e ≤ η·r`.

So the *equation* was never the mathematical requirement; it was the shape the hypothesis
happened to be written in.  What did not exist until `PhaseMeanRoute.lean` was a
**provider** for the `TVLe` input against `coolLaw`.  That is what this file plugs in.

## §1.  What Cousins–Vempala actually assume  (`CLAUDE.md` §5, the bug-oracle direction)

`/home/devel/Documents/kr-25-ssm/1409.6011/vol3_journal.tex`.  The unbiasedness computation
`E(Y) = F(σ_{i+1}²)/F(σ_i²)` is at `:325-330`, under the explicit stipulation "*Let `X` be a
random sample point from `μ_i`*" — the **exact** phase law.  The proof of the accuracy lemma
`lem:accuracy` (`:1419-1424`) then never applies that computation to the sampler's own
output.  It introduces coupled exact-law shadow variables (`:1426`):

> "The distribution of each `X_i` is approximately the correct distribution, but slightly
> off based on the error parameter `ν` in each phase that bounds the total variation
> distance.  We will define new random variables `X̄_j^i` that have the correct distribution
> for each phase."

and prices the coupling in **failure probability**, not in bias (`:1429-1430`):

> `Pr(X_i^j = X̄_i^j, ∀ i,j) ≥ 1 − tν`.

The unbiasedness claim is then made only of the barred variables (`:1439`: "*all of the
`Y_j^i` have the same expectation since they are from the exact distribution*"), and the
final assembly (`:1588`) reads

> "`W̄_1 … W̄_m = W_1 … W_m` with probability at least `1 − 2kmν`.  Recall that
> `E(W̄_1) … E(W̄_m) = R_1 … R_m`."

with the per-sample budget `ν = (ε/n)^16` fixed in the algorithm box (`:212`) and justified
at `:1021` by "*a straightforward union bound*".

**Three consequences, all of them findings.**

1. **The paper's *architecture* has no unbiasedness gap.**  The naive charge — "they assume
   the realised estimator is unbiased while running a finitely-mixed chain" — is **false for
   this paper** and must not be made.  The coupling at `:1426-1431` plus the `ν`-independence
   machinery of `lem:delta-ind` (`:1481-1488`, accumulating `3kmν`) is the LV/`CV2014`
   template, and it is carried through the second-moment computation *across* phases.  What
   that architecture does **not** cover is stated at `:1441`: the variance step `eq:var-bound`
   writes the cross terms of one phase's `k` samples as `k_i(k_i−1)R_i²`, which assumes those
   `k` samples are exactly pairwise independent *and* exactly unbiased, and `lem:delta-ind`(c)
   (`:1487`) corrects only `W̄_i` against `W̄_{i+1}`, i.e. only across phases.  So the correct
   statement is: the architecture pushes total-variation error into failure probability rather
   than into bias, and the *within-phase* execution of that architecture is where the text is
   loose.
2. **The equation Cousins–Vempala use is `integral_phaseScore_coolLaw`** (`PhaseVar.lean:445`)
   — the mean *at the exact law* — which this repository already proves outright, with no
   sampler hypothesis at all.  It is a theorem here, not a hypothesis.
3. **So `hphase_mean` as bound in `Ttc/Volume/CVInstantiate.lean:277-281` is stronger than
   both the mathematics and the paper require**, because it demands the equation of the
   *sampled* law `ν j i` rather than of `coolLaw`.  The docstring at
   `Ttc/Volume/CVInstantiate.lean:80-83` offers the dichotomy "a perfect sampler *or*
   restating §5.2 with an approximately-unbiased score"; Cousins–Vempala do **neither** —
   they keep the exact-law equation and pay for the sampler with a coupling.  That third
   route is described in §5 below.

Three further textual defects found on the way, recorded for the record and not relied on
anywhere below.  At `:1434` `Y_j^i` is defined from the **unbarred** `X_j^i` yet averaged into
`W̄_i` at `:1436` and asserted at `:1439` to be "from the exact distribution" — the overbar is
dropped at exactly the load-bearing step of the coupling argument.  `:1430` prices the
coupling at `tν` while `:1588` prices it at `2kmν`, with `t = km`, unexplained.  And the
sampler's target is the **truncated** density `f(σᵢ², K ∩ 4σᵢ√n·Bₙ)` (`:228`, and `thm:ball-walk`
at `:195`) while every quantity in the volume analysis — `F(σ²)` at `:322-323`, `E(Y)` at
`:327-329`, `R_i` at `:1386` — is untruncated over `K`; the discrepancy is never quantified in
the file (`lem:starting-gauss`, `:1321-1325`, covers only the initial `σ₀` and the final switch
to uniform).  None of these refutes `lem:accuracy`; they are textual and are stated as such.

## §2.  The repository's own framing is stale, in two files this agent may not edit

* `Ttc/Volume/CVInstantiate.lean:83` — "This is where the development actually stops."
* `Ttc/Exec/RuntimeMN4.lean:133` — hypothesis #12's available route: "**nothing.**"

Both are contradicted by `Ttc/Volume/CousinsVempala.lean` itself, which at `:250` says
"`hphase_mean`'s equality idealization has been removed — twice over", and supplies
`Ttc.CV.run_relErr_four_fifths_approxMean` (`:777`), the derived approximate `hphase_mean`
(`:911`), and the constructors `Ttc.VolumeAlgorithm.cousinsVempalaOfApproxMean`,
`cousinsVempalaOfSampler`, `cousinsVempalaOfSamplerCooling`.  The equality survives only
because the **live** path — `cousinsVempalaOfRuns` (`CVInstantiate.lean:265`), the one
`Ttc.ttc_runtime_mn4` goes through — was never rewired to the approximate-mean constructor.
Removing hypothesis #12 from `ttc_runtime_mn4` is that rewiring plus the discharge below; the
rewiring is a `Ttc`-side edit and is not performed here.

## §3.  What is proved here

* `integral_natScore_coord` — the coordinate transport on the universal run space.  (The
  `Ttc`-side twin is `Ttc.CV.integral_natRunCoord`, `CVInstantiate.lean:208`; this is where
  it belongs, since nothing about it mentions a volume oracle.)
* `integral_phaseScore_mem_Icc_of_tvLe` — **the relaxed per-phase hypothesis, discharged from
  a TV bound**: `TVLe ν (coolLaw m σsq K i) e` and the slack `e^{R²/(2σᵢ²)}·e ≤ η·r` give
  `∫ phaseScore ∂ν ∈ (1 ± η)·r`.  (The `Ttc`-side twin is
  `Ttc.CV.sampledPhase_mean_mem_relErr`, `CousinsVempala.lean:911`, which routes through a
  sampling map; this one is stated directly on the law and lives upstream of the volume
  oracle.  One of the two should be deleted once both have landed, exactly as
  `PhaseMean.lean` records for `abs_integral_sub_le_of_tvLe_scaled`.)
* `integral_prod_phaseScore_mem_relErr` — **the downstream estimator conclusion, proved from
  the relaxed hypothesis**: `m` independent phases, each within a relative `η` of its chain
  ratio, telescope to a product mean within a relative `τ` of `chain m / chain 0` whenever
  `2mη ≤ τ ≤ 1`; and `integral_prod_phaseScore_pos`, the positivity Chebyshev needs.
* `integral_phaseScore_mem_Icc_of_mixing` — **the relaxed hypothesis discharged from the
  actual chain**, by composing with `mixesWithin_lazy_metropolisGaussian_coolLaw`.  It is new
  in *this* file; what `PhaseMeanRoute.lean` supplied is the measure identification that makes
  it possible.
* `log_one_div_tvBudget`, `tvBudget_le_one`, `slack_of_le_tvBudget`,
  `integral_phaseScore_mem_Icc_of_mixing_steps` — **the step count**, with the cost visible
  in the statement (§4).
* `measureReal_relErr_ge_of_tvLe` — **the route Cousins–Vempala actually take** (§5): a TV
  bound on the run's joint law moves the success probability by `e` and pays **no** sup-norm
  factor at all.
* `exists_phaseMeanApprox_witness`, `exists_prod_phaseMeanApprox_witness` — non-vacuity
  (`CLAUDE.md` §11).

## §4.  The price, stated loudly: this route does **not** keep `O(n²)` steps per phase

The slack the per-phase discharge needs is `B·eps ≤ η·r` with `B = e^{R²/(2σᵢ²)}` — the
**sup-norm** bound on the phase score (`phaseScore_le`) — and `r = chain(i+1)/chain i`.  The
largest admissible mixing error is therefore `eps = η·r/B`, and `log_one_div_tvBudget` proves
the exact identity

    log(1/eps) = R²/(2σᵢ²) + log(1/η) + log(1/r).

The mixing theorem's step count is `t = Θ(n²·(log M + 2·log(1/eps)))`, so with the per-phase
budget `η = τ/(2m)`,

    t = Θ( n² · ( log M + 2·[ R²/(2σᵢ²) + log(2m/τ) + log(1/r) ] ) ).

`log(2m/τ)` is a log factor and costs nothing.  **`R²/(2σᵢ²)` is not a log factor.**  It is
the exponent of the score's sup norm, and on any schedule that actually cools — i.e. one that
drives `σᵢ² ≪ R²`, which is the entire point of Gaussian cooling — it is polynomially large
in `n`, so `t` acquires a polynomial factor `R²/σᵢ²` on top of `n²`.  The exponent changes.
This is stated as arithmetic, not proved: the machine-checked content is the identity above.

The one regime in which `R²/(2σᵢ²)` stays logarithmic is `σᵢ² = Ω(R²/polylog)` — precisely
the near-flat schedules that `Ttc/Volume/CousinsVempala.lean`'s own recorded finding (its
"THE FINDING" section, and `Ttc.CV.cold_start_mem_relErr_of_flat`) shows have nothing left to
telescope, because the first chain entry already estimates `Vol(K)` to relative error
`O(1/n)`.  So on this route the two failure modes are exclusive: either the schedule cools
and the step count is not `O*(n²)`, or the step count is `O*(n²)` and the schedule does not
cool.  Nothing here proves a lower bound; the disjunction is the honest reading of the
identity together with an already-recorded result.

`− log r` does not rescue this.  `r ≥ 1` on a monotone schedule (the weights increase), which
makes `log(1/r) ≤ 0`, but `r ≤ B` is all that is available in general
(`integral_le_bound` at `coolLaw`), and `B/r` is exactly the sup-to-mean gap the estimator's
variance analysis exists to exploit.  Bounding it below needs Gaussian-integral estimates that
are not attempted here, so no unconditional lower bound on `log(1/eps)` is claimed.

## §5.  Why Cousins–Vempala do not pay that price

Their coupling (§1) never converts a TV bound into a statement about a *mean*.  It converts
it into a statement about the *success event* of the whole run, and total variation is
preserved by every measurable map (`Arlib.TVLe.map`) and read off directly on sets
(`Arlib.TVLe.abs_measureReal_sub_le`).  `measureReal_relErr_ge_of_tvLe` below is that step in
`Arlib` terms: if the estimator is `acc`-accurate with probability `q` under the exact joint
law, it is `acc`-accurate with probability `q − e` under any joint law within total variation
`e` — **with no `B`, no radius and no schedule hypothesis whatsoever**.

The piece that route needs and this repository does **not** have is the tensorization
`TVLe (⨂ᵢ νᵢ) (⨂ᵢ ν'ᵢ) (Σᵢ eᵢ)` — the "union bound" of `vol3_journal.tex:1021` — which would
turn `m·k` per-sample mixing bounds into one bound on the joint law of the run.  It is not in
`Arlib`, it is not built here, and it is the natural next target: it costs `log(1/eps) =
O(log(km/δ))` per sample instead of `Ω(R²/σᵢ²)`, i.e. it is the route on which `O*(n²)` per
phase survives.  It is flagged, not faked.

## §6.  Scope

* Every statement here that mentions `metropolisGaussian` is **exactly as conditional as**
  `PhaseMeanRoute.lean`'s: it carries `hiso` (Cousins–Vempala's isoperimetric inequality for
  the Gaussian-restricted density) as an unproved binder, and a warm start `hwarm`.  Neither
  is proved anywhere in this repository.
* §3's TV-input statements, the product bookkeeping, the log identity and §5 carry **no** such
  condition.
* Nothing here is a running-time statement — §4 is an arithmetic reading of a step-count
  hypothesis, not a theorem about running time — and nothing here touches `hphase_var`.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set ProbabilityTheory
open scoped ENNReal

variable {n : ℕ}

/-! ## 1.  The coordinate transport on the universal run space

`Arlib.Probability.natScore g j i ω = g j i (ω j i)` reads the `(run, phase)` coordinate of
the countable product measure `Arlib.Probability.natRunMeasure ν`, whose `(j, i)` marginal is
`ν j i` (`Arlib.Probability.measurePreserving_natCoord`).  So a hypothesis about the
sampler's *own* law transfers to the product space for free. -/

/-- **The `(j, i)` coordinate of the universal run space has law `ν j i`.**  The integral of
a phase score against the big product measure is its integral against that phase's own law.

This is the `Arlib` original of `Ttc.CV.integral_natRunCoord`
(`Ttc/Volume/CVInstantiate.lean:208`); it mentions no volume oracle, so it belongs here. -/
theorem integral_natScore_coord {E : Type*} [MeasurableSpace E] (ν : ℕ → ℕ → Measure E)
    [∀ j i, IsProbabilityMeasure (ν j i)] {g : ℕ → ℕ → E → ℝ}
    (hg : ∀ j i, Measurable (g j i)) (j i : ℕ) :
    ∫ ω, Arlib.Probability.natScore g j i ω ∂(Arlib.Probability.natRunMeasure ν)
      = ∫ x, g j i x ∂(ν j i) := by
  have hmp := Arlib.Probability.measurePreserving_natCoord ν j i
  rw [← hmp.map_eq, integral_map hmp.measurable.aemeasurable]
  · rfl
  · rw [hmp.map_eq]
    exact (hg j i).aestronglyMeasurable

/-! ## 2.  The relaxed per-phase hypothesis, discharged from a total-variation bound

This is `hphase_mean` with the equation replaced by the two-sided relative bound, and it is a
pure instantiation: `Arlib.GaussianCooling.integral_mem_Icc_of_tvLe` (`PhaseMean.lean`) at
`f = phaseScore`, `B = e^{R²/(2σᵢ²)}` (`phaseScore_le`) and `r = chain(i+1)/chain i`
(`integral_phaseScore_coolLaw`). -/

/-- **`hphase_mean`, relaxed and discharged from a TV bound.**

If the sampled law `ν` is within total variation `e` of the exact phase law `coolLaw`, the
body sits inside `R·Bₙ`, and the slack condition

    `e^{R²/(2σᵢ²)} · e ≤ η · (chain(i+1)/chain i)`

holds, then the phase score's mean under `ν` lies in `(1 ± η)·(chain(i+1)/chain i)`.

This is *exactly* the shape `integral_prod_mem_relErr_of_budget` consumes, one phase at a
time, and it is exactly the shape `Ttc.VolumeAlgorithm.cousinsVempalaOfApproxMean`'s
`hphase_mean` binder takes (`Ttc.relErr η b` is reducibly `Set.Icc ((1-η)*b) ((1+η)*b)`). -/
theorem integral_phaseScore_mem_Icc_of_tvLe {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ}
    (hσ : ∀ j, 0 < σsq j) {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R)
    {ν : Measure (EuclSpace n)} [IsProbabilityMeasure ν] {e : ℝ≥0∞}
    (hTV : TVLe ν (coolLaw m σsq K i) e) (he : e ≠ ⊤) {η : ℝ}
    (hslack : Real.exp (R ^ 2 / (2 * σsq i)) * e.toReal
      ≤ η * (chain m σsq K (i + 1) / chain m σsq K i)) :
    ∫ x, phaseScore m σsq K i x ∂ν
      ∈ Set.Icc ((1 - η) * (chain m σsq K (i + 1) / chain m σsq K i))
          ((1 + η) * (chain m σsq K (i + 1) / chain m σsq K i)) := by
  haveI := coolLaw_isProbabilityMeasure (m := m) hσ hball hfin i
  have hc : 0 < chain m σsq K i := chain_pos hσ hball hfin i
  exact integral_mem_Icc_of_tvLe hTV he (measurable_phaseScore hKm i) (Real.exp_pos _)
    (phaseScore_nonneg m σsq K i) (phaseScore_le hσ hKR i)
    (integral_phaseScore_coolLaw hKm hc) hslack

/-- **The chain ratio never exceeds the score's sup norm.**  `r ≤ B`, read off from
`integral_phaseScore_coolLaw` and `integral_le_bound`.  Recorded because the step-count
statement below needs `η·r/B ≤ 1`, and because §4 of the module docstring turns on the size
of `B/r`. -/
theorem chain_ratio_le_exp {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R) :
    chain m σsq K (i + 1) / chain m σsq K i ≤ Real.exp (R ^ 2 / (2 * σsq i)) := by
  haveI := coolLaw_isProbabilityMeasure (m := m) hσ hball hfin i
  have hc : 0 < chain m σsq K i := chain_pos hσ hball hfin i
  rw [← integral_phaseScore_coolLaw hKm hc]
  exact integral_le_bound (measurable_phaseScore hKm i) (phaseScore_nonneg m σsq K i)
    (phaseScore_le hσ hKR i)

/-! ## 3.  The downstream estimator conclusion, from the relaxed hypothesis

`PhaseMean.lean`'s `integral_prod_mem_relErr_of_budget` does the compounding; the only work
here is the plumbing onto the universal run space, so that the per-phase hypotheses can be
stated about the samplers' own laws. -/

/-- **The telescoped product's mean, from `m` approximately unbiased phases.**

Each phase `i < m` draws from its own law `ν j i`, within total variation `e i` of the exact
phase law, on a body inside `R·Bₙ`; the per-phase slack `e^{R²/(2σᵢ²)}·(e i) ≤ η·(chain(i+1)/
chain i)` holds; and the budget is `2mη ≤ τ ≤ 1`.  Then run `j`'s product estimator has mean
within a **relative `τ`** of `chain m / chain 0`.

This is the downstream conclusion `hphase_mean` was there to supply, obtained without the
equation.  Independence across phases is `Arlib.Probability.iIndepFun_natScore_phases`; the
compounding is `integral_prod_mem_relErr_of_budget`; the telescoping is
`prod_fin_telescope`. -/
theorem integral_prod_phaseScore_mem_relErr {m : ℕ} {σsq : ℕ → ℝ}
    (hσ : ∀ j, 0 < σsq j) {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R)
    (ν : ℕ → ℕ → Measure (EuclSpace n)) [hν : ∀ j i, IsProbabilityMeasure (ν j i)] (j : ℕ)
    {e : ℕ → ℝ≥0∞} (he : ∀ i, e i ≠ ⊤)
    (hTV : ∀ i : Fin m, TVLe (ν j (i : ℕ)) (coolLaw m σsq K (i : ℕ)) (e (i : ℕ)))
    {η τ : ℝ} (hm : 0 < m) (hη : 0 ≤ η) (hτ : τ ≤ 1) (hbudget : 2 * (m : ℝ) * η ≤ τ)
    (hslack : ∀ i : Fin m, Real.exp (R ^ 2 / (2 * σsq (i : ℕ))) * (e (i : ℕ)).toReal
      ≤ η * (chain m σsq K ((i : ℕ) + 1) / chain m σsq K (i : ℕ))) :
    ∫ ω, ∏ i : Fin m, Arlib.Probability.natScore
          (fun (_ i : ℕ) => phaseScore m σsq K i) j (i : ℕ) ω
        ∂(Arlib.Probability.natRunMeasure ν)
      ∈ Set.Icc ((1 - τ) * (chain m σsq K m / chain m σsq K 0))
          ((1 + τ) * (chain m σsq K m / chain m σsq K 0)) := by
  have hgm : ∀ a b : ℕ, Measurable (phaseScore (n := n) m σsq K b) := fun _ b =>
    measurable_phaseScore hKm b
  refine integral_prod_mem_relErr_of_budget (A := fun i => chain m σsq K i) hm hη hτ hbudget
    (Arlib.Probability.iIndepFun_natScore_phases ν hgm j m)
    (fun i => (Arlib.Probability.measurable_natScore hgm j (i : ℕ)).aestronglyMeasurable)
    (fun i => chain_pos hσ hball hfin i) (fun i => ?_)
  rw [integral_natScore_coord ν hgm j (i : ℕ)]
  exact integral_phaseScore_mem_Icc_of_tvLe hσ hKm hball hfin hKR (hTV i) (he _) (hslack i)

/-- **Positivity of the product estimator's mean** — the side condition the downstream
Chebyshev step needs, read off the lower half of the interval above. -/
theorem integral_prod_phaseScore_pos {m : ℕ} {σsq : ℕ → ℝ}
    (hσ : ∀ j, 0 < σsq j) {K : Set (EuclSpace n)}
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (ν : ℕ → ℕ → Measure (EuclSpace n)) [∀ j i, IsProbabilityMeasure (ν j i)] (j : ℕ)
    {τ : ℝ} (hτ : τ < 1)
    (h : ∫ ω, ∏ i : Fin m, Arlib.Probability.natScore
          (fun (_ i : ℕ) => phaseScore m σsq K i) j (i : ℕ) ω
        ∂(Arlib.Probability.natRunMeasure ν)
      ∈ Set.Icc ((1 - τ) * (chain m σsq K m / chain m σsq K 0))
          ((1 + τ) * (chain m σsq K m / chain m σsq K 0))) :
    0 < ∫ ω, ∏ i : Fin m, Arlib.Probability.natScore
          (fun (_ i : ℕ) => phaseScore m σsq K i) j (i : ℕ) ω
        ∂(Arlib.Probability.natRunMeasure ν) :=
  integral_prod_pos hτ (div_pos (chain_pos hσ hball hfin m) (chain_pos hσ hball hfin 0)) h

/-! ## 4.  The relaxed hypothesis, discharged from the chain the algorithm runs

Composition of §2 with `mixesWithin_lazy_metropolisGaussian_coolLaw`
(`PhaseMeanRoute.lean`).  Every binder of the mixing theorem is passed through verbatim;
`hiso` and `hwarm` are unproved and carried, exactly as there. -/

/-- **`hphase_mean`, relaxed and discharged for the actual Metropolis–Gaussian chain.**

After the mixing theorem's step count, the law of the lazy Metropolis-filtered Gaussian ball
walk gives the phase-`i` score a mean within a relative `η` of the chain ratio, provided the
slack `e^{R²/(2σᵢ²)}·eps ≤ η·(chain(i+1)/chain i)` holds.

**This carries `hiso` as an unproved binder** — module docstring §6.  It is a mixing
statement, not a running-time statement. -/
theorem integral_phaseScore_mem_Icc_of_mixing (hn : 2 ≤ n)
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
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) {i : ℕ} (hi : i < m) (hs : σ ^ 2 = σsq i)
    {η : ℝ} (hslack : Real.exp (R ^ 2 / (2 * σsq i)) * eps
      ≤ η * (chain m σsq K (i + 1) / chain m σsq K i)) :
    ∫ x, phaseScore m σsq K i x
        ∂(MarkovChains.iterate
            (MarkovChains.lazy (MarkovChains.metropolisGaussian K δ (σ ^ 2))) mu0 t)
      ∈ Set.Icc ((1 - η) * (chain m σsq K (i + 1) / chain m σsq K i))
          ((1 + η) * (chain m σsq K (i + 1) / chain m σsq K i)) := by
  have hmix := mixesWithin_lazy_metropolisGaussian_coolLaw hn hσpos hδop hR hK hKc hKR hKtop
    hK0 hell hfloor hiso hM hwarm heps0 heps1 ht hσsch hball hi hs
  have hKR' : K ⊆ closedBall (0 : EuclSpace n) R := fun x hx =>
    mem_closedBall_zero_iff.2 (hKR x hx)
  refine integral_phaseScore_mem_Icc_of_tvLe hσsch hK hball hKtop hKR' hmix
    ENNReal.ofReal_ne_top ?_
  rwa [ENNReal.toReal_ofReal heps0.le]

/-! ## 5.  The step count, with the cost visible in the statement

The largest mixing error the slack admits is `eps = η·r/B`, `B = e^{R²/(2σᵢ²)}`.  The
identity below is the whole quantitative content of §4 of the module docstring: the additive
`R²/(2σᵢ²)` in `log(1/eps)` is not a log factor, and it is what the mixing theorem's step
count multiplies by `n²`. -/

/-- **The exact size of the mixing budget this route demands.**

    `log(1/(η·r/B)) = log B + log(1/η) + log(1/r)`.

With `B = e^{R²/(2σᵢ²)}` the first summand is `R²/(2σᵢ²)` (see
`log_one_div_tvBudget_exp`), which is the term that breaks the `O*(n²)` step count on any
schedule that actually cools. -/
theorem log_one_div_tvBudget {B η r : ℝ} (hB : 0 < B) (hη : 0 < η) (hr : 0 < r) :
    Real.log (1 / (η * r / B)) = Real.log B + Real.log (1 / η) + Real.log (1 / r) := by
  have h1 : 1 / (η * r / B) = B / (η * r) := by
    field_simp
  rw [h1, Real.log_div hB.ne' (by positivity), Real.log_mul hη.ne' hr.ne', one_div, one_div,
    Real.log_inv, Real.log_inv]
  ring

/-- **The same at `B = e^{R²/(2s)}`**: the sup-norm exponent enters `log(1/eps)` additively
and undamped. -/
theorem log_one_div_tvBudget_exp {R s η r : ℝ} (hη : 0 < η) (hr : 0 < r) :
    Real.log (1 / (η * r / Real.exp (R ^ 2 / (2 * s))))
      = R ^ 2 / (2 * s) + Real.log (1 / η) + Real.log (1 / r) := by
  rw [log_one_div_tvBudget (Real.exp_pos _) hη hr, Real.log_exp]

/-- **The budget is a legal mixing error**: `η·r/B ≤ 1` once `η ≤ 1` and `r ≤ B`. -/
theorem tvBudget_le_one {B η r : ℝ} (hB : 0 < B) (hη : η ≤ 1) (hr0 : 0 ≤ r)
    (hrB : r ≤ B) : η * r / B ≤ 1 := by
  rw [div_le_one hB]
  nlinarith

/-- **The budget meets the slack condition**, with equality at the top: `B·(η·r/B) = η·r`. -/
theorem slack_of_le_tvBudget {B η r eps : ℝ} (hB : 0 < B) (heps : eps ≤ η * r / B) :
    B * eps ≤ η * r := by
  have := mul_le_mul_of_nonneg_left heps hB.le
  rwa [mul_div_cancel₀ _ hB.ne'] at this

/-- **The headline step count.**

The mixing error is set to the largest value the slack admits, `eps = η·r/B` with
`B = e^{R²/(2σᵢ²)}` and `r = chain(i+1)/chain i`, and the step-count hypothesis is written
with `log(1/eps)` **expanded by `log_one_div_tvBudget_exp`**, so the additive `R²/(2σᵢ²)` is
visible in the statement rather than hidden inside an `eps`:

    `t ≥ 4·(5120²·n²·(log M + 2·[R²/(2σᵢ²) + log(1/η) + log(chain i / chain(i+1))])/log²2) + 1`.

Under it, the phase-`i` score's mean along the actual chain is within a relative `η` of the
chain ratio.  Chained with `integral_prod_phaseScore_mem_relErr` at `η ≤ τ/(2m)`
(`phaseBias_le_of_div`), this is the whole approximate route.

**Read the `R²/(2σᵢ²)` term, not past it**: it is the exponent of the score's sup norm, it is
multiplied by `n²`, and it is polynomially large in `n` on any schedule that cools.  Module
docstring §4.  Carries `hiso` and `hwarm`. -/
theorem integral_phaseScore_mem_Icc_of_mixing_steps (hn : 2 ≤ n)
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
    {mu0 : Measure (EuclSpace n)} [IsProbabilityMeasure mu0] {M : ℝ} (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0 (Arlib.uniformOn
      ((volume : Measure (EuclSpace n)).withDensity
        (MarkovChains.gaussianWeight (σ ^ 2))) K))
    {m : ℕ} {σsq : ℕ → ℝ} (hσsch : ∀ j, 0 < σsq j)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) {i : ℕ} (hi : i < m) (hs : σ ^ 2 = σsq i)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    {t : ℕ} (ht : 4 * (5120 ^ 2 * (n : ℝ) ^ 2 *
        (Real.log M + 2 * (R ^ 2 / (2 * σsq i) + Real.log (1 / η)
          + Real.log (1 / (chain m σsq K (i + 1) / chain m σsq K i))))
        / Real.log 2 ^ 2) + 1 ≤ (t : ℝ)) :
    ∫ x, phaseScore m σsq K i x
        ∂(MarkovChains.iterate
            (MarkovChains.lazy (MarkovChains.metropolisGaussian K δ (σ ^ 2))) mu0 t)
      ∈ Set.Icc ((1 - η) * (chain m σsq K (i + 1) / chain m σsq K i))
          ((1 + η) * (chain m σsq K (i + 1) / chain m σsq K i)) := by
  have hKR' : K ⊆ closedBall (0 : EuclSpace n) R := fun x hx =>
    mem_closedBall_zero_iff.2 (hKR x hx)
  have hB : (0 : ℝ) < Real.exp (R ^ 2 / (2 * σsq i)) := Real.exp_pos _
  have hr : 0 < chain m σsq K (i + 1) / chain m σsq K i :=
    div_pos (chain_pos hσsch hball hKtop (i + 1)) (chain_pos hσsch hball hKtop i)
  have hrB : chain m σsq K (i + 1) / chain m σsq K i ≤ Real.exp (R ^ 2 / (2 * σsq i)) :=
    chain_ratio_le_exp hσsch hK hball hKtop hKR'
  set eps : ℝ := η * (chain m σsq K (i + 1) / chain m σsq K i)
      / Real.exp (R ^ 2 / (2 * σsq i)) with heps_def
  have heps0 : 0 < eps := by positivity
  have heps1 : eps ≤ 1 := tvBudget_le_one hB hη1 hr.le hrB
  have hlog : Real.log (1 / eps)
      = R ^ 2 / (2 * σsq i) + Real.log (1 / η)
        + Real.log (1 / (chain m σsq K (i + 1) / chain m σsq K i)) :=
    log_one_div_tvBudget_exp hη0 hr
  have ht' : 4 * (5120 ^ 2 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2) + 1 ≤ (t : ℝ) := by rwa [hlog]
  refine integral_phaseScore_mem_Icc_of_mixing hn hσpos hδop hR hK hKc hKR hKtop hK0 hell
    hfloor hiso hM hwarm heps0 heps1 ht' hσsch hball hi hs ?_
  exact slack_of_le_tvBudget hB le_rfl

/-! ## 6.  The route Cousins–Vempala actually take, and what it costs

Their coupling never bounds a *mean*.  It bounds the probability of the estimator's success
event, and total variation transfers that at additive cost `e` — with no sup-norm factor.
Contrast the `e^{R²/(2σᵢ²)}` of §2. -/

/-- **A TV bound on the run's law costs the success probability `e`, and nothing else.**

If the estimator `V` is `acc`-relatively accurate for `vol` with probability at least `q`
under the exact joint law `μ`, then under *any* law `μ'` within total variation `e` of `μ` it
is `acc`-accurate with probability at least `q − e`.

No radius, no schedule, no bound on `V`: this is `Arlib.TVLe.abs_measureReal_sub_le`, i.e.
the definition of total variation.  It is the `Arlib` reading of `vol3_journal.tex:1426-1431`
and `:1588`, where the accumulated sampling error `tν` (resp. `2kmν`) enters the *failure
probability* and never the bias.

What is missing for that route is the tensorization `TVLe (⨂ᵢ νᵢ) (⨂ᵢ ν'ᵢ) (Σᵢ eᵢ)` — the
union bound of `vol3_journal.tex:1021` — which would turn per-sample mixing bounds into the
`hTV` this theorem consumes.  It is not in `Arlib` and is not built here. -/
theorem measureReal_relErr_ge_of_tvLe {Ω : Type*} [MeasurableSpace Ω]
    {μ' μ : Measure Ω} [IsProbabilityMeasure μ'] [IsProbabilityMeasure μ] {e : ℝ≥0∞}
    (hTV : TVLe μ' μ e) (he : e ≠ ⊤) {V : Ω → ℝ} (hV : Measurable V) {vol acc q : ℝ}
    (hgood : q ≤ μ.real {ω | |V ω - vol| ≤ acc * vol}) :
    q - e.toReal ≤ μ'.real {ω | |V ω - vol| ≤ acc * vol} := by
  have hS : MeasurableSet {ω | |V ω - vol| ≤ acc * vol} :=
    measurableSet_le ((hV.sub measurable_const).abs) measurable_const
  have hd := hTV.abs_measureReal_sub_le he hS
  rw [abs_le] at hd
  linarith [hd.1]

/-! ## 7.  Non-vacuity (`CLAUDE.md` §11)

§2 and §3 quantify over a bundle — a positive schedule, a body containing the unit ball, of
finite volume, inside a radius `R`, a sampled law within TV `e`, and budgets `η`, `τ`
satisfying `2mη ≤ τ ≤ 1`.  A green build over an unsatisfiable bundle certifies nothing.
Here is one instance meeting all of it at once:

    n = 1,  K = closedBall 0 1 ⊆ ℝ¹,  σsq ≡ 1,  m = 1,  i = 0,  R = 1,
    ν = coolLaw itself (so e = 0),  η = 1/4,  τ = 1/2   (budget: 2·1·(1/4) = 1/2 ≤ 1/2).

Note the bias `η = 1/4` is **strictly positive**: the witness exhibits the relaxed interval,
not the equation in disguise, so it certifies that the relaxed hypothesis is satisfiable at a
genuine slack.

**What this does not certify.**  §4's composed theorems additionally carry `hiso`, which is
not proved anywhere in this repository, and a warm start.  No witness for those is claimed
here, and none is offered — see `PhaseMeanRoute.lean` §6, which records why the existing
`Arlib.MarkovChains.exists_mixesWithin_lazy_metropolisGaussian_witness` (on `B(0,1/2) ⊆ ℝ²`)
cannot serve: its body does not contain the unit ball, so it is not simultaneously a witness
for `chain_pos`.  Flagged, not faked. -/

/-- **Non-vacuity of the relaxed per-phase hypothesis (§2).**  One concrete body, schedule,
law and bias satisfying every binder of `integral_phaseScore_mem_Icc_of_tvLe` at once, with
`η = 1/4 > 0`. -/
theorem exists_phaseMeanApprox_witness :
    ∃ (K : Set (EuclSpace 1)) (σsq : ℕ → ℝ) (ν : Measure (EuclSpace 1)) (η : ℝ),
      (∀ j, 0 < σsq j) ∧ MeasurableSet K ∧ Convex ℝ K ∧
      ball (0 : EuclSpace 1) 1 ⊆ K ∧ volume K ≠ ⊤ ∧
      K ⊆ closedBall (0 : EuclSpace 1) 1 ∧ IsProbabilityMeasure ν ∧
      TVLe ν (coolLaw 1 σsq K 0) 0 ∧ 0 < η ∧
      ∫ x, phaseScore 1 σsq K 0 x ∂ν
        ∈ Set.Icc ((1 - η) * (chain 1 σsq K 1 / chain 1 σsq K 0))
            ((1 + η) * (chain 1 σsq K 1 / chain 1 σsq K 0)) := by
  set K : Set (EuclSpace 1) := closedBall (0 : EuclSpace 1) 1 with hK_def
  have hσ : ∀ j : ℕ, (0 : ℝ) < (fun _ : ℕ => (1 : ℝ)) j := fun _ => one_pos
  have hKm : MeasurableSet K := measurableSet_closedBall
  have hball : ball (0 : EuclSpace 1) 1 ⊆ K := ball_subset_closedBall
  have hfin : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  haveI := coolLaw_isProbabilityMeasure (m := 1) (σsq := fun _ => 1) hσ hball hfin 0
  have hr : 0 < chain 1 (fun _ => 1) K 1 / chain 1 (fun _ => 1) K 0 :=
    div_pos (chain_pos hσ hball hfin 1) (chain_pos hσ hball hfin 0)
  refine ⟨K, fun _ => 1, coolLaw 1 (fun _ => 1) K 0, 1 / 4, hσ, hKm, convex_closedBall _ _,
    hball, hfin, subset_rfl, inferInstance, TVLe.refl _, by norm_num, ?_⟩
  have hr' : 0 < chain 1 (fun _ : ℕ => (1 : ℝ)) K (0 + 1) / chain 1 (fun _ : ℕ => (1 : ℝ)) K 0 :=
    div_pos (chain_pos hσ hball hfin (0 + 1)) (chain_pos hσ hball hfin 0)
  refine integral_phaseScore_mem_Icc_of_tvLe hσ hKm hball hfin (R := 1) subset_rfl
    (TVLe.refl _) (by simp) ?_
  simp only [ENNReal.toReal_zero, mul_zero]
  linarith

/-- **Non-vacuity of the product conclusion (§3).**  The same body and schedule with one
phase, all coordinate laws exact, `η = 1/4` and `τ = 1/2` — the budget `2mη ≤ τ ≤ 1` holds
with equality, and both are strictly positive. -/
theorem exists_prod_phaseMeanApprox_witness :
    ∃ (K : Set (EuclSpace 1)) (σsq : ℕ → ℝ) (ν : ℕ → ℕ → Measure (EuclSpace 1)) (η τ : ℝ),
      (∀ j i, IsProbabilityMeasure (ν j i)) ∧
      (∀ j, 0 < σsq j) ∧ MeasurableSet K ∧ ball (0 : EuclSpace 1) 1 ⊆ K ∧
      volume K ≠ ⊤ ∧ K ⊆ closedBall (0 : EuclSpace 1) 1 ∧
      0 < η ∧ 0 < τ ∧ τ ≤ 1 ∧ 2 * (1 : ℝ) * η ≤ τ ∧
      ∫ ω, ∏ i : Fin 1, Arlib.Probability.natScore
            (fun (_ i : ℕ) => phaseScore 1 σsq K i) 0 (i : ℕ) ω
          ∂(Arlib.Probability.natRunMeasure ν)
        ∈ Set.Icc ((1 - τ) * (chain 1 σsq K 1 / chain 1 σsq K 0))
            ((1 + τ) * (chain 1 σsq K 1 / chain 1 σsq K 0)) := by
  set K : Set (EuclSpace 1) := closedBall (0 : EuclSpace 1) 1 with hK_def
  have hσ : ∀ j : ℕ, (0 : ℝ) < (fun _ : ℕ => (1 : ℝ)) j := fun _ => one_pos
  have hKm : MeasurableSet K := measurableSet_closedBall
  have hball : ball (0 : EuclSpace 1) 1 ⊆ K := ball_subset_closedBall
  have hfin : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  haveI hprob : ∀ _j _i : ℕ, IsProbabilityMeasure (coolLaw 1 (fun _ : ℕ => (1 : ℝ)) K 0) :=
    fun _ _ => coolLaw_isProbabilityMeasure (m := 1) hσ hball hfin 0
  have hr' : 0 < chain 1 (fun _ : ℕ => (1 : ℝ)) K (0 + 1) / chain 1 (fun _ : ℕ => (1 : ℝ)) K 0 :=
    div_pos (chain_pos hσ hball hfin (0 + 1)) (chain_pos hσ hball hfin 0)
  refine ⟨K, fun _ => 1, fun _ _ => coolLaw 1 (fun _ => 1) K 0, 1 / 4, 1 / 2, hprob, hσ, hKm,
    hball, hfin, subset_rfl, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  refine integral_prod_phaseScore_mem_relErr (R := 1) (hν := hprob) (η := 1 / 4) (τ := 1 / 2)
    hσ hKm hball hfin subset_rfl
    (e := fun _ => 0) _ 0 (fun _ => by simp) (fun i => ?_) Nat.one_pos (by norm_num)
    (by norm_num) (by norm_num) (fun i => ?_)
  · have hi : (i : ℕ) = 0 := by omega
    rw [hi]
    exact TVLe.refl _
  · have hi : (i : ℕ) = 0 := by omega
    rw [hi]
    simp only [ENNReal.toReal_zero, mul_zero]
    linarith

end Arlib.GaussianCooling

/-! ## Axiom audit (`CLAUDE.md` §4) -/

#print axioms Arlib.GaussianCooling.integral_natScore_coord
#print axioms Arlib.GaussianCooling.integral_phaseScore_mem_Icc_of_tvLe
#print axioms Arlib.GaussianCooling.chain_ratio_le_exp
#print axioms Arlib.GaussianCooling.integral_prod_phaseScore_mem_relErr
#print axioms Arlib.GaussianCooling.integral_prod_phaseScore_pos
#print axioms Arlib.GaussianCooling.integral_phaseScore_mem_Icc_of_mixing
#print axioms Arlib.GaussianCooling.log_one_div_tvBudget
#print axioms Arlib.GaussianCooling.log_one_div_tvBudget_exp
#print axioms Arlib.GaussianCooling.tvBudget_le_one
#print axioms Arlib.GaussianCooling.slack_of_le_tvBudget
#print axioms Arlib.GaussianCooling.integral_phaseScore_mem_Icc_of_mixing_steps
#print axioms Arlib.GaussianCooling.measureReal_relErr_ge_of_tvLe
#print axioms Arlib.GaussianCooling.exists_phaseMeanApprox_witness
#print axioms Arlib.GaussianCooling.exists_prod_phaseMeanApprox_witness
