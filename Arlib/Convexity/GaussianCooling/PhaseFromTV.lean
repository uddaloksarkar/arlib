/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.PhaseVar
import Arlib.Convexity.GaussianCooling.PhaseMeanApprox
import Mathlib.Analysis.Convex.Measure

/-!
# Both remaining hypotheses of the volume algorithm, from one per-phase TV bound

`Ttc/Volume/CVInstantiate.lean` discharges twelve of the fourteen hypotheses of
`Ttc.VolumeAlgorithm.cousinsVempala`.  The two survivors, `hphase_mean` and `hphase_var`,
are both about the sampler, and the constructor the capstone `Ttc.ttc_runtime_mn4` actually
runs on is `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`
(`Ttc/Volume/CVInstantiate.lean:458`), whose two binders are, character for character:

```
(hphase_mean : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
  Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
  ∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ)) ∈
    relErr (ε / (2 * (2 + ε) * (phases K ε p : ℝ)))
      (Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1) /
        Arlib.GaussianCooling.chain (phases K ε p) (σsq K ε p) K (i : ℕ)))
(hphase_var : ∀ (K : Set (Space n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
  Metric.ball (0 : Space n) 1 ⊆ K → volume K ≠ ⊤ → ∀ j (i : Fin (phases K ε p)),
  ∫ x, (g K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ))
    ≤ (1 + Arlib.GaussianCooling.varBudget (ε / 2) / (phases K ε p : ℝ)) *
        (∫ x, g K ε p j (i : ℕ) x ∂(ν j (i : ℕ))) ^ 2)
```

§4 below proves **both of those propositions**, from one per-phase total-variation
hypothesis and explicit schedule side conditions.  `Arlib` may not import `Ttc`
(`lakefile.toml`), so as in `PhaseMean.lean` and `PhaseMeanRoute.lean` the two reducible
translations are made in prose rather than in code: `Ttc.Space n` and
`Arlib.GaussianCooling.EuclSpace n` are both `abbrev`s of `EuclideanSpace ℝ (Fin n)`
(`Ttc/Model/Prelude.lean:48`, `Arlib/Convexity/GaussianCooling/Variance.lean:72`), and
`Ttc.relErr η b` is `@[reducible] def relErr (ε b : ℝ) : Set ℝ := Set.Icc ((1-ε)*b) ((1+ε)*b)`
(`Ttc/Model/ProblemSetting.lean:36`), so the `Set.Icc` written here *is* the `relErr`
written there.  Drift therefore becomes a type error at the `Ttc`-side application
`fun K ε p hε hp hp1 hconv hball hfin j i => hphase_mean_of_tvLe … K ε p hε hp hp1 hconv
hball hfin j i`, not silence.

## The finding this file exists to record: `MeasurableSet K` is **not** available

Every per-phase lemma this file builds on — `measurable_phaseScore`,
`integral_phaseScore_coolLaw`, `coolLaw_sq_moment_le`,
`integral_phaseScore_mem_Icc_of_tvLe` — carries a hypothesis `hKm : MeasurableSet K`.
The two binders above quantify over **every** `K` with `Convex ℝ K`,
`Metric.ball 0 1 ⊆ K` and `volume K ≠ ⊤`, and supply no measurability.  Those three do
**not** imply `MeasurableSet K`: `MeasurableSet` on `EuclideanSpace ℝ (Fin n)` is *Borel*
measurability, and `K = Metric.ball 0 2 ∪ S` with `S` an arbitrary (possibly non-Borel)
subset of `Metric.sphere 0 2` is convex, contains the unit ball and has finite volume while
being non-Borel.  So a hypothesis of the form

    ∀ K ε p, 0 < ε → … → volume K ≠ ⊤ → MeasurableSet K

is **false**, and adding it to either binder's antecedent would have produced a green,
axiom-clean, vacuously-instantiable theorem.  It is not added.

**The repair, and it is a modelling decision (`CLAUDE.md` §6).**  §1 scores the body's
*interior* instead: `interior K` is open, hence Borel, and inherits every other hypothesis
(`Convex.interior`, `interior_maximal`, `measure_mono interior_subset`).  Nothing is lost on
the `K` side because `Convex.addHaar_frontier` makes the frontier null, so
`volume.restrict (interior K) = volume.restrict K` and therefore
`chain m σsq (interior K) i = chain m σsq K i` and
`coolLaw m σsq (interior K) i = coolLaw m σsq K i` — the chain ratios and the exact phase law
in the binders are unchanged, and are written at `K` throughout.  What *is* a real choice:
the score `phaseScore … (interior K) i` and the score `phaseScore … K i` differ on the
frontier, and the sampled law `ν` — known only to be within total variation of `coolLaw` —
may charge the frontier, so the two are not interchangeable *under `ν`*.  The algorithm is
therefore modelled as scoring `x ∈ interior K`, which is what a Borel-measurable score can
do; this is stated, not hidden.

## What already existed and is reused verbatim (nothing below re-proves it)

* `Arlib.GaussianCooling.sq_moment_le_of_tvLe_map` — `PhaseVar.lean:286`, the second-moment
  transport through a sampling map.
* `Arlib.GaussianCooling.coolLaw_sq_moment_le` — `PhaseVar.lean:513`, the exact-law
  second-moment bound at an interior phase, with **no** assumed input.
* `Arlib.GaussianCooling.integral_phaseScore_coolLaw` — `PhaseVar.lean:447`,
  `phaseScore_le` — `:374`, `phaseScore_nonneg` — `:369`, `measurable_phaseScore` — `:384`,
  `coolLaw_isProbabilityMeasure` — `:415`, `fixedRate_meets_budget_iff` — `:572`.
* `Arlib.GaussianCooling.integral_phaseScore_mem_Icc_of_tvLe` — `PhaseMeanApprox.lean:262`,
  the mean transport, itself `PhaseMean.lean:361`'s `integral_mem_Icc_of_tvLe` at
  `f = phaseScore`.

`PhaseVar.lean:677`'s `sampled_phase_sq_moment_le` and `:707`'s `…_budget` are the same
transport at `K` itself, i.e. **with** the `hKm` binder that the finding above shows is
undischargeable from the algorithm's own side conditions; §2–§3 are their `interior K`
counterparts, which is the only change.

## Hypotheses carried unproved (all explicit binders, none of them provable here)

* `hTV` — the sampler's guarantee, `TVLe ((ν j i).map (X K ε p j i)) (coolLaw … K i) …`.
  Producing it is conductance/mixing and is **not** touched here.
* `hKR` — a radius `K ⊆ closedBall 0 (R K ε p)`.  Not cosmetic: it is the only source of the
  bound `B = e^{R²/(2σᵢ²)}` on the score (`phaseScore_le`), and `coolRatio` is unbounded on
  an unbounded body.  `cousinsVempala` exposes no radius; see `PhaseVar.lean`'s scope note.
* `hslack` — the explicit smallness condition on the TV error.
* `hrate`, `hn : 3 ≤ n` — the fixed cooling rate `σᵢ₊₁² = σᵢ²(1 + 1/n)`, the regime of
  `coolLaw_sq_moment_le`.
* `hbudget` — `2m ≤ n·varBudget (ε/2)`.  Satisfiable (the witnesses below satisfy it), but
  `geomSchedule_total_cooling_lt` (`PhaseVar.lean:620`) shows what it costs: at the fixed
  rate a schedule meeting the budget cools by a total factor `< 1.1`, i.e. it does not cool.
  That obstruction is inherited unchanged; nothing here removes it.
* `hterm` — the exact-law second-moment bound at the **terminal** phase `i + 1 = m`, where
  the score is the Gaussian-to-uniform switch `e^{‖x‖²/(2σᵢ²)}`.  `coolLaw_sq_moment_le`
  needs `i + 1 < m` and does not cover it; every other index is discharged outright by
  `coolLaw_interior_sq_moment_le`.  This is the one exact-law input still owed.

## Scope

Nothing here produces a TV bound, and nothing here touches the *other* obstruction recorded
at `Ttc/Volume/CVInstantiate.lean:629-633` — that `hgb` asks for a bound on the score
**uniform in `K`** while the chain ratio is unbounded over the bodies the binders range
over.  That is a defect of the `Ttc` interface, not of these two propositions, and no file
under `Ttc/` is edited here.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open scoped ENNReal

/-! ## 1.  The interior bridge -/

variable {n : ℕ}

/-- **A convex body and its interior carry the same restricted Lebesgue measure.**
`Convex.addHaar_frontier` says the frontier of a convex set is null, so
`interior K =ᵐ[volume] K`. -/
theorem restrict_interior_eq {K : Set (EuclSpace n)} (hK : Convex ℝ K) :
    (volume : Measure (EuclSpace n)).restrict (interior K) = volume.restrict K :=
  Measure.restrict_congr_set (interior_ae_eq_of_null_frontier (hK.addHaar_frontier volume))

/-- The cooling chain does not see the frontier. -/
theorem chain_interior {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (i : ℕ) : chain m σsq (interior K) i = chain m σsq K i := by
  simp only [chain_def, restrict_interior_eq hK]

/-- Neither does the exact phase law. -/
theorem coolLaw_interior {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} (hK : Convex ℝ K)
    (i : ℕ) : coolLaw m σsq (interior K) i = coolLaw m σsq K i := by
  simp only [coolLaw, restrict_interior_eq hK, chain_interior hK]

/-- The interior of a body that contains the unit ball is a body that contains the unit
ball: everything the per-phase lemmas ask of `K` they get from `interior K`. -/
theorem ball_subset_interior {K : Set (EuclSpace n)} (hball : ball (0 : EuclSpace n) 1 ⊆ K) :
    ball (0 : EuclSpace n) 1 ⊆ interior K :=
  interior_maximal hball isOpen_ball

theorem volume_interior_ne_top {K : Set (EuclSpace n)} (hfin : volume K ≠ ⊤) :
    volume (interior K) ≠ ⊤ :=
  ne_top_of_le_ne_top hfin (measure_mono interior_subset)

/-! ## 2.  The two per-phase consequences of one TV bound -/

section PerPhase

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {m : ℕ} {σsq : ℕ → ℝ} {i : ℕ} {K : Set (EuclSpace n)} {X : Ω → EuclSpace n} {e : ℝ≥0∞}

/-- **The interior score is unbiased at the exact phase law**, with the law and the chain
ratio both written at `K`.  `integral_phaseScore_coolLaw` moved across the bridge. -/
theorem integral_phaseScore_interior_coolLaw (hσ : ∀ j, 0 < σsq j) (hK : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤) :
    ∫ x, phaseScore m σsq (interior K) i x ∂(coolLaw m σsq K i)
      = chain m σsq K (i + 1) / chain m σsq K i := by
  rw [← coolLaw_interior hK i, ← chain_interior hK (i + 1), ← chain_interior hK i]
  exact integral_phaseScore_coolLaw isOpen_interior.measurableSet
    (chain_pos hσ (ball_subset_interior hball) (volume_interior_ne_top hfin) i)

/-- **The approximate-mean consequence.**  The interior score's mean under the *sampled*
law lies in `(1 ± η)·(chain(i+1)/chain i)`, with the chain ratio written at `K` itself. -/
theorem integral_phaseScore_interior_mem_Icc_of_tvLe (hσ : ∀ j, 0 < σsq j)
    (hK : Convex ℝ K) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R) (hX : Measurable X)
    (hTV : TVLe (μ.map X) (coolLaw m σsq K i) e) (he : e ≠ ⊤) {η : ℝ}
    (hslack : Real.exp (R ^ 2 / (2 * σsq i)) * e.toReal
      ≤ η * (chain m σsq K (i + 1) / chain m σsq K i)) :
    ∫ ω, phaseScore m σsq (interior K) i (X ω) ∂μ
      ∈ Set.Icc ((1 - η) * (chain m σsq K (i + 1) / chain m σsq K i))
          ((1 + η) * (chain m σsq K (i + 1) / chain m σsq K i)) := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  have hmap : ∫ x, phaseScore m σsq (interior K) i x ∂(μ.map X)
      = ∫ ω, phaseScore m σsq (interior K) i (X ω) ∂μ :=
    integral_map hX.aemeasurable
      (measurable_phaseScore isOpen_interior.measurableSet i).aestronglyMeasurable
  rw [← hmap, ← chain_interior hK (i + 1), ← chain_interior hK i]
  exact integral_phaseScore_mem_Icc_of_tvLe hσ isOpen_interior.measurableSet
    (ball_subset_interior hball) (volume_interior_ne_top hfin) (interior_subset.trans hKR)
    (by rw [coolLaw_interior hK]; exact hTV) he
    (by rw [chain_interior hK (i + 1), chain_interior hK i]; exact hslack)

/-- **The second-moment consequence, in workhorse form.**  The exact-law bound `hexact` is
an *input* here; §3 discharges it at every interior phase. -/
theorem phaseScore_interior_sq_moment_le_of_tvLe (hσ : ∀ j, 0 < σsq j)
    (hK : Convex ℝ K) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R) (hX : Measurable X)
    (hTV : TVLe (μ.map X) (coolLaw m σsq K i) e) (he : e ≠ ⊤)
    {C s : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ s)
    (hexact : ∫ x, phaseScore m σsq (interior K) i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ C * (∫ x, phaseScore m σsq (interior K) i x ∂(coolLaw m σsq K i)) ^ 2)
    (hslack : e.toReal * (Real.exp (R ^ 2 / (2 * σsq i)) ^ 2 * (1 + 2 * (C + s)))
      ≤ s * (chain m σsq K (i + 1) / chain m σsq K i) ^ 2) :
    ∫ ω, phaseScore m σsq (interior K) i (X ω) ^ 2 ∂μ
      ≤ (C + s) * (∫ ω, phaseScore m σsq (interior K) i (X ω) ∂μ) ^ 2 := by
  haveI := coolLaw_isProbabilityMeasure (m := m) (σsq := σsq) hσ hball hfin i
  have hmean := integral_phaseScore_interior_coolLaw (m := m) (i := i) hσ hK hball hfin
  exact sq_moment_le_of_tvLe_map hX hTV he (Real.exp_pos _)
    (measurable_phaseScore isOpen_interior.measurableSet i)
    (phaseScore_nonneg m σsq (interior K) i)
    (phaseScore_le hσ (interior_subset.trans hKR) i) hC hs hexact
    (by rw [hmean]; exact hslack)

/-! ## 3.  Discharging the exact-law input, and the algorithm's own constant -/

/-- **The exact-law input, discharged at an interior phase.**  `coolLaw_sq_moment_le` at
`interior K`, moved back to `K` by the bridge.  No sampler hypothesis, no TV bound. -/
theorem coolLaw_interior_sq_moment_le (hσ : ∀ j, 0 < σsq j) (hK : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤) (hi : i + 1 < m)
    (hn : 3 ≤ n) (hrate : σsq (i + 1) = σsq i * (1 + 1 / (n : ℝ))) :
    ∫ x, phaseScore m σsq (interior K) i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ (1 + 2 / (n : ℝ))
        * (∫ x, phaseScore m σsq (interior K) i x ∂(coolLaw m σsq K i)) ^ 2 := by
  rw [← coolLaw_interior hK i]
  exact coolLaw_sq_moment_le hσ hK.interior isOpen_interior.measurableSet
    (ball_subset_interior hball) (volume_interior_ne_top hfin) hi hn hrate

/-- **The second-moment consequence at the constant the algorithm writes**, `1 + κ/m`.
`κ = varBudget (ε/2)` is what `cousinsVempalaOfRunsApproxMean`'s `hphase_var` asks for. -/
theorem phaseScore_interior_sq_moment_le_budget (hσ : ∀ j, 0 < σsq j)
    (hK : Convex ℝ K) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R) (hX : Measurable X)
    (hTV : TVLe (μ.map X) (coolLaw m σsq K i) e) (he : e ≠ ⊤)
    {κ : ℝ} (hm : 0 < m) (hn : 0 < n) (hbudget : 2 * (m : ℝ) ≤ (n : ℝ) * κ)
    (hexact : ∫ x, phaseScore m σsq (interior K) i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ (1 + 2 / (n : ℝ))
        * (∫ x, phaseScore m σsq (interior K) i x ∂(coolLaw m σsq K i)) ^ 2)
    (hslack : e.toReal * (Real.exp (R ^ 2 / (2 * σsq i)) ^ 2 * (1 + 2 * (1 + κ / (m : ℝ))))
      ≤ (κ / (m : ℝ) - 2 / (n : ℝ)) * (chain m σsq K (i + 1) / chain m σsq K i) ^ 2) :
    ∫ ω, phaseScore m σsq (interior K) i (X ω) ^ 2 ∂μ
      ≤ (1 + κ / (m : ℝ)) * (∫ ω, phaseScore m σsq (interior K) i (X ω) ∂μ) ^ 2 := by
  have hs : (0 : ℝ) ≤ κ / (m : ℝ) - 2 / (n : ℝ) := by
    have := (fixedRate_meets_budget_iff hn hm κ).2 hbudget
    linarith
  have hC : (0 : ℝ) ≤ 1 + 2 / (n : ℝ) := by positivity
  have heq : 1 + 2 / (n : ℝ) + (κ / (m : ℝ) - 2 / (n : ℝ)) = 1 + κ / (m : ℝ) := by ring
  have hmain := phaseScore_interior_sq_moment_le_of_tvLe hσ hK hball hfin hKR hX hTV he hC hs
    hexact (by rw [heq]; exact hslack)
  rwa [heq] at hmain

end PerPhase

/-! ## 4.  The two hypothesis binders, verbatim -/

section Family

/-- **`cousinsVempalaOfRunsApproxMean`'s `hphase_mean`, discharged from a per-phase TV
bound.**  The conclusion is that binder character-for-character, at

    g K ε p j i = fun x => phaseScore (phases K ε p) (σsq K ε p) (interior K) i
                             (X K ε p j i x)

(`Space n` and `EuclSpace n` are both `abbrev`s of `EuclideanSpace ℝ (Fin n)`, and
`Ttc.relErr η b` is a `@[reducible] def` for `Set.Icc ((1-η)*b) ((1+η)*b)`). -/
theorem hphase_mean_of_tvLe (E : Type) [MeasurableSpace E]
    (phases : Set (EuclSpace n) → ℝ → ℝ → ℕ)
    (σsq : Set (EuclSpace n) → ℝ → ℝ → ℕ → ℝ)
    (ν : ℕ → ℕ → Measure E) [∀ j i, IsProbabilityMeasure (ν j i)]
    (X : Set (EuclSpace n) → ℝ → ℝ → ℕ → ℕ → E → EuclSpace n)
    (R : Set (EuclSpace n) → ℝ → ℝ → ℝ)
    (tvErr : Set (EuclSpace n) → ℝ → ℝ → ℕ → ℕ → ℝ≥0∞)
    (hσ : ∀ K ε p j, 0 < σsq K ε p j)
    (hX : ∀ K ε p j i, Measurable (X K ε p j i))
    (hKR : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)),
      K ⊆ Metric.closedBall (0 : EuclSpace n) (R K ε p))
    (htop : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      tvErr K ε p j (i : ℕ) ≠ ⊤)
    (hTV : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      TVLe ((ν j (i : ℕ)).map (X K ε p j (i : ℕ)))
        (coolLaw (phases K ε p) (σsq K ε p) K (i : ℕ)) (tvErr K ε p j (i : ℕ)))
    (hslack : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      Real.exp (R K ε p ^ 2 / (2 * σsq K ε p (i : ℕ))) * (tvErr K ε p j (i : ℕ)).toReal
        ≤ ε / (2 * (2 + ε) * (phases K ε p : ℝ))
            * (chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1)
                / chain (phases K ε p) (σsq K ε p) K (i : ℕ))) :
    ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      ∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
            (X K ε p j (i : ℕ) x) ∂(ν j (i : ℕ)) ∈
        Set.Icc ((1 - ε / (2 * (2 + ε) * (phases K ε p : ℝ)))
            * (chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1)
                / chain (phases K ε p) (σsq K ε p) K (i : ℕ)))
          ((1 + ε / (2 * (2 + ε) * (phases K ε p : ℝ)))
            * (chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1)
                / chain (phases K ε p) (σsq K ε p) K (i : ℕ))) :=
  fun K ε p hε hp hp1 hconv hball hfin j i =>
    integral_phaseScore_interior_mem_Icc_of_tvLe (hσ K ε p) hconv hball hfin
      (hKR K ε p hε hp hp1 hconv hball hfin j i) (hX K ε p j (i : ℕ))
      (hTV K ε p hε hp hp1 hconv hball hfin j i)
      (htop K ε p hε hp hp1 hconv hball hfin j i)
      (hslack K ε p hε hp hp1 hconv hball hfin j i)

/-- **`cousinsVempalaOfRunsApproxMean`'s `hphase_var`, discharged from the same per-phase
TV bound.**  The conclusion is that binder character-for-character, at the same `g`.

`hterm` is the only exact-law input left: at the *terminal* phase (`i + 1 = m`) the score
is the Gaussian-to-uniform switch `e^{‖x‖²/(2σᵢ²)}`, which `coolLaw_sq_moment_le` does not
cover.  Every other phase is discharged by `coolLaw_interior_sq_moment_le`. -/
theorem hphase_var_of_tvLe (E : Type) [MeasurableSpace E] (hn : 3 ≤ n)
    (phases : Set (EuclSpace n) → ℝ → ℝ → ℕ)
    (σsq : Set (EuclSpace n) → ℝ → ℝ → ℕ → ℝ)
    (ν : ℕ → ℕ → Measure E) [∀ j i, IsProbabilityMeasure (ν j i)]
    (X : Set (EuclSpace n) → ℝ → ℝ → ℕ → ℕ → E → EuclSpace n)
    (R : Set (EuclSpace n) → ℝ → ℝ → ℝ)
    (tvErr : Set (EuclSpace n) → ℝ → ℝ → ℕ → ℕ → ℝ≥0∞)
    (hσ : ∀ K ε p j, 0 < σsq K ε p j)
    (hX : ∀ K ε p j i, Measurable (X K ε p j i))
    (hKR : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)),
      K ⊆ Metric.closedBall (0 : EuclSpace n) (R K ε p))
    (htop : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      tvErr K ε p j (i : ℕ) ≠ ⊤)
    (hTV : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      TVLe ((ν j (i : ℕ)).map (X K ε p j (i : ℕ)))
        (coolLaw (phases K ε p) (σsq K ε p) K (i : ℕ)) (tvErr K ε p j (i : ℕ)))
    (hrate : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (i : Fin (phases K ε p)),
      σsq K ε p ((i : ℕ) + 1) = σsq K ε p (i : ℕ) * (1 + 1 / (n : ℝ)))
    (hbudget : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)),
      2 * (phases K ε p : ℝ) ≤ (n : ℝ) * varBudget (ε / 2))
    (hterm : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (i : Fin (phases K ε p)),
      (i : ℕ) + 1 = phases K ε p →
      ∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ) x ^ 2
          ∂(coolLaw (phases K ε p) (σsq K ε p) K (i : ℕ))
        ≤ (1 + 2 / (n : ℝ))
            * (∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ) x
                ∂(coolLaw (phases K ε p) (σsq K ε p) K (i : ℕ))) ^ 2)
    (hslack : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      (tvErr K ε p j (i : ℕ)).toReal
          * (Real.exp (R K ε p ^ 2 / (2 * σsq K ε p (i : ℕ))) ^ 2
              * (1 + 2 * (1 + varBudget (ε / 2) / (phases K ε p : ℝ))))
        ≤ (varBudget (ε / 2) / (phases K ε p : ℝ) - 2 / (n : ℝ))
            * (chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1)
                / chain (phases K ε p) (σsq K ε p) K (i : ℕ)) ^ 2) :
    ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      ∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
            (X K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ))
        ≤ (1 + varBudget (ε / 2) / (phases K ε p : ℝ))
            * (∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
                (X K ε p j (i : ℕ) x) ∂(ν j (i : ℕ))) ^ 2 := by
  intro K ε p hε hp hp1 hconv hball hfin j i
  have hexact : ∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ) x ^ 2
        ∂(coolLaw (phases K ε p) (σsq K ε p) K (i : ℕ))
      ≤ (1 + 2 / (n : ℝ))
          * (∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ) x
              ∂(coolLaw (phases K ε p) (σsq K ε p) K (i : ℕ))) ^ 2 := by
    rcases Nat.lt_or_ge ((i : ℕ) + 1) (phases K ε p) with hlt | hge
    · exact coolLaw_interior_sq_moment_le (hσ K ε p) hconv hball hfin hlt hn
        (hrate K ε p hε hp hp1 hconv hball hfin j i)
    · have heq : (i : ℕ) + 1 = phases K ε p := by have := i.isLt; omega
      exact hterm K ε p hε hp hp1 hconv hball hfin j i heq
  exact phaseScore_interior_sq_moment_le_budget (hσ K ε p) hconv hball hfin
    (hKR K ε p hε hp hp1 hconv hball hfin j i) (hX K ε p j (i : ℕ))
    (hTV K ε p hε hp hp1 hconv hball hfin j i)
    (htop K ε p hε hp hp1 hconv hball hfin j i) (Fin.pos i) (by omega)
    (hbudget K ε p hε hp hp1 hconv hball hfin j i) hexact
    (hslack K ε p hε hp hp1 hconv hball hfin j i)

end Family

/-! ## 5.  Non-vacuity (`CLAUDE.md` §11)

Two kinds of witness.  The **per-phase** ones are genuine: a concrete body
(`closedBall 0 1`, convex, containing the unit ball, of finite volume, of radius `1`), a
concrete fixed-rate schedule `σᵢ² = (1 + 1/n)^i`, and an exact sampler (`tvErr = 0`, whose
law is `coolLaw` itself), so `hTV`, `hslack`, `hrate`, `hbudget` and the exact-law input hold
simultaneously and the conclusions are the exact-law statements with no loss.

The **family** ones are degenerate on purpose, exactly as
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMeanWitness`
(`Ttc/Volume/CVInstantiate.lean:634`) is, and for a reason worth stating: `ν` is a *fixed*
family of laws chosen before the input `K` is seen, while `hTV` asks each `ν j i` to be
within a small total variation of `coolLaw … K i` for **every** admissible `K`.  With
`phases = 0` every `i`-indexed hypothesis is vacuous (`Fin.elim0`) and the bundle is
inhabited; with `phases > 0` it is the `Ttc` interface's own structural obstruction, not
something these two propositions could repair.  That is why every sampler-side family
hypothesis below sits under `∀ (j : ℕ) (i : Fin (phases K ε p))`, including `hKR`. -/

section Witness

/-- Non-vacuity of `integral_phaseScore_interior_mem_Icc_of_tvLe`: at an exact sampler the
interval collapses onto the exact-law mean. -/
theorem integral_phaseScore_interior_mem_Icc_of_tvLe_witness (hn : 3 ≤ n) :
    ∫ ω, phaseScore 2 (fun j => (1 + 1 / (n : ℝ)) ^ j)
          (interior (closedBall (0 : EuclSpace n) 1)) 0 (id ω)
        ∂(coolLaw 2 (fun j => (1 + 1 / (n : ℝ)) ^ j) (closedBall (0 : EuclSpace n) 1) 0)
      ∈ Set.Icc ((1 - (0 : ℝ)) * (chain 2 (fun j => (1 + 1 / (n : ℝ)) ^ j)
              (closedBall (0 : EuclSpace n) 1) (0 + 1)
            / chain 2 (fun j => (1 + 1 / (n : ℝ)) ^ j) (closedBall (0 : EuclSpace n) 1) 0))
          ((1 + (0 : ℝ)) * (chain 2 (fun j => (1 + 1 / (n : ℝ)) ^ j)
              (closedBall (0 : EuclSpace n) 1) (0 + 1)
            / chain 2 (fun j => (1 + 1 / (n : ℝ)) ^ j)
                (closedBall (0 : EuclSpace n) 1) 0)) := by
  have hc : (0 : ℝ) < 1 + 1 / (n : ℝ) := by positivity
  have hσ : ∀ j, (0 : ℝ) < (1 + 1 / (n : ℝ)) ^ j := fun j => pow_pos hc j
  have hball : ball (0 : EuclSpace n) 1 ⊆ closedBall (0 : EuclSpace n) 1 :=
    ball_subset_closedBall
  have hfin : volume (closedBall (0 : EuclSpace n) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  haveI := coolLaw_isProbabilityMeasure (m := 2) (σsq := fun j => (1 + 1 / (n : ℝ)) ^ j)
    hσ hball hfin 0
  exact integral_phaseScore_interior_mem_Icc_of_tvLe hσ (convex_closedBall _ _) hball hfin
    subset_rfl measurable_id (e := 0) (by rw [Measure.map_id]; exact TVLe.refl _) (by simp)
    (by simp)

/-- Non-vacuity of `phaseScore_interior_sq_moment_le_of_tvLe`: at an exact sampler and zero
slack the conclusion is `coolLaw_interior_sq_moment_le` with no degradation. -/
theorem phaseScore_interior_sq_moment_le_of_tvLe_witness (hn : 3 ≤ n) :
    ∫ ω, phaseScore 2 (fun j => (1 + 1 / (n : ℝ)) ^ j)
          (interior (closedBall (0 : EuclSpace n) 1)) 0 (id ω) ^ 2
        ∂(coolLaw 2 (fun j => (1 + 1 / (n : ℝ)) ^ j) (closedBall (0 : EuclSpace n) 1) 0)
      ≤ (1 + 2 / (n : ℝ) + 0)
        * (∫ ω, phaseScore 2 (fun j => (1 + 1 / (n : ℝ)) ^ j)
              (interior (closedBall (0 : EuclSpace n) 1)) 0 (id ω)
            ∂(coolLaw 2 (fun j => (1 + 1 / (n : ℝ)) ^ j)
                (closedBall (0 : EuclSpace n) 1) 0)) ^ 2 := by
  have hc : (0 : ℝ) < 1 + 1 / (n : ℝ) := by positivity
  have hσ : ∀ j, (0 : ℝ) < (1 + 1 / (n : ℝ)) ^ j := fun j => pow_pos hc j
  have hball : ball (0 : EuclSpace n) 1 ⊆ closedBall (0 : EuclSpace n) 1 :=
    ball_subset_closedBall
  have hfin : volume (closedBall (0 : EuclSpace n) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  haveI := coolLaw_isProbabilityMeasure (m := 2) (σsq := fun j => (1 + 1 / (n : ℝ)) ^ j)
    hσ hball hfin 0
  exact phaseScore_interior_sq_moment_le_of_tvLe hσ (convex_closedBall _ _) hball hfin
    subset_rfl measurable_id (e := 0) (by rw [Measure.map_id]; exact TVLe.refl _) (by simp)
    (by positivity) le_rfl
    (coolLaw_interior_sq_moment_le hσ (convex_closedBall _ _) hball hfin (by norm_num) hn
      (by simp)) (by simp)

/-- Non-vacuity of `phaseScore_interior_sq_moment_le_budget`, the version that also carries
`hbudget : 2m ≤ nκ`: at `m = 2` and `κ = 4/n` the budget holds with equality, the slack is
exactly `0`, and the conclusion is the `1 + κ/m` bound. -/
theorem phaseScore_interior_sq_moment_le_budget_witness (hn : 3 ≤ n) :
    ∫ ω, phaseScore 2 (fun j => (1 + 1 / (n : ℝ)) ^ j)
          (interior (closedBall (0 : EuclSpace n) 1)) 0 (id ω) ^ 2
        ∂(coolLaw 2 (fun j => (1 + 1 / (n : ℝ)) ^ j) (closedBall (0 : EuclSpace n) 1) 0)
      ≤ (1 + 4 / (n : ℝ) / ((2 : ℕ) : ℝ))
        * (∫ ω, phaseScore 2 (fun j => (1 + 1 / (n : ℝ)) ^ j)
              (interior (closedBall (0 : EuclSpace n) 1)) 0 (id ω)
            ∂(coolLaw 2 (fun j => (1 + 1 / (n : ℝ)) ^ j)
                (closedBall (0 : EuclSpace n) 1) 0)) ^ 2 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hc : (0 : ℝ) < 1 + 1 / (n : ℝ) := by positivity
  have hσ : ∀ j, (0 : ℝ) < (1 + 1 / (n : ℝ)) ^ j := fun j => pow_pos hc j
  have hball : ball (0 : EuclSpace n) 1 ⊆ closedBall (0 : EuclSpace n) 1 :=
    ball_subset_closedBall
  have hfin : volume (closedBall (0 : EuclSpace n) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hzero : 4 / (n : ℝ) / ((2 : ℕ) : ℝ) - 2 / (n : ℝ) = 0 := by push_cast; ring
  haveI := coolLaw_isProbabilityMeasure (m := 2) (σsq := fun j => (1 + 1 / (n : ℝ)) ^ j)
    hσ hball hfin 0
  exact phaseScore_interior_sq_moment_le_budget hσ (convex_closedBall _ _) hball hfin
    subset_rfl measurable_id (e := 0) (by rw [Measure.map_id]; exact TVLe.refl _) (by simp)
    (κ := 4 / (n : ℝ)) (by norm_num) (by omega) (by push_cast; field_simp; norm_num)
    (coolLaw_interior_sq_moment_le hσ (convex_closedBall _ _) hball hfin (by norm_num) hn
      (by simp))
    (by rw [show ENNReal.toReal 0 = 0 from rfl, zero_mul, hzero, zero_mul])

/-- Non-vacuity of the `hphase_mean_of_tvLe` bundle — **degenerate on purpose** (zero
phases); see the section docstring. -/
theorem hphase_mean_of_tvLe_witness :
    ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (_j : ℕ) (i : Fin 0),
      ∫ x, phaseScore 0 (fun _ => (1 : ℝ)) (interior K) (i : ℕ) (id x)
          ∂(Measure.dirac (0 : EuclSpace n)) ∈
        Set.Icc ((1 - ε / (2 * (2 + ε) * ((0 : ℕ) : ℝ)))
            * (chain 0 (fun _ => (1 : ℝ)) K ((i : ℕ) + 1)
                / chain 0 (fun _ => (1 : ℝ)) K (i : ℕ)))
          ((1 + ε / (2 * (2 + ε) * ((0 : ℕ) : ℝ)))
            * (chain 0 (fun _ => (1 : ℝ)) K ((i : ℕ) + 1)
                / chain 0 (fun _ => (1 : ℝ)) K (i : ℕ))) :=
  hphase_mean_of_tvLe (EuclSpace n) (fun _ _ _ => 0) (fun _ _ _ _ => 1)
    (fun _ _ => Measure.dirac 0) (fun _ _ _ _ _ => id) (fun _ _ _ => 1) (fun _ _ _ _ _ => 0)
    (fun _ _ _ _ => one_pos) (fun _ _ _ _ _ => measurable_id)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)

/-- Non-vacuity of the `hphase_var_of_tvLe` bundle — **degenerate on purpose** (zero
phases); see the section docstring. -/
theorem hphase_var_of_tvLe_witness (hn : 3 ≤ n) :
    ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (_j : ℕ) (i : Fin 0),
      ∫ x, phaseScore 0 (fun _ => (1 : ℝ)) (interior K) (i : ℕ) (id x) ^ 2
          ∂(Measure.dirac (0 : EuclSpace n))
        ≤ (1 + varBudget (ε / 2) / ((0 : ℕ) : ℝ))
            * (∫ x, phaseScore 0 (fun _ => (1 : ℝ)) (interior K) (i : ℕ) (id x)
                ∂(Measure.dirac (0 : EuclSpace n))) ^ 2 :=
  hphase_var_of_tvLe (EuclSpace n) hn (fun _ _ _ => 0) (fun _ _ _ _ => 1)
    (fun _ _ => Measure.dirac 0) (fun _ _ _ _ _ => id) (fun _ _ _ => 1) (fun _ _ _ _ _ => 0)
    (fun _ _ _ _ => one_pos) (fun _ _ _ _ _ => measurable_id)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)

end Witness

end Arlib.GaussianCooling

/-! ## Axiom audit (`CLAUDE.md` §4)

Every declaration above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms Arlib.GaussianCooling.restrict_interior_eq
#print axioms Arlib.GaussianCooling.chain_interior
#print axioms Arlib.GaussianCooling.coolLaw_interior
#print axioms Arlib.GaussianCooling.ball_subset_interior
#print axioms Arlib.GaussianCooling.volume_interior_ne_top
#print axioms Arlib.GaussianCooling.integral_phaseScore_interior_coolLaw
#print axioms Arlib.GaussianCooling.integral_phaseScore_interior_mem_Icc_of_tvLe
#print axioms Arlib.GaussianCooling.phaseScore_interior_sq_moment_le_of_tvLe
#print axioms Arlib.GaussianCooling.coolLaw_interior_sq_moment_le
#print axioms Arlib.GaussianCooling.phaseScore_interior_sq_moment_le_budget
#print axioms Arlib.GaussianCooling.hphase_mean_of_tvLe
#print axioms Arlib.GaussianCooling.hphase_var_of_tvLe
#print axioms Arlib.GaussianCooling.integral_phaseScore_interior_mem_Icc_of_tvLe_witness
#print axioms Arlib.GaussianCooling.phaseScore_interior_sq_moment_le_of_tvLe_witness
#print axioms Arlib.GaussianCooling.phaseScore_interior_sq_moment_le_budget_witness
#print axioms Arlib.GaussianCooling.hphase_mean_of_tvLe_witness
#print axioms Arlib.GaussianCooling.hphase_var_of_tvLe_witness
