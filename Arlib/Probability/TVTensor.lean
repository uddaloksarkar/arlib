/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Probability.TV
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Tensorization of total variation: the union bound over independent samples

A sampler is run many times.  Each run's law is within total variation `eᵢ` of its target,
and the analysis of the algorithm is carried out against the **joint** law of all the runs
at once.  The bridge between the two is the fact proved here:

    `TVLe (⨂ᵢ νᵢ) (⨂ᵢ ν'ᵢ) (∑ᵢ eᵢ)`

— the total variation distance between two product measures is at most the *sum* of the
coordinatewise distances.  This is the "union bound" step of Cousins–Vempala's volume
algorithm (`vol3_journal.tex:1021`, per-sample budget `ν = (ε/n)^16` at `:212`), where the
accumulated sampling error `k·m·ν` enters the estimator's **failure probability** and never
its bias.

## Why this and not an approximate-mean route

`Arlib/Convexity/GaussianCooling/PhaseMeanApprox.lean` proves the alternative: a TV bound on
a single phase's law can be turned into a relaxed `(1 ± η)` bound on that phase's *mean*.
That route is real but it pays the sup norm of the score, `B = e^{R²/(2σᵢ²)}`, in the
admissible mixing error (`log_one_div_tvBudget_exp` there), and on a schedule that actually
cools that exponent is polynomial in `n`.  Cousins–Vempala do not take it.  They introduce
exact-law shadow variables and price the coupling in failure probability
(`vol3_journal.tex:1426-1430`), which costs `log(1/eps) = O(log(km/δ))` per sample and no
sup-norm factor at all.  `Arlib.GaussianCooling.measureReal_relErr_ge_of_tvLe` is the
single-sample half of that route; **this file is the other half**, the piece its docstring
records as missing.

## Mathlib status

Mathlib v4.32 has no total variation distance between measures at all — the only
`totalVariation` in the library is the Jordan decomposition of a *signed* measure
(`Mathlib/MeasureTheory/VectorMeasure/Decomposition/Jordan.lean`), and there is no
tensorization lemma for it.  So there is nothing to bridge to; this is proved from scratch
against `Arlib.TVLe`.

## `IsProbabilityMeasure` is load-bearing, not hygiene

The union bound is **false** for unnormalised measures.  Inserting the hybrid `μ₁' ⊗ μ₂`
between `μ₁ ⊗ μ₂` and `μ₁' ⊗ μ₂'` costs `μ₂(univ) · e₁` on one side and `μ₁'(univ) · e₂` on
the other: with `μ₁' = 2·(a probability measure)` the second term is `2·e₂`, and the
conclusion `e₁ + e₂` fails.  Every statement below therefore carries
`IsProbabilityMeasure` on **all** the factors, and that hypothesis cannot be weakened to
`IsFiniteMeasure`.

## Main results

* `Arlib.lintegral_le_of_tvLe` — a `TVLe` bound survives a lower integral of a `[0,1]`-valued
  observable.  This is an intentional duplicate of
  `Arlib.MarkovChains.lintegral_le_of_tvLe` (`Arlib/MarkovChains/Continuous/Warmness.lean`),
  copied rather than imported so that a file under `Arlib/Probability/` does not depend on
  `Arlib/MarkovChains/` — that import would invert the layering, since `Warmness.lean`
  itself imports `Arlib/Probability/TV.lean`.  The two should be consolidated when the
  layering is settled.
* `Arlib.TVLe.prod` — **the two-factor case**: `TVLe (μ₁.prod μ₂) (μ₁'.prod μ₂') (e₁ + e₂)`.
* `Arlib.TVLe.pi` — **the finite-product case**, over a dependent family indexed by `Fin m`:
  `TVLe (Measure.pi μ) (Measure.pi μ') (∑ i, e i)`.
* `Arlib.tvLe_pi_pi`, `Arlib.tvLe_pi_pi_const` — the doubly-indexed form, i.e. `r` runs of
  `m` phases each.  `Measure.pi fun j => Measure.pi fun i => ν j i` is *syntactically*
  `Arlib.Probability.runMeasure ν` (`Arlib/Probability/RunPlumbing.lean`), so these apply to
  the run space without importing it.  The constant-budget form reads
  `TVLe … ((r · m) · b)`, which is Cousins–Vempala's `k·m·ν` verbatim.
* `Arlib.le_measureReal_of_tvLe_pi_pi` — the composite: `r·m` per-sample mixing bounds move
  the estimator's success probability by at most `∑∑ eⱼᵢ` and nothing else.  This is
  `Arlib.GaussianCooling.measureReal_relErr_ge_of_tvLe` with its `hTV` supplied; it is
  restated here rather than imported so that this file stays inside `Arlib/Probability/`.

## Non-vacuity (`CLAUDE.md` §11)

`tvLe_bernoulli_witness` and `tvLe_prod_witness` exhibit a concrete two-factor instance with
`e₁ = e₂ = 1/4` — strictly positive, and with total `1/2` strictly below `1`, so the
conclusion is *not* the trivial `tvLe_one`.  `not_tvLe_prod_witness_quarter` shows the
tensorized bound is genuinely needed: for that instance the product measures differ by
`7/16` on a single point, which exceeds either factor's `1/4`.

## Scope

Finite products only.  Nothing here addresses `Measure.infinitePi` (the union bound over
infinitely many coordinates is false as stated — `∑ᵢ eᵢ` need not converge), and nothing
here is a statement about running time.
-/

namespace Arlib

open MeasureTheory Set
open scoped ENNReal

universe u

/-! ## 1.  A `TVLe` bound passes a lower integral

The ingredient the product argument needs and `Arlib/Probability/TV.lean` deliberately does
not have: the section function `x ↦ μ₂(Sₓ)` is a general `[0,1]`-valued observable, not an
indicator, so moving a setwise bound past `∫⁻ · ∂μ₁` needs a layer cake. -/

section Lintegral

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **A `TVLe` bound survives a lower integral of a `[0,1]`-valued observable**: for
measurable `f : Ω → ℝ≥0∞` with `f ≤ 1`,

  `∫⁻ f ∂μ ≤ ∫⁻ f ∂ν + ε`.

This is the `ℝ≥0∞` companion of `Arlib.TVLe.integral_le`, and unlike that lemma it needs
no finiteness of `ε` and no probability-measure hypothesis.

The proof is the layer cake `∫⁻ f ∂μ = ∫⁻_{t > 0} μ {f ≥ t} dt`
(`MeasureTheory.lintegral_eq_lintegral_meas_le`).  Because `f ≤ 1`, the tail set `{f ≥ t}`
is empty for `t > 1`, so only `t ∈ (0,1]` contributes; there the hypothesis gives
`μ {f ≥ t} ≤ ν {f ≥ t} + ε` pointwise, and `(0,1]` has Lebesgue measure `1`, so integrating
the slack costs exactly `ε` and no more.

**Duplication, deliberate.** This is verbatim `Arlib.MarkovChains.lintegral_le_of_tvLe`.
It is copied rather than imported because importing
`Arlib/MarkovChains/Continuous/Warmness.lean` from a file under `Arlib/Probability/` would
invert the library's layering. -/
theorem lintegral_le_of_tvLe {μ ν : Measure Ω} {ε : ℝ≥0∞} (h : TVLe μ ν ε) {f : Ω → ℝ≥0∞}
    (hf : Measurable f) (hf1 : ∀ x, f x ≤ 1) :
    ∫⁻ x, f x ∂μ ≤ ∫⁻ x, f x ∂ν + ε := by
  -- Move to the real-valued `g = f.toReal`, which is what the layer cake consumes.
  set g : Ω → ℝ := fun x => (f x).toReal with hgdef
  have hgm : Measurable g := hf.ennreal_toReal
  have hofReal : ∀ x, ENNReal.ofReal (g x) = f x := fun x =>
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hf1 x))
  have hg1 : ∀ x, g x ≤ 1 := fun x => by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (hf1 x)
    simpa [hgdef] using this
  -- The tail sets.
  set A : ℝ → Set Ω := fun t => {x | t ≤ g x} with hAdef
  have hAm : ∀ t, MeasurableSet (A t) := fun t => measurableSet_le measurable_const hgm
  have hlayer : ∀ ρ : Measure Ω, ∫⁻ x, f x ∂ρ = ∫⁻ t in Ioi (0 : ℝ), ρ (A t) := by
    intro ρ
    have : ∫⁻ x, ENNReal.ofReal (g x) ∂ρ = ∫⁻ t in Ioi (0 : ℝ), ρ {x | t ≤ g x} :=
      lintegral_eq_lintegral_meas_le ρ
        (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hgm.aemeasurable
    simpa only [hofReal, hAdef] using this
  -- The slack, supported on `(0,1]`.
  set c : ℝ → ℝ≥0∞ := (Ioc (0 : ℝ) 1).indicator (fun _ => ε) with hcdef
  have hcm : Measurable c := measurable_const.indicator measurableSet_Ioc
  have hcint : ∫⁻ t in Ioi (0 : ℝ), c t = ε := by
    rw [hcdef, lintegral_indicator measurableSet_Ioc, setLIntegral_const,
      Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_self_of_subset_left Set.Ioc_subset_Ioi_self]
    simp
  -- The pointwise bound on `(0, ∞)`.
  have hpt : ∀ t ∈ Ioi (0 : ℝ), μ (A t) ≤ ν (A t) + c t := by
    intro t ht
    rcases le_or_gt t 1 with ht1 | ht1
    · have hmem : t ∈ Ioc (0 : ℝ) 1 := ⟨ht, ht1⟩
      rw [hcdef, Set.indicator_of_mem hmem]
      exact (h (A t) (hAm t)).1
    · have hempty : A t = ∅ := by
        rw [hAdef]
        exact Set.eq_empty_of_forall_notMem fun x hx => absurd (hx.trans (hg1 x)) (not_le.2 ht1)
      simp [hempty]
  calc ∫⁻ x, f x ∂μ = ∫⁻ t in Ioi (0 : ℝ), μ (A t) := hlayer μ
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (ν (A t) + c t) := by
        refine lintegral_mono_ae ?_
        filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        exact hpt t ht
    _ = (∫⁻ t in Ioi (0 : ℝ), ν (A t)) + ∫⁻ t in Ioi (0 : ℝ), c t :=
        lintegral_add_right _ hcm
    _ = ∫⁻ x, f x ∂ν + ε := by rw [← hlayer ν, hcint]

end Lintegral

/-! ## 2.  The two-factor case

The whole argument is the hybrid `μ₁ ⊗ μ₂ → μ₁' ⊗ μ₂ → μ₁' ⊗ μ₂'`.  The first swap is
§1 applied to the section function `x ↦ μ₂ (Sₓ)`, which is measurable and `≤ 1`; the second
is the pointwise bound `μ₂ (Sₓ) ≤ μ₂' (Sₓ) + e₂` integrated against the probability measure
`μ₁'`, whose total mass `1` is exactly what stops the slack from being inflated. -/

section Prod

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ₁ μ₁' : Measure α} {μ₂ μ₂' : Measure β} {e₁ e₂ : ℝ≥0∞}

/-- **The one-sided product bound.** For a measurable `S ⊆ α × β`,

  `(μ₁ ⊗ μ₂) S ≤ (μ₁' ⊗ μ₂') S + (e₁ + e₂)`.

`IsProbabilityMeasure μ₁'` and `IsProbabilityMeasure μ₂` are load-bearing: the first keeps
the `e₂` slack from being multiplied by `μ₁' univ`, the second keeps the section function
inside `[0,1]` so that §1 applies. -/
theorem measure_prod_le_of_tvLe [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₁']
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₂']
    (h₁ : TVLe μ₁ μ₁' e₁) (h₂ : TVLe μ₂ μ₂' e₂) {S : Set (α × β)} (hS : MeasurableSet S) :
    (μ₁.prod μ₂) S ≤ (μ₁'.prod μ₂') S + (e₁ + e₂) := by
  have hsec : ∀ x : α, MeasurableSet (Prod.mk x ⁻¹' S) := fun _ => measurable_prodMk_left hS
  have hf : Measurable fun x => μ₂ (Prod.mk x ⁻¹' S) := measurable_measure_prodMk_left hS
  have hf1 : ∀ x : α, μ₂ (Prod.mk x ⁻¹' S) ≤ 1 := fun _ => prob_le_one
  -- Swap the outer factor: `μ₁ → μ₁'`, at cost `e₁`.
  have hstep1 : ∫⁻ x, μ₂ (Prod.mk x ⁻¹' S) ∂μ₁ ≤ (∫⁻ x, μ₂ (Prod.mk x ⁻¹' S) ∂μ₁') + e₁ :=
    lintegral_le_of_tvLe h₁ hf hf1
  -- Swap the inner factor: `μ₂ → μ₂'`, at cost `e₂ · μ₁' univ = e₂`.
  have hstep2 :
      (∫⁻ x, μ₂ (Prod.mk x ⁻¹' S) ∂μ₁') ≤ (∫⁻ x, μ₂' (Prod.mk x ⁻¹' S) ∂μ₁') + e₂ := by
    calc ∫⁻ x, μ₂ (Prod.mk x ⁻¹' S) ∂μ₁'
        ≤ ∫⁻ x, (μ₂' (Prod.mk x ⁻¹' S) + e₂) ∂μ₁' :=
          lintegral_mono fun x => (h₂ _ (hsec x)).1
      _ = (∫⁻ x, μ₂' (Prod.mk x ⁻¹' S) ∂μ₁') + e₂ := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  rw [Measure.prod_apply hS, Measure.prod_apply hS]
  calc ∫⁻ x, μ₂ (Prod.mk x ⁻¹' S) ∂μ₁
      ≤ (∫⁻ x, μ₂ (Prod.mk x ⁻¹' S) ∂μ₁') + e₁ := hstep1
    _ ≤ ((∫⁻ x, μ₂' (Prod.mk x ⁻¹' S) ∂μ₁') + e₂) + e₁ := by gcongr
    _ = (∫⁻ x, μ₂' (Prod.mk x ⁻¹' S) ∂μ₁') + (e₁ + e₂) := by ring

/-- **Total variation tensorizes over a product of two factors.**

  `TVLe μ₁ μ₁' e₁ → TVLe μ₂ μ₂' e₂ → TVLe (μ₁ ⊗ μ₂) (μ₁' ⊗ μ₂') (e₁ + e₂)`.

The errors add; they are not multiplied and no mass factor appears.  All four measures must
be probability measures — see the module docstring, the statement is false without it. -/
theorem TVLe.prod [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₁']
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₂']
    (h₁ : TVLe μ₁ μ₁' e₁) (h₂ : TVLe μ₂ μ₂' e₂) :
    TVLe (μ₁.prod μ₂) (μ₁'.prod μ₂') (e₁ + e₂) := fun _ hS =>
  ⟨measure_prod_le_of_tvLe h₁ h₂ hS, measure_prod_le_of_tvLe h₁.symm h₂.symm hS⟩

end Prod

/-! ## 3.  The finite-product case

Induction on the number of coordinates, peeling coordinate `0` with the measure-preserving
equivalence `MeasurableEquiv.piFinSuccAbove` and applying §2 to the resulting pair.  The
family is allowed to be *dependent* (`π : Fin m → Type u`), which costs nothing and is what
makes the doubly-indexed corollary of §4 a direct instance. -/

section Pi

/-- The `∀`-form of `TVLe.pi`, in the shape the induction on the number of coordinates
needs: every parameter that mentions `m` is generalised.  Users want `TVLe.pi`. -/
theorem tvLe_pi_aux :
    ∀ (m : ℕ) {π : Fin m → Type u} [_inst : ∀ i, MeasurableSpace (π i)]
      (μ μ' : ∀ i, Measure (π i)), (∀ i, IsProbabilityMeasure (μ i)) →
      (∀ i, IsProbabilityMeasure (μ' i)) → ∀ e : Fin m → ℝ≥0∞,
      (∀ i, TVLe (μ i) (μ' i) (e i)) → TVLe (Measure.pi μ) (Measure.pi μ') (∑ i, e i) := by
  intro m
  induction m with
  | zero =>
      intro π _ μ μ' _ _ e _
      rw [Fin.sum_univ_zero, tvLe_zero_iff, Measure.pi_of_empty μ, Measure.pi_of_empty μ']
  | succ m ih =>
      intro π _ μ μ' hμ hμ' e h
      haveI : ∀ i, IsProbabilityMeasure (μ i) := hμ
      haveI : ∀ i, IsProbabilityMeasure (μ' i) := hμ'
      -- The `m` remaining coordinates, by the induction hypothesis.
      have hIH :=
        ih (fun j => μ ((0 : Fin (m + 1)).succAbove j))
          (fun j => μ' ((0 : Fin (m + 1)).succAbove j)) (fun j => hμ _) (fun j => hμ' _)
          (fun j => e ((0 : Fin (m + 1)).succAbove j)) fun j => h _
      -- Coordinate `0` against the rest, by the two-factor case.
      have hprod := TVLe.prod (h 0) hIH
      -- Transport back along the measure-preserving equivalence.
      have hmp := (MeasureTheory.measurePreserving_piFinSuccAbove μ (0 : Fin (m + 1))).symm
        (MeasurableEquiv.piFinSuccAbove π 0)
      have hmp' := (MeasureTheory.measurePreserving_piFinSuccAbove μ' (0 : Fin (m + 1))).symm
        (MeasurableEquiv.piFinSuccAbove π 0)
      have hmap := hprod.map (MeasurableEquiv.piFinSuccAbove π 0).symm.measurable
      rw [hmp.map_eq, hmp'.map_eq] at hmap
      rw [Fin.sum_univ_succAbove e 0]
      exact hmap

/-- **Total variation tensorizes over a finite product, with a union bound.**

  `(∀ i, TVLe (μ i) (μ' i) (e i)) → TVLe (Measure.pi μ) (Measure.pi μ') (∑ i, e i)`.

This is the union bound of `vol3_journal.tex:1021`: `m` samples each within `eᵢ` of their
target give a joint law within `∑ᵢ eᵢ`.  No sup norm, no mass factor, no schedule.

All coordinate measures must be probability measures on both sides. -/
theorem TVLe.pi {m : ℕ} {π : Fin m → Type u} [∀ i, MeasurableSpace (π i)]
    {μ μ' : ∀ i, Measure (π i)} [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (μ' i)] {e : Fin m → ℝ≥0∞}
    (h : ∀ i, TVLe (μ i) (μ' i) (e i)) :
    TVLe (Measure.pi μ) (Measure.pi μ') (∑ i, e i) :=
  tvLe_pi_aux m μ μ' (fun _ => inferInstance) (fun _ => inferInstance) e h

end Pi

/-! ## 4.  The run space: `r` runs of `m` phases

`Measure.pi fun j => Measure.pi fun i => ν j i` is *syntactically* the definition of
`Arlib.Probability.runMeasure ν` (`Arlib/Probability/RunPlumbing.lean`), so the statements
here apply to the run space verbatim without this file importing it — which it must not,
since `RunPlumbing` pulls in `Arlib/Convexity/GaussianCooling/Estimator.lean`. -/

section Run

variable {r m : ℕ} {E : Type u} [MeasurableSpace E]
variable {ν ν' : Fin r → Fin m → Measure E}

/-- **The union bound over `r · m` samples.**  Each of the `r · m` coordinates within `e j i`
of its target puts the joint law within `∑ⱼ ∑ᵢ e j i`. -/
theorem tvLe_pi_pi [∀ j i, IsProbabilityMeasure (ν j i)]
    [∀ j i, IsProbabilityMeasure (ν' j i)] {e : Fin r → Fin m → ℝ≥0∞}
    (h : ∀ j i, TVLe (ν j i) (ν' j i) (e j i)) :
    TVLe (Measure.pi fun j => Measure.pi fun i => ν j i)
      (Measure.pi fun j => Measure.pi fun i => ν' j i) (∑ j, ∑ i, e j i) :=
  TVLe.pi fun j => TVLe.pi fun i => h j i

/-- **Cousins–Vempala's `k·m·ν`, verbatim.**  A *uniform* per-sample budget `b` over `r`
runs of `m` phases costs `(r · m) · b` on the joint law — `vol3_journal.tex:1021` with the
per-sample budget of `:212`. -/
theorem tvLe_pi_pi_const [∀ j i, IsProbabilityMeasure (ν j i)]
    [∀ j i, IsProbabilityMeasure (ν' j i)] {b : ℝ≥0∞}
    (h : ∀ j i, TVLe (ν j i) (ν' j i) b) :
    TVLe (Measure.pi fun j => Measure.pi fun i => ν j i)
      (Measure.pi fun j => Measure.pi fun i => ν' j i) ((r * m : ℕ) * b) := by
  have := tvLe_pi_pi (e := fun _ _ => b) h
  simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using this

/-- **The composite: `r · m` per-sample mixing bounds move the estimator's success
probability by `∑ⱼ ∑ᵢ e j i` and by nothing else.**

If the estimator `V` is `acc`-relatively accurate for `vol` with probability at least `q`
under the exact joint law `⨂ ν'`, then it is `acc`-accurate with probability at least
`q − (∑ⱼ∑ᵢ eⱼᵢ)` under the *sampled* joint law `⨂ ν`.  No radius, no schedule, no bound on
`V`, no sup norm of any score.

This is `Arlib.GaussianCooling.measureReal_relErr_ge_of_tvLe` with its `hTV` hypothesis
finally supplied by `tvLe_pi_pi`; it is restated here rather than imported so that this file
stays inside `Arlib/Probability/`. -/
theorem le_measureReal_of_tvLe_pi_pi [∀ j i, IsProbabilityMeasure (ν j i)]
    [∀ j i, IsProbabilityMeasure (ν' j i)] {e : Fin r → Fin m → ℝ≥0∞}
    (h : ∀ j i, TVLe (ν j i) (ν' j i) (e j i)) (he : (∑ j, ∑ i, e j i) ≠ ⊤)
    {V : (Fin r → Fin m → E) → ℝ} (hV : Measurable V) {vol acc q : ℝ}
    (hgood : q ≤ (Measure.pi fun j => Measure.pi fun i => ν' j i).real
      {ω | |V ω - vol| ≤ acc * vol}) :
    q - (∑ j, ∑ i, e j i).toReal ≤ (Measure.pi fun j => Measure.pi fun i => ν j i).real
      {ω | |V ω - vol| ≤ acc * vol} := by
  have hVs : Measurable fun ω : Fin r → Fin m → E => V ω - vol := hV.sub measurable_const
  have hS : MeasurableSet {ω : Fin r → Fin m → E | |V ω - vol| ≤ acc * vol} :=
    measurableSet_le hVs.abs measurable_const
  have hd := (tvLe_pi_pi h).abs_measureReal_sub_le he hS
  rw [abs_le] at hd
  linarith [hd.1]

end Run

/-! ## 5.  Non-vacuity (`CLAUDE.md` §11)

`TVLe.prod` quantifies over four probability measures and two error budgets.  A green build
over an unsatisfiable bundle certifies nothing, and a bundle satisfiable only at `e₁ = e₂ = 0`
(equal measures) or at `e₁ + e₂ ≥ 1` (where `Arlib.tvLe_one` already gives the conclusion for
free) would certify almost nothing.  The witness below is neither: two genuinely different
Bernoulli laws at distance exactly `1/4`, tensorized to a total of `1/2 < 1`.

`not_tvLe_prod_witness_quarter` is the sharpness half: on that instance the two product
measures differ by `1 − 9/16 = 7/16` at the single point `(true, true)`, which is strictly
more than either factor's `1/4`.  So the `e₁ + e₂` of `TVLe.prod` is doing real work — the
conclusion does not hold with `max e₁ e₂`, let alone with either budget alone. -/

section Witness

/-- The biased coin: `true` with probability `3/4`. -/
private theorem isProbabilityMeasure_witness :
    IsProbabilityMeasure
      ((3 / 4 : ℝ≥0∞) • Measure.dirac true + (1 / 4 : ℝ≥0∞) • Measure.dirac false) := by
  constructor
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [ENNReal.div_add_div_same, show (3 : ℝ≥0∞) + 1 = 4 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

attribute [local instance] isProbabilityMeasure_witness

/-- **Non-vacuity, one factor.**  The point mass at `true` is at total variation distance
`1/4` from the `3/4`-biased coin, and `1/4 > 0`: the hypothesis of `TVLe.prod` is
satisfiable at a *strictly positive* budget by measures that are genuinely unequal. -/
theorem tvLe_bernoulli_witness :
    TVLe (Measure.dirac true)
      ((3 / 4 : ℝ≥0∞) • Measure.dirac true + (1 / 4 : ℝ≥0∞) • Measure.dirac false)
      (1 / 4) := by
  have h1 : (3 / 4 : ℝ≥0∞) + 1 / 4 = 1 := by
    rw [ENNReal.div_add_div_same, show (3 : ℝ≥0∞) + 1 = 4 by norm_num]
    exact ENNReal.div_self (by norm_num) (by norm_num)
  have h2 : (3 / 4 : ℝ≥0∞) + 4⁻¹ = 1 := by rw [← one_div]; exact h1
  have h3 : (3 / 4 : ℝ≥0∞) ≤ 1 := by rw [← h2]; exact le_self_add
  have h4 : (3 / 4 : ℝ≥0∞) ≤ 1 + 4⁻¹ := h3.trans le_self_add
  intro S hS
  simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hS]
  by_cases ht : (true : Bool) ∈ S <;> by_cases hf : (false : Bool) ∈ S <;>
    simp [ht, hf, h2, h4]

/-- **Non-vacuity, the two-factor conclusion.**  `TVLe.prod` instantiated at the witness:
two independent draws, each within `1/4` of its target, put the pair within `1/2`.  The
total `1/2` is strictly below `1`, so this is not an instance of `Arlib.tvLe_one`. -/
theorem tvLe_prod_witness :
    TVLe ((Measure.dirac true).prod (Measure.dirac true))
      (((3 / 4 : ℝ≥0∞) • Measure.dirac true + (1 / 4 : ℝ≥0∞) • Measure.dirac false).prod
        ((3 / 4 : ℝ≥0∞) • Measure.dirac true + (1 / 4 : ℝ≥0∞) • Measure.dirac false))
      (1 / 4 + 1 / 4) :=
  TVLe.prod tvLe_bernoulli_witness tvLe_bernoulli_witness

/-- **The sum in `TVLe.prod` is not slack.**  On the witness instance the two product laws
differ by `7/16` at the single point `(true, true)`, so the conclusion fails at the budget
`1/4` of either single factor.  The tensorized bound has to grow. -/
theorem not_tvLe_prod_witness_quarter :
    ¬ TVLe ((Measure.dirac true).prod (Measure.dirac true))
      (((3 / 4 : ℝ≥0∞) • Measure.dirac true + (1 / 4 : ℝ≥0∞) • Measure.dirac false).prod
        ((3 / 4 : ℝ≥0∞) • Measure.dirac true + (1 / 4 : ℝ≥0∞) • Measure.dirac false))
      (1 / 4) := by
  intro h
  have hpt : MeasurableSet ({(true, true)} : Set (Bool × Bool)) :=
    measurableSet_singleton _
  have hle := (h _ hpt).1
  have hdir : (Measure.dirac (true : Bool)) ({true} : Set Bool) = 1 :=
    Measure.dirac_apply_of_mem (Set.mem_singleton _)
  have hmix : ((3 / 4 : ℝ≥0∞) • Measure.dirac true + (1 / 4 : ℝ≥0∞) • Measure.dirac false)
      ({true} : Set Bool) = 3 / 4 := by
    simp only [Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton (true : Bool))]
    rw [Set.indicator_of_mem (Set.mem_singleton _), Set.indicator_of_notMem (by simp),
      Pi.one_apply, mul_one, mul_zero, add_zero]
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, Measure.prod_prod, hdir, hmix,
    one_mul] at hle
  -- `hle : 1 ≤ 3/4 * (3/4) + 1/4`, i.e. `1 ≤ 13/16`.  Compare in `ℝ`.
  have hne : (3 / 4 * (3 / 4) + 1 / 4 : ℝ≥0∞) ≠ ⊤ := by finiteness
  have h1 := ENNReal.toReal_mono hne hle
  rw [ENNReal.toReal_one, ENNReal.toReal_add (by finiteness) (by finiteness)] at h1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div] at h1
  norm_num at h1

end Witness

end Arlib
