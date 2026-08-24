/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.ColdPhaseRegime
import Arlib.Convexity.GaussianCooling.PhaseMeanRoute

/-!
# Truncating the body at the Gaussian radius, and the `R`-free cost of doing so

## The gap this file closes

`Arlib/MarkovChains/Continuous/ColdPhaseRegime.lean` removed the step-size binder
`hσn : 4 ≤ σ·√n` from the per-phase mixing theorems.  One binder survived,

    `hRσ : R ≤ 2·σ·√n`   where `K ⊆ closedBall 0 R`,

inherited from `Arlib.conductance_speedyMetropolisGaussian_ge_uncond`
(`Arlib/Convexity/IsoIndicator.lean`).  It is **isoperimetric compatibility**, not a step-size
condition: shrinking `δ` does not touch it.  At the Gaussian-cooling cold start `σ² = 1/n` it
reads `R ≤ 2`, so a body with `ball 0 1 ⊆ K ⊆ closedBall 0 R` and `R > 2` is outside the
per-phase theorem at its coldest variances.

## The repair

Run the cold phases on the **truncated body**

    `K' := K ∩ closedBall 0 r`,   `r := 2·σ·√n`,

for which `hRσ` holds by construction, at `R' = r`, with `le_rfl`.  §1 proves `K'` is
admissible — convex, measurable, `ball 0 1 ⊆ K'` as soon as `1 ≤ r`, of positive finite
volume — and §4 instantiates `ColdPhaseRegime`'s per-phase mixing theorems at `K'`.

The cost is the discarded Gaussian mass.  §2 bounds it **without any reference to `R`**.

## Why the bound is `R`-free (§2, the mathematical core)

The naive route bounds the discarded mass by `vol(K)·max γ`, which drags in `R^n` and merely
replaces `R ≤ 2` by `R ≤ e^{3/2}`.  Instead, for `t ∈ (0,1)`, split the Gaussian pointwise on
`{‖x‖ > r}`:

    `e^{-‖x‖²/(2s)} = e^{-t‖x‖²/(2s)}·e^{-(1-t)‖x‖²/(2s)} ≤ e^{-t r²/(2s)}·e^{-‖x‖²/(2·(s/(1-t)))}`,

and integrate the second factor over **all of `ℝⁿ`**:

    `∫_{‖x‖>r} e^{-‖x‖²/(2s)} dx ≤ e^{-t r²/(2s)}·(2π·s/(1-t))^{n/2}`.

That is `lintegral_gaussianWeight_norm_gt_le`, and no set other than `ℝⁿ` appears in it.  For
the denominator only `ball 0 1 ⊆ K` is used:

    `∫_K e^{-‖x‖²/(2s)} dx ≥ e^{-1/(2s)}·vol(B(0,1))`

(`le_lintegral_gaussianWeight_of_unitBall_subset`).  Neither side knows about `R`.

## Main results

| name | content |
| --- | --- |
| `unitBall_subset_inter_closedBall`, `convex_inter_closedBall`, … | §1, `K'` is admissible |
| `lintegral_gaussianWeight_norm_gt_le` | §2, the `R`-free Gaussian tail |
| `le_lintegral_gaussianWeight_of_unitBall_subset` | §2, the `R`-free denominator |
| `lintegral_gaussianWeight_sdiff_le_mul` | §2, **the truncation error**, `≤ C·∫_K γ` |
| `tvLe_condOn_subset` | §3, `TV(condOn μ A, condOn μ B) ≤ μ(B∖A)/μ(B)` for `A ⊆ B` |
| `tvLe_coolLaw_inter_closedBall` | §3, **the TV consequence** for the phase law `coolLaw` |
| `mixesWithin_lazy_speedyMetropolisGaussian_cold_truncated` | §4, `hRσ` discharged by `le_rfl` |
| `coldTruncation_bound_witness` | §5, the bound is `< 1` at `n = 21`, `σ² = 1/n` |
| `coldTruncation_witness` | §5, the full package at `K = closedBall 0 10`, `R = 10 > 2` |

## The numbers

At `r = 2σ√n`, `t = 1/2`, `s = σ²` the §2 bound is

    `e^{-n + 1/(2σ²)}·(4πσ²)^{n/2} / vol(B(0,1))`,

which at `σ² = 1/n` is `e^{-n/2}·(4/n)^{n/2}·Γ(n/2+1)`, asymptotically `√(πn)·(√2/e)^n`.  At
`n = 21` its true value is `8.99·10⁻⁶`; §5 proves the (deliberately slack, rational) bound
`1/1000` for it, entirely from `vol(B(0,1)) = π¹⁰·2¹¹/21‼` and `e^{1/2} ≥ 3/2`.

## What is assumed

**Nothing.**  There is no `def`, `structure`, `class`, `axiom`, `sorry` or `native_decide` in
this file; every declaration is a `theorem`, and none takes an unproved hypothesis bundle.
Every hypothesis of every theorem is discharged outright in §5.

## What is NOT proved

* **Exponential decay in `n` is not proved for general `n`.**  §2 gives an explicit, `R`-free
  bound for every `n`, `σ`, `t`; that it tends to `0` requires a Stirling upper bound on
  `Γ(n/2+1)`, which is not in scope.  Non-vacuity is exhibited numerically at `n = 21`
  (`coldTruncation_bound_witness`), where the bound is `≤ 1/1000 < 1`.
* **Cross-phase composition is not proved.**  The truncation radius `2σ√n` depends on the
  phase variance, so different cold phases run on *different* truncated bodies.  Warm-starting
  phase `i+1` from phase `i`'s truncated law would need a comparison between `K ∩ B(0,2σᵢ√n)`
  and `K ∩ B(0,2σᵢ₊₁√n)`; every statement here is per-phase, as the brief asks.  `TVLe`
  composes by `Arlib.TVLe.trans`, so §3's bound slots in beside the sampler's own TV error,
  but that composition is performed downstream, not here.
* **No running-time claim.**  §4 inherits `ColdPhaseRegime.lean`'s scope verbatim: a step count
  is not a running time, and nothing under `Ttc/` is touched.
-/

open MeasureTheory Metric Set

open scoped ENNReal

namespace Arlib.MarkovChains

open Arlib.GaussianCooling

variable {n : ℕ}

/-! ## 1.  The truncated body is admissible

Everything in this section is about `K ∩ closedBall 0 r` for an arbitrary radius `r`; the
specialisation `r = 2σ√n` — the one that makes `hRσ` an identity — happens in §4. -/

/-- **The truncated body is convex.** -/
theorem convex_inter_closedBall {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (r : ℝ) : Convex ℝ (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r) :=
  hKc.inter (convex_closedBall _ _)

/-- **The truncated body is measurable.** -/
theorem measurableSet_inter_closedBall {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (r : ℝ) :
    MeasurableSet (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r) :=
  hK.inter measurableSet_closedBall

/-- **The truncated body still contains the unit ball**, as soon as the truncation radius is
at least `1`.  At the Gaussian-cooling cold start `σ² = 1/n` the radius `2σ√n` is `2`, so the
hypothesis reads `1 ≤ 2`. -/
theorem unitBall_subset_inter_closedBall {K : Set (EuclideanSpace ℝ (Fin n))} {r : ℝ}
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hr : 1 ≤ r) :
    ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r :=
  subset_inter hball (ball_subset_closedBall.trans (closedBall_subset_closedBall hr))

/-- **The truncated body has the truncation radius as a bounding radius** — this is the fact
that turns `hRσ : R ≤ 2σ√n` into `le_rfl`. -/
theorem norm_le_of_mem_inter_closedBall {K : Set (EuclideanSpace ℝ (Fin n))} {r : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r) :
    ‖x‖ ≤ r := by
  simpa [mem_closedBall_zero_iff] using hx.2

/-- **The truncated body has positive volume**, from the unit ball alone. -/
theorem volume_inter_closedBall_ne_zero {K : Set (EuclideanSpace ℝ (Fin n))} {r : ℝ}
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hr : 1 ≤ r) :
    volume (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r) ≠ 0 := by
  intro h
  have hsub := measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (unitBall_subset_inter_closedBall hball hr)
  rw [h, le_zero_iff] at hsub
  have : (0 : ℝ) < 1 := one_pos
  exact (measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (0 : EuclideanSpace ℝ (Fin n)) this).ne' hsub

/-- **The truncated body has finite volume**, whatever `K` is: it sits inside a ball. -/
theorem volume_inter_closedBall_ne_top (K : Set (EuclideanSpace ℝ (Fin n))) (r : ℝ) :
    volume (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono inter_subset_right)
  exact (measure_closedBall_lt_top).ne

/-! ## 2.  The truncation error, and why no `R` appears in it -/

/-- **The total Gaussian mass of `ℝⁿ`**: `∫_{ℝⁿ} e^{-‖x‖²/(2s)} dx = (2πs)^{n/2}`, as a
lower Lebesgue integral.  A repackaging of `Arlib.GaussianCooling.integral_gaussWeight_univ`
across `ofReal_integral_eq_lintegral_ofReal`. -/
theorem lintegral_gaussianWeight_univ {s : ℝ} (hs : 0 < s) :
    ∫⁻ x : EuclideanSpace ℝ (Fin n), gaussianWeight s x
      = ENNReal.ofReal ((2 * Real.pi * s) ^ ((n : ℝ) / 2)) := by
  have hint : Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-(‖x‖ ^ 2) / (2 * s))) volume := integrable_gaussWeight_univ n hs
  have hnn : (0 : EuclideanSpace ℝ (Fin n) → ℝ) ≤ᵐ[volume]
      fun x => Real.exp (-(‖x‖ ^ 2) / (2 * s)) :=
    Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  have h := ofReal_integral_eq_lintegral_ofReal hint hnn
  rw [integral_gaussWeight_univ n hs] at h
  simpa [gaussianWeight, gaussianWeightReal] using h.symm

/-- **The Gaussian mass of a body is finite** — for every measurable `K`, with no bound on
`K` at all. -/
theorem lintegral_gaussianWeight_ne_top_of_univ {s : ℝ} (hs : 0 < s)
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    ∫⁻ x in K, gaussianWeight s x ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (setLIntegral_le_lintegral _ _)
  rw [lintegral_gaussianWeight_univ hs]
  exact ENNReal.ofReal_ne_top

/-- **The `R`-free Gaussian tail.**  For `t ∈ (0,1)` and `r ≥ 0`,

    `∫_{‖x‖ > r} e^{-‖x‖²/(2s)} dx ≤ e^{-t·r²/(2s)}·(2π·s/(1-t))^{n/2}`.

This is the crux of the file.  The pointwise split
`e^{-‖x‖²/(2s)} = e^{-t‖x‖²/(2s)}·e^{-‖x‖²/(2·(s/(1-t)))}` bounds the first factor by its value
at `‖x‖ = r` and integrates the second over **all of `ℝⁿ`** — so no set other than `ℝⁿ`, and in
particular no circumscribed radius `R`, occurs anywhere in the statement or the proof.  The
alternative route, `vol(K)·max γ`, would carry a factor `R^n`. -/
theorem lintegral_gaussianWeight_norm_gt_le {s r t : ℝ} (hs : 0 < s) (hr : 0 ≤ r)
    (ht0 : 0 < t) (ht1 : t < 1) :
    ∫⁻ x in {x : EuclideanSpace ℝ (Fin n) | r < ‖x‖}, gaussianWeight s x
      ≤ ENNReal.ofReal (Real.exp (-(t * r ^ 2) / (2 * s))
          * (2 * Real.pi * (s / (1 - t))) ^ ((n : ℝ) / 2)) := by
  set b : ℝ := s / (1 - t) with hbdef
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hb : 0 < b := div_pos hs h1t
  set c : ℝ := Real.exp (-(t * r ^ 2) / (2 * s)) with hcdef
  have hc : 0 < c := Real.exp_pos _
  have hSm : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | r < ‖x‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  -- the pointwise bound on `{‖x‖ > r}`
  have hpt : ∀ x ∈ {x : EuclideanSpace ℝ (Fin n) | r < ‖x‖},
      gaussianWeight s x ≤ ENNReal.ofReal (c * Real.exp (-(‖x‖ ^ 2) / (2 * b))) := by
    intro x hx
    have hxr : r < ‖x‖ := hx
    have hsq : r ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith
    have hsplit : -(‖x‖ ^ 2) / (2 * s)
        = -(t * ‖x‖ ^ 2) / (2 * s) + -(‖x‖ ^ 2) / (2 * b) := by
      rw [hbdef]
      field_simp
      ring
    have hmono : Real.exp (-(t * ‖x‖ ^ 2) / (2 * s)) ≤ Real.exp (-(t * r ^ 2) / (2 * s)) := by
      apply Real.exp_le_exp.2
      rw [div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < 2 * s)]
      nlinarith
    have : Real.exp (-(‖x‖ ^ 2) / (2 * s)) ≤ c * Real.exp (-(‖x‖ ^ 2) / (2 * b)) := by
      rw [hsplit, Real.exp_add, hcdef]
      exact mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le
    simpa [gaussianWeight, gaussianWeightReal] using ENNReal.ofReal_le_ofReal this
  calc ∫⁻ x in {x : EuclideanSpace ℝ (Fin n) | r < ‖x‖}, gaussianWeight s x
      ≤ ∫⁻ x in {x : EuclideanSpace ℝ (Fin n) | r < ‖x‖},
          ENNReal.ofReal (c * Real.exp (-(‖x‖ ^ 2) / (2 * b))) := by
        refine lintegral_mono_ae ?_
        filter_upwards [self_mem_ae_restrict hSm] with x hx using hpt x hx
    _ ≤ ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (c * Real.exp (-(‖x‖ ^ 2) / (2 * b))) :=
        setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal c * ∫⁻ x : EuclideanSpace ℝ (Fin n), gaussianWeight b x := by
        simp only [gaussianWeight, gaussianWeightReal,
          ENNReal.ofReal_mul hc.le]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (c * (2 * Real.pi * b) ^ ((n : ℝ) / 2)) := by
        rw [lintegral_gaussianWeight_univ hb, ← ENNReal.ofReal_mul hc.le]

/-- **The `R`-free denominator.**  Using nothing but `ball 0 1 ⊆ K`,

    `∫_K e^{-‖x‖²/(2s)} dx ≥ e^{-1/(2s)}·vol(B(0,1))`.

No bound on `K` is used, so — as with the tail — no `R` occurs. -/
theorem le_lintegral_gaussianWeight_of_unitBall_subset {s : ℝ} (hs : 0 < s)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) :
    ENNReal.ofReal (Real.exp (-1 / (2 * s)))
        * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      ≤ ∫⁻ x in K, gaussianWeight s x := by
  have hpt : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      ENNReal.ofReal (Real.exp (-1 / (2 * s))) ≤ gaussianWeight s x := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := by
      rw [mem_ball_zero_iff] at hx
      exact hx.le
    have := exp_le_gaussianWeightReal hs hx1
    rw [one_pow] at this
    exact ENNReal.ofReal_le_ofReal this
  calc ENNReal.ofReal (Real.exp (-1 / (2 * s)))
        * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      = ∫⁻ _ in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          ENNReal.ofReal (Real.exp (-1 / (2 * s))) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1, gaussianWeight s x := by
        refine lintegral_mono_ae ?_
        filter_upwards [self_mem_ae_restrict measurableSet_ball] with x hx using hpt x hx
    _ ≤ ∫⁻ x in K, gaussianWeight s x := lintegral_mono_set hball

/-- **The truncation error, in the form the consumer needs**: the Gaussian mass discarded by
intersecting with `closedBall 0 r` is at most `C` times the Gaussian mass kept, whenever the
real number `C` dominates the explicit ratio

    `e^{-t·r²/(2s)}·(2π·s/(1-t))^{n/2} / (e^{-1/(2s)}·vol(B(0,1)))`.

**Neither the hypothesis `hCb` nor the conclusion mentions any circumscribed radius `R`**, and
the only thing assumed about `K` is `ball 0 1 ⊆ K`.  That is the whole point: the truncation
cost does not degrade as the body grows. -/
theorem lintegral_gaussianWeight_sdiff_le_mul {s r t C : ℝ}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hs : 0 < s) (hr : 0 ≤ r) (ht0 : 0 < t) (ht1 : t < 1)
    (hC : 0 ≤ C) (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    (hCb : Real.exp (-(t * r ^ 2) / (2 * s)) * (2 * Real.pi * (s / (1 - t))) ^ ((n : ℝ) / 2)
      ≤ C * (Real.exp (-1 / (2 * s))
          * (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)) :
    ∫⁻ x in K \ closedBall (0 : EuclideanSpace ℝ (Fin n)) r, gaussianWeight s x
      ≤ ENNReal.ofReal C * ∫⁻ x in K, gaussianWeight s x := by
  have hVtop : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hsub : K \ closedBall (0 : EuclideanSpace ℝ (Fin n)) r
      ⊆ {x : EuclideanSpace ℝ (Fin n) | r < ‖x‖} := by
    intro x hx
    have : x ∉ closedBall (0 : EuclideanSpace ℝ (Fin n)) r := hx.2
    rw [mem_closedBall_zero_iff, not_le] at this
    exact this
  calc ∫⁻ x in K \ closedBall (0 : EuclideanSpace ℝ (Fin n)) r, gaussianWeight s x
      ≤ ∫⁻ x in {x : EuclideanSpace ℝ (Fin n) | r < ‖x‖}, gaussianWeight s x :=
        lintegral_mono_set hsub
    _ ≤ ENNReal.ofReal (Real.exp (-(t * r ^ 2) / (2 * s))
          * (2 * Real.pi * (s / (1 - t))) ^ ((n : ℝ) / 2)) :=
        lintegral_gaussianWeight_norm_gt_le hs hr ht0 ht1
    _ ≤ ENNReal.ofReal (C * (Real.exp (-1 / (2 * s))
          * (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)) :=
        ENNReal.ofReal_le_ofReal hCb
    _ = ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (-1 / (2 * s)))
          * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.ofReal_toReal hVtop]
    _ ≤ ENNReal.ofReal C * ∫⁻ x in K, gaussianWeight s x :=
        mul_le_mul_right (le_lintegral_gaussianWeight_of_unitBall_subset hs hball) _

/-! ## 3.  The total-variation consequence

`Arlib.TVLe` composes by the triangle inequality (`Arlib.TVLe.trans`), so the bound proved
here adds to the sampler's own TV error rather than replacing it. -/

section CondOn

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Conditioning on a subset costs exactly the relative mass of what is discarded.**

For `A ⊆ B` with `μ A ≠ 0` and `μ B ≠ ⊤`,

    `TVLe (condOn μ A) (condOn μ B) (μ (B ∖ A) / μ B)`.

Both directions are elementary `ℝ≥0∞` arithmetic on `p = μ(S∩A)`, `q = μ(S∩B)`, `a = μ A`,
`b = μ B`, `d = μ(B∖A)`, using only `b = a + d` and `q = p + μ(S∩(B∖A)) ≤ p + d`. -/
theorem tvLe_condOn_subset {μ : Measure Ω} {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : A ⊆ B) (hA0 : μ A ≠ 0) (hBtop : μ B ≠ ⊤) :
    TVLe (condOn μ A) (condOn μ B) (μ (B \ A) / μ B) := by
  have hAB' : μ A ≤ μ B := measure_mono hAB
  have hAtop : μ A ≠ ⊤ := ne_top_of_le_ne_top hBtop hAB'
  have hB0 : μ B ≠ 0 := fun h => hA0 (by simpa [h] using hAB')
  have hadd : μ A + μ (B \ A) = μ B := by
    have := measure_inter_add_sdiff (μ := μ) B hA
    rwa [inter_eq_self_of_subset_right hAB] at this
  intro S hS
  have hqadd : μ (S ∩ A) + μ ((S ∩ B) \ A) = μ (S ∩ B) := by
    have := measure_inter_add_sdiff (μ := μ) (S ∩ B) hA
    rwa [show S ∩ B ∩ A = S ∩ A by
      ext x; simp only [mem_inter_iff]; exact ⟨fun h => ⟨h.1.1, h.2⟩,
        fun h => ⟨⟨h.1, hAB h.2⟩, h.2⟩⟩] at this
  have hle : μ ((S ∩ B) \ A) ≤ μ (B \ A) := measure_mono (fun x hx => ⟨hx.1.2, hx.2⟩)
  have hpa : μ (S ∩ A) ≤ μ A := measure_mono inter_subset_right
  have hpq : μ (S ∩ A) ≤ μ (S ∩ B) := by rw [← hqadd]; exact le_self_add
  rw [condOn_apply μ hA hS, condOn_apply μ hB hS]
  constructor
  · -- `p/a ≤ q/b + d/b = (q+d)/b`, from `p·b = p·(a+d) ≤ q·a + a·d = (q+d)·a`
    rw [← ENNReal.add_div]
    have key : μ (S ∩ A) * μ B ≤ (μ (S ∩ B) + μ (B \ A)) * μ A := by
      calc μ (S ∩ A) * μ B = μ (S ∩ A) * (μ A + μ (B \ A)) := by rw [hadd]
        _ = μ (S ∩ A) * μ A + μ (S ∩ A) * μ (B \ A) := by rw [mul_add]
        _ ≤ μ (S ∩ B) * μ A + μ A * μ (B \ A) := by gcongr
        _ = (μ (S ∩ B) + μ (B \ A)) * μ A := by rw [add_mul, mul_comm (μ A)]
    calc μ (S ∩ A) / μ A = μ (S ∩ A) * μ B / (μ A * μ B) :=
          (ENNReal.mul_div_mul_right _ _ hB0 hBtop).symm
      _ ≤ (μ (S ∩ B) + μ (B \ A)) * μ A / (μ A * μ B) := ENNReal.div_le_div_right key _
      _ = (μ (S ∩ B) + μ (B \ A)) * μ A / (μ B * μ A) := by rw [mul_comm (μ A) (μ B)]
      _ = (μ (S ∩ B) + μ (B \ A)) / μ B := ENNReal.mul_div_mul_right _ _ hA0 hAtop
  · -- `q/b ≤ (p+d)/b = p/b + d/b ≤ p/a + d/b`
    calc μ (S ∩ B) / μ B ≤ (μ (S ∩ A) + μ (B \ A)) / μ B := by
          refine ENNReal.div_le_div_right ?_ _
          rw [← hqadd]
          gcongr
      _ = μ (S ∩ A) / μ B + μ (B \ A) / μ B := ENNReal.add_div
      _ ≤ μ (S ∩ A) / μ A + μ (B \ A) / μ B := by gcongr

end CondOn

/-- **The truncation error as a total-variation bound on the phase law.**

    `TVLe (coolLaw m σsq (K ∩ closedBall 0 r) i) (coolLaw m σsq K i) (ofReal C)`

for every interior phase `i < m`, under exactly the hypothesis `hCb` of
`lintegral_gaussianWeight_sdiff_le_mul` — which, again, contains **no circumscribed radius**.

`Arlib.GaussianCooling.coolLaw` is the measure `Ttc/Volume/CVAmended.lean`'s sampler
hypothesis is stated against, and `Arlib.TVLe` composes by `Arlib.TVLe.trans`, so this bound
adds to the sampler's own TV error rather than replacing it. -/
theorem tvLe_coolLaw_inter_closedBall {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : ℕ} (hi : i < m) {r t C : ℝ} (hr1 : 1 ≤ r) (ht0 : 0 < t) (ht1 : t < 1) (hC : 0 ≤ C)
    (hCb : Real.exp (-(t * r ^ 2) / (2 * σsq i))
          * (2 * Real.pi * (σsq i / (1 - t))) ^ ((n : ℝ) / 2)
      ≤ C * (Real.exp (-1 / (2 * σsq i))
          * (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal)) :
    TVLe (coolLaw m σsq (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r) i)
      (coolLaw m σsq K i) (ENNReal.ofReal C) := by
  have hs : 0 < σsq i := hσ i
  have hr0 : (0 : ℝ) ≤ r := le_trans zero_le_one hr1
  set A : Set (EuclideanSpace ℝ (Fin n)) := K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) r
    with hAdef
  have hAm : MeasurableSet A := measurableSet_inter_closedBall hK r
  have hAball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ A :=
    unitBall_subset_inter_closedBall hball hr1
  have hAfin : volume A ≠ ⊤ := volume_inter_closedBall_ne_top K r
  set μ : Measure (EuclideanSpace ℝ (Fin n)) :=
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity (gaussianWeight (σsq i)) with hμdef
  have hmeas : Measurable (gaussianWeight (σsq i) : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) :=
    measurable_gaussianWeight _
  have hμapply : ∀ S : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet S →
      μ S = ∫⁻ x in S, gaussianWeight (σsq i) x := fun S hS => withDensity_apply _ hS
  have hA0 : μ A ≠ 0 := by
    rw [hμapply A hAm]
    intro h
    have hpos := le_lintegral_gaussianWeight_of_unitBall_subset (n := n) hs hAball
    rw [h, le_zero_iff, mul_eq_zero] at hpos
    rcases hpos with h1 | h2
    · exact (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' h1
    · exact (measure_ball_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) 0 one_pos).ne' h2
  have hBtop : μ K ≠ ⊤ := by
    rw [hμapply K hK]; exact lintegral_gaussianWeight_ne_top_of_univ hs K
  have hdiff : K \ A = K \ closedBall (0 : EuclideanSpace ℝ (Fin n)) r := by
    rw [hAdef, Set.sdiff_self_inter]
  have hratio : μ (K \ A) / μ K ≤ ENNReal.ofReal C := by
    have hB0 : μ K ≠ 0 := fun h =>
      hA0 (le_antisymm (h ▸ measure_mono inter_subset_left) (by simp))
    rw [ENNReal.div_le_iff hB0 hBtop, hμapply _ (hK.diff hAm), hμapply K hK, hdiff]
    exact lintegral_gaussianWeight_sdiff_le_mul hs hr0 ht0 ht1 hC hball hCb
  rw [coolLaw_eq_uniformOn_gaussianWeight hσ hAm hAball hAfin hi,
    coolLaw_eq_uniformOn_gaussianWeight hσ hK hball hfin hi]
  exact (tvLe_condOn_subset hAm hK inter_subset_left hA0 hBtop).mono hratio

/-! ## 4.  The payoff: `hRσ` discharged by construction

The two per-phase mixing theorems of `Arlib/MarkovChains/Continuous/ColdPhaseRegime.lean`,
instantiated at `K' = K ∩ closedBall 0 (2σ√n)`.  In both, the binder `hRσ : R ≤ 2σ√n` is
supplied by `le_rfl` at `R = 2σ√n`, and `hKR` by `norm_le_of_mem_inter_closedBall`.  **No
hypothesis relating `K` to any radius is carried.**

Scope, inherited verbatim from `ColdPhaseRegime.lean`: these are step counts for a Markov
chain, not running times, and nothing under `Ttc/` is touched. -/

/-- **The cold phases on the truncated body**, at `δ = min(σ/(8√n), 1/(2n))`, uniformly in
`σ`.  Compared with `Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_coldStep`
the binders `hR`, `hKR`, `hRσ` are gone: the body is `K ∩ closedBall 0 (2σ√n)` and they hold
by construction.  What replaces them is `hrad : 1 ≤ 2σ√n`, which at the Gaussian-cooling cold
start `σ² = 1/n` reads `1 ≤ 2`. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_coldStep_truncated (hn : 21 ≤ n) {σ : ℝ}
    (hσ : 0 < σ) (hrad : 1 ≤ 2 * σ * Real.sqrt n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (ellGaussianProb (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 6553600 * (σ ^ 2 * (n : ℝ) ^ 3 + 16 * (n : ℝ) ^ 2)
      * (Real.log M + 2 * Real.log (1 / eps)) / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin
      (lazy (speedyMetropolisGaussian
        (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
      (ellGaussianProb (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)) mu0 t
      (ENNReal.ofReal eps) :=
  mixesWithin_lazy_speedyMetropolisGaussian_coldStep hn hσ
    (measurableSet_inter_closedBall hK _) (convex_inter_closedBall hKc _)
    (volume_inter_closedBall_ne_zero hball hrad) (le_trans zero_le_one hrad)
    (fun _ hx => norm_le_of_mem_inter_closedBall hx) le_rfl hM hwarm heps0 heps1 ht

/-- **The sharp cold count on the truncated body**: dimension exponent `n²`, no `σ`, and no
radius hypothesis on `K` whatsoever.  This is the statement the residual `hRσ` gap was
blocking at `σ² = 1/n`, `R > 2`. -/
theorem mixesWithin_lazy_speedyMetropolisGaussian_cold_truncated (hn : 21 ≤ n) {σ : ℝ}
    (hσ : 0 < σ) (hcold : σ * Real.sqrt n ≤ 4) (hrad : 1 ≤ 2 * σ * Real.sqrt n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    {mu0 : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure mu0] {M eps : ℝ}
    (hM : 1 ≤ M)
    (hwarm : IsWarm (ENNReal.ofReal M) mu0
      (ellGaussianProb (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
    (heps0 : 0 < eps) (heps1 : eps ≤ 1)
    {t : ℕ} (ht : 104857600 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2 + 1 ≤ (t : ℝ)) :
    MixesWithin
      (lazy (speedyMetropolisGaussian
        (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
      (ellGaussianProb (K ∩ closedBall (0 : EuclideanSpace ℝ (Fin n)) (2 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)) mu0 t
      (ENNReal.ofReal eps) :=
  mixesWithin_lazy_speedyMetropolisGaussian_cold hn hσ hcold
    (measurableSet_inter_closedBall hK _) (convex_inter_closedBall hKc _)
    (volume_inter_closedBall_ne_zero hball hrad) (le_trans zero_le_one hrad)
    (fun _ hx => norm_le_of_mem_inter_closedBall hx) le_rfl hM hwarm heps0 heps1 ht

/-! ## 5.  Non-vacuity (`CLAUDE.md` §11)

Everything is discharged at `n = 21`, `σ = 1/√21` (so `σ² = 1/n`, the Gaussian-cooling cold
start), truncation radius `2σ√n = 2`, and `K = closedBall 0 10` — a body with `R = 10`, so
`hRσ : R ≤ 2σ√n` is **false** for it, and `ColdPhaseRegime.lean`'s theorems do not apply to
`K` at this variance.  They do apply to `K ∩ closedBall 0 2`, and the price is `≤ 1/1000`. -/

/-- **The truncation bound is a real number strictly below `1`**, at `n = 21`, `σ² = 1/n`,
`r = 2σ√n = 2`, `t = 1/2`.

This is `lintegral_gaussianWeight_sdiff_le_mul`'s hypothesis `hCb`, discharged outright with
`C = 1/1000`.  The bound is deliberately slack: the true value of the left/right ratio is
`e^{-21/2}·(4π/21)^{21/2}/vol(B(0,1)) ≈ 8.99·10⁻⁶`.  The slack comes from two crude but
elementary substitutions — `e^{1/2} ≥ 3/2` (whence `e^{-21/2} ≤ (2/3)²¹`) and
`(4π/21)^{1/2} ≤ 1` — after which `π¹⁰` cancels against
`vol(B(0,1)) = π¹⁰·2¹¹/21‼` and the comparison is rational.

**No radius `R` occurs in this statement.**  That is what makes the truncation affordable for
an arbitrarily large body. -/
theorem coldTruncation_bound_witness :
    Real.exp (-((1 / 2 : ℝ) * (2 : ℝ) ^ 2) / (2 * (1 / 21 : ℝ)))
        * (2 * Real.pi * ((1 / 21 : ℝ) / (1 - 1 / 2))) ^ (((21 : ℕ) : ℝ) / 2)
      ≤ (1 / 1000 : ℝ) * (Real.exp (-1 / (2 * (1 / 21 : ℝ)))
          * (volume (ball (0 : EuclideanSpace ℝ (Fin 21)) 1)).toReal) := by
  -- `vol(B(0,1)) = π¹⁰·2¹¹/21‼` in dimension `21 = 2·10+1`
  have hV : (volume (ball (0 : EuclideanSpace ℝ (Fin 21)) 1)).toReal
      = Real.pi ^ 10 * 2 ^ 11 / 13749310575 := by
    have hk : Module.finrank ℝ (EuclideanSpace ℝ (Fin 21)) = 2 * 10 + 1 := by
      rw [finrank_euclideanSpace_fin]
    rw [InnerProductSpace.volume_ball_of_dim_odd hk 0 1, hk, ENNReal.toReal_mul]
    norm_num [Nat.doubleFactorial]
    positivity
  -- `e^{-21/2} ≤ (2/3)²¹`, from `1 + 1/2 ≤ e^{1/2}`
  have hexp : Real.exp (-(21 / 2 : ℝ)) ≤ (2 / 3 : ℝ) ^ 21 := by
    have h : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
      have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
    have hpow : ((3 : ℝ) / 2) ^ 21 ≤ Real.exp (1 / 2) ^ 21 :=
      pow_le_pow_left₀ (by norm_num) h 21
    have he : Real.exp (1 / 2 : ℝ) ^ 21 = Real.exp (21 / 2) := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [he] at hpow
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have hinv : (((2 : ℝ) / 3) ^ (21 : ℕ))⁻¹ = ((3 : ℝ) / 2) ^ (21 : ℕ) := by
      rw [← inv_pow]; norm_num
    rw [hinv]; exact hpow
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  set x : ℝ := 4 * Real.pi / 21 with hxdef
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hx1 : x ≤ 1 := by rw [hxdef]; linarith
  have hbase : 2 * Real.pi * ((1 / 21 : ℝ) / (1 - 1 / 2)) = x := by rw [hxdef]; ring
  have hexpo : ((21 : ℕ) : ℝ) / 2 = (10 : ℕ) + (1 : ℝ) / 2 := by norm_num
  -- `x^{21/2} = x¹⁰·x^{1/2} ≤ x¹⁰`, since `0 < x ≤ 1`
  have hsplit : x ^ (((21 : ℕ) : ℝ) / 2) ≤ x ^ (10 : ℕ) := by
    rw [hexpo, Real.rpow_add hx0, Real.rpow_natCast]
    nlinarith [Real.rpow_le_one hx0.le hx1 (by norm_num : (0 : ℝ) ≤ 1 / 2),
      Real.rpow_nonneg hx0.le ((1 : ℝ) / 2), pow_pos hx0 10]
  have hL : Real.exp (-((1 / 2 : ℝ) * (2 : ℝ) ^ 2) / (2 * (1 / 21 : ℝ)))
      = Real.exp (-(21 / 2 : ℝ)) * Real.exp (-(21 / 2 : ℝ)) := by
    rw [← Real.exp_add]; norm_num
  have hR : Real.exp (-1 / (2 * (1 / 21 : ℝ))) = Real.exp (-(21 / 2 : ℝ)) := by norm_num
  rw [hbase, hL, hR, hV]
  have hE : (0 : ℝ) < Real.exp (-(21 / 2 : ℝ)) := Real.exp_pos _
  have hkey : Real.exp (-(21 / 2 : ℝ)) * x ^ (10 : ℕ)
      ≤ (1 / 1000 : ℝ) * (Real.pi ^ 10 * 2 ^ 11 / 13749310575) := by
    have h1 : Real.exp (-(21 / 2 : ℝ)) * x ^ (10 : ℕ) ≤ (2 / 3 : ℝ) ^ 21 * x ^ (10 : ℕ) :=
      mul_le_mul_of_nonneg_right hexp (by positivity)
    have hcoef : ((2 : ℝ) / 3) ^ 21 * (4 ^ 10 / 21 ^ 10)
        ≤ 1 / 1000 * ((2 : ℝ) ^ 11 / 13749310575) := by norm_num
    refine h1.trans ?_
    rw [hxdef]
    calc ((2 : ℝ) / 3) ^ 21 * (4 * Real.pi / 21) ^ (10 : ℕ)
        = (((2 : ℝ) / 3) ^ 21 * (4 ^ 10 / 21 ^ 10)) * Real.pi ^ 10 := by ring
      _ ≤ (1 / 1000 * ((2 : ℝ) ^ 11 / 13749310575)) * Real.pi ^ 10 :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = 1 / 1000 * (Real.pi ^ 10 * 2 ^ 11 / 13749310575) := by ring
  calc Real.exp (-(21 / 2 : ℝ)) * Real.exp (-(21 / 2 : ℝ)) * x ^ (((21 : ℕ) : ℝ) / 2)
      ≤ Real.exp (-(21 / 2 : ℝ)) * Real.exp (-(21 / 2 : ℝ)) * x ^ (10 : ℕ) :=
        mul_le_mul_of_nonneg_left hsplit (by positivity)
    _ = Real.exp (-(21 / 2 : ℝ)) * (Real.exp (-(21 / 2 : ℝ)) * x ^ (10 : ℕ)) := by ring
    _ ≤ Real.exp (-(21 / 2 : ℝ)) * ((1 / 1000 : ℝ)
          * (Real.pi ^ 10 * 2 ^ 11 / 13749310575)) := mul_le_mul_of_nonneg_left hkey hE.le
    _ = 1 / 1000 * (Real.exp (-(21 / 2 : ℝ))
          * (Real.pi ^ 10 * 2 ^ 11 / 13749310575)) := by ring

/-- **The full package, on a body the untruncated theorem cannot handle.**

`n = 21`, `σ = 1/√21` (so `σ² = 1/n`: the coldest phase of `ColdStart.lean`'s schedule),
`K = closedBall 0 10`, hence `R = 10` and `2σ√n = 2`, so

    `hRσ : R ≤ 2·σ·√n`   is FALSE

— that conjunct is asserted, and proved, below.  On the truncated body
`K' = K ∩ closedBall 0 2` every hypothesis of
`mixesWithin_lazy_speedyMetropolisGaussian_cold_truncated` holds and the chain mixes to within
`ε = 1/2` of its stationary law from the stationary start `M = 1`; and the phase law on `K'`
is within total variation `1/1000 < 1` of the phase law on `K`.

Nothing here is a placeholder: `ε = 1/2 < 1` and `C = 1/1000 < 1`, so both conclusions are
genuine bounds and not the trivial ones. -/
theorem coldTruncation_witness :
    ∃ (K K' : Set (EuclideanSpace ℝ (Fin 21))) (R σ C : ℝ) (σsq : ℕ → ℝ) (m i : ℕ)
      (mu0 : Measure (EuclideanSpace ℝ (Fin 21))) (t : ℕ),
      MeasurableSet K ∧ Convex ℝ K ∧ ball (0 : EuclideanSpace ℝ (Fin 21)) 1 ⊆ K ∧
        volume K ≠ 0 ∧ volume K ≠ ⊤ ∧ (∀ x ∈ K, ‖x‖ ≤ R) ∧ R = 10 ∧
      σ ^ 2 = 1 / ((21 : ℕ) : ℝ) ∧ σ * Real.sqrt ((21 : ℕ) : ℝ) = 1 ∧
        2 * σ * Real.sqrt ((21 : ℕ) : ℝ) = 2 ∧
      -- the isoperimetric binder of the untruncated per-phase theorem is FALSE here
      ¬ (R ≤ 2 * σ * Real.sqrt ((21 : ℕ) : ℝ)) ∧
      K' = K ∩ closedBall (0 : EuclideanSpace ℝ (Fin 21)) (2 * σ * Real.sqrt ((21 : ℕ) : ℝ)) ∧
        MeasurableSet K' ∧ Convex ℝ K' ∧ ball (0 : EuclideanSpace ℝ (Fin 21)) 1 ⊆ K' ∧
        volume K' ≠ 0 ∧ volume K' ≠ ⊤ ∧
        (∀ x ∈ K', ‖x‖ ≤ 2 * σ * Real.sqrt ((21 : ℕ) : ℝ)) ∧
      IsProbabilityMeasure mu0 ∧
      MixesWithin
        (lazy (speedyMetropolisGaussian K'
          (min (σ / (8 * Real.sqrt ((21 : ℕ) : ℝ))) (1 / (2 * ((21 : ℕ) : ℝ)))) (σ ^ 2)))
        (ellGaussianProb K'
          (min (σ / (8 * Real.sqrt ((21 : ℕ) : ℝ))) (1 / (2 * ((21 : ℕ) : ℝ)))) (σ ^ 2))
        mu0 t (ENNReal.ofReal (1 / 2)) ∧
      m = 2 ∧ i = 0 ∧ i < m ∧ σsq i = σ ^ 2 ∧ C = 1 / 1000 ∧ C < 1 ∧
      TVLe (coolLaw m σsq K' i) (coolLaw m σsq K i) (ENNReal.ofReal C) := by
  classical
  have hcast : ((21 : ℕ) : ℝ) = (21 : ℝ) := by norm_num
  have h21 : (0 : ℝ) < ((21 : ℕ) : ℝ) := by rw [hcast]; norm_num
  have hsq21 : Real.sqrt ((21 : ℕ) : ℝ) ^ 2 = ((21 : ℕ) : ℝ) := Real.sq_sqrt h21.le
  have hspos : (0 : ℝ) < Real.sqrt ((21 : ℕ) : ℝ) := Real.sqrt_pos.2 h21
  have hsne : Real.sqrt ((21 : ℕ) : ℝ) ≠ 0 := ne_of_gt hspos
  set σ : ℝ := 1 / Real.sqrt ((21 : ℕ) : ℝ) with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; positivity
  have hσmul : σ * Real.sqrt ((21 : ℕ) : ℝ) = 1 := by rw [hσdef, div_mul_cancel₀ _ hsne]
  have hσsq : σ ^ 2 = 1 / ((21 : ℕ) : ℝ) := by rw [hσdef, div_pow, hsq21, one_pow]
  have hr2 : 2 * σ * Real.sqrt ((21 : ℕ) : ℝ) = 2 := by
    rw [mul_assoc, hσmul, mul_one]
  have hrad : (1 : ℝ) ≤ 2 * σ * Real.sqrt ((21 : ℕ) : ℝ) := by rw [hr2]; norm_num
  have hcold : σ * Real.sqrt ((21 : ℕ) : ℝ) ≤ 4 := by rw [hσmul]; norm_num
  -- the body
  set K : Set (EuclideanSpace ℝ (Fin 21)) := closedBall 0 10 with hKdef
  have hKm : MeasurableSet K := measurableSet_closedBall
  have hKc : Convex ℝ K := convex_closedBall _ _
  have hball : ball (0 : EuclideanSpace ℝ (Fin 21)) 1 ⊆ K :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  have hKtop : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  have hK0 : volume K ≠ 0 :=
    (measure_closedBall_pos (volume : Measure (EuclideanSpace ℝ (Fin 21))) 0
      (by norm_num : (0 : ℝ) < 10)).ne'
  have hKR : ∀ x ∈ K, ‖x‖ ≤ (10 : ℝ) := by
    intro x hx
    rw [hKdef, mem_closedBall_zero_iff] at hx
    exact hx
  -- the truncated body
  set K' : Set (EuclideanSpace ℝ (Fin 21)) :=
    K ∩ closedBall (0 : EuclideanSpace ℝ (Fin 21)) (2 * σ * Real.sqrt ((21 : ℕ) : ℝ))
    with hK'def
  have hK'm : MeasurableSet K' := measurableSet_inter_closedBall hKm _
  have hK'c : Convex ℝ K' := convex_inter_closedBall hKc _
  have hK'ball : ball (0 : EuclideanSpace ℝ (Fin 21)) 1 ⊆ K' :=
    unitBall_subset_inter_closedBall hball hrad
  have hK'0 : volume K' ≠ 0 := volume_inter_closedBall_ne_zero hball hrad
  have hK'top : volume K' ≠ ⊤ := volume_inter_closedBall_ne_top K _
  have hK'R : ∀ x ∈ K', ‖x‖ ≤ 2 * σ * Real.sqrt ((21 : ℕ) : ℝ) :=
    fun _ hx => norm_le_of_mem_inter_closedBall hx
  have hK'b : Bornology.IsBounded K' :=
    Metric.isBounded_closedBall.subset inter_subset_right
  -- the step size and the stationary start
  set δ : ℝ := min (σ / (8 * Real.sqrt ((21 : ℕ) : ℝ))) (1 / (2 * ((21 : ℕ) : ℝ))) with hδdef
  have hδpos : 0 < δ := coldStep_pos (by norm_num) hσpos
  have hσ2pos : (0 : ℝ) < σ ^ 2 := by positivity
  haveI hprob : IsProbabilityMeasure (ellGaussianProb K' δ (σ ^ 2)) :=
    isProbabilityMeasure_ellGaussianProb
      (ellGaussianMeasure_univ_ne_zero hK'm hK'c hK'b hK'0 hδpos (σ ^ 2))
      (ne_top_of_le_ne_top hK'top (ellGaussianMeasure_univ_le hσ2pos K' _))
  have hwarm : IsWarm (ENNReal.ofReal (1 : ℝ)) (ellGaussianProb K' δ (σ ^ 2))
      (ellGaussianProb K' δ (σ ^ 2)) := by
    intro S _
    exact le_of_eq (by rw [ENNReal.ofReal_one, one_mul])
  -- the deadline
  set t : ℕ := ⌈104857600 * (((21 : ℕ) : ℝ)) ^ 2
      * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / Real.log 2 ^ 2 + 1⌉₊ with htdef
  have hts : 104857600 * (((21 : ℕ) : ℝ)) ^ 2
      * (Real.log 1 + 2 * Real.log (1 / (1 / 2 : ℝ))) / Real.log 2 ^ 2 + 1 ≤ (t : ℝ) := by
    rw [htdef]; exact Nat.le_ceil _
  have hmix := mixesWithin_lazy_speedyMetropolisGaussian_cold_truncated (n := 21)
    (σ := σ) (M := 1) (eps := 1 / 2) (mu0 := ellGaussianProb K' δ (σ ^ 2)) (t := t)
    le_rfl hσpos hcold hrad hKm hKc hball le_rfl hwarm (by norm_num) (by norm_num) hts
  -- the truncation error
  set σsq : ℕ → ℝ := fun _ => (1 : ℝ) / 21 with hσsqdef
  have hσsqpos : ∀ j, 0 < σsq j := fun _ => by rw [hσsqdef]; norm_num
  have hCb : Real.exp (-((1 / 2 : ℝ) * (2 * σ * Real.sqrt ((21 : ℕ) : ℝ)) ^ 2)
        / (2 * σsq 0)) * (2 * Real.pi * (σsq 0 / (1 - 1 / 2))) ^ (((21 : ℕ) : ℝ) / 2)
      ≤ (1 / 1000 : ℝ) * (Real.exp (-1 / (2 * σsq 0))
          * (volume (ball (0 : EuclideanSpace ℝ (Fin 21)) 1)).toReal) := by
    rw [hr2]
    exact coldTruncation_bound_witness
  have htv := tvLe_coolLaw_inter_closedBall (n := 21) (m := 2) (σsq := σsq) (i := 0)
    (r := 2 * σ * Real.sqrt ((21 : ℕ) : ℝ)) (t := 1 / 2) (C := 1 / 1000)
    hσsqpos hKm hball hKtop (by norm_num) hrad (by norm_num) (by norm_num) (by norm_num) hCb
  refine ⟨K, K', 10, σ, 1 / 1000, σsq, 2, 0, ellGaussianProb K' δ (σ ^ 2), t,
    hKm, hKc, hball, hK0, hKtop, hKR, rfl,
    hσsq, hσmul, hr2, ?_, rfl, hK'm, hK'c, hK'ball, hK'0, hK'top, hK'R,
    hprob, hmix, rfl, rfl, (by norm_num), ?_, rfl, (by norm_num), htv⟩
  · rw [hr2]; norm_num
  · rw [hσsqdef, hσsq]; norm_num

/-! ### Axiom audit (`CLAUDE.md` §4)

Every theorem of this file, re-checked at elaboration time.  Each must print exactly
`[propext, Classical.choice, Quot.sound]`; anything else — in particular `sorryAx` — means the
file is not finished. -/

section AxiomCheck

#print axioms convex_inter_closedBall
#print axioms measurableSet_inter_closedBall
#print axioms unitBall_subset_inter_closedBall
#print axioms norm_le_of_mem_inter_closedBall
#print axioms volume_inter_closedBall_ne_zero
#print axioms volume_inter_closedBall_ne_top
#print axioms lintegral_gaussianWeight_univ
#print axioms lintegral_gaussianWeight_ne_top_of_univ
#print axioms lintegral_gaussianWeight_norm_gt_le
#print axioms le_lintegral_gaussianWeight_of_unitBall_subset
#print axioms lintegral_gaussianWeight_sdiff_le_mul
#print axioms tvLe_condOn_subset
#print axioms tvLe_coolLaw_inter_closedBall
#print axioms mixesWithin_lazy_speedyMetropolisGaussian_coldStep_truncated
#print axioms mixesWithin_lazy_speedyMetropolisGaussian_cold_truncated
#print axioms coldTruncation_bound_witness
#print axioms coldTruncation_witness

end AxiomCheck

end Arlib.MarkovChains
