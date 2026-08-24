/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.GaussianCooling.PhaseSamplerTV
import Arlib.MarkovChains.Continuous.ColdTruncation

/-!
# The per-phase sampler guarantee with **no radius bound on `K`**

## The circularity this file removes

`Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_of_mixing`
(`Arlib/Convexity/GaussianCooling/PhaseSamplerTV.lean:198`) carries

    `hRσ : R ≤ 2·σ·√n`   where `∀ x ∈ K, ‖x‖ ≤ R`,

and `Ttc/Volume/CVSampler.lean`'s `hTV_cvLaw` therefore carries it at **every** phase `j`.
Since `σsq` increases along a Gaussian-cooling schedule the binder is tightest at `j = 0`, and
a non-circular cooling must start cold, `σ₀² ≲ 1/n` (`Arlib/Convexity/GaussianCooling/
ColdStart.lean`; a warmer start makes the first phase ratio `chain 0 ≈ vol K`, which is the
unknown the algorithm exists to compute).  At `σ₀² = 1/n` the binder reads

    `R ≤ 2`,

i.e. `K ⊆ 2·Bₙ` — a sandwiching ratio of at most `2`, not the general problem.

## What replaces it

`hRσ` is **isoperimetric compatibility**, not a step-size condition, so it cannot be repaired
by shrinking `δ`.  It is repaired instead by running the walk on the truncated body

    `K' := K ∩ closedBall 0 (2·σ·√n)`,

for which it holds by construction, and paying the discarded Gaussian mass in total variation.
Both halves were already proved and simply never chained:

| step | supplier |
| --- | --- |
| mixing on `K'`, **no radius binder on `K`**, at a `σ`-free step count | `Arlib.MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_cold_truncated` |
| the Cousins–Vempala rejection routine, on `K'` | `Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw` |
| transport `coolLaw … K' i ↝ coolLaw … K i` | `Arlib.MarkovChains.tvLe_coolLaw_inter_closedBall` |

glued by `Arlib.TVLe.trans`.

## Main result

`tvLe_speedyRejection_coolLaw_truncated_of_mixing` (§1).  Compared with
`tvLe_speedyRejection_coolLaw_of_mixing` the differences are exactly these:

* **gone**: `hR : 0 ≤ R`, `hKR : ∀ x ∈ K, ‖x‖ ≤ R`, `hRσ : R ≤ 2σ√n`.  **No radius, bounding
  or otherwise, occurs anywhere in the statement.**  The only hypotheses on `K` are
  `MeasurableSet K`, `Convex ℝ K`, `ball 0 1 ⊆ K`, `volume K ≠ ⊤` — the four the
  Cousins–Vempala interface already carries;
* **gone**: the two step-size binders `hδσ`, `hδn`, and `δ` itself.  The step size is fixed to
  `min (σ/(8√n)) (1/(2n))`, which meets *both* regimes (`Arlib.MarkovChains.coldStep_valid`);
* **new**: `hcold : σ·√n ≤ 4` and `hrad : 1 ≤ 2σ√n`, the cold-regime window of
  `ColdTruncation.lean`.  Neither mentions `K`;
* **new**: the truncation-cost binders `θ ∈ (0,1)`, `0 ≤ C`, and `hCb` (§2 below);
* **changed**: the walk runs on `K ∩ closedBall 0 (2σ√n)`, not on `K`.  This is a genuine
  change to the algorithm, not a proof device, and is visible in the conclusion;
* **changed**: the error is `64·eps + C` instead of `64·eps`.  The `+ C` is the truncation
  price;
* **changed**: the step count is `104857600·n²·(log M + 2log(1/eps))/log 2 ² + 1`, which is
  `σ`- and `δ`-free.

## 2.  `hCb`, the one hypothesis carried unproved — and why

`hCb` is `Arlib.MarkovChains.lintegral_gaussianWeight_sdiff_le_mul`'s hypothesis verbatim:

    `e^{-θ·r²/(2s)}·(2π·s/(1−θ))^{n/2} ≤ C·(e^{-1/(2s)}·vol(B(0,1)))`,  `r = 2σ√n`, `s = σsq i`.

**It contains no radius of `K`**, so carrying it does not smuggle `hRσ` back in; it is a
numeric statement about `n`, `σ` and `C` alone.  It is *not* discharged here, and the reason is
sharp rather than incidental.  Writing `σ² = a/n` and using `Γ(n/2+1) ≈ (n/2e)^{n/2}√(πn)`, the
left/right ratio at the optimal split `θ = 3/4` is

    `√(πn) · exp( n·[ −1.3069… + 1/(2a) + (1/2)·log a ] )`,

whose bracket is negative for `a ≲ 12` and **positive at `a = 16`**.  So across the *whole*
cold window `hcold : σ√n ≤ 4` (i.e. `a ≤ 16`) no `C < 1` exists for large `n`: the bound is
genuinely lost at the warm end of the window.  It decays only for `σ²·n ≲ 12`, and proving that
for general `n` needs a Stirling upper bound on `Γ(n/2+1)`, which `ColdTruncation.lean`'s own
header declares out of scope.  Accordingly `hCb` is a binder, and §3 discharges it at the
witness point together with everything else.

## 3.  Non-vacuity, which is the whole point (`CLAUDE.md` §11)

`tvLe_speedyRejection_coolLaw_truncated_of_mixing_witness` (§3) discharges **every** binder
simultaneously at

    n = 21,  K = closedBall 0 10 ⊆ ℝ²¹,  σ = 1/√21  (so σ² = 1/n, the cold start),
    m = 2,  i = 0,  σsq ≡ 1/21,  M = 1,  eps = 1/128,  θ = 1/2,  C = 1/1000,

and asserts, as conjuncts,

* `R = 10` with `∀ x ∈ K, ‖x‖ ≤ R` — so **`R > 2`**, and
* `¬ (R ≤ 2·σ·√21)` — the binder of the untruncated theorem is **FALSE** for this body, so
  `tvLe_speedyRejection_coolLaw_of_mixing` does not apply to it at this variance, and
* the total error `64·(1/128) + 1/1000 = 501/1000 < 1` — a genuine bound, not the vacuous one.

A witness with `R ≤ 2` would prove nothing here; this one has `R = 10`.

## 4.  Scope

Unchanged from the suppliers: a step count is not a running time; the warm start `hwarm` is
carried, not proved (it is the residual gap `PhaseSamplerTV.lean` §4 names, now stated against
the truncated body `K'`); and cross-phase composition — the truncation radius `2σ√n` moves with
the phase, so successive cold phases run on different truncated bodies — is not addressed here.
Nothing under `Ttc/` is touched.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1.  The per-phase guarantee, with no radius bound on `K` -/

/-- **`hTV` for one cold phase, with `hRσ : R ≤ 2σ√n` removed.**

Run the lazy speedy Metropolis–Gaussian walk at variance `σsq i = σ²` and step
`δ = min (σ/(8√n)) (1/(2n))` on the **truncated body** `K ∩ closedBall 0 (2σ√n)`, from an
`M`-warm start `mu0`, for `t` steps; then post-process by the Cousins–Vempala rejection routine
at `c = 1 − 1/(2n)`.  The resulting law is within total variation

    `64·eps + C`

of the phase law `coolLaw m σsq K i` — the law **on `K` itself**, not on the truncated body.

The hypotheses on `K` are exactly `MeasurableSet K`, `Convex ℝ K`, `ball 0 1 ⊆ K`,
`volume K ≠ ⊤`.  **No circumscribed radius appears in the statement at all**, which is the
point: `Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_of_mixing` forces `R ≤ 2` at the
cold start `σ² = 1/n`, and this theorem does not.

What is paid for that: the walk runs on the truncated body (a real change to the algorithm,
visible in the conclusion), the error gains `+ C`, and `hCb` — a numeric hypothesis mentioning
`n`, `σ`, `θ` and `C` but **not `K`** — is carried.  See the module docstring §2 for why `hCb`
is not discharged in the full cold window, and §3 for its discharge at the witness point. -/
theorem tvLe_speedyRejection_coolLaw_truncated_of_mixing (hn : 21 ≤ n) {m : ℕ} {σsq : ℕ → ℝ}
    (hσ : ∀ j, 0 < σsq j) {σ : ℝ} (hσpos : 0 < σ) (hcold : σ * Real.sqrt n ≤ 4)
    (hrad : 1 ≤ 2 * σ * Real.sqrt n)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : ℕ} (hi : i < m) (hσsq : σsq i = σ ^ 2)
    {mu0 : Measure (EuclSpace n)} [IsProbabilityMeasure mu0] {M eps : ℝ} (hM : 1 ≤ M)
    (hwarm : Arlib.IsWarm (ENNReal.ofReal M) mu0
      (MarkovChains.ellGaussianProb (K ∩ closedBall (0 : EuclSpace n) (2 * σ * Real.sqrt n))
        (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σ ^ 2)))
    (heps0 : 0 < eps) (heps32 : eps ≤ 1 / 32)
    {t : ℕ} (ht : 104857600 * (n : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
      / Real.log 2 ^ 2 + 1 ≤ (t : ℝ))
    {θ C : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hC : 0 ≤ C)
    (hCb : Real.exp (-(θ * (2 * σ * Real.sqrt n) ^ 2) / (2 * σsq i))
          * (2 * Real.pi * (σsq i / (1 - θ))) ^ ((n : ℝ) / 2)
        ≤ C * (Real.exp (-1 / (2 * σsq i))
            * (volume (ball (0 : EuclSpace n) 1)).toReal)) :
    Arlib.TVLe
      (Arlib.condOn
        ((Measure.map (fun x : EuclSpace n => (1 - 1 / (2 * (n : ℝ)))⁻¹ • x)
            (Arlib.condOn
              (MarkovChains.iterate
                (MarkovChains.lazy (MarkovChains.speedyMetropolisGaussian
                  (K ∩ closedBall (0 : EuclSpace n) (2 * σ * Real.sqrt n))
                  (min (σ / (8 * Real.sqrt n)) (1 / (2 * (n : ℝ)))) (σsq i))) mu0 t)
              ((1 - 1 / (2 * (n : ℝ))) •
                (K ∩ closedBall (0 : EuclSpace n) (2 * σ * Real.sqrt n))))).withDensity
          fun v => ENNReal.ofReal
            (MarkovChains.speedyAcceptReal (1 - 1 / (2 * (n : ℝ))) (σsq i) v))
        Set.univ)
      (coolLaw m σsq K i) (64 * ENNReal.ofReal eps + ENNReal.ofReal C) := by
  have hn1 : 1 ≤ n := by omega
  have hrad0 : (0 : ℝ) ≤ 2 * σ * Real.sqrt n := le_trans zero_le_one hrad
  -- mixing on the truncated body: no radius binder on `K`
  have hmix := MarkovChains.mixesWithin_lazy_speedyMetropolisGaussian_cold_truncated hn hσpos
    hcold hrad hKm hKc hball hM hwarm heps0 (le_trans heps32 (by norm_num)) ht
  rw [Arlib.MarkovChains.mixesWithin_iff] at hmix
  rw [← hσsq] at hmix
  -- the rejection routine, on the truncated body
  have h₁ := tvLe_speedyRejection_coolLaw (n := n) hn1 (m := m) hσ
    (MarkovChains.measurableSet_inter_closedBall hKm _)
    (MarkovChains.convex_inter_closedBall hKc _)
    (MarkovChains.unitBall_subset_inter_closedBall hball hrad)
    (MarkovChains.volume_inter_closedBall_ne_top K _)
    (MarkovChains.coldStep_pos hn1 hσpos) MarkovChains.coldStep_le_kls hi hmix
    (ENNReal.ofReal_le_ofReal heps32)
  -- the truncation price, transporting the target back to `K`
  have h₂ := MarkovChains.tvLe_coolLaw_inter_closedBall (n := n) (m := m) (σsq := σsq) (i := i)
    (r := 2 * σ * Real.sqrt n) (t := θ) (C := C) hσ hKm hball hfin hi hrad hθ0 hθ1 hC hCb
  exact h₁.trans h₂

/-! ## 2.  Non-vacuity at a body with `R = 10 > 2` (`CLAUDE.md` §11)

The untruncated theorem's binder `hRσ : R ≤ 2σ√n` reads `R ≤ 2` at the cold start `σ² = 1/n`,
so `K = closedBall 0 10 ⊆ ℝ²¹` is outside its reach; it is *inside* the reach of §1, and the
witness below asserts both facts. -/

/-- **Every binder of §1 discharged at once, on a body with `R = 10`.**

`n = 21`, `σ = 1/√21` (so `σ² = 1/n = 1/21`, the coldest phase of `ColdStart.lean`'s
schedule, and `2σ√n = 2`), `K = closedBall 0 10`, `m = 2`, `i = 0`, `σsq ≡ 1/21`, `M = 1` from
the stationary start on the truncated body, `eps = 1/128`, `θ = 1/2`, `C = 1/1000`.

Three conjuncts make the point:

* `∀ x ∈ K, ‖x‖ ≤ R` with `R = 10`, so the body has sandwiching ratio `10`, not `≤ 2`;
* `¬ (R ≤ 2·σ·√21)` — the untruncated per-phase theorem's isoperimetric binder is **false**
  here, so it genuinely does not apply to this body at this variance;
* `64·ofReal (1/128) + ofReal (1/1000) = ofReal (501/1000)` and `ofReal (501/1000) < 1`, so the
  `TVLe` conclusion is a real bound and not the trivial one that every pair of probability
  measures satisfies.

`eps = 1/128` rather than the largest legal `1/32`: at `1/32` the rejection constant gives
`64/32 = 2 ≥ 1` and the conclusion would be vacuous. -/
theorem tvLe_speedyRejection_coolLaw_truncated_of_mixing_witness :
    ∃ (nn m : ℕ) (K : Set (EuclSpace nn)) (σsq : ℕ → ℝ) (σ R : ℝ) (i : ℕ)
      (mu0 : Measure (EuclSpace nn)) (M eps θ C : ℝ) (t : ℕ),
      nn = 21 ∧ 21 ≤ nn ∧ (∀ j, 0 < σsq j) ∧ 0 < σ ∧
      σ * Real.sqrt nn ≤ 4 ∧ 1 ≤ 2 * σ * Real.sqrt nn ∧
      MeasurableSet K ∧ Convex ℝ K ∧ ball (0 : EuclSpace nn) 1 ⊆ K ∧ volume K ≠ ⊤ ∧
      -- the body is big: `R = 10 > 2`, and the untruncated theorem's binder is FALSE for it
      (∀ x ∈ K, ‖x‖ ≤ R) ∧ R = 10 ∧ 2 < R ∧ ¬ (R ≤ 2 * σ * Real.sqrt nn) ∧
      i < m ∧ σsq i = σ ^ 2 ∧
      IsProbabilityMeasure mu0 ∧ 1 ≤ M ∧
      Arlib.IsWarm (ENNReal.ofReal M) mu0
        (MarkovChains.ellGaussianProb
          (K ∩ closedBall (0 : EuclSpace nn) (2 * σ * Real.sqrt nn))
          (min (σ / (8 * Real.sqrt nn)) (1 / (2 * (nn : ℝ)))) (σ ^ 2)) ∧
      0 < eps ∧ eps ≤ 1 / 32 ∧
      104857600 * (nn : ℝ) ^ 2 * (Real.log M + 2 * Real.log (1 / eps))
        / Real.log 2 ^ 2 + 1 ≤ (t : ℝ) ∧
      0 < θ ∧ θ < 1 ∧ 0 ≤ C ∧
      Real.exp (-(θ * (2 * σ * Real.sqrt nn) ^ 2) / (2 * σsq i))
          * (2 * Real.pi * (σsq i / (1 - θ))) ^ ((nn : ℝ) / 2)
        ≤ C * (Real.exp (-1 / (2 * σsq i))
            * (volume (ball (0 : EuclSpace nn) 1)).toReal) ∧
      -- the conclusion is a genuine bound
      (64 : ℝ≥0∞) * ENNReal.ofReal eps + ENNReal.ofReal C = ENNReal.ofReal (501 / 1000) ∧
      ENNReal.ofReal (501 / 1000) < 1 ∧
      Arlib.TVLe
        (Arlib.condOn
          ((Measure.map (fun x : EuclSpace nn => (1 - 1 / (2 * (nn : ℝ)))⁻¹ • x)
              (Arlib.condOn
                (MarkovChains.iterate
                  (MarkovChains.lazy (MarkovChains.speedyMetropolisGaussian
                    (K ∩ closedBall (0 : EuclSpace nn) (2 * σ * Real.sqrt nn))
                    (min (σ / (8 * Real.sqrt nn)) (1 / (2 * (nn : ℝ)))) (σsq i))) mu0 t)
                ((1 - 1 / (2 * (nn : ℝ))) •
                  (K ∩ closedBall (0 : EuclSpace nn) (2 * σ * Real.sqrt nn))))).withDensity
            fun v => ENNReal.ofReal
              (MarkovChains.speedyAcceptReal (1 - 1 / (2 * (nn : ℝ))) (σsq i) v))
          Set.univ)
        (coolLaw m σsq K i) (64 * ENNReal.ofReal eps + ENNReal.ofReal C) := by
  classical
  have hcast : ((21 : ℕ) : ℝ) = (21 : ℝ) := by norm_num
  have h21 : (0 : ℝ) < ((21 : ℕ) : ℝ) := by rw [hcast]; norm_num
  have hsq21 : Real.sqrt ((21 : ℕ) : ℝ) ^ 2 = ((21 : ℕ) : ℝ) := Real.sq_sqrt h21.le
  have hspos : (0 : ℝ) < Real.sqrt ((21 : ℕ) : ℝ) := Real.sqrt_pos.2 h21
  have hsne : Real.sqrt ((21 : ℕ) : ℝ) ≠ 0 := ne_of_gt hspos
  set σ : ℝ := 1 / Real.sqrt ((21 : ℕ) : ℝ) with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; positivity
  have hσmul : σ * Real.sqrt ((21 : ℕ) : ℝ) = 1 := by rw [hσdef, div_mul_cancel₀ _ hsne]
  have hσsq : σ ^ 2 = (1 : ℝ) / 21 := by
    rw [hσdef, div_pow, hsq21, one_pow, hcast]
  have hr2 : 2 * σ * Real.sqrt ((21 : ℕ) : ℝ) = 2 := by rw [mul_assoc, hσmul, mul_one]
  have hrad : (1 : ℝ) ≤ 2 * σ * Real.sqrt ((21 : ℕ) : ℝ) := by rw [hr2]; norm_num
  have hcold : σ * Real.sqrt ((21 : ℕ) : ℝ) ≤ 4 := by rw [hσmul]; norm_num
  -- the body: `R = 10`
  set K : Set (EuclSpace 21) := closedBall 0 10 with hKdef
  have hKm : MeasurableSet K := measurableSet_closedBall
  have hKc : Convex ℝ K := convex_closedBall _ _
  have hball : ball (0 : EuclSpace 21) 1 ⊆ K :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  have hfin : volume K ≠ ⊤ := measure_closedBall_lt_top.ne
  have hK0 : volume K ≠ 0 :=
    (measure_closedBall_pos (volume : Measure (EuclSpace 21)) 0 (by norm_num : (0 : ℝ) < 10)).ne'
  have hKR : ∀ x ∈ K, ‖x‖ ≤ (10 : ℝ) := by
    intro x hx
    rw [hKdef, mem_closedBall_zero_iff] at hx
    exact hx
  -- the truncated body
  set K' : Set (EuclSpace 21) :=
    K ∩ closedBall (0 : EuclSpace 21) (2 * σ * Real.sqrt ((21 : ℕ) : ℝ)) with hK'def
  have hK'm : MeasurableSet K' := MarkovChains.measurableSet_inter_closedBall hKm _
  have hK'c : Convex ℝ K' := MarkovChains.convex_inter_closedBall hKc _
  have hK'ball : ball (0 : EuclSpace 21) 1 ⊆ K' :=
    MarkovChains.unitBall_subset_inter_closedBall hball hrad
  have hK'0 : volume K' ≠ 0 := MarkovChains.volume_inter_closedBall_ne_zero hball hrad
  have hK'top : volume K' ≠ ⊤ := MarkovChains.volume_inter_closedBall_ne_top K _
  have hK'b : Bornology.IsBounded K' :=
    Metric.isBounded_closedBall.subset inter_subset_right
  -- the step size and the stationary start on `K'`
  set δ : ℝ := min (σ / (8 * Real.sqrt ((21 : ℕ) : ℝ))) (1 / (2 * ((21 : ℕ) : ℝ))) with hδdef
  have hδpos : 0 < δ := MarkovChains.coldStep_pos (by norm_num) hσpos
  have hσ2pos : (0 : ℝ) < σ ^ 2 := by positivity
  haveI hprob : IsProbabilityMeasure (MarkovChains.ellGaussianProb K' δ (σ ^ 2)) :=
    MarkovChains.isProbabilityMeasure_ellGaussianProb
      (MarkovChains.ellGaussianMeasure_univ_ne_zero hK'm hK'c hK'b hK'0 hδpos (σ ^ 2))
      (ne_top_of_le_ne_top hK'top (MarkovChains.ellGaussianMeasure_univ_le hσ2pos K' _))
  have hwarm : Arlib.IsWarm (ENNReal.ofReal (1 : ℝ))
      (MarkovChains.ellGaussianProb K' δ (σ ^ 2))
      (MarkovChains.ellGaussianProb K' δ (σ ^ 2)) := by
    intro S _
    exact le_of_eq (by rw [ENNReal.ofReal_one, one_mul])
  -- the deadline
  set t : ℕ := ⌈104857600 * (((21 : ℕ) : ℝ)) ^ 2
      * (Real.log 1 + 2 * Real.log (1 / (1 / 128 : ℝ))) / Real.log 2 ^ 2 + 1⌉₊ with htdef
  have hts : 104857600 * (((21 : ℕ) : ℝ)) ^ 2
      * (Real.log 1 + 2 * Real.log (1 / (1 / 128 : ℝ))) / Real.log 2 ^ 2 + 1 ≤ (t : ℝ) := by
    rw [htdef]; exact Nat.le_ceil _
  -- the variance schedule and the truncation cost
  set σsq : ℕ → ℝ := fun _ => (1 : ℝ) / 21 with hσsqdef
  have hσsqpos : ∀ j, 0 < σsq j := fun _ => by rw [hσsqdef]; norm_num
  have hσsq0 : σsq 0 = σ ^ 2 := by rw [hσsqdef, hσsq]
  have hCb : Real.exp (-((1 / 2 : ℝ) * (2 * σ * Real.sqrt ((21 : ℕ) : ℝ)) ^ 2) / (2 * σsq 0))
        * (2 * Real.pi * (σsq 0 / (1 - 1 / 2))) ^ ((((21 : ℕ) : ℝ)) / 2)
      ≤ (1 / 1000 : ℝ) * (Real.exp (-1 / (2 * σsq 0))
          * (volume (ball (0 : EuclSpace 21) 1)).toReal) := by
    rw [hr2, hσsqdef]
    exact Arlib.MarkovChains.coldTruncation_bound_witness
  -- the main theorem at these data
  have hmain := tvLe_speedyRejection_coolLaw_truncated_of_mixing (n := 21) (m := 2)
    (σsq := σsq) (σ := σ) (i := 0) (mu0 := MarkovChains.ellGaussianProb K' δ (σ ^ 2))
    (M := 1) (eps := 1 / 128) (t := t) (θ := 1 / 2) (C := 1 / 1000)
    le_rfl hσsqpos hσpos hcold hrad hKm hKc hball hfin (by norm_num) hσsq0 le_rfl hwarm
    (by norm_num) (by norm_num) hts (by norm_num) (by norm_num) (by norm_num) hCb
  -- the total error
  have herr : (64 : ℝ≥0∞) * ENNReal.ofReal (1 / 128 : ℝ) + ENNReal.ofReal (1 / 1000 : ℝ)
      = ENNReal.ofReal (501 / 1000 : ℝ) := by
    rw [show (64 : ℝ≥0∞) = ENNReal.ofReal 64 by simp,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  refine ⟨21, 2, K, σsq, σ, 10, 0, MarkovChains.ellGaussianProb K' δ (σ ^ 2), 1, 1 / 128,
    1 / 2, 1 / 1000, t, rfl, le_rfl, hσsqpos, hσpos, hcold, hrad, hKm, hKc, hball, hfin,
    hKR, rfl, by norm_num, ?_, by norm_num, hσsq0, hprob, le_rfl, hwarm, by norm_num,
    by norm_num, hts, by norm_num, by norm_num, by norm_num, hCb, herr, ?_, hmain⟩
  · rw [hr2]; norm_num
  · rw [ENNReal.ofReal_lt_one]; norm_num

/-! ## 3.  Axiom check (`CLAUDE.md` §4) -/

section AxiomCheck

#print axioms Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_truncated_of_mixing
#print axioms Arlib.GaussianCooling.tvLe_speedyRejection_coolLaw_truncated_of_mixing_witness

end AxiomCheck

end Arlib.GaussianCooling
