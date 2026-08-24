/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.EllLogConcave
import Arlib.MarkovChains.Continuous.EllFloor

/-!
# `δ√n` smoothness: the average local-conductance deficit is `O(δ√n)`, not `O(δn)`

`Arlib.MarkovChains.isSmooth_of_ball_subset` (`EllFloor.lean:549`) certifies
`IsSmooth K δ (1 − (1−δ)ⁿ)` for every convex `K ⊇ B(0,1)`, i.e. a deficit `≈ nδ`.  Lee's book
(`ball_walk.tex:674-678`, `lem:avg-local-conductance`) claims `vol{ℓ ≥ 3/4} ≥ (1 − 2δ√n)vol K`
— a deficit `≈ δ√n`.  Since the step count of the speedy route goes as `δ⁻²`, that single
`√n` is a factor `n` in the final bound.

**This file proves the `δ√n` bound, in both shapes, under exactly the hypotheses we already
carry: `K` convex, measurable, `B(0,1) ⊆ K`, `vol K < ⊤`.  No isotropy, no well-roundedness,
no diameter bound.**

## The mechanism, and why it is not the homothety

`isSmooth_of_ball_subset` uses the homothety `(1−δ)K`, on which `ℓ = 1`; that is a
*direction-blind* inner approximation and it loses `√n` (already for `K = B(0,1)`, where the
truth is `≈ 0.4 δ√n` and the homothety gives `nδ`).  The `√n` is a boundary-layer statement:
`ℓ` decays over a shell of width `δ/√n`, not `δ`.  The proof here is

1. `volume_ball_inter_le_cap` — for **convex** `K` and `y` at distance `u` from `K`, the
   separating hyperplane at the nearest point puts `B(y,δ) ∩ K` inside a ball of radius
   `√(δ²−u²)`, so `ℓ(y) ≤ (1 − u²/δ²)^{n/2} ≤ e^{−nu²/(2δ²)}` (`ell_le_cap`).  This is the
   sub-Gaussian decay, obtained with no rotation, no surface measure and no Cauchy formula:
   the cap is contained in a ball because `‖z−p‖² = ‖z−y‖² + 2⟪z−p,y−p⟫ − ‖y−p‖² < δ² − u²`.
2. `volume_shell_le` — `B(0,1) ⊆ K` convex gives `{d(·,K) < t} ⊆ (1+t)·K`, so the
   `t`-shell outside `K` has volume `≤ ((1+t)ⁿ − 1)·vol K`.
3. The layer cake balances (1) against (2): `∫_{Kᶜ} ℓ ≤ C·δ√n·vol K`, `C = 4e²`.
4. `lintegral_volume_inter_ball_comm` (`BallWalk.lean:225`) — the ball relation is symmetric —
   turns `∫_{Kᶜ} ℓ` into the deficit `∫_K (1 − ℓ)`.

Step (1) is where convexity enters, and it is the step the book replaces by an unproved
boundary-crossing estimate (`ball_walk.tex:686-699`: "It suffices to consider the case when
`L` is infinitesimally small").

## Main results

* `isSmooth_sqrt_of_ball_subset` — **the crux**: `IsSmooth K δ (ofReal (4e²·δ√n))` for every
  measurable convex `K ⊇ B(0,1)` of finite volume, at every `0 < δ` with `δ√n ≤ 1`.
* `smoothSqrt_le_smoothBall_mul` — **the machine-checked improvement, as a rate**: for
  `nδ ≤ 1`, the new `s` is at most `(8e²/√n)·(1 − (1−δ)ⁿ)`, i.e. one whole factor `√n`
  smaller than the constant of `isSmooth_of_ball_subset`.
* `smoothSqrt_le_half_smoothBall` — the same, as a strict inequality: from `n ≥ 15000` the
  new `s` is at most **half** the old one.  (The threshold is the crude constant `4e²`; the
  book's is `2`, the truth `≈ 0.4`.)
* `volume_goodPoints_ge` — the book's shape: `vol{x ∈ K : ℓ(x) ≥ 3/4} ≥ (1 − 16e²·δ√n)·vol K`,
  by Markov from the crux.
* `convex_goodPoints` — the book's `lem:avg-local-conductance` first half (left as an
  exercise there, `ball_walk.tex:680-682`): `{x ∈ K : ℓ(x) ≥ c}` is **convex** for `c > 0`.
  This is log-concavity of `ell` (`Arlib.isLogConcave_ell_toReal`), i.e. Brunn–Minkowski.
* `isSmooth_sqrt_witness` — non-vacuity, at `K = [-1,1]¹⁰⁰ ⊆ ℝ¹⁰⁰`, `δ = 1/2000`: both
  constants `< 1`, `0 < vol K < ⊤`, and the good-points set nonempty and convex.

## Scope

Nothing here is a conductance or a mixing-time statement.  `IsSmooth` is the *average* of
`ell`; the *pointwise* floor is refuted on this class by `EllFloor.lean`, and nothing here
contradicts that — `volume_goodPoints_ge` says the bad points are few, not that there are
none.  There is no `def`, `structure`, `class` or `axiom` in this file.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric Set
open scoped ENNReal Pointwise InnerProductSpace

variable {n : ℕ}

/-! ## 1. The good points form a convex set

`ball_walk.tex:676` asserts that `K_δ = {u ∈ K : ℓ(u) ≥ 3/4}` is convex and leaves the proof
as an exercise (`ball_walk.tex:680-682`).  It is the superlevel set of a log-concave
function. -/

/-- **Superlevel sets of `ell` are convex**, for every positive level.  This is
`Arlib.isLogConcave_ell_toReal` (Brunn–Minkowski) plus `c^a·c^b = c`. -/
theorem convex_ell_superlevel {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (δ : ℝ) {c : ℝ} (hc : 0 < c) :
    Convex ℝ {x : EuclideanSpace ℝ (Fin n) | ENNReal.ofReal c ≤ ell K δ x} := by
  have hlc := Arlib.isLogConcave_ell_toReal hK hKc δ
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  -- pass to the real form
  have hne : ∀ z : EuclideanSpace ℝ (Fin n), ell K δ z ≠ ⊤ := fun z =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ z)
  have htx : c ≤ (ell K δ x).toReal := (ENNReal.ofReal_le_iff_le_toReal (hne x)).1 hx
  have hty : c ≤ (ell K δ y).toReal := (ENNReal.ofReal_le_iff_le_toReal (hne y)).1 hy
  have hgeom := hlc.geom_le x y ha hb hab
  have hcc : c = c ^ a * c ^ b := by
    rw [← Real.rpow_add hc, hab, Real.rpow_one]
  have hle : c ≤ (ell K δ x).toReal ^ a * (ell K δ y).toReal ^ b := by
    rw [hcc]
    exact mul_le_mul (Real.rpow_le_rpow hc.le htx ha) (Real.rpow_le_rpow hc.le hty hb)
      (Real.rpow_nonneg hc.le b) (Real.rpow_nonneg (hc.le.trans htx) a)
  exact ENNReal.ofReal_le_of_le_toReal (hle.trans hgeom)

/-- **The good-points set `K_δ = {x ∈ K : ℓ(x) ≥ c}` is convex** (`ball_walk.tex:676`, first
half of `lem:avg-local-conductance`). -/
theorem convex_goodPoints {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (δ : ℝ) {c : ℝ} (hc : 0 < c) :
    Convex ℝ (K ∩ {x : EuclideanSpace ℝ (Fin n) | ENNReal.ofReal c ≤ ell K δ x}) :=
  hKc.inter (convex_ell_superlevel hK hKc δ hc)

/-! ## 2. Outside a convex body the local conductance decays like a Gaussian -/

/-- **The variational inequality of the nearest point.**  If `p` minimises the distance to
`y` over a convex set `C`, then `C` lies in the half-space `⟪· − p, y − p⟫ ≤ 0`. -/
theorem inner_nearest_le_zero {C : Set (EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C)
    {y p : EuclideanSpace ℝ (Fin n)} (hp : p ∈ C)
    (hmin : ∀ z ∈ C, dist y p ≤ dist y z) :
    ∀ z ∈ C, ⟪z - p, y - p⟫_ℝ ≤ 0 := by
  intro z hz
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rcases eq_or_lt_of_le (norm_nonneg (z - p)) with hzp | hzp
  · -- `z = p`
    have : z - p = 0 := by
      rwa [eq_comm, norm_eq_zero] at hzp
    simp [this, hε.le]
  · set t : ℝ := min 1 (2 * ε / ‖z - p‖ ^ 2) with htdef
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have htbd : t * ‖z - p‖ ^ 2 ≤ 2 * ε := by
      have h2 : t ≤ 2 * ε / ‖z - p‖ ^ 2 := min_le_right _ _
      have := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ ‖z - p‖ ^ 2)
      rwa [div_mul_cancel₀ _ (by positivity : ‖z - p‖ ^ 2 ≠ 0)] at this
    have hmem : (1 - t) • p + t • z ∈ C := hC hp hz (by linarith) ht0.le (by ring)
    have hdist := hmin _ hmem
    have hrw : y - ((1 - t) • p + t • z) = (y - p) - t • (z - p) := by
      rw [smul_sub]; module
    have hsq : ‖y - p‖ ^ 2 ≤ ‖(y - p) - t • (z - p)‖ ^ 2 := by
      have h1 : ‖y - p‖ ≤ ‖(y - p) - t • (z - p)‖ := by
        rw [← hrw, ← dist_eq_norm, ← dist_eq_norm]
        exact hdist
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hexp : ‖(y - p) - t • (z - p)‖ ^ 2
        = ‖y - p‖ ^ 2 - 2 * (t * ⟪y - p, z - p⟫_ℝ) + t ^ 2 * ‖z - p‖ ^ 2 := by
      rw [norm_sub_sq_real (y - p) (t • (z - p)), real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht0, mul_pow]
    rw [hexp] at hsq
    -- `0 ≤ -2t⟪y−p, z−p⟫ + t²‖z−p‖²`
    have hinner : ⟪z - p, y - p⟫_ℝ = ⟪y - p, z - p⟫_ℝ := real_inner_comm _ _
    nlinarith [hsq, htbd, ht0, sq_nonneg (‖z - p‖)]

/-- **The cap bound.**  For a convex `K` and any `y`, the part of the proposal ball `B(y,δ)`
that lies in `K` is contained in a ball of radius `√(δ² − d(y,K)²)`: the separating hyperplane
at the nearest point `p` cuts `B(y,δ)` in a cap, and `‖z − p‖² < δ² − d²` for every `z` in it.

No hypothesis on `δ`, and `y` may lie in `K` (then `d = 0` and the bound is trivial). -/
theorem volume_ball_inter_le_cap {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hKne : K.Nonempty) (y : EuclideanSpace ℝ (Fin n)) (δ : ℝ) :
    volume (Metric.ball y δ ∩ K)
      ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n))
          (Real.sqrt (δ ^ 2 - (Metric.infDist y K) ^ 2))) := by
  set u : ℝ := Metric.infDist y K with hudef
  have hu0 : 0 ≤ u := Metric.infDist_nonneg
  rcases eq_or_lt_of_le hu0 with hu | hu
  · -- `d(y,K) = 0`: the trivial bound
    have : Real.sqrt (δ ^ 2 - u ^ 2) = |δ| := by rw [← hu]; simp [Real.sqrt_sq_eq_abs]
    rw [this]
    calc volume (Metric.ball y δ ∩ K) ≤ volume (Metric.ball y δ) :=
          measure_mono Set.inter_subset_left
      _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) := volume_ball_eq y δ
      _ ≤ volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) |δ|) :=
          measure_mono (Metric.ball_subset_ball (le_abs_self δ))
  · -- `d(y,K) > 0`: the genuine cap
    have hCne : (closure K).Nonempty := hKne.closure
    obtain ⟨p, hpC, hpd⟩ := IsClosed.exists_infDist_eq_dist isClosed_closure hCne y
    have hclos : Metric.infDist y (closure K) = u := by
      rw [hudef, Metric.infDist_closure]
    have hnorm : ‖y - p‖ = u := by
      rw [← dist_eq_norm, ← hpd, hclos]
    have hmin : ∀ z ∈ closure K, dist y p ≤ dist y z := by
      intro z hz
      rw [← hpd, hclos, hudef, ← Metric.infDist_closure]
      exact Metric.infDist_le_dist_of_mem hz
    have hvar := inner_nearest_le_zero hKc.closure hpC hmin
    have hsub : Metric.ball y δ ∩ K
        ⊆ Metric.ball p (Real.sqrt (δ ^ 2 - u ^ 2)) := by
      rintro z ⟨hzb, hzK⟩
      have hzC : z ∈ closure K := subset_closure hzK
      have hzy : ‖z - y‖ < δ := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.1 hzb
      have hip : ⟪z - p, y - p⟫_ℝ ≤ 0 := hvar z hzC
      have hexp : ‖z - p‖ ^ 2 = ‖z - y‖ ^ 2 + 2 * ⟪z - p, y - p⟫_ℝ - ‖y - p‖ ^ 2 := by
        have h1 : z - y = (z - p) - (y - p) := by abel
        have h2 : ‖(z - p) - (y - p)‖ ^ 2
            = ‖z - p‖ ^ 2 - 2 * ⟪z - p, y - p⟫_ℝ + ‖y - p‖ ^ 2 := norm_sub_sq_real _ _
        rw [h1, h2]; ring
      have hlt : ‖z - p‖ ^ 2 < δ ^ 2 - u ^ 2 := by
        rw [hexp, hnorm]
        nlinarith [hzy, norm_nonneg (z - y), hip]
      rw [Metric.mem_ball, dist_eq_norm]
      exact (Real.lt_sqrt (norm_nonneg _)).2 hlt
    calc volume (Metric.ball y δ ∩ K)
        ≤ volume (Metric.ball p (Real.sqrt (δ ^ 2 - u ^ 2))) := measure_mono hsub
      _ = volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n))
            (Real.sqrt (δ ^ 2 - u ^ 2))) := volume_ball_eq _ _

/-- **The sub-Gaussian decay of `ell` outside a convex body**, in ratio form:
`ℓ(y) ≤ (√(δ² − d(y,K)²)/δ)ⁿ`. -/
theorem ell_le_cap [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hKne : K.Nonempty) {δ : ℝ} (hδ : 0 < δ) (y : EuclideanSpace ℝ (Fin n)) :
    ell K δ y
      ≤ ENNReal.ofReal
          ((Real.sqrt (δ ^ 2 - (Metric.infDist y K) ^ 2) / δ) ^ n) := by
  set u : ℝ := Metric.infDist y K with hudef
  set r : ℝ := Real.sqrt (δ ^ 2 - u ^ 2) with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hB0 : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
    (Metric.measure_ball_pos volume 0 one_pos).ne'
  have hBtop : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hballr : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r)
      = ENNReal.ofReal (r ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [Measure.addHaar_ball volume 0 hr0, finrank_euclideanSpace_fin]
  have hballd : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ)
      = ENNReal.ofReal (δ ^ n) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [Measure.addHaar_ball volume 0 hδ.le, finrank_euclideanSpace_fin]
  have hkey := volume_ball_inter_le_cap hKc hKne y δ
  rw [ell_apply, volume_ball_eq y δ]
  rw [ENNReal.div_le_iff_le_mul (Or.inl (by rw [hballd]; positivity))
    (Or.inl (by rw [hballd]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hBtop))]
  refine hkey.trans ?_
  rw [← hrdef, hballr, hballd, ← mul_assoc]
  gcongr
  rw [← ENNReal.ofReal_mul (by positivity), div_pow, div_mul_cancel₀]
  positivity

/-! ## 3. The outer shell of a body containing the unit ball -/

/-- **`{d(·,K) < t} ⊆ (1+t)·K`** for convex `K ⊇ B(0,1)`: a point within `t` of `K` is a
convex combination of a point of `K` and a point of `B(0,1) ⊆ K`, scaled by `1+t`. -/
theorem thickening_subset_smul {K : Set (EuclideanSpace ℝ (Fin n))} (hKc : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) {t : ℝ} (ht : 0 < t) :
    {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K < t} ⊆ (1 + t) • K := by
  have hKne : K.Nonempty := ⟨0, hball (by simpa using zero_lt_one)⟩
  intro y hy
  obtain ⟨z, hzK, hzd⟩ := (Metric.infDist_lt_iff hKne).1 hy
  have hv : ‖y - z‖ < t := by rwa [← dist_eq_norm]
  have ht1 : (0:ℝ) < 1 + t := by linarith
  have hmemball : t⁻¹ • (y - z) ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 ht)]
    calc t⁻¹ * ‖y - z‖ < t⁻¹ * t := by
          exact mul_lt_mul_of_pos_left hv (inv_pos.2 ht)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt ht)
  have hcomb : (1 + t)⁻¹ • z + (t / (1 + t)) • (t⁻¹ • (y - z)) ∈ K := by
    refine hKc hzK (hball hmemball) (by positivity) (by positivity) ?_
    field_simp
  refine Set.mem_smul_set.2 ⟨(1 + t)⁻¹ • y, ?_, ?_⟩
  · have hy' : (1 + t)⁻¹ • y
        = (1 + t)⁻¹ • z + (t / (1 + t)) • (t⁻¹ • (y - z)) := by
      rw [smul_smul, show t / (1 + t) * t⁻¹ = (1 + t)⁻¹ by field_simp, ← smul_add]
      congr 1
      abel
    rw [hy']
    exact hcomb
  · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt ht1), one_smul]

/-- **The `t`-shell outside `K` has volume at most `((1+t)ⁿ − 1)·vol K`.** -/
theorem volume_shell_le {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (hKc : Convex ℝ K) (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K)
    (hKtop : volume K ≠ ⊤) {t : ℝ} (ht : 0 < t) :
    volume ({y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K < t} \ K)
      ≤ ENNReal.ofReal ((1 + t) ^ n - 1) * volume K := by
  have ht1 : (0:ℝ) < 1 + t := by linarith
  have hsub : K ⊆ {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K < t} := by
    intro y hy
    simpa [Metric.infDist_zero_of_mem hy] using ht
  have hthick : volume {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K < t}
      ≤ ENNReal.ofReal ((1 + t) ^ n) * volume K := by
    refine le_trans (measure_mono (thickening_subset_smul hKc hball ht)) (le_of_eq ?_)
    rw [Measure.addHaar_smul, finrank_euclideanSpace_fin,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + t) ^ n)]
  have hdiff : volume ({y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K < t} \ K)
      = volume {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K < t} - volume K :=
    measure_sdiff hsub hK.nullMeasurableSet hKtop
  rw [hdiff]
  have hstep : volume {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K < t} - volume K
      ≤ ENNReal.ofReal ((1 + t) ^ n) * volume K - volume K := tsub_le_tsub_right hthick _
  refine hstep.trans (le_of_eq ?_)
  have h1 : ENNReal.ofReal ((1 + t) ^ n - 1)
      = ENNReal.ofReal ((1 + t) ^ n) - 1 := by
    rw [ENNReal.ofReal_sub _ zero_le_one, ENNReal.ofReal_one]
  rw [h1, ENNReal.sub_mul (fun _ _ => hKtop), one_mul]

/-! ## 4. The real-analytic core: the layer-cake integrand -/

/-- `√(2L) ≤ L/4 + 2` for `L ≥ 0`. -/
theorem sqrt_two_mul_le (L : ℝ) (hL : 0 ≤ L) : Real.sqrt (2 * L) ≤ L / 4 + 2 := by
  have h0 : (0:ℝ) ≤ 2 * L := by linarith
  have hsq : Real.sqrt (2 * L) ^ 2 = 2 * L := Real.sq_sqrt h0
  nlinarith [Real.sqrt_nonneg (2 * L), sq_nonneg (Real.sqrt (2 * L) - 4), hsq]

/-- `z·exp z` majorises `exp z − 1` for `z ≥ 0`. -/
theorem exp_sub_one_le_mul (z : ℝ) (hz : 0 ≤ z) : Real.exp z - 1 ≤ z * Real.exp z := by
  have h := Real.add_one_le_exp (-z)
  have hz1 : (1 - z) * Real.exp z ≤ 1 := by
    have hexp : Real.exp (-z) * Real.exp z = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos z, h, hexp]
  nlinarith

/-- **The layer-cake integrand is `O(δ√n · t^{-1/2})`.**

For `0 < t ≤ 1` and `δ√n ≤ 1`, `(1 + δ√(1 − t^{2/n}))ⁿ − 1 ≤ 2e²·δ√n·t^{-1/2}`.  The three
ingredients are `1 − t^{2/n} ≤ (2/n)·log(1/t)` (convexity of `exp`), `(1+x)ⁿ ≤ e^{nx}`, and
`√(2L)e^{√(2L)} ≤ 2e²e^{L/2}`. -/
theorem thickening_pow_le (hn : n ≠ 0) {δ t : ℝ} (hδ : 0 < δ)
    (hc : δ * Real.sqrt n ≤ 1) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (1 + δ * Real.sqrt (1 - t ^ ((2:ℝ) / n))) ^ n - 1
      ≤ 2 * Real.exp 2 * (δ * Real.sqrt n) * t ^ (-(1:ℝ) / 2) := by
  have hn0 : (0:ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  set L : ℝ := -Real.log t with hLdef
  have hL0 : 0 ≤ L := by
    have hlog : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht1
    rw [hLdef]; linarith
  -- (1) `1 − t^{2/n} ≤ 2L/n`
  have hstep1 : 1 - t ^ ((2:ℝ) / n) ≤ 2 * L / n := by
    have h := Real.add_one_le_exp (Real.log t * (2 / (n:ℝ)))
    rw [← Real.rpow_def_of_pos ht0] at h
    have hrw : Real.log t * (2 / (n:ℝ)) = -(2 * L / n) := by rw [hLdef]; ring
    rw [hrw] at h
    linarith
  set x : ℝ := δ * Real.sqrt (1 - t ^ ((2:ℝ) / n)) with hxdef
  set z : ℝ := (δ * Real.sqrt n) * Real.sqrt (2 * L) with hzdef
  have hx0 : 0 ≤ x := by rw [hxdef]; positivity
  have hz0 : 0 ≤ z := by rw [hzdef]; positivity
  have hsq2 : Real.sqrt (2 * L / n) * Real.sqrt n = Real.sqrt (2 * L) := by
    rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ (ne_of_gt hn0)]
  -- (2) `n·x ≤ z`
  have hnx : (n : ℝ) * x ≤ z := by
    have h1 : Real.sqrt (1 - t ^ ((2:ℝ) / n)) ≤ Real.sqrt (2 * L / n) :=
      Real.sqrt_le_sqrt hstep1
    have hnn : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hn0.le
    have h2 : (n : ℝ) * Real.sqrt (2 * L / n) = Real.sqrt n * Real.sqrt (2 * L) := by
      calc (n : ℝ) * Real.sqrt (2 * L / n)
          = (Real.sqrt n * Real.sqrt n) * Real.sqrt (2 * L / n) := by rw [hnn]
        _ = Real.sqrt n * (Real.sqrt (2 * L / n) * Real.sqrt n) := by ring
        _ = Real.sqrt n * Real.sqrt (2 * L) := by rw [hsq2]
    calc (n : ℝ) * x = δ * ((n : ℝ) * Real.sqrt (1 - t ^ ((2:ℝ) / n))) := by
          rw [hxdef]; ring
      _ ≤ δ * ((n : ℝ) * Real.sqrt (2 * L / n)) := by
          have := mul_le_mul_of_nonneg_left h1 hn0.le
          exact mul_le_mul_of_nonneg_left this hδ.le
      _ = z := by rw [h2, hzdef]; ring
  -- (3) `(1+x)ⁿ ≤ exp(n x)`
  have hpow : (1 + x) ^ n ≤ Real.exp ((n : ℝ) * x) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp x]) n
  -- (4) `exp(n x) − 1 ≤ z·exp z`
  have hmono : Real.exp ((n : ℝ) * x) - 1 ≤ z * Real.exp z := by
    have h1 : Real.exp ((n : ℝ) * x) - 1 ≤ ((n : ℝ) * x) * Real.exp ((n : ℝ) * x) :=
      exp_sub_one_le_mul _ (by positivity)
    have h2 : ((n : ℝ) * x) * Real.exp ((n : ℝ) * x) ≤ z * Real.exp z :=
      mul_le_mul hnx (Real.exp_le_exp.2 hnx) (Real.exp_pos _).le hz0
    linarith
  -- (5) pull out the factor `δ√n`
  have hzle : z ≤ Real.sqrt (2 * L) := by
    rw [hzdef]
    nlinarith [Real.sqrt_nonneg (2 * L), hc]
  have hz5 : z * Real.exp z
      ≤ (δ * Real.sqrt n) * (Real.sqrt (2 * L) * Real.exp (Real.sqrt (2 * L))) := by
    calc z * Real.exp z ≤ z * Real.exp (Real.sqrt (2 * L)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hzle) hz0
      _ = (δ * Real.sqrt n) * (Real.sqrt (2 * L) * Real.exp (Real.sqrt (2 * L))) := by
          rw [hzdef]; ring
  -- (6) `√(2L)·e^{√(2L)} ≤ 2e²·e^{L/2}`
  have hkey : Real.sqrt (2 * L) * Real.exp (Real.sqrt (2 * L))
      ≤ 2 * Real.exp 2 * Real.exp (L / 2) := by
    have h1 : Real.sqrt (2 * L) ≤ L / 4 + 2 := sqrt_two_mul_le L hL0
    have h3 : L / 4 + 2 ≤ 2 * Real.exp (L / 4) := by
      have := Real.add_one_le_exp (L / 4)
      linarith
    have h4 : Real.exp (L / 4 + 2) = Real.exp 2 * Real.exp (L / 4) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.sqrt (2 * L) * Real.exp (Real.sqrt (2 * L))
        ≤ (L / 4 + 2) * (Real.exp 2 * Real.exp (L / 4)) := by
          rw [← h4]
          exact mul_le_mul h1 (Real.exp_le_exp.2 h1) (Real.exp_pos _).le (by linarith)
      _ ≤ (2 * Real.exp (L / 4)) * (Real.exp 2 * Real.exp (L / 4)) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = 2 * Real.exp 2 * Real.exp (L / 2) := by
          rw [show L / 2 = L / 4 + L / 4 by ring, Real.exp_add]; ring
  -- (7) `e^{L/2} = t^{-1/2}`
  have hexpt : Real.exp (L / 2) = t ^ (-(1:ℝ) / 2) := by
    rw [Real.rpow_def_of_pos ht0, hLdef]
    congr 1
    ring
  -- assemble
  have hfin : z * Real.exp z ≤ 2 * Real.exp 2 * (δ * Real.sqrt n) * t ^ (-(1:ℝ) / 2) := by
    refine hz5.trans ?_
    have := mul_le_mul_of_nonneg_left hkey (by positivity : (0:ℝ) ≤ δ * Real.sqrt n)
    rw [hexpt] at this
    calc (δ * Real.sqrt n) * (Real.sqrt (2 * L) * Real.exp (Real.sqrt (2 * L)))
        ≤ (δ * Real.sqrt n) * (2 * Real.exp 2 * t ^ (-(1:ℝ) / 2)) := this
      _ = 2 * Real.exp 2 * (δ * Real.sqrt n) * t ^ (-(1:ℝ) / 2) := by ring
  linarith [hpow, hmono, hfin]

/-! ## 5. The layer cake -/

/-- `∫_0^1 t^{-1/2} dt = 2`, in `ℝ≥0∞` form. -/
theorem lintegral_rpow_neg_half :
    ∫⁻ t in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (t ^ (-(1:ℝ) / 2)) = ENNReal.ofReal 2 := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (-(1:ℝ) / 2)) (Set.Ioc (0:ℝ) 1) volume := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := 1)
      (r := -(1:ℝ) / 2) (by norm_num)
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
  have hval : ∫ t in Set.Ioc (0:ℝ) 1, t ^ (-(1:ℝ) / 2) = 2 := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_rpow (Or.inl (by norm_num))]
    norm_num
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0:ℝ) 1)] fun t : ℝ => t ^ (-(1:ℝ) / 2) := by
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioc (a := (0:ℝ)) (b := 1))] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]

/-- **The layer-cake bound on one superlevel set.**  For `0 < t ≤ 1`, the part of `Kᶜ` where
`ℓ > t` sits in the shell `{d(·,K) < δ√(1 − t^{2/n})}`, whose volume is
`≤ 2e²·δ√n·t^{-1/2}·vol K`. -/
theorem volume_compl_superlevel_le [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hKtop : volume K ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) (hδn : δ * Real.sqrt n ≤ 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    volume (Kᶜ ∩ {y : EuclideanSpace ℝ (Fin n) | t < (ell K δ y).toReal})
      ≤ ENNReal.ofReal (2 * Real.exp 2 * (δ * Real.sqrt n) * t ^ (-(1:ℝ) / 2)) * volume K := by
  have hn : n ≠ 0 := NeZero.ne n
  have hn0 : (0:ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hKne : K.Nonempty := ⟨0, hball (by simpa using zero_lt_one)⟩
  rcases eq_or_lt_of_le ht1 with hteq | htlt
  · -- `t = 1`: the set is empty, since `ℓ ≤ 1`
    have hempty : Kᶜ ∩ {y : EuclideanSpace ℝ (Fin n) | t < (ell K δ y).toReal} = ∅ := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro _ hlt
      have h1 : (ell K δ y).toReal ≤ 1 := by
        have := ell_le_one K δ y
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
      rw [hteq] at hlt
      linarith
    rw [hempty, measure_empty]
    exact zero_le
  · -- `t < 1`: the genuine shell bound
    set r : ℝ := δ * Real.sqrt (1 - t ^ ((2:ℝ) / n)) with hrdef
    have hnum : 0 < 1 - t ^ ((2:ℝ) / n) := by
      have : t ^ ((2:ℝ) / n) < 1 := by
        refine Real.rpow_lt_one ht0.le htlt (by positivity)
      linarith
    have hr0 : 0 < r := by rw [hrdef]; positivity
    have hsub : Kᶜ ∩ {y : EuclideanSpace ℝ (Fin n) | t < (ell K δ y).toReal}
        ⊆ {y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K < r} \ K := by
      rintro y ⟨hyK, hyt⟩
      refine ⟨?_, hyK⟩
      set u : ℝ := Metric.infDist y K with hudef
      have hu0 : 0 ≤ u := Metric.infDist_nonneg
      set q : ℝ := Real.sqrt (δ ^ 2 - u ^ 2) / δ with hqdef
      have hq0 : 0 ≤ q := by rw [hqdef]; positivity
      have hcap := ell_le_cap hKc hKne hδ y
      have hqt : t < q ^ n := by
        refine lt_of_lt_of_le hyt ?_
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) (by rw [← hqdef] at hcap; exact hcap)
      have hqpos : 0 < q := by
        rcases eq_or_lt_of_le hq0 with h | h
        · exfalso; rw [← h] at hqt; simp [zero_pow hn] at hqt; linarith
        · exact h
      -- `δ² − u² > 0`
      have hdu : 0 < δ ^ 2 - u ^ 2 := by
        by_contra hcon
        push_neg at hcon
        have : Real.sqrt (δ ^ 2 - u ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos hcon
        rw [hqdef, this] at hqpos
        simp at hqpos
      have hqsq : q ^ 2 = (δ ^ 2 - u ^ 2) / δ ^ 2 := by
        rw [hqdef, div_pow, Real.sq_sqrt hdu.le]
      -- raise `t < qⁿ` to the power `2/n`
      have hrpow : t ^ ((2:ℝ) / n) < q ^ 2 := by
        have h1 : t ^ ((2:ℝ) / n) < (q ^ n) ^ ((2:ℝ) / n) :=
          Real.rpow_lt_rpow ht0.le hqt (by positivity)
        have h2 : (q ^ n) ^ ((2:ℝ) / n) = q ^ 2 := by
          rw [← Real.rpow_natCast q n, ← Real.rpow_mul hq0]
          rw [mul_div_cancel₀ _ (ne_of_gt hn0)]
          norm_num
        rwa [h2] at h1
      -- hence `u < r`
      have hu2 : u ^ 2 < r ^ 2 := by
        have hrsq : r ^ 2 = δ ^ 2 * (1 - t ^ ((2:ℝ) / n)) := by
          rw [hrdef, mul_pow, Real.sq_sqrt hnum.le]
        rw [hrsq, hqsq] at *
        have hlt : t ^ ((2:ℝ) / n) < (δ ^ 2 - u ^ 2) / δ ^ 2 := hrpow
        rw [lt_div_iff₀ (by positivity)] at hlt
        nlinarith
      have hlt2 := Real.sqrt_lt_sqrt (by positivity) hu2
      rwa [Real.sqrt_sq hu0, Real.sqrt_sq hr0.le] at hlt2
    calc volume (Kᶜ ∩ {y : EuclideanSpace ℝ (Fin n) | t < (ell K δ y).toReal})
        ≤ volume ({y : EuclideanSpace ℝ (Fin n) | Metric.infDist y K < r} \ K) :=
          measure_mono hsub
      _ ≤ ENNReal.ofReal ((1 + r) ^ n - 1) * volume K :=
          volume_shell_le hK hKc hball hKtop hr0
      _ ≤ ENNReal.ofReal (2 * Real.exp 2 * (δ * Real.sqrt n) * t ^ (-(1:ℝ) / 2))
            * volume K := by
          gcongr
          rw [hrdef]
          exact thickening_pow_le hn hδ hδn ht0 ht1

/-- **`∫_{Kᶜ} ℓ ≤ 4e²·δ√n·vol K`** — the crux estimate, by the layer cake. -/
theorem lintegral_ell_compl_le [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hKtop : volume K ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) (hδn : δ * Real.sqrt n ≤ 1) :
    ∫⁻ y in Kᶜ, ell K δ y
      ≤ ENNReal.ofReal (4 * Real.exp 2 * (δ * Real.sqrt n)) * volume K := by
  have hmeas : Measurable fun y : EuclideanSpace ℝ (Fin n) => (ell K δ y).toReal :=
    (measurable_ell hK δ).ennreal_toReal
  have hne : ∀ y : EuclideanSpace ℝ (Fin n), ell K δ y ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (ell_le_one K δ y)
  -- rewrite as an integral of `ofReal ∘ toReal`
  have hrw : ∫⁻ y in Kᶜ, ell K δ y
      = ∫⁻ y in Kᶜ, ENNReal.ofReal ((ell K δ y).toReal) := by
    refine lintegral_congr fun y => ?_
    rw [ENNReal.ofReal_toReal (hne y)]
  rw [hrw, lintegral_eq_lintegral_meas_lt (volume.restrict Kᶜ)
    (Filter.Eventually.of_forall fun y => ENNReal.toReal_nonneg) hmeas.aemeasurable]
  -- split `Ioi 0 = Ioc 0 1 ∪ Ioi 1`
  have hsplit : Set.Ioi (0:ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi (by norm_num)).symm
  have hzero : ∀ t : ℝ, 1 < t →
      (volume.restrict (Kᶜ : Set (EuclideanSpace ℝ (Fin n))))
        {y | t < (ell K δ y).toReal} = 0 := by
    intro t ht
    have hempty : {y : EuclideanSpace ℝ (Fin n) | t < (ell K δ y).toReal} = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have h1 : (ell K δ y).toReal ≤ 1 :=
        ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using ell_le_one K δ y)
      linarith
    rw [hempty, measure_empty]
  calc ∫⁻ t in Set.Ioi (0:ℝ),
        (volume.restrict (Kᶜ : Set (EuclideanSpace ℝ (Fin n)))) {y | t < (ell K δ y).toReal}
      = ∫⁻ t in Set.Ioc (0:ℝ) 1 ∪ Set.Ioi 1,
          (volume.restrict (Kᶜ : Set (EuclideanSpace ℝ (Fin n))))
            {y | t < (ell K δ y).toReal} := by rw [hsplit]
    _ ≤ (∫⁻ t in Set.Ioc (0:ℝ) 1,
          (volume.restrict (Kᶜ : Set (EuclideanSpace ℝ (Fin n))))
            {y | t < (ell K δ y).toReal})
        + ∫⁻ t in Set.Ioi (1:ℝ),
          (volume.restrict (Kᶜ : Set (EuclideanSpace ℝ (Fin n))))
            {y | t < (ell K δ y).toReal} := lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (4 * Real.exp 2 * (δ * Real.sqrt n)) * volume K + 0 := by
        gcongr ?_ + ?_
        · -- the main piece
          have hbd : ∀ t ∈ Set.Ioc (0:ℝ) 1,
              (volume.restrict (Kᶜ : Set (EuclideanSpace ℝ (Fin n))))
                  {y | t < (ell K δ y).toReal}
                ≤ ENNReal.ofReal (2 * Real.exp 2 * (δ * Real.sqrt n))
                    * ENNReal.ofReal (t ^ (-(1:ℝ) / 2)) * volume K := by
            intro t ht
            have hmset : MeasurableSet
                {y : EuclideanSpace ℝ (Fin n) | t < (ell K δ y).toReal} :=
              measurableSet_lt measurable_const hmeas
            rw [Measure.restrict_apply hmset, Set.inter_comm]
            refine (volume_compl_superlevel_le hK hKc hball hKtop hδ hδn ht.1 ht.2).trans ?_
            rw [← ENNReal.ofReal_mul (by positivity)]
          refine le_trans (setLIntegral_mono' measurableSet_Ioc hbd) ?_
          rw [lintegral_mul_const' _ _ hKtop, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_rpow_neg_half, ← ENNReal.ofReal_mul (by positivity)]
          refine le_of_eq ?_
          have hcst : (2:ℝ) * Real.exp 2 * (δ * Real.sqrt n) * 2
              = 4 * Real.exp 2 * (δ * Real.sqrt n) := by ring
          rw [hcst]
        · -- the tail vanishes
          refine le_of_eq ?_
          refine (setLIntegral_congr_fun measurableSet_Ioi (fun t ht => hzero t ht)).trans ?_
          simp
    _ = ENNReal.ofReal (4 * Real.exp 2 * (δ * Real.sqrt n)) * volume K := by rw [add_zero]

/-! ## 6. From the outside integral to `IsSmooth` -/

/-- `ℓ_K(x) + ℓ_{Kᶜ}(x) = 1`: the proposal ball splits into its part inside and outside `K`. -/
theorem ell_add_ell_compl {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {δ : ℝ} (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n)) :
    ell K δ x + ell Kᶜ δ x = 1 := by
  have hV0 : volume (Metric.ball x δ) ≠ 0 := (Metric.measure_ball_pos volume x hδ).ne'
  have hVtop : volume (Metric.ball x δ) ≠ ⊤ := measure_ball_lt_top.ne
  rw [ell_apply, ell_apply, ENNReal.div_add_div_same]
  have hsplit : volume (Metric.ball x δ ∩ K) + volume (Metric.ball x δ ∩ Kᶜ)
      = volume (Metric.ball x δ) := by
    rw [← Set.diff_eq]
    exact measure_inter_add_diff _ hK
  rw [hsplit, ENNReal.div_self hV0 hVtop]

/-- **The deficit inside equals the mass outside**: `∫_K ℓ_{Kᶜ} = ∫_{Kᶜ} ℓ_K`.  This is the
symmetry of the ball relation (`lintegral_volume_inter_ball_comm`). -/
theorem lintegral_ell_compl_comm {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    (δ : ℝ) :
    ∫⁻ x in K, ell Kᶜ δ x = ∫⁻ y in Kᶜ, ell K δ y := by
  have hrw : ∀ (A : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n)),
      ell A δ x = volume (A ∩ Metric.ball x δ)
        / volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) δ) := by
    intro A x
    rw [ell_apply, Set.inter_comm, volume_ball_eq]
  simp only [hrw, ENNReal.div_eq_inv_mul]
  rw [lintegral_const_mul'' _ (measurable_volume_inter_ball hK.compl δ).aemeasurable,
    lintegral_const_mul'' _ (measurable_volume_inter_ball hK δ).aemeasurable,
    lintegral_volume_inter_ball_comm hK hK.compl δ]

/-- **The crux, in `IsSmooth` shape.**  Every measurable convex `K ⊇ B(0,1)` of finite volume
is `(δ, 4e²·δ√n)`-smooth, for every `0 < δ` with `δ√n ≤ 1`.

Compare `Arlib.MarkovChains.isSmooth_of_ball_subset` (`EllFloor.lean:549`), which gives
`s = 1 − (1−δ)ⁿ ≈ nδ` under the *same* hypotheses. -/
theorem isSmooth_sqrt_of_ball_subset [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hKtop : volume K ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) (hδn : δ * Real.sqrt n ≤ 1) :
    IsSmooth K δ (ENNReal.ofReal (4 * Real.exp 2 * (δ * Real.sqrt n))) := by
  set s : ℝ≥0∞ := ENNReal.ofReal (4 * Real.exp 2 * (δ * Real.sqrt n)) with hsdef
  have hstop : s ≠ ⊤ := by rw [hsdef]; exact ENNReal.ofReal_ne_top
  have hdef : ∫⁻ x in K, ell Kᶜ δ x ≤ s * volume K := by
    rw [lintegral_ell_compl_comm hK δ, hsdef]
    exact lintegral_ell_compl_le hK hKc hball hKtop hδ hδn
  have hsplit : volume K = (∫⁻ x in K, ell K δ x) + ∫⁻ x in K, ell Kᶜ δ x := by
    calc volume K = ∫⁻ _ in K, 1 := (setLIntegral_one K).symm
      _ = ∫⁻ x in K, (ell K δ x + ell Kᶜ δ x) :=
          lintegral_congr fun x => (ell_add_ell_compl hK hδ x).symm
      _ = (∫⁻ x in K, ell K δ x) + ∫⁻ x in K, ell Kᶜ δ x :=
          lintegral_add_left (measurable_ell hK δ) _
  have hle : volume K ≤ (∫⁻ x in K, ell K δ x) + s * volume K := by
    nth_rewrite 1 [hsplit]
    exact add_le_add le_rfl hdef
  have hfin : s * volume K ≠ ⊤ := ENNReal.mul_ne_top hstop hKtop
  rw [IsSmooth, ENNReal.sub_mul (fun _ _ => hKtop), one_mul]
  calc volume K - s * volume K ≤ ((∫⁻ x in K, ell K δ x) + s * volume K) - s * volume K :=
        tsub_le_tsub_right hle _
    _ = ∫⁻ x in K, ell K δ x := ENNReal.add_sub_cancel_right hfin

/-! ## 7. The book's shape: the good points fill `K` up to `O(δ√n)` -/

/-- **`vol{x ∈ K : ℓ(x) ≥ 3/4} ≥ (1 − 16e²·δ√n)·vol K`** — `ball_walk.tex:677`, second half of
`lem:avg-local-conductance`, with `16e²` in place of the book's `2`.  Markov's inequality
applied to the deficit `1 − ℓ`, which `isSmooth_sqrt_of_ball_subset` bounds by `4e²δ√n`. -/
theorem volume_goodPoints_ge [NeZero n] {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : MeasurableSet K) (hKc : Convex ℝ K)
    (hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ K) (hKtop : volume K ≠ ⊤)
    {δ : ℝ} (hδ : 0 < δ) (hδn : δ * Real.sqrt n ≤ 1) :
    (1 - ENNReal.ofReal (16 * Real.exp 2 * (δ * Real.sqrt n))) * volume K
      ≤ volume (K ∩ {x : EuclideanSpace ℝ (Fin n) | ENNReal.ofReal (3 / 4) ≤ ell K δ x}) := by
  set S : Set (EuclideanSpace ℝ (Fin n)) :=
    {x : EuclideanSpace ℝ (Fin n) | ENNReal.ofReal (3 / 4) ≤ ell K δ x} with hSdef
  have hSm : MeasurableSet S := measurableSet_le measurable_const (measurable_ell hK δ)
  have hBm : MeasurableSet (K \ S) := hK.diff hSm
  -- on the bad set the deficit is at least `1/4`
  have hbad : ∀ x ∈ K \ S, ENNReal.ofReal (1 / 4) ≤ ell Kᶜ δ x := by
    rintro x ⟨-, hxS⟩
    rw [hSdef] at hxS
    simp only [Set.mem_setOf_eq, not_le] at hxS
    have hsum := ell_add_ell_compl hK hδ x
    have h34 : ENNReal.ofReal (1 / 4) + ENNReal.ofReal (3 / 4) = 1 := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    by_contra hcon
    push_neg at hcon
    have : ell K δ x + ell Kᶜ δ x < ENNReal.ofReal (3 / 4) + ENNReal.ofReal (1 / 4) :=
      ENNReal.add_lt_add hxS hcon
    rw [hsum, add_comm (ENNReal.ofReal (3 / 4)), h34] at this
    exact lt_irrefl 1 this
  -- Markov
  have hmarkov : ENNReal.ofReal (1 / 4) * volume (K \ S) ≤ ∫⁻ x in K, ell Kᶜ δ x := by
    calc ENNReal.ofReal (1 / 4) * volume (K \ S) = ∫⁻ _ in K \ S, ENNReal.ofReal (1 / 4) := by
          rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ x in K \ S, ell Kᶜ δ x := by
          refine setLIntegral_mono' hBm ?_
          exact fun x hx => hbad x hx
      _ ≤ ∫⁻ x in K, ell Kᶜ δ x :=
          lintegral_mono' (Measure.restrict_mono Set.diff_subset le_rfl) le_rfl
  have hdef : ∫⁻ x in K, ell Kᶜ δ x
      ≤ ENNReal.ofReal (4 * Real.exp 2 * (δ * Real.sqrt n)) * volume K := by
    rw [lintegral_ell_compl_comm hK δ]
    exact lintegral_ell_compl_le hK hKc hball hKtop hδ hδn
  -- hence the bad set is small
  have hbadvol : volume (K \ S)
      ≤ ENNReal.ofReal (16 * Real.exp 2 * (δ * Real.sqrt n)) * volume K := by
    have h4 : ENNReal.ofReal (1 / 4) * volume (K \ S)
        ≤ ENNReal.ofReal (4 * Real.exp 2 * (δ * Real.sqrt n)) * volume K :=
      hmarkov.trans hdef
    have hfour : ENNReal.ofReal 4 * ENNReal.ofReal (1 / 4) = 1 := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      norm_num
    calc volume (K \ S)
        = ENNReal.ofReal 4 * (ENNReal.ofReal (1 / 4) * volume (K \ S)) := by
          rw [← mul_assoc, hfour, one_mul]
      _ ≤ ENNReal.ofReal 4
            * (ENNReal.ofReal (4 * Real.exp 2 * (δ * Real.sqrt n)) * volume K) :=
          mul_le_mul_left' h4 _
      _ = ENNReal.ofReal (16 * Real.exp 2 * (δ * Real.sqrt n)) * volume K := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
            show (4:ℝ) * (4 * Real.exp 2 * (δ * Real.sqrt n))
              = 16 * Real.exp 2 * (δ * Real.sqrt n) by ring]
  -- and the good set fills the rest
  have hsum : volume (K ∩ S) + volume (K \ S) = volume K := measure_inter_add_diff K hSm
  have hKS : volume (K ∩ S) ≠ ⊤ := ne_top_of_le_ne_top hKtop (measure_mono Set.inter_subset_left)
  rw [ENNReal.sub_mul (fun _ _ => hKtop), one_mul]
  refine (tsub_le_tsub_left hbadvol _).trans ?_
  rw [← hsum]
  exact le_of_eq (ENNReal.add_sub_cancel_right (ne_top_of_le_ne_top hKtop
    (measure_mono Set.diff_subset)))

/-! ## 8. The improvement, machine-checked -/

/-- `(1−δ)ⁿ ≤ 1 − nδ/2` for `0 ≤ δ` and `nδ ≤ 1`: the old smoothness constant
`1 − (1−δ)ⁿ` really is `Ω(nδ)`. -/
theorem pow_one_sub_le (hn : n ≠ 0) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδn : (n : ℝ) * δ ≤ 1) :
    (1 - δ) ^ n ≤ 1 - (n : ℝ) * δ / 2 := by
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have hδ1 : δ ≤ 1 := by nlinarith
  have h1 : (1 - δ) ^ n ≤ Real.exp (-δ) ^ n :=
    pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-δ)]) n
  have h2 : Real.exp (-δ) ^ n = Real.exp (-((n : ℝ) * δ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h3 : Real.exp ((n : ℝ) * δ) * Real.exp (-((n : ℝ) * δ)) = 1 := by
    rw [← Real.exp_add]; simp
  have h4 : 1 + (n : ℝ) * δ ≤ Real.exp ((n : ℝ) * δ) := by
    have := Real.add_one_le_exp ((n : ℝ) * δ)
    linarith
  have h5 : Real.exp (-((n : ℝ) * δ)) ≤ 1 - (n : ℝ) * δ / 2 := by
    have hpos : 0 < Real.exp (-((n : ℝ) * δ)) := Real.exp_pos _
    have hx0 : 0 ≤ (n : ℝ) * δ := by positivity
    nlinarith [h3, h4, hpos, hx0, hδn]
  rw [h2] at h1
  linarith

/-- **The improvement, as a rate.**  Under `0 < δ` and `nδ ≤ 1`, the smoothness constant of
`isSmooth_sqrt_of_ball_subset` is at most `8e²/√n` times the constant `1 − (1−δ)ⁿ` of
`Arlib.MarkovChains.isSmooth_of_ball_subset` (`EllFloor.lean:549`).  The gain is exactly one
factor `√n`, which is one factor `n` in the `δ⁻²` step count. -/
theorem smoothSqrt_le_smoothBall_mul (hn : n ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (hδn : (n : ℝ) * δ ≤ 1) :
    ENNReal.ofReal (4 * Real.exp 2 * (δ * Real.sqrt n))
      ≤ ENNReal.ofReal (8 * Real.exp 2 / Real.sqrt n)
          * (1 - ENNReal.ofReal ((1 - δ) ^ n)) := by
  have hn0 : (0:ℝ) < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  have hδ1 : δ ≤ 1 := by nlinarith
  have hpow0 : (0:ℝ) ≤ (1 - δ) ^ n := by positivity
  -- the old constant, in real form
  have hold : ENNReal.ofReal ((n : ℝ) * δ / 2) ≤ 1 - ENNReal.ofReal ((1 - δ) ^ n) := by
    have h := pow_one_sub_le hn hδ.le hδn
    have hrw : (1 : ℝ≥0∞) - ENNReal.ofReal ((1 - δ) ^ n)
        = ENNReal.ofReal (1 - (1 - δ) ^ n) := by
      rw [ENNReal.ofReal_sub _ hpow0, ENNReal.ofReal_one]
    rw [hrw]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  -- the identity `(8e²/√n)·(nδ/2) = 4e²·δ√n`
  have hid : 8 * Real.exp 2 / Real.sqrt n * ((n : ℝ) * δ / 2)
      = 4 * Real.exp 2 * (δ * Real.sqrt n) := by
    have hns : (n : ℝ) / Real.sqrt n = Real.sqrt n := Real.div_sqrt
    field_simp
    nlinarith [Real.sq_sqrt hn0.le, hsq]
  calc ENNReal.ofReal (4 * Real.exp 2 * (δ * Real.sqrt n))
      = ENNReal.ofReal (8 * Real.exp 2 / Real.sqrt n) * ENNReal.ofReal ((n : ℝ) * δ / 2) := by
        rw [← ENNReal.ofReal_mul (by positivity), hid]
    _ ≤ ENNReal.ofReal (8 * Real.exp 2 / Real.sqrt n)
          * (1 - ENNReal.ofReal ((1 - δ) ^ n)) := mul_le_mul_left' hold _

/-- **The improvement, as a strict inequality.**  From dimension `15000` on (with `nδ ≤ 1`),
the `δ√n` constant is at most **half** the `1 − (1−δ)ⁿ` constant.  The threshold is an
artefact of the crude constant `4e²`; the book's constant is `2`, and the true one is
`≈ 0.4`. -/
theorem smoothSqrt_le_half_smoothBall (hn : 15000 ≤ n) {δ : ℝ} (hδ : 0 < δ)
    (hδn : (n : ℝ) * δ ≤ 1) :
    ENNReal.ofReal (4 * Real.exp 2 * (δ * Real.sqrt n))
      ≤ ENNReal.ofReal (1 / 2) * (1 - ENNReal.ofReal ((1 - δ) ^ n)) := by
  have hn0 : n ≠ 0 := by omega
  have hnR : (15000:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexp : Real.exp 2 < 7.39 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1, h1, h2]
  have hsqrt : (118.3 : ℝ) ≤ Real.sqrt n := by
    rw [show (118.3:ℝ) = Real.sqrt (118.3 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hratio : 8 * Real.exp 2 / Real.sqrt n ≤ 1 / 2 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < Real.sqrt n)]
    nlinarith
  refine (smoothSqrt_le_smoothBall_mul hn0 hδ hδn).trans ?_
  exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal hratio) _

/-! ## 9. Non-vacuity (`CLAUDE.md` §11) -/

/-- **Non-vacuity witness.**  At `n = 100`, `K = [-1,1]¹⁰⁰` (a body with `2¹⁰⁰` corners, on
which no pointwise `ℓ`-floor survives — `EllFloor.lean`) and `δ = 1/2000`:

* every hypothesis of `isSmooth_sqrt_of_ball_subset` and `volume_goodPoints_ge` holds;
* `vol K ∉ {0, ⊤}`, so the conclusions are not `0 ≤ 0`;
* both constants are `< 1`, so `IsSmooth K δ s` has content (`s ≈ 0.148`) and the
  good-points bound has content (`1 − 16e²δ√n ≈ 0.41`);
* the good-points set is **nonempty**: `ℓ(0) = 1 ≥ 3/4`, since `B(0,δ) ⊆ B(0,1) ⊆ K`;
* and it is convex. -/
theorem isSmooth_sqrt_witness :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 100))) (δ : ℝ),
      MeasurableSet K ∧ Convex ℝ K ∧
      Metric.ball (0 : EuclideanSpace ℝ (Fin 100)) 1 ⊆ K ∧
      volume K ≠ ⊤ ∧ volume K ≠ 0 ∧ 0 < δ ∧ δ * Real.sqrt 100 ≤ 1 ∧
      4 * Real.exp 2 * (δ * Real.sqrt 100) < 1 ∧
      16 * Real.exp 2 * (δ * Real.sqrt 100) < 1 ∧
      IsSmooth K δ (ENNReal.ofReal (4 * Real.exp 2 * (δ * Real.sqrt 100))) ∧
      (1 - ENNReal.ofReal (16 * Real.exp 2 * (δ * Real.sqrt 100))) * volume K
        ≤ volume (K ∩ {x : EuclideanSpace ℝ (Fin 100) |
            ENNReal.ofReal (3 / 4) ≤ ell K δ x}) ∧
      (K ∩ {x : EuclideanSpace ℝ (Fin 100) | ENNReal.ofReal (3 / 4) ≤ ell K δ x}).Nonempty ∧
      Convex ℝ (K ∩ {x : EuclideanSpace ℝ (Fin 100) |
        ENNReal.ofReal (3 / 4) ≤ ell K δ x}) := by
  classical
  set K : Set (EuclideanSpace ℝ (Fin 100)) := {y : EuclideanSpace ℝ (Fin 100) | ∀ j, |y j| ≤ 1}
    with hKdef
  have hKm : MeasurableSet K := measurableSet_supNormCube
  have hKc : Convex ℝ K := convex_supNormCube
  have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin 100)) 1 ⊆ K := ball_subset_cube
  have hKtop : volume K ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono
      (show K ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 100)) (Real.sqrt 100) from
        fun y hy => mem_closedBall_zero_iff.2 (norm_le_sqrt_of_mem_cube hy)))
      measure_closedBall_lt_top)
  have hK0 : volume K ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (Metric.measure_ball_pos volume 0 one_pos) (measure_mono hball))
  have hs100 : Real.sqrt (100 : ℝ) = 10 := by
    rw [show (100:ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hδ : (0:ℝ) < 1 / 2000 := by norm_num
  have hexp : Real.exp 2 < 7.39 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 1, h1, h2]
  have hδn : (1 / 2000 : ℝ) * Real.sqrt 100 ≤ 1 := by rw [hs100]; norm_num
  have hcast : Real.sqrt ((100 : ℕ) : ℝ) = Real.sqrt (100 : ℝ) := by norm_num
  refine ⟨K, 1 / 2000, hKm, hKc, hball, hKtop, hK0, hδ, hδn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs100]; nlinarith [Real.exp_pos 2]
  · rw [hs100]; nlinarith [Real.exp_pos 2]
  · have := isSmooth_sqrt_of_ball_subset (n := 100) hKm hKc hball hKtop hδ (by
      rw [hcast]; exact hδn)
    rwa [hcast] at this
  · have := volume_goodPoints_ge (n := 100) hKm hKc hball hKtop hδ (by
      rw [hcast]; exact hδn)
    rwa [hcast] at this
  · refine ⟨0, ?_, ?_⟩
    · exact hball (by simpa using zero_lt_one)
    · have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin 100)) (1 / 2000) ⊆ K :=
        subset_trans (Metric.ball_subset_ball (by norm_num)) hball
      have hell : ell K (1 / 2000) (0 : EuclideanSpace ℝ (Fin 100)) = 1 := by
        rw [ell_apply, Set.inter_eq_self_of_subset_left hsub]
        exact ENNReal.div_self (Metric.measure_ball_pos volume _ hδ).ne' measure_ball_lt_top.ne
      rw [Set.mem_setOf_eq, hell]
      exact ENNReal.ofReal_le_one.2 (by norm_num)
  · exact convex_goodPoints hKm hKc _ (by norm_num : (0:ℝ) < 3 / 4)

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.convex_ell_superlevel
#print axioms Arlib.MarkovChains.convex_goodPoints
#print axioms Arlib.MarkovChains.inner_nearest_le_zero
#print axioms Arlib.MarkovChains.volume_ball_inter_le_cap
#print axioms Arlib.MarkovChains.ell_le_cap
#print axioms Arlib.MarkovChains.thickening_subset_smul
#print axioms Arlib.MarkovChains.volume_shell_le
#print axioms Arlib.MarkovChains.sqrt_two_mul_le
#print axioms Arlib.MarkovChains.exp_sub_one_le_mul
#print axioms Arlib.MarkovChains.thickening_pow_le
#print axioms Arlib.MarkovChains.lintegral_rpow_neg_half
#print axioms Arlib.MarkovChains.volume_compl_superlevel_le
#print axioms Arlib.MarkovChains.lintegral_ell_compl_le
#print axioms Arlib.MarkovChains.ell_add_ell_compl
#print axioms Arlib.MarkovChains.lintegral_ell_compl_comm
#print axioms Arlib.MarkovChains.isSmooth_sqrt_of_ball_subset
#print axioms Arlib.MarkovChains.volume_goodPoints_ge
#print axioms Arlib.MarkovChains.pow_one_sub_le
#print axioms Arlib.MarkovChains.smoothSqrt_le_smoothBall_mul
#print axioms Arlib.MarkovChains.smoothSqrt_le_half_smoothBall
#print axioms Arlib.MarkovChains.isSmooth_sqrt_witness
