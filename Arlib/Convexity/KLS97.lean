/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Convex.Basic

/-!
# How much of a ball around a point of `K` sticks out of `K`, on average

This file proves an *unconditional* bound on

`∫_K vol((x + tB) \ K) dx`,

the quantity that Kannan–Lovász–Simonovits call `1 − ℓ` (one minus the average local
conductance of the `δ`-step walk), for a convex body `K` containing a ball of radius `r`.

## Provenance, and exactly what is and is not proved here

The target is **Corollary 4.6** of

> R. Kannan, L. Lovász, M. Simonovits, *Random walks and an `O*(n⁵)` volume algorithm for
> convex bodies*, Random Structures & Algorithms **11** (1997), 1–50,

quoted without proof as **Lemma 3.3** of Lovász–Vempala, *Hit-and-Run from a Corner*, in the
form

`∫_K vol((x + tB) \ K) dx ≤ (t·√n / 2r) · vol(K) · vol(tB)`.      (KLS)

The KLS97 text was consulted directly (pp. 23–24 of the journal version).  Its proof is the
three-step chain

* **Lemma 4.3**: for `L` a measurable piece of `∂K`, the `2n`-measure of
  `S = {(x,y) : x ∈ K, y ∉ K, ‖x−y‖ ≤ δ, [x,y] ∩ L ≠ ∅}` is at most
  `vol_{n−1}(L) · δ^{n+1} · vol_{n−1}(B) / (n+1)`;
* **Corollary 4.4/4.5**: hence `1 − ℓ ≤ (δ / 2√n) · vol_{n−1}(∂K) / vol(K)`;
* **Corollary 4.6**: and `vol(K) ≥ (r/n)·vol_{n−1}(∂K)` when `K ⊇ rB`, giving `1 − ℓ ≤ δ√n/2r`.

The constants check out: the half-space computation behind Lemma 4.3 gives exactly
`vol_{n−1}(L)·δ^{n+1}·κ_{n−1}/(n+1)`, so the probability in Corollary 4.4 is exactly
`δ·vol_{n−1}(L)·κ_{n−1}/((n+1)·κ_n·vol(K))`, and `κ_{n−1}/κ_n ≤ (n+1)/(2√n)` for every `n ≥ 1`
turns that into the printed `δ·vol_{n−1}(L)/(2√n·vol(K))`.  So the `√n` in Corollary 4.6 is
correct, and no unstated hypothesis on `n` is hiding in it.

Two remarks on that argument, both relevant to what is done here.

1. **The `√n` is Cauchy's projection formula.**  Corollaries 4.4/4.5 are, in substance, the
   statement that the *average over directions* of the shadow area `vol_{n−1}(P_θ K)` equals
   `κ_{n−1}/(n κ_n) · vol_{n−1}(∂K) ≈ vol_{n−1}(∂K)/(2√n)`.  The `√n` cannot be obtained
   direction-by-direction: for a cone of height comparable to its base radius the single worst
   direction already forces the factor `n`, and only the average over the sphere is `√n`.  So
   any proof of (KLS) as stated must integrate over directions.  Mathlib v4.32 has neither the
   surface-area measure of a convex body, nor mixed volumes, nor Cauchy's formula, so (KLS) with
   the constant `√n` is out of reach here.
2. **KLS97's proof of Lemma 4.3 is not rigorous as printed.**  It reads, in full: *"It suffices
   to prove the assertion for the case when `L` is infinitesimally small.  In this case, the
   measure of `S` is maximized when the surface of `K` is a hyperplane in a large neighborhood
   of `L`.  Then the measure of `S` is independent of `K` and, by a direct computation, is in
   fact equal to the upper bound given."*  Neither reduction ("infinitesimally small";
   "maximized when ... a hyperplane") is justified — the first is a differentiation of the
   surface measure, the second a monotonicity claim about all convex bodies at once — and the
   "direct computation" is left to the reader.  This is a gap in the source, not merely a gap in
   this formalization; unlike the `n ≥ 6` gap this development found in Lovász–Vempala's Lemma
   3.2, it is a gap in *rigour*, not in the truth of the statement: Corollary 4.6 is true as
   printed (the ball nearly attains it, at `1/√(2π)` against the stated `1/2`).

**What this file proves instead** is the same inequality with `√n` replaced by `n`:

`∫_K vol((x + tB) \ K) dx ≤ (t·n / 2r) · vol(K) · vol(tB)`.        (KLS-n)

This is unconditional — no inline hypotheses, nothing assumed — and it is proved by a genuinely
different, elementary route: the **shrink-and-shift** inclusion
`(1−λ)K + λz − u/2 ⊆ K ∩ (K − u)` for `λ = ‖u‖/2r`, which needs only convexity and `B(z,r) ⊆ K`
(no Brunn–Minkowski, no surface area).  See `Arlib.volume_inter_translate_ge`.

`(KLS-n)` is off from `(KLS)` by exactly the factor `√n`, and that factor is *real*, not an
artifact: the direction-by-direction bound behind `(KLS-n)` is attained, up to a factor `1.21`,
by a cone whose height equals its base radius.  There is no route from `(KLS-n)` to `(KLS)`.

## Consequence downstream (read this before using)

`Arlib.volume_goodSet_ge` and `Arlib.lintegral_stepRadius_ge` in `Arlib/Convexity/StepLength.lean`
carry `(KLS)` at `r = 1` as an inline `∀`-hypothesis `hLem33`.  `Arlib.lem33_const_n` below has
**exactly** the shape of that hypothesis except that `Real.sqrt n` is replaced by `(n : ℝ)`.  Since
`√n ≤ n`, the theorem proved here is *weaker* and does **not** discharge `hLem33` for `n ≥ 2`;
feeding it to those two theorems requires restating them with `Real.sqrt n` replaced by `(n : ℝ)`
throughout, at which point Lemma 3.4's conclusion degrades from

`∫_K s_α ≥ ((1−α)/√n)·vol(K)`  to  `∫_K s_α ≥ ((1−α)/n)·vol(K)`

(the constant enters as `c` in `∫₀^∞ (1−α−ct)₊ dt = (1−α)²/2c`, with `c = n/2` instead of
`c = √n/2`).  So: the weaker constant **does not** suffice for the paper's `(1−α)/√n`; it gives
`(1−α)/n`.  For `n = 1` the two agree and the discharge is exact.

An intermediate route does exist and is *not* pursued here, for cost reasons: bounding
`K ∩ B(y,t)` for `y ∉ K` by the spherical cap cut off by the supporting hyperplane at the
metric projection of `y` (the cap `{u : ‖u‖ ≤ t, ⟨ν,u⟩ ≥ h}` is contained in the ball
`B(hν, √(t²−h²))`, so has volume at most `(1−h²/t²)^{n/2}·vol(tB)`), and integrating that
Gaussian-tailed weight against the shell bound `vol(K + hB) ≤ (1+h/r)ⁿ vol(K)`.  That yields
`C·t√n/(2r)` for an explicit absolute `C > 1` — the right order in `n`, but it needs a
layer-cake against a monotone weight and a Gaussian-type one-dimensional integral, and it is a
substantially larger development than the one below.

## Main results

* `Arlib.volume_inter_translate_ge` — the shrink-and-shift bound
  `vol(K ∩ (K − u)) ≥ (1 − ‖u‖/2r)ⁿ · vol(K)`.
* `Arlib.volume_sdiff_translate_le` — its consequence `vol(K \ (K − u)) ≤ (n‖u‖/2r) · vol(K)`.
* `Arlib.lintegral_volume_closedBall_sdiff_le` — `(KLS-n)`, general inradius `r`.
* `Arlib.lem33_const_n` — the specialisation to `r = 1`, in the shape of `hLem33`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace Arlib

section KLS

variable {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))} {z : EuclideanSpace ℝ (Fin n)} {r : ℝ}

/-! ### Indicator bookkeeping -/

private lemma one_indicator_mul {α : Type*} (S T : Set α) (x : α) :
    S.indicator (1 : α → ℝ≥0∞) x * T.indicator 1 x = (S ∩ T).indicator 1 x := by
  by_cases h1 : x ∈ S <;> by_cases h2 : x ∈ T <;> simp [h1, h2]

private lemma indicator_one_mul {α : Type*} (S : Set α) (g : α → ℝ≥0∞) (x : α) :
    S.indicator (1 : α → ℝ≥0∞) x * g x = S.indicator g x := by
  by_cases h : x ∈ S <;> simp [h]

/-! ### The shrink-and-shift inclusion -/

/-- If `K` is convex and contains the ball `B(z,r)`, then the homothety of `K` about `z` with
ratio `1 − λ` may be shifted by any vector of length at most `λ·r` and still stay inside `K`.

This is the only geometric input to the whole file: it is elementary convexity, and needs
neither Brunn–Minkowski nor any surface-area notion. -/
theorem homothety_add_mem (hKc : Convex ℝ K) (hball : Metric.closedBall z r ⊆ K)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K)
    {w : EuclideanSpace ℝ (Fin n)} (hw : ‖w‖ ≤ lam * r) :
    AffineMap.homothety z (1 - lam) x + w ∈ K := by
  rcases eq_or_lt_of_le hlam0 with h0 | h0
  · -- `lam = 0`: the homothety is the identity and `w = 0`.
    have hw0 : w = 0 := by
      have : ‖w‖ ≤ 0 := by rw [← h0] at hw; simpa using hw
      simpa using le_antisymm this (norm_nonneg w)
    have h1 : (1 : ℝ) - lam = 1 := by rw [← h0]; ring
    have h2 : AffineMap.homothety z (1 : ℝ) x = x := by
      simp
    rw [h1, h2, hw0, add_zero]
    exact hx
  · -- `lam > 0`: write the point as a convex combination of `x ∈ K` and a point of `B(z,r) ⊆ K`.
    have hz : z + lam⁻¹ • w ∈ K := by
      refine hball ?_
      simp only [Metric.mem_closedBall, dist_eq_norm]
      have : ‖z + lam⁻¹ • w - z‖ = lam⁻¹ * ‖w‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h0)]
      rw [this]
      calc lam⁻¹ * ‖w‖ ≤ lam⁻¹ * (lam * r) := by
            exact mul_le_mul_of_nonneg_left hw (le_of_lt (inv_pos.mpr h0))
        _ = r := by field_simp
    have hcomb := hKc hx hz (by linarith : (0:ℝ) ≤ 1 - lam) hlam0 (by ring)
    have hl : lam • lam⁻¹ • w = w := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt h0), one_smul]
    have hrw : (1 - lam) • x + lam • (z + lam⁻¹ • w)
        = AffineMap.homothety z (1 - lam) x + w := by
      rw [AffineMap.homothety_apply]
      simp only [vsub_eq_sub, vadd_eq_add, smul_add, smul_sub, hl]
      module
    rwa [hrw] at hcomb

/-- **The shrink-and-shift bound.**  For `K` convex containing `B(z,r)` and any `u` with
`‖u‖ < 2r`, the overlap of `K` with its translate by `u` is at least `(1 − ‖u‖/2r)ⁿ · vol(K)`.

The witness is `(1−λ)K + λz` shifted by `−u/2`, with `λ = ‖u‖/(2r)`: shifting the shrunken copy
by `±u/2` keeps it inside `K` by `Arlib.homothety_add_mem`, and a set that stays inside `K` after
being shifted both ways by `u/2` lies in `K ∩ (K − u)`. -/
theorem volume_inter_translate_ge (hKc : Convex ℝ K) (hball : Metric.closedBall z r ⊆ K)
    (hr : 0 < r) {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ ≤ 2 * r) :
    ENNReal.ofReal ((1 - ‖u‖ / (2 * r)) ^ n) * volume K
      ≤ volume (K ∩ (fun x => x + u) ⁻¹' K) := by
  set lam : ℝ := ‖u‖ / (2 * r) with hlamdef
  have h2r : (0:ℝ) < 2 * r := by linarith
  have hlam0 : 0 ≤ lam := by positivity
  have hlam1 : lam ≤ 1 := by
    rw [hlamdef, div_le_one h2r]; exact hu
  have hnorm : ‖(2:ℝ)⁻¹ • u‖ ≤ lam * r := by
    have h1 : ‖(2:ℝ)⁻¹ • u‖ = ‖u‖ / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < (2:ℝ)⁻¹)]
      ring
    have h2 : lam * r = ‖u‖ / 2 := by
      rw [hlamdef]; field_simp
    rw [h1, h2]
  -- the shrunken and shifted copy
  set A : Set (EuclideanSpace ℝ (Fin n)) :=
    (fun x => AffineMap.homothety z (1 - lam) x - (2:ℝ)⁻¹ • u) '' K with hAdef
  have hsub : A ⊆ K ∩ (fun x => x + u) ⁻¹' K := by
    rintro y ⟨x, hx, rfl⟩
    constructor
    · have := homothety_add_mem hKc hball hlam0 hlam1 hx
        (w := -((2:ℝ)⁻¹ • u)) (by simpa using hnorm)
      simpa [sub_eq_add_neg] using this
    · have hrw : AffineMap.homothety z (1 - lam) x - (2:ℝ)⁻¹ • u + u
          = AffineMap.homothety z (1 - lam) x + (2:ℝ)⁻¹ • u := by
        module
      show AffineMap.homothety z (1 - lam) x - (2:ℝ)⁻¹ • u + u ∈ K
      rw [hrw]
      exact homothety_add_mem hKc hball hlam0 hlam1 hx hnorm
  have hvol : volume A = ENNReal.ofReal ((1 - lam) ^ n) * volume K := by
    have himg : A = (fun y => y - (2:ℝ)⁻¹ • u) ''
        (AffineMap.homothety z (1 - lam) '' K) := by
      rw [hAdef, Set.image_image]
    have hshift : ∀ B : Set (EuclideanSpace ℝ (Fin n)),
        volume ((fun y => y - (2:ℝ)⁻¹ • u) '' B) = volume B := by
      intro B
      have : (fun y : EuclideanSpace ℝ (Fin n) => y - (2:ℝ)⁻¹ • u) '' B
          = (fun y => y + (2:ℝ)⁻¹ • u) ⁻¹' B := by
        ext y
        constructor
        · rintro ⟨b, hb, rfl⟩; simpa using hb
        · intro hy; exact ⟨y + (2:ℝ)⁻¹ • u, hy, by simp⟩
      rw [this, measure_preimage_add_right]
    rw [himg, hshift, MeasureTheory.Measure.addHaar_image_homothety]
    congr 1
    rw [finrank_euclideanSpace_fin, abs_of_nonneg (pow_nonneg (by linarith) n)]
  calc ENNReal.ofReal ((1 - lam) ^ n) * volume K = volume A := hvol.symm
    _ ≤ volume (K ∩ (fun x => x + u) ⁻¹' K) := measure_mono hsub

/-- **The complementary form.**  `vol(K \ (K − u)) ≤ (n‖u‖ / 2r) · vol(K)`.

This is the direction-by-direction bound behind `(KLS-n)`.  It is essentially sharp: for a cone
whose height equals its base radius and `u` along the axis, the true value is within a factor
`1.21` of this bound.  Any improvement to `√n` must therefore average over the direction of `u`,
which is Cauchy's projection formula (see the module docstring). -/
theorem volume_sdiff_translate_le (hn : n ≠ 0) (hKc : Convex ℝ K) (hKm : MeasurableSet K)
    (hKfin : volume K ≠ ⊤) (hball : Metric.closedBall z r ⊆ K) (hr : 0 < r)
    (u : EuclideanSpace ℝ (Fin n)) :
    volume (K \ (fun x => x + u) ⁻¹' K)
      ≤ ENNReal.ofReal ((n : ℝ) * ‖u‖ / (2 * r)) * volume K := by
  have h2r : (0:ℝ) < 2 * r := by linarith
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  rcases le_or_gt 1 ((n : ℝ) * ‖u‖ / (2 * r)) with hbig | hsmall
  · -- the bound is vacuous
    refine le_trans (measure_mono Set.sdiff_subset) ?_
    calc volume K = 1 * volume K := (one_mul _).symm
      _ ≤ ENNReal.ofReal ((n : ℝ) * ‖u‖ / (2 * r)) * volume K :=
          mul_le_mul' (ENNReal.one_le_ofReal.mpr hbig) le_rfl
  · -- the substantial case
    set lam : ℝ := ‖u‖ / (2 * r) with hlamdef
    have hlam0 : 0 ≤ lam := by positivity
    have hlamn : (n : ℝ) * lam = (n : ℝ) * ‖u‖ / (2 * r) := by rw [hlamdef]; ring
    have hlam1 : lam ≤ 1 := by
      have : (n : ℝ) * lam < 1 := by rw [hlamn]; exact hsmall
      nlinarith
    have hu2r : ‖u‖ ≤ 2 * r := by rw [div_le_one h2r] at hlam1; exact hlam1
    have hSm : MeasurableSet ((fun x => x + u) ⁻¹' K) := hKm.preimage (measurable_add_const u)
    have hsplit : volume (K ∩ (fun x => x + u) ⁻¹' K) + volume (K \ (fun x => x + u) ⁻¹' K)
        = volume K := measure_inter_add_sdiff _ hSm
    -- Bernoulli
    have hbern : (1:ℝ) ≤ (n : ℝ) * lam + (1 - lam) ^ n := by
      have := one_add_mul_le_pow (a := -lam) (by linarith) n
      simp only [mul_neg] at this
      have hrw : (1 : ℝ) + -lam = 1 - lam := by ring
      rw [hrw] at this
      linarith
    have hle : volume K
        ≤ ENNReal.ofReal ((n : ℝ) * lam) * volume K
          + ENNReal.ofReal ((1 - lam) ^ n) * volume K := by
      rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (pow_nonneg (by linarith) n)]
      calc volume K = 1 * volume K := (one_mul _).symm
        _ ≤ _ := mul_le_mul' (ENNReal.one_le_ofReal.mpr hbern) le_rfl
    have hge := volume_inter_translate_ge hKc hball hr hu2r
    rw [← hlamdef] at hge
    rw [← hlamn]
    have hfin : volume (K ∩ (fun x => x + u) ⁻¹' K) ≠ ⊤ :=
      ne_top_of_le_ne_top hKfin (measure_mono Set.inter_subset_left)
    have : volume (K \ (fun x => x + u) ⁻¹' K)
        = volume K - volume (K ∩ (fun x => x + u) ⁻¹' K) := by
      rw [← hsplit]
      exact (ENNReal.add_sub_cancel_left hfin).symm
    rw [this, tsub_le_iff_right]
    exact le_trans hle (add_le_add le_rfl hge)

/-! ### The Fubini step and the main bound -/

/-- The `2n`-dimensional identity behind `(KLS-n)`:
`∫_K vol((x+tB) \ K) dx = ∫_{tB} vol(K \ (K−u)) du`.

Both sides compute the measure of `{(x,u) : x ∈ K, ‖u‖ ≤ t, x + u ∉ K}`. -/
theorem lintegral_volume_closedBall_sdiff_eq (hKm : MeasurableSet K) (t : ℝ) :
    ∫⁻ x in K, volume (Metric.closedBall x t \ K)
      = ∫⁻ u in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t,
          volume (K \ (fun x => x + u) ⁻¹' K) := by
  classical
  set B : Set (EuclideanSpace ℝ (Fin n)) := Metric.closedBall 0 t with hBdef
  have hBm : MeasurableSet B := measurableSet_closedBall
  set f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun x u => K.indicator 1 x * (B.indicator 1 u * (Kᶜ).indicator 1 (x + u)) with hfdef
  have hindic : ∀ (S : Set (EuclideanSpace ℝ (Fin n))) (v w : EuclideanSpace ℝ (Fin n)),
      S.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (v + w)
        = ((fun y => v + y) ⁻¹' S).indicator 1 w := by
    intro S v w
    simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
  -- the `u`-marginal
  have hx : ∀ x, ∫⁻ u, f x u = K.indicator 1 x * volume (Metric.closedBall x t \ K) := by
    intro x
    rw [hfdef]
    simp only
    rw [lintegral_const_mul' _ _ (by
      by_cases h : x ∈ K
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h])]
    congr 1
    have hset : ∀ u, B.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) u *
        (Kᶜ).indicator 1 (x + u)
        = (B ∩ ((fun y => x + y) ⁻¹' Kᶜ)).indicator 1 u := by
      intro u
      rw [hindic Kᶜ x u, one_indicator_mul]
    simp_rw [hset]
    rw [lintegral_indicator_one (hBm.inter ((hKm.compl).preimage (measurable_const_add x)))]
    have himg : B ∩ ((fun y => x + y) ⁻¹' Kᶜ)
        = (fun y => x + y) ⁻¹' (Metric.closedBall x t \ K) := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_sdiff, Set.mem_compl_iff, hBdef,
        Metric.mem_closedBall, dist_eq_norm, sub_zero]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by simpa using h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by simpa using h1, h2⟩
    rw [himg, measure_preimage_add]
  -- the `x`-marginal
  have hu : ∀ u, ∫⁻ x, f x u = B.indicator 1 u * volume (K \ (fun x => x + u) ⁻¹' K) := by
    intro u
    have hrw : ∀ x, f x u = B.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) u *
        (K.indicator 1 x * (Kᶜ).indicator 1 (x + u)) := by
      intro x; rw [hfdef]; ring
    simp_rw [hrw]
    rw [lintegral_const_mul' _ _ (by
      by_cases h : u ∈ B
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h])]
    congr 1
    have hset : ∀ x, K.indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) x *
        (Kᶜ).indicator 1 (x + u)
        = (K \ (fun y => y + u) ⁻¹' K).indicator 1 x := by
      intro x
      have h1 : (Kᶜ).indicator (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (x + u)
          = (((fun y => y + u) ⁻¹' K)ᶜ).indicator 1 x := by
        simp only [Set.indicator_apply, Set.mem_compl_iff, Set.mem_preimage, Pi.one_apply]
      rw [h1, one_indicator_mul, Set.sdiff_eq]
    simp_rw [hset]
    rw [lintegral_indicator_one (hKm.diff (hKm.preimage (measurable_add_const u)))]
  -- Tonelli
  have hmeas : Measurable (Function.uncurry f) := by
    rw [hfdef]
    exact ((measurable_one.indicator hKm).comp measurable_fst).mul
      (((measurable_one.indicator hBm).comp measurable_snd).mul
        ((measurable_one.indicator hKm.compl).comp (measurable_fst.add measurable_snd)))
  have hswap := lintegral_lintegral_swap (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (ν := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hmeas.aemeasurable
  simp_rw [hx, hu] at hswap
  have e1 : (∫⁻ x, K.indicator (fun y => volume (Metric.closedBall y t \ K)) x)
      = ∫⁻ x, K.indicator 1 x * volume (Metric.closedBall x t \ K) :=
    lintegral_congr fun x => (indicator_one_mul K _ x).symm
  have e2 : (∫⁻ u, B.indicator (fun v => volume (K \ (fun x => x + v) ⁻¹' K)) u)
      = ∫⁻ u, B.indicator 1 u * volume (K \ (fun x => x + u) ⁻¹' K) :=
    lintegral_congr fun u => (indicator_one_mul B _ u).symm
  rw [← lintegral_indicator hKm, ← lintegral_indicator hBm, e1, e2]
  exact hswap

/-- **`(KLS-n)`: Corollary 4.6 of Kannan–Lovász–Simonovits 1997, with `n` in place of `√n`.**

For a convex, measurable `K` of finite volume containing a ball of radius `r > 0`, and any
`t > 0`,

`∫_K vol((x + tB) \ K) dx ≤ (t·n / 2r) · vol(K) · vol(tB)`.

Unconditional: no inline hypotheses, nothing assumed.  The constant is `n`, not the paper's `√n`;
see the module docstring for why the `√n` is out of reach (it is Cauchy's projection formula) and
for what the loss costs downstream. -/
theorem lintegral_volume_closedBall_sdiff_le (hn : n ≠ 0) (hKc : Convex ℝ K)
    (hKm : MeasurableSet K) (hKfin : volume K ≠ ⊤) (hball : Metric.closedBall z r ⊆ K)
    (hr : 0 < r) (t : ℝ) :
    ∫⁻ x in K, volume (Metric.closedBall x t \ K)
      ≤ ENNReal.ofReal (t * (n : ℝ) / (2 * r)) * volume K
          * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) := by
  rw [lintegral_volume_closedBall_sdiff_eq hKm t]
  have hpt : ∀ u ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t,
      volume (K \ (fun x => x + u) ⁻¹' K)
        ≤ ENNReal.ofReal (t * (n : ℝ) / (2 * r)) * volume K := by
    intro u hu
    refine le_trans (volume_sdiff_translate_le hn hKc hKm hKfin hball hr u) ?_
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have hut : ‖u‖ ≤ t := by simpa [dist_eq_norm] using hu
    have h2r : (0:ℝ) < 2 * r := by linarith
    rw [div_le_div_iff_of_pos_right h2r, mul_comm t]
    exact mul_le_mul_of_nonneg_left hut (Nat.cast_nonneg n)
  calc ∫⁻ u in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t,
          volume (K \ (fun x => x + u) ⁻¹' K)
      ≤ ∫⁻ _ in Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t,
          ENNReal.ofReal (t * (n : ℝ) / (2 * r)) * volume K :=
        setLIntegral_mono' measurableSet_closedBall hpt
    _ = ENNReal.ofReal (t * (n : ℝ) / (2 * r)) * volume K
          * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) := by
        rw [setLIntegral_const]

/-- **`(KLS-n)` at inradius `1`**, in exactly the shape of the `hLem33` hypothesis carried by
`Arlib.volume_goodSet_ge` and `Arlib.lintegral_stepRadius_ge` — *except* that `Real.sqrt n` is
replaced by `(n : ℝ)`.

Because `√n ≤ n`, this is strictly weaker than `hLem33` for `n ≥ 2` and does **not** discharge it.
For `n = 1` the two statements coincide. -/
theorem lem33_const_n (hn : n ≠ 0) (hKc : Convex ℝ K) (hKm : MeasurableSet K)
    (hKfin : volume K ≠ ⊤)
    (hball : Metric.closedBall z 1 ⊆ K) :
    ∀ t : ℝ, 0 < t → ∫⁻ x in K, volume (Metric.closedBall x t \ K)
      ≤ ENNReal.ofReal (t * (n : ℝ) / 2) * volume K
          * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) t) := by
  intro t _ht
  have := lintegral_volume_closedBall_sdiff_le hn hKc hKm hKfin hball (by norm_num) t
  simpa using this

end KLS

end Arlib


