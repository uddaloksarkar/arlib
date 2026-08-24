/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.LovaszSmoothing
import Arlib.Convexity.Localization

/-!
# Lovász–Vempala's smoothing `f̂` at its true `1/16` normalisation

Lovász–Vempala, *The geometry of logconcave functions and sampling algorithms*, RSA
30(3):307–358, 2007, §6.1 defines the smoothing

    `f̂(x) = inf_C (1/vol C) ∫_C f(x+u) du`,   `C` convex `⊆ rB` with `vol(C) = ω_n rⁿ/16`,

i.e. at **one sixteenth** of the ball's volume.  `Arlib.MarkovChains.Continuous.LovaszSmoothing`
formalises instead the function of Cousins–Vempala's transcription
(`1409.6011/vol3_journal.tex:862`), which reads "a convex subset `D` of `δBₙ` of **half** its
volume".  This file formalises Lovász–Vempala's own function, `ballSmoothing16`, and reproves
the pointwise theory for it.

## Paper-oracle: three transcription defects in Cousins–Vempala's §"lem:lambda-bound"

1. **The volume in the definition of `f̂` is wrong.**  `vol3_journal.tex:862` says "half its
   volume"; Lovász–Vempala say `ω_n rⁿ/16`.  The half-ball appears in Lovász–Vempala only in
   the easy remark (16), `f̂(x) ≤ f(x)`.  The two functions are genuinely different; they are
   comparable only up to a constant (`ballSmoothing16_le_two_mul_ballSmoothing`, which *is*
   Lovász–Vempala's Lemma 6.1).  Consequently the hypothesis `hLov` carried by
   `avgLocalConductance_ge_half_of_lovasz` in `LovaszSmoothing.lean` is a statement about a
   function that Lovász–Vempala's Lemma 6.3 says nothing about;
   `avgLocalConductance_ge_half_of_lovasz16` here restates it about the right one.

2. **The definition of `a`-rounded is transcribed with the wrong quantifier.**
   `vol3_journal.tex:851` says "any level set `L` contains a ball of radius `a · μ_f(L)`"
   (universal).  Lovász–Vempala (p. 311) say: "a density function is `a`-rounded if for every
   `0 ≤ s ≤ 1` **it has a** level set `L` of probability at most `s` that contains a ball of
   radius `a·s`" (existential).  Cousins–Vempala's version is the *stronger* hypothesis, so
   their appeal to Lemma 6.3 is still sound provided the level-set measure takes the value
   `s` (true for a log-concave density), but the printed definition is not the source's.

3. **The printed proof chain at `vol3_journal.tex:869` does not compose as written** — line 1's
   numerator is missing `∩ K` and line 2's denominator must be `vol(δBₙ)`; and its last step
   treats `{y ∈ x+δBₙ : f(y) ≤ f(x)}` as an admissible index of the infimum, which it is not
   (it is neither convex nor of the prescribed volume).  This defect was already recorded in
   `LambdaBoundSharp`; it is repeated here because it is what the sharp constant rests on.

**Not a defect:** the constant of Lemma 6.3 itself.  Lovász–Vempala state
`∫_{ℝⁿ} f̂ ≥ 1 − 32 r^{1/2} n^{1/4} / a^{1/2}`, which is Cousins–Vempala's
`1 − 32 δ^{1/2} n^{1/4} / a^{1/2}` verbatim after `r ↦ δ`.  (Internal check: at `a = 1/4` this
is the `1 − 64 r^{1/2} n^{1/4}` they quote for the isotropic case.)  Nothing was weakened
there.

## PROVED here, unconditionally

* **`exists_volume_cut_eq`** — a bounded measurable set can be cut by a hyperplane of any
  prescribed direction at any prescribed volume.  The content is that `t ↦ vol(S ∩ {φ ≤ t})`
  is continuous (`continuous_volume_cut`), which holds because level hyperplanes are null.
* **`exists_convex_partition`** — the parallel slicing of Lovász–Vempala's Lemma 6.1: a bounded
  convex measurable set of volume `k·w` splits into `k` disjoint convex measurable pieces of
  volume exactly `w`.
* **`ballSmoothing16`** (`def`) — Lovász–Vempala's `f̂`, verbatim except that the index set is
  restricted to *measurable* `C` and the minimum is an infimum.  The restriction shrinks the
  index set, so `ballSmoothing16 ≥` the paper's `f̂`: every upper bound proved here holds a
  fortiori for the paper's `f̂`, and every lower bound on `∫_K` of the paper's `f̂` holds a
  fortiori for `∫_K ballSmoothing16`.  Both consumers compose in the safe direction.
* **`exists_eight_sixteenthBalls`** — a half-ball splits into exactly eight admissible pieces.
* **`ballSmoothing16_le_self`** — Lovász–Vempala's inequality (16), `f̂ ≤ f`.  Sharp.
* **`ballSmoothing16_le_two_mul_ell_mul`** — the pointwise step `f̂(x) ≤ 2·ℓ(x)·f(x)`.
* **`ballSmoothing16_le_ell_mul_of_balanced`** — the **sharp** `f̂(x) ≤ ℓ(x)·f(x)` whenever some
  separating half of the proposal ball carries at most half of `K`'s share of that ball.
* **`ballSmoothing16_eq_zero_of_far_half_free`** — the sharp bound (indeed `f̂(x) = 0`) in the
  opposite extreme, when all of `K`'s share lies strictly on the near side.
* **`exists_balanced_dual_of_isMax` / `ballSmoothing16_le_ell_mul_of_isMax`** — the **sharp**
  constant holds outright at every maximum point of `f` (so at the mode of a log-concave
  density, and everywhere for a uniform density): with an empty superlevel set every
  hyperplane separates, and one of the two halves is the balanced one.
* **`ballSmoothing16_mul_volume_le_two_mul`** — **Lovász–Vempala Lemma 6.1**, with their
  constant `2`, in full generality.
* **`isLogConcaveENN_ballSmoothing16`** — **Lovász–Vempala Lemma 6.2**: `f̂` is log-concave.
  Their proof, via the repository's Prékopa–Leindler marginal lemma
  (`Arlib.isLogConcaveENN_marginal_prod`) transported from `Fin n → ℝ` to
  `EuclideanSpace ℝ (Fin n)` along `WithLp.toLp`.
* **`lovasz16_bound_indicator_ball`** — a genuine, proved instance of the *conclusion* of
  Lemma 6.3 for `ballSmoothing16`.

## NOT proved, and why

**Lovász–Vempala Lemma 6.3 and Lemma 6.4 are not formalised.**  Lemma 6.4 ("`K` convex
containing a ball of radius `t`, `X` uniform in `K`, `Y` uniform in `X + sB`; then
`P(Y ∉ K) ≤ s√n/(2t)`") is Corollary 4.6 of Kannan–Lovász–Simonovits, *Random walks and an
O*(n⁵) volume algorithm*, RSA 11 (1997) §4.2, whose proof runs through the surface area:
`P ≤ (δ/(2√n))·vol_{n−1}(∂K)/vol(K)` (their Corollary 4.5) together with
`vol(K) ≥ (r/n)·vol_{n−1}(∂K)`.  **Mathlib has no `(n−1)`-dimensional surface measure of a
convex body** in a usable form — no boundary Hausdorff measure with the Cauchy/Fubini
projection formula, no `vol(K) ≥ (r/n)·area(∂K)`.  Building that development is out of scope
here, and inventing a surrogate would be worse than saying so.  Lemma 6.3 is therefore carried
as the binder `hLov` of `avgLocalConductance_ge_half_of_lovasz16` and
`avgLocalConductance_ge_of_lovasz16_balanced`, exactly as before — but now stated about
Lovász–Vempala's own `f̂`.

**The sharp pointwise step is not proved unconditionally**, and the factor `2` here is *not*
the factor `2` of `LovaszSmoothing.lean`.  That file's factor `2` came with a counterexample
showing it is a hard limit *of the half-volume definition*; that counterexample **dies** at
the `1/16` normalisation, because there is now room to slide the index set `C` off `K`
(checked by hand, **not** formalised here).  So the constant `2` proved here is not known to
be optimal.  What *is* structural is this:

> the separating half-ball has volume `vol(δBₙ)/2`, so it contains **exactly eight** pairwise
> disjoint admissible pieces, never sixteen (`exists_eight_sixteenthBalls`).  Any argument
> whose only input is "log-concavity gives a half-ball on which `f ≤ f(x)`" therefore yields
> `min_i ∫_{Pᵢ} f ≤ (1/8)·f(x)·vol(B(x,δ) ∩ K)`, i.e. `f̂(x) ≤ 2·ℓ(x)·f(x)`, and cannot do
> better.

Reaching `ℓ(x)·f(x)` needs a genuine dichotomy: when the separating half carries more than
half of `K ∩ B(x,δ)` one must place `C` in the *opposite* half, where `f` may exceed `f(x)`,
and control it by the fact that `K` is thin there.  The two proved cases
(`ballSmoothing16_le_ell_mul_of_balanced` and `ballSmoothing16_eq_zero_of_far_half_free`) are
the two ends of that dichotomy; closing the middle needs quantitative spherical-cap volume
estimates that are not in Mathlib either.  Cousins–Vempala's three displayed lines contain no
such argument.

## Scope

The only `def` is `ballSmoothing16` and the only `structure` is `IsSixteenthBall`; neither name
asserts an identity that is not either definitional or proved.  Nothing here is a conductance,
mixing-time or polynomial-time statement.  `avgLocalConductance_ge_half_of_lovasz16` and
`avgLocalConductance_ge_of_lovasz16_balanced` each carry exactly one unproved binder, `hLov`;
`exists_lovasz16_balanced_instance` is a non-vacuity witness for the second in which `hLov`
*and* the balance condition are both **proved**, not assumed.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1. Cutting a set by a hyperplane at a prescribed volume -/

/-- A nonzero functional is surjective. -/
theorem exists_apply_eq {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0) (s : ℝ) :
    ∃ z, φ z = s := by
  obtain ⟨z₀, hz₀⟩ : ∃ z, φ z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (ContinuousLinearMap.ext h)
  exact ⟨(s / φ z₀) • z₀, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hz₀]⟩

/-- Every level hyperplane of a nonzero functional is Lebesgue-null. -/
theorem volume_setOf_apply_eq {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0) (s : ℝ) :
    volume {z : EuclideanSpace ℝ (Fin n) | φ z = s} = 0 := by
  obtain ⟨x, hx⟩ := exists_apply_eq hφ s
  have h := volume_setOf_eq_apply hφ x
  rwa [hx] at h

/-- **The cut volume is continuous in the cut level.**  For a measurable set `S` of finite
volume and a nonzero functional `φ`, `t ↦ vol(S ∩ {φ ≤ t})` is continuous: the only
discontinuity could come from an atom of the pushforward, i.e. from a level hyperplane of
positive volume, and there are none. -/
theorem continuous_volume_cut {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    (hSfin : volume S ≠ ⊤) {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0) :
    Continuous fun t : ℝ => (volume (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t})).toReal := by
  have hmeas : ∀ t : ℝ, MeasurableSet (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t}) := fun t =>
    hS.inter (measurableSet_le φ.continuous.measurable measurable_const)
  have hEq : ∀ t : ℝ, (volume (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t})).toReal
      = ∫ z, (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t}).indicator (fun _ => (1 : ℝ)) z := by
    intro t
    rw [integral_indicator_const _ (hmeas t)]
    simp [MeasureTheory.measureReal_def]
  simp only [hEq]
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, Filter.tendsto_iff_seq_tendsto]
  intro u hu
  have hbound : Integrable (S.indicator fun _ => (1 : ℝ)) := by
    rw [integrable_indicator_iff hS]
    exact integrableOn_const (C := (1 : ℝ)) hSfin (by simp)
  refine tendsto_integral_of_dominated_convergence (S.indicator fun _ => (1 : ℝ))
    (fun k => ((measurable_const.indicator (hmeas (u k)))).aestronglyMeasurable) hbound
    (fun k => Filter.Eventually.of_forall fun z => ?_) ?_
  · by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
      by_cases hz2 : z ∈ S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ u k}
      · rw [Set.indicator_of_mem hz2]; simp
      · rw [Set.indicator_of_notMem hz2]; simp
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz h.1)]
      simp
  · have hnull : volume {z : EuclideanSpace ℝ (Fin n) | φ z = s} = 0 := volume_setOf_apply_eq hφ s
    have hae : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), φ z ≠ s := by
      rw [MeasureTheory.ae_iff]
      simpa using hnull
    refine Filter.Eventually.mono hae ?_
    intro z hz
    by_cases hzS : z ∈ S
    · rcases lt_or_gt_of_ne (show φ z ≠ s from hz) with hlt | hgt
      · have h1 : ∀ᶠ k in Filter.atTop, φ z ≤ u k := by
          have := hu.eventually (eventually_gt_nhds hlt)
          exact this.mono fun k hk => hk.le
        have h2 : (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ s}).indicator
            (fun _ => (1 : ℝ)) z = 1 :=
          Set.indicator_of_mem (Set.mem_inter hzS hlt.le) _
        rw [h2]
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        exact h1.mono fun k hk =>
          (Set.indicator_of_mem (s := S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ u k})
            (Set.mem_inter hzS hk) (fun _ => (1 : ℝ))).symm
      · have h1 : ∀ᶠ k in Filter.atTop, ¬ (φ z ≤ u k) := by
          have := hu.eventually (eventually_lt_nhds hgt)
          exact this.mono fun k hk => not_le.2 hk
        have h2 : (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ s}).indicator
            (fun _ => (1 : ℝ)) z = 0 :=
          Set.indicator_of_notMem (fun h => absurd h.2 (not_le.2 hgt)) _
        rw [h2]
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        exact h1.mono fun k hk => (Set.indicator_of_notMem (fun h => hk h.2) _).symm
    · have h2 : ∀ t : ℝ, (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t}).indicator
          (fun _ => (1 : ℝ)) z = 0 := fun t => Set.indicator_of_notMem (fun h => hzS h.1) _
      simp only [h2]
      exact tendsto_const_nhds

/-- **Cutting at a prescribed volume.**  A bounded measurable set can be cut by a hyperplane
with prescribed normal `φ` so that the lower piece has any prescribed volume `v ≤ vol S`.
This is the intermediate value theorem applied to `continuous_volume_cut`. -/
theorem exists_volume_cut_eq {S : Set (EuclideanSpace ℝ (Fin n))} (hS : MeasurableSet S)
    {R : ℝ} (hSR : S ⊆ ball 0 R) {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0)
    {v : ℝ≥0∞} (hv : v ≤ volume S) :
    ∃ t : ℝ, volume (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t}) = v := by
  have hSfin : volume S ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hSR)
  have hvtop : v ≠ ⊤ := ne_top_of_le_ne_top hSfin hv
  set M : ℝ := ‖φ‖ * |R| + 1 with hM
  have hbdd : ∀ z ∈ S, |φ z| < M := by
    intro z hz
    have h1 : ‖z‖ < R := by simpa [mem_ball, dist_zero_right] using hSR hz
    have h2 : |φ z| ≤ ‖φ‖ * ‖z‖ := φ.le_opNorm z
    have h3 : ‖z‖ ≤ |R| := le_trans h1.le (le_abs_self R)
    have h4 : ‖φ‖ * ‖z‖ ≤ ‖φ‖ * |R| := by
      exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    rw [hM]
    linarith
  have hMpos : (0 : ℝ) ≤ M := by
    have : (0 : ℝ) ≤ ‖φ‖ * |R| := mul_nonneg (norm_nonneg _) (abs_nonneg _)
    rw [hM]; linarith
  have htop : S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ M} = S := by
    refine Set.inter_eq_self_of_subset_left fun z hz => ?_
    exact le_of_lt (lt_of_le_of_lt (le_abs_self _) (hbdd z hz))
  have hbot : S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ -M} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hz, hz2⟩
    have h := hbdd z hz
    have : -M < φ z := by
      have := abs_lt.1 h
      exact this.1
    exact absurd hz2 (not_le.2 this)
  set G : ℝ → ℝ := fun t => (volume (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t})).toReal with hG
  have hGcont : Continuous G := continuous_volume_cut hS hSfin hφ
  have hGbot : G (-M) = 0 := by simp [hG, hbot]
  have hGtop : G M = (volume S).toReal := by simp [hG, htop]
  have hmem : v.toReal ∈ Set.Icc (G (-M)) (G M) := by
    rw [hGbot, hGtop]
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hSfin hv⟩
  obtain ⟨t, -, hteq⟩ :=
    intermediate_value_Icc (by linarith : (-M : ℝ) ≤ M) hGcont.continuousOn hmem
  refine ⟨t, ?_⟩
  have hfin : volume (S ∩ {z : EuclideanSpace ℝ (Fin n) | φ z ≤ t}) ≠ ⊤ :=
    ne_top_of_le_ne_top hSfin (measure_mono Set.inter_subset_left)
  rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_toReal hvtop]
  exact congrArg ENNReal.ofReal hteq

/-- **Parallel slicing.**  A bounded convex measurable set of volume `k · w` can be cut by
`k − 1` parallel hyperplanes into `k` pairwise disjoint convex measurable pieces, each of
volume exactly `w`.  This is the decomposition used in Lovász–Vempala's Lemma 6.1. -/
theorem exists_convex_partition {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0) {R : ℝ} :
    ∀ (k : ℕ) {S : Set (EuclideanSpace ℝ (Fin n))}, MeasurableSet S → S ⊆ ball 0 R →
      Convex ℝ S → ∀ {w : ℝ≥0∞}, volume S = k * w →
      ∃ P : Fin k → Set (EuclideanSpace ℝ (Fin n)),
        (∀ i, Convex ℝ (P i)) ∧ (∀ i, MeasurableSet (P i)) ∧ (∀ i, P i ⊆ S) ∧
        (∀ i, volume (P i) = w) ∧ Pairwise (Function.onFun Disjoint P) := by
  intro k
  induction k with
  | zero =>
      intro S _ _ _ w _
      exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0⟩
  | succ k ih =>
      intro S hS hSR hSconv w hvol
      have hSfin : volume S ≠ ⊤ :=
        ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hSR)
      have hwtop : w ≠ ⊤ := by
        intro h
        rw [h, ENNReal.mul_top (by exact_mod_cast Nat.succ_ne_zero k)] at hvol
        exact hSfin hvol
      have hwle : w ≤ volume S := by
        rw [hvol, Nat.cast_succ]
        calc w = 1 * w := (one_mul w).symm
          _ ≤ ((k : ℝ≥0∞) + 1) * w := by
              exact mul_le_mul_right' (by simp) w
      obtain ⟨t, ht⟩ := exists_volume_cut_eq hS hSR hφ hwle
      set A : Set (EuclideanSpace ℝ (Fin n)) := S ∩ {z | φ z ≤ t} with hA
      set B : Set (EuclideanSpace ℝ (Fin n)) := S ∩ {z | t < φ z} with hB
      have hAmeas : MeasurableSet A :=
        hS.inter (measurableSet_le φ.continuous.measurable measurable_const)
      have hBmeas : MeasurableSet B :=
        hS.inter (measurableSet_lt measurable_const φ.continuous.measurable)
      have hAconv : Convex ℝ A := hSconv.inter
        (convex_halfSpace_le (f := fun z => φ z)
          ⟨fun a b => φ.map_add a b, fun c a => φ.map_smul c a⟩ t)
      have hBconv : Convex ℝ B := hSconv.inter
        (convex_halfSpace_gt (f := fun z => φ z)
          ⟨fun a b => φ.map_add a b, fun c a => φ.map_smul c a⟩ t)
      have hBeq : B = S \ A := by
        ext z
        simp only [hA, hB, Set.mem_inter_iff, Set.mem_diff, Set.mem_setOf_eq, not_and, not_le]
        exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
      have hBvol : volume B = k * w := by
        rw [hBeq, measure_diff Set.inter_subset_left hAmeas.nullMeasurableSet
          (ne_top_of_le_ne_top hSfin (measure_mono Set.inter_subset_left)), ht, hvol,
          Nat.cast_succ, add_mul, one_mul]
        exact ENNReal.add_sub_cancel_right hwtop
      obtain ⟨Q, hQconv, hQmeas, hQsub, hQvol, hQdisj⟩ :=
        ih hBmeas (hBeq ▸ (Set.diff_subset.trans hSR)) hBconv hBvol
      have hBsubS : B ⊆ S := by rw [hBeq]; exact Set.diff_subset
      have hABdisj : ∀ i, Disjoint A (Q i) := by
        intro i
        refine Set.disjoint_left.2 fun z hzA hzQ => ?_
        have h := hQsub i hzQ
        rw [hBeq] at h
        exact h.2 hzA
      obtain ⟨P, hP0, hPs⟩ : ∃ P : Fin (k + 1) → Set (EuclideanSpace ℝ (Fin n)),
          P 0 = A ∧ ∀ i : Fin k, P i.succ = Q i :=
        ⟨Fin.cons A Q, Fin.cons_zero _ _, fun i => Fin.cons_succ _ _ i⟩
      have hconv : ∀ i, Convex ℝ (P i) := by
        refine Fin.cases ?_ ?_
        · rw [hP0]; exact hAconv
        · intro i; rw [hPs]; exact hQconv i
      have hmeas : ∀ i, MeasurableSet (P i) := by
        refine Fin.cases ?_ ?_
        · rw [hP0]; exact hAmeas
        · intro i; rw [hPs]; exact hQmeas i
      have hsub : ∀ i, P i ⊆ S := by
        refine Fin.cases ?_ ?_
        · rw [hP0]; exact Set.inter_subset_left
        · intro i; rw [hPs]; exact (hQsub i).trans hBsubS
      have hvols : ∀ i, volume (P i) = w := by
        refine Fin.cases ?_ ?_
        · rw [hP0]; exact ht
        · intro i; rw [hPs]; exact hQvol i
      have hdisj : ∀ i j : Fin (k + 1), i ≠ j → Disjoint (P i) (P j) := by
        refine Fin.cases ?_ ?_
        · refine Fin.cases ?_ ?_
          · intro h; exact absurd rfl h
          · intro j' _
            rw [hP0, hPs]
            exact hABdisj j'
        · intro i'
          refine Fin.cases ?_ ?_
          · intro _
            rw [hP0, hPs]
            exact (hABdisj i').symm
          · intro j' hij
            rw [hPs, hPs]
            exact hQdisj (fun h => hij (by rw [h]))
      exact ⟨P, hconv, hmeas, hsub, hvols, fun i j hij => hdisj i j hij⟩

/-- In a family of `k > 0` nonnegative extended reals whose sum is at most `A`, some member
is at most `A/k`, in the multiplication-free form `k · aᵢ ≤ A`. -/
theorem exists_nsmul_le_of_sum_le {k : ℕ} (hk : 0 < k) (a : Fin k → ℝ≥0∞) {A : ℝ≥0∞}
    (h : ∑ i, a i ≤ A) : ∃ i, (k : ℝ≥0∞) * a i ≤ A := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin k)) a ⟨⟨0, hk⟩, by simp⟩
  refine ⟨i₀, le_trans ?_ h⟩
  have hcard : (Finset.univ : Finset (Fin k)).card • a i₀ ≤ ∑ i, a i :=
    Finset.card_nsmul_le_sum _ _ _ fun i _ => hi₀ i (Finset.mem_univ i)
  simpa [nsmul_eq_mul] using hcard

/-! ## 2. The smoothing at Lovász–Vempala's `1/16` normalisation -/

/-- `IsSixteenthBall δ D` says `D` is a convex measurable subset of `δBₙ` of exactly **one
sixteenth** of its volume.  This — not "half its volume" — is the index set of the minimum in
Lovász–Vempala §6.1:

> `f̂(x) = inf_C (1/vol C) ∫_C f(x+u) du`, where `C` ranges over all convex subsets of the
> ball `rB` with `vol(C) = ω_n rⁿ/16`.

Cousins–Vempala (`1409.6011/vol3_journal.tex:862`) transcribe this as "a convex subset `D` of
`δBₙ` of half its volume", which is a different function; see the module docstring. -/
structure IsSixteenthBall (δ : ℝ) (D : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  convex : Convex ℝ D
  measurableSet : MeasurableSet D
  subset_ball : D ⊆ ball 0 δ
  sixteen_mul_volume : 16 * volume D = volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ)

theorem IsSixteenthBall.volume_ne_top {δ : ℝ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsSixteenthBall δ D) : volume D ≠ ⊤ :=
  ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hD.subset_ball)

theorem IsSixteenthBall.volume_ne_zero {δ : ℝ} (hδ : 0 < δ)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsSixteenthBall δ D) : volume D ≠ 0 := by
  intro h
  have h16 := hD.sixteen_mul_volume
  rw [h, mul_zero] at h16
  exact (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hδ).ne' h16.symm

/-- **The Lovász–Vempala smoothing** (RSA 30(3):307–358, §6.1),

    `f̂(x) = inf_C (∫_{y ∈ x+C} f(y) dy) / vol(C)`,

the infimum over convex **measurable** subsets `C ⊆ δBₙ` with `16·vol(C) = vol(δBₙ)`.

Two deviations from the printed formula, both recorded here rather than hidden in a name:

* the `inf` is a `⨅` — Lovász–Vempala speak of the convex set "attaining the minimum";
  nothing below needs attainment;
* the index set additionally requires `C` to be **measurable**, without which `∫_{x+C} f` and
  `vol(C)` are not the quantities the paper means.  This *shrinks* the index set, so
  `ballSmoothing16 f δ x ≥` the paper's `f̂(x)`: every upper bound proved here is a fortiori
  an upper bound for the paper's `f̂`, and every lower bound on `∫_K` of the paper's `f̂` is a
  fortiori one for `∫_K ballSmoothing16`.  Both consumers compose in the safe direction. -/
noncomputable def ballSmoothing16 (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨅ D ∈ {D : Set (EuclideanSpace ℝ (Fin n)) | IsSixteenthBall δ D},
    (∫⁻ y in x +ᵥ D, f y) / volume D

/-- Any single admissible `D` bounds `ballSmoothing16` from above. -/
theorem ballSmoothing16_le {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {δ : ℝ}
    (x : EuclideanSpace ℝ (Fin n)) {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsSixteenthBall δ D) :
    ballSmoothing16 f δ x ≤ (∫⁻ y in x +ᵥ D, f y) / volume D :=
  iInf₂_le (f := fun D (_ : D ∈ {D : Set (EuclideanSpace ℝ (Fin n)) | IsSixteenthBall δ D}) =>
    (∫⁻ y in x +ᵥ D, f y) / volume D) D hD

/-- `ballSmoothing16` is bounded below by `c` as soon as every admissible `D` is. -/
theorem le_ballSmoothing16 {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {δ : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {c : ℝ≥0∞}
    (h : ∀ D : Set (EuclideanSpace ℝ (Fin n)), IsSixteenthBall δ D →
      c ≤ (∫⁻ y in x +ᵥ D, f y) / volume D) :
    c ≤ ballSmoothing16 f δ x :=
  le_iInf₂ h

/-- The multiplication-free form of `ballSmoothing16_le`. -/
theorem ballSmoothing16_mul_volume_le {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {δ : ℝ}
    (hδ : 0 < δ) (x : EuclideanSpace ℝ (Fin n)) {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsSixteenthBall δ D) :
    ballSmoothing16 f δ x * volume D ≤ ∫⁻ y in x +ᵥ D, f y := by
  refine le_trans (mul_le_mul_right' (ballSmoothing16_le x hD) _) ?_
  rw [ENNReal.div_mul_cancel (hD.volume_ne_zero hδ) hD.volume_ne_top]

/-! ### Sixteenth-balls exist, and eight of them fill a half-ball -/

/-- **Eight sixteenths of the ball fill a half-ball.**  The half of `δBₙ` cut off by a
hyperplane through the centre splits, by seven parallel cuts, into eight pairwise disjoint
convex pieces, each an admissible index of `ballSmoothing16`.  Eight is the largest number of
disjoint `1/16`-pieces a half-ball can hold, and that is exactly why the half-ball route
cannot beat the constant `2`; see the module docstring. -/
theorem exists_eight_sixteenthBalls {δ : ℝ}
    {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0) :
    ∃ P : Fin 8 → Set (EuclideanSpace ℝ (Fin n)),
      (∀ i, IsSixteenthBall δ (P i)) ∧
      (∀ i, P i ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) δ ∩ {z | φ z ≤ 0}) ∧
      Pairwise (Function.onFun Disjoint P) := by
  set H : Set (EuclideanSpace ℝ (Fin n)) := ball 0 δ ∩ {z | φ z ≤ 0} with hH
  have hHhalf : IsHalfBall δ H := isHalfBall_ball_inter_halfSpace hφ
  have hHtop : volume H ≠ ⊤ := hHhalf.volume_ne_top
  have hcancel : 8 * (volume H / 8) = volume H :=
    ENNReal.mul_div_cancel' (by norm_num) (by norm_num)
  have h16 : 16 * (volume H / 8) = volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) := by
    rw [show (16 : ℝ≥0∞) = 2 * 8 by norm_num, mul_assoc, hcancel]
    exact hHhalf.two_mul_volume
  obtain ⟨P, hconv, hmeas, hsub, hvol, hdisj⟩ :=
    exists_convex_partition (φ := φ) hφ (R := δ) 8 hHhalf.measurableSet hHhalf.subset_ball
      hHhalf.convex (w := volume H / 8) (by simpa using hcancel.symm)
  refine ⟨P, fun i => ⟨hconv i, hmeas i, (hsub i).trans hHhalf.subset_ball, ?_⟩, hsub, hdisj⟩
  rw [hvol i]
  exact h16

/-- Sixteenth-balls exist as soon as `δ > 0` and the space is nontrivial. -/
theorem exists_isSixteenthBall (hn : 1 ≤ n) (δ : ℝ) :
    ∃ D : Set (EuclideanSpace ℝ (Fin n)), IsSixteenthBall δ D := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  obtain ⟨φ, hφ1, -⟩ := exists_dual_vector ℝ v (by simpa using hv)
  have hφ0 : φ ≠ 0 := by
    intro h
    rw [h] at hφ1
    simp at hφ1
  obtain ⟨P, hP, -, -⟩ := exists_eight_sixteenthBalls (δ := δ) hφ0
  exact ⟨P 0, hP 0⟩

/-! ## 3. The pointwise step -/

/-- Translation is monotone on sets. -/
theorem vadd_set_subset_vadd_set (x : EuclideanSpace ℝ (Fin n))
    {A B : Set (EuclideanSpace ℝ (Fin n))} (h : A ⊆ B) : x +ᵥ A ⊆ x +ᵥ B := by
  rw [vadd_set_eq_preimage, vadd_set_eq_preimage]
  exact Set.preimage_mono h

/-- Translation preserves disjointness. -/
theorem disjoint_vadd_set (x : EuclideanSpace ℝ (Fin n))
    {A B : Set (EuclideanSpace ℝ (Fin n))} (h : Disjoint A B) :
    Disjoint (x +ᵥ A) (x +ᵥ B) := by
  rw [vadd_set_eq_preimage, vadd_set_eq_preimage]
  exact h.preimage _

/-- **The separation bound.**  If the functional `φ` separates `x` from the strict superlevel
set `{y : f(x) < f(y)}` — which is what log-concavity of `f` supplies — then on *any*
measurable set `A` lying in the closed half-space `{φ ≤ φ x}`,

    `∫_A f ≤ vol(A ∩ K)·f(x)`,

because `f ≤ f(x)` on the open half-space, `f = 0` off `K`, and the bounding hyperplane is
Lebesgue-null. -/
theorem lintegral_le_of_sep {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    {x : EuclideanSpace ℝ (Fin n)} {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ0 : φ ≠ 0)
    (hφ : ∀ y, f x < f y → φ x ≤ φ y)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hAsub : A ⊆ {y | φ y ≤ φ x}) :
    (∫⁻ y in A, f y) ≤ volume (A ∩ K) * f x := by
  set A' : Set (EuclideanSpace ℝ (Fin n)) := A ∩ {y | φ y < φ x} with hA'def
  have hmA' : MeasurableSet A' :=
    hA.inter (measurableSet_lt φ.continuous.measurable measurable_const)
  have hae : A =ᵐ[volume] A' := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null (fun y hy => ?_) (volume_setOf_eq_apply hφ0 x)
      have h1 : φ y ≤ φ x := hAsub hy.1
      have h2 : ¬ (y ∈ A ∧ φ y < φ x) := hy.2
      simp only [mem_setOf_eq]
      by_contra hne
      exact h2 ⟨hy.1, lt_of_le_of_ne h1 hne⟩
    · have hemp : A' \ A = ∅ := by
        rw [Set.sdiff_eq_empty]
        exact fun y hy => hy.1
      rw [hemp]
      exact measure_empty
  have hmAK : MeasurableSet (A ∩ K) := hA.inter hK
  rw [Measure.restrict_congr_set hae]
  calc ∫⁻ y in A', f y
      = ∫⁻ y, A'.indicator f y := (lintegral_indicator hmA' f).symm
    _ ≤ ∫⁻ y, (A ∩ K).indicator (fun _ => f x) y := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ A'
        · rw [Set.indicator_of_mem hy]
          by_cases hyK : y ∈ K
          · rw [Set.indicator_of_mem (Set.mem_inter hy.1 hyK)]
            by_contra hcon
            push Not at hcon
            exact absurd (hφ y hcon) (not_le.2 hy.2)
          · rw [hfK y hyK]; simp
        · rw [Set.indicator_of_notMem hy]; simp
    _ = volume (A ∩ K) * f x := by
        rw [lintegral_indicator hmAK, setLIntegral_const, mul_comm]

/-- The eight pieces of the separating half of `B(x,δ)`, translated to `x`. -/
private theorem exists_eight_pieces_at {K : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {δ : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ0 : φ ≠ 0) (hK : MeasurableSet K)
    (hfK : ∀ y, y ∉ K → f y = 0) (hφ : ∀ y, f x < f y → φ x ≤ φ y) :
    ∃ D : Set (EuclideanSpace ℝ (Fin n)), IsSixteenthBall δ D ∧
      8 * (∫⁻ y in x +ᵥ D, f y)
        ≤ volume (ball x δ ∩ {y | φ y ≤ φ x} ∩ K) * f x := by
  obtain ⟨P, hP, hPsub, hPdisj⟩ := exists_eight_sixteenthBalls (δ := δ) hφ0
  set S : Set (EuclideanSpace ℝ (Fin n)) := ball x δ ∩ {y | φ y ≤ φ x} with hS
  have hSeq : x +ᵥ (ball (0 : EuclideanSpace ℝ (Fin n)) δ ∩ {z | φ z ≤ 0}) = S :=
    vadd_ball_inter_halfSpace x
  have hmS : MeasurableSet S :=
    measurableSet_ball.inter (measurableSet_le φ.continuous.measurable measurable_const)
  have hPS : ∀ i, (x +ᵥ P i) ⊆ S := fun i => hSeq ▸ vadd_set_subset_vadd_set x (hPsub i)
  have hsum : ∑ i, (∫⁻ y in x +ᵥ P i, f y) ≤ ∫⁻ y in S, f y := by
    calc ∑ i, (∫⁻ y in x +ᵥ P i, f y)
        = ∑' i, (∫⁻ y in x +ᵥ P i, f y) := (tsum_fintype _).symm
      _ = ∫⁻ y in ⋃ i, (x +ᵥ P i), f y :=
          (lintegral_iUnion (fun i => measurableSet_vadd_set (hP i).measurableSet x)
            (fun i j hij => disjoint_vadd_set x (hPdisj hij)) f).symm
      _ ≤ ∫⁻ y in S, f y :=
          lintegral_mono' (Measure.restrict_mono (Set.iUnion_subset hPS) le_rfl) le_rfl
  have hSbound : (∫⁻ y in S, f y) ≤ volume (S ∩ K) * f x :=
    lintegral_le_of_sep hK hfK hφ0 hφ hmS Set.inter_subset_right
  obtain ⟨i, hi⟩ := exists_nsmul_le_of_sum_le (by norm_num)
    (fun i => ∫⁻ y in x +ᵥ P i, f y) (hsum.trans hSbound)
  exact ⟨P i, hP i, by simpa using hi⟩

/-- **`f̂ ≤ f` at the `1/16` normalisation** — Lovász–Vempala's inequality (16), and it is
sharp.  Their one-line justification is: "by the log-concavity of `f`, the level set
`{f ≥ f(x)}` is convex, and hence there is a half-ball of `B` on which `f ≤ f(x)`". -/
theorem ballSmoothing16_le_self (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    {δ : ℝ} (hδ : 0 < δ) {x : EuclideanSpace ℝ (Fin n)}
    (hquasi : Convex ℝ {y : EuclideanSpace ℝ (Fin n) | f x < f y}) :
    ballSmoothing16 f δ x ≤ f x := by
  obtain ⟨φ, hφ0, hφ⟩ := exists_dual_le_on_of_notMem hn hquasi (x := x) (by simp)
  obtain ⟨P, hP, hPsub, -⟩ := exists_eight_sixteenthBalls (δ := δ) hφ0
  have hsub : (x +ᵥ P 0) ⊆ {y : EuclideanSpace ℝ (Fin n) | φ y ≤ φ x} := by
    refine le_trans (vadd_set_subset_vadd_set x (hPsub 0)) ?_
    rw [vadd_ball_inter_halfSpace x]
    exact Set.inter_subset_right
  have hbound : (∫⁻ y in x +ᵥ P 0, f y) ≤ volume (P 0) * f x := by
    refine le_trans (lintegral_le_of_sep hK hfK hφ0 hφ
      (measurableSet_vadd_set (hP 0).measurableSet x) hsub) ?_
    refine le_trans (mul_le_mul_right' (measure_mono Set.inter_subset_left) _) ?_
    rw [volume_vadd_set]
  refine (ballSmoothing16_le x (hP 0)).trans (ENNReal.div_le_of_le_mul ?_)
  rw [mul_comm]
  exact hbound

/-- **The pointwise step at the `1/16` normalisation, with a factor `2`.**

For a function `f` vanishing off `K` whose strict superlevel set at `x` is convex — implied
by, and strictly weaker than, log-concavity of `f` —

    `f̂(x) ≤ 2 · ℓ(x) · f(x)`.

Cousins–Vempala claim this without the factor `2` (`vol3_journal.tex:869`).  The factor `2`
here is *not* the one produced by their half-volume definition: it survives the passage to
Lovász–Vempala's correct `1/16` volume, and for a structural reason recorded in the module
docstring — the separating half-ball holds exactly eight disjoint sixteenths, never sixteen. -/
theorem ballSmoothing16_le_two_mul_ell_mul (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    {δ : ℝ} (hδ : 0 < δ) {x : EuclideanSpace ℝ (Fin n)}
    (hquasi : Convex ℝ {y : EuclideanSpace ℝ (Fin n) | f x < f y}) :
    ballSmoothing16 f δ x ≤ 2 * ell K δ x * f x := by
  obtain ⟨φ, hφ0, hφ⟩ := exists_dual_le_on_of_notMem hn hquasi (x := x) (by simp)
  obtain ⟨D, hD, hDle⟩ := exists_eight_pieces_at (δ := δ) hφ0 hK hfK hφ
  have hbt : volume (ball x δ) ≠ ⊤ := measure_ball_lt_top.ne
  have hb0 : volume (ball x δ) ≠ 0 := (Metric.measure_ball_pos volume x hδ).ne'
  have hellV : ell K δ x * volume (ball x δ) = volume (ball x δ ∩ K) := by
    rw [ell_apply, ENNReal.div_mul_cancel hb0 hbt]
  have h16 : (16 : ℝ≥0∞) * volume D = volume (ball x δ) := by
    rw [hD.sixteen_mul_volume]
    exact (volume_ball_eq x δ).symm
  have key : (8 : ℝ≥0∞) * (∫⁻ y in x +ᵥ D, f y) ≤ 8 * (2 * ell K δ x * f x * volume D) := by
    refine hDle.trans ?_
    calc volume (ball x δ ∩ {y | φ y ≤ φ x} ∩ K) * f x
        ≤ volume (ball x δ ∩ K) * f x :=
          mul_le_mul_right' (measure_mono (Set.inter_subset_inter_left _ Set.inter_subset_left)) _
      _ = ell K δ x * (16 * volume D) * f x := by rw [h16, hellV]
      _ = 8 * (2 * ell K δ x * f x * volume D) := by ring
  have hcancel : (∫⁻ y in x +ᵥ D, f y) ≤ 2 * ell K δ x * f x * volume D :=
    (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 key
  exact (ballSmoothing16_le x hD).trans (ENNReal.div_le_of_le_mul hcancel)

/-- **The sharp pointwise step, under an explicit balance condition.**

If some functional `φ` separating `x` from the strict superlevel set of `f` has the property
that the half of the proposal ball it cuts off carries **at most half of `K`'s share** of that
ball, then Cousins–Vempala's sharp inequality

    `f̂(x) ≤ ℓ(x) · f(x)`

holds.  The hypothesis is not tautological: it is a statement about `K`, `x` and `φ` only,
with no reference to `f̂`, and it holds automatically whenever `K` is symmetric about the
bounding hyperplane, and in particular whenever `B(x,δ) ⊆ K` (`ℓ(x) = 1`). -/
theorem ballSmoothing16_le_ell_mul_of_balanced
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    {δ : ℝ} (hδ : 0 < δ) {x : EuclideanSpace ℝ (Fin n)}
    {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ0 : φ ≠ 0)
    (hφ : ∀ y, f x < f y → φ x ≤ φ y)
    (hbal : 2 * volume (ball x δ ∩ {y | φ y ≤ φ x} ∩ K) ≤ volume (ball x δ ∩ K)) :
    ballSmoothing16 f δ x ≤ ell K δ x * f x := by
  obtain ⟨D, hD, hDle⟩ := exists_eight_pieces_at (δ := δ) hφ0 hK hfK hφ
  have hbt : volume (ball x δ) ≠ ⊤ := measure_ball_lt_top.ne
  have hb0 : volume (ball x δ) ≠ 0 := (Metric.measure_ball_pos volume x hδ).ne'
  have hellV : ell K δ x * volume (ball x δ) = volume (ball x δ ∩ K) := by
    rw [ell_apply, ENNReal.div_mul_cancel hb0 hbt]
  have h16 : (16 : ℝ≥0∞) * volume D = volume (ball x δ) := by
    rw [hD.sixteen_mul_volume]
    exact (volume_ball_eq x δ).symm
  have key : (16 : ℝ≥0∞) * (∫⁻ y in x +ᵥ D, f y) ≤ 16 * (ell K δ x * f x * volume D) := by
    have h2 : (16 : ℝ≥0∞) * (∫⁻ y in x +ᵥ D, f y)
        = 2 * (8 * (∫⁻ y in x +ᵥ D, f y)) := by ring
    rw [h2]
    calc (2 : ℝ≥0∞) * (8 * (∫⁻ y in x +ᵥ D, f y))
        ≤ 2 * (volume (ball x δ ∩ {y | φ y ≤ φ x} ∩ K) * f x) :=
          mul_le_mul_left' hDle 2
      _ = (2 * volume (ball x δ ∩ {y | φ y ≤ φ x} ∩ K)) * f x := by ring
      _ ≤ volume (ball x δ ∩ K) * f x := mul_le_mul_right' hbal _
      _ = ell K δ x * (16 * volume D) * f x := by rw [h16, hellV]
      _ = 16 * (ell K δ x * f x * volume D) := by ring
  have hcancel : (∫⁻ y in x +ᵥ D, f y) ≤ ell K δ x * f x * volume D :=
    (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 key
  exact (ballSmoothing16_le x hD).trans (ENNReal.div_le_of_le_mul hcancel)

/-- **The sharp pointwise step in the complementary case.**  If the *whole* of `K`'s share of
the proposal ball lies in the separating half — the configuration that defeats
`ballSmoothing16_le_ell_mul_of_balanced` — then `f` vanishes a.e. on the opposite half, that
half also holds eight sixteenth-balls, and `f̂(x) = 0`. -/
theorem ballSmoothing16_eq_zero_of_far_half_free
    {K : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    {δ : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ0 : φ ≠ 0)
    (hfree : ball x δ ∩ K ⊆ {y | φ y < φ x}) :
    ballSmoothing16 f δ x = 0 := by
  obtain ⟨P, hP, hPsub, -⟩ := exists_eight_sixteenthBalls (δ := δ) (neg_ne_zero.2 hφ0)
  have hsub : (x +ᵥ P 0) ⊆ ball x δ ∩ {y : EuclideanSpace ℝ (Fin n) | φ x ≤ φ y} := by
    refine le_trans (vadd_set_subset_vadd_set x (hPsub 0)) ?_
    rw [vadd_ball_inter_halfSpace (φ := -φ) x]
    intro y hy
    refine ⟨hy.1, ?_⟩
    have h := hy.2
    simp only [Set.mem_setOf_eq, ContinuousLinearMap.neg_apply, neg_le_neg_iff] at h
    exact h
  have hzero : (∫⁻ y in x +ᵥ P 0, f y) = 0 := by
    rw [setLIntegral_congr_fun (measurableSet_vadd_set (hP 0).measurableSet x)
      (g := fun _ => (0 : ℝ≥0∞))
      (fun y hy => hfK y (fun hyK =>
        absurd (show φ x ≤ φ y from (hsub hy).2)
          (not_le.2 (show φ y < φ x from hfree ⟨(hsub hy).1, hyK⟩))))]
    simp
  refine le_antisymm ?_ (by simp)
  refine (ballSmoothing16_le x (hP 0)).trans ?_
  rw [hzero, ENNReal.zero_div]

/-! ## 4. Lovász–Vempala Lemma 6.1 -/

/-- A nonzero continuous linear functional exists as soon as `n ≥ 1`. -/
theorem exists_ne_zero_dual (hn : 1 ≤ n) :
    ∃ φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ, φ ≠ 0 := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
  obtain ⟨φ, hφ1, -⟩ := exists_dual_vector ℝ v (by simpa using hv)
  refine ⟨φ, fun h => ?_⟩
  rw [h] at hφ1
  simp at hφ1

/-- **Lovász–Vempala Lemma 6.1.**  For every convex `D ⊆ δBₙ` with `vol(D) ≥ vol(δBₙ)/16`,

    `(1/vol D) ∫_{x+D} f  ≥  (1/2) · f̂(x)`,

stated multiplication-free as `f̂(x)·vol(D) ≤ 2·∫_{x+D} f`.  This is Lovász–Vempala's
observation that one "could, at the cost of a factor of 2, replace equality in the condition
on `C` by inequality", and the proof is theirs: slice `D` by parallel hyperplanes into `m`
convex pieces of equal volume, each of volume between `vol(δBₙ)/16` and `vol(δBₙ)/8`; one of
them carries at most `1/m` of the integral; cut that one down to volume exactly
`vol(δBₙ)/16`, which is then an admissible index of the infimum. -/
theorem ballSmoothing16_mul_volume_le_two_mul (hn : 1 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {δ : ℝ} (hδ : 0 < δ)
    (x : EuclideanSpace ℝ (Fin n)) {D : Set (EuclideanSpace ℝ (Fin n))}
    (hDconv : Convex ℝ D) (hDmeas : MeasurableSet D) (hDsub : D ⊆ ball 0 δ)
    (hDvol : volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) ≤ 16 * volume D) :
    ballSmoothing16 f δ x * volume D ≤ 2 * ∫⁻ y in x +ᵥ D, f y := by
  obtain ⟨φ, hφ⟩ := exists_ne_zero_dual hn
  set V : ℝ≥0∞ := volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) with hVdef
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hδ).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  set w : ℝ≥0∞ := V / 16 with hwdef
  have h16w : (16 : ℝ≥0∞) * w = V := ENNReal.mul_div_cancel' (by norm_num) (by norm_num)
  have hwt : w ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top (by norm_num)] at h16w
    exact hVt h16w.symm
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, mul_zero] at h16w
    exact hV0 h16w.symm
  set vD : ℝ≥0∞ := volume D with hvDdef
  have hvDt : vD ≠ ⊤ := ne_top_of_le_ne_top hVt (measure_mono hDsub)
  have hwvD : w ≤ vD := ENNReal.div_le_of_le_mul (by rw [mul_comm]; exact hDvol)
  -- the number of slices
  have hwr : 0 < w.toReal := ENNReal.toReal_pos hw0 hwt
  set m : ℕ := ⌊vD.toReal / w.toReal⌋₊ with hmdef
  have hratio : 1 ≤ vD.toReal / w.toReal := by
    rw [le_div_iff₀ hwr, one_mul]
    exact ENNReal.toReal_mono hvDt hwvD
  have hm1 : 1 ≤ m := Nat.le_floor (by exact_mod_cast hratio)
  have hm0 : (0 : ℕ) < m := hm1
  have hmle : (m : ℝ) * w.toReal ≤ vD.toReal := by
    have := Nat.floor_le (le_trans zero_le_one hratio)
    rw [le_div_iff₀ hwr] at this
    exact this
  have hmlt : vD.toReal ≤ 2 * ((m : ℝ) * w.toReal) := by
    have h1 : vD.toReal / w.toReal < (m : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [div_lt_iff₀ hwr] at h1
    have h2 : ((m : ℝ) + 1) ≤ 2 * (m : ℝ) := by
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      linarith
    nlinarith [hwr.le]
  have hmR0 : ((m : ℝ≥0∞)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hmRt : ((m : ℝ≥0∞)) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hmw_le : (m : ℝ≥0∞) * w ≤ vD := by
    rw [← ENNReal.ofReal_toReal (a := (m : ℝ≥0∞) * w) (ENNReal.mul_ne_top hmRt hwt),
      ← ENNReal.ofReal_toReal hvDt]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    exact hmle
  have hvD_le : vD ≤ 2 * ((m : ℝ≥0∞) * w) := by
    rw [← ENNReal.ofReal_toReal (a := 2 * ((m : ℝ≥0∞) * w))
        (ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top hmRt hwt)),
      ← ENNReal.ofReal_toReal hvDt]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast]
    simpa using hmlt
  -- slice `D` into `m` pieces of equal volume
  have hDeq : vD = (m : ℝ≥0∞) * (vD / m) :=
    (ENNReal.mul_div_cancel' (fun h => absurd h hmR0) (fun h => absurd h hmRt)).symm
  obtain ⟨P, hPconv, hPmeas, hPsub, hPvol, hPdisj⟩ :=
    exists_convex_partition (φ := φ) hφ (R := δ) m hDmeas hDsub hDconv (w := vD / m) hDeq
  have hsum : ∑ i, (∫⁻ y in x +ᵥ P i, f y) ≤ ∫⁻ y in x +ᵥ D, f y := by
    calc ∑ i, (∫⁻ y in x +ᵥ P i, f y)
        = ∑' i, (∫⁻ y in x +ᵥ P i, f y) := (tsum_fintype _).symm
      _ = ∫⁻ y in ⋃ i, (x +ᵥ P i), f y :=
          (lintegral_iUnion (fun i => measurableSet_vadd_set (hPmeas i) x)
            (fun i j hij => disjoint_vadd_set x (hPdisj hij)) f).symm
      _ ≤ ∫⁻ y in x +ᵥ D, f y :=
          lintegral_mono' (Measure.restrict_mono
            (Set.iUnion_subset fun i => vadd_set_subset_vadd_set x (hPsub i)) le_rfl) le_rfl
  obtain ⟨i, hi⟩ :=
    exists_nsmul_le_of_sum_le hm0 (fun i => ∫⁻ y in x +ᵥ P i, f y) hsum
  -- cut the chosen piece down to volume exactly `w`
  have hwPi : w ≤ volume (P i) := by
    rw [hPvol i, ENNReal.le_div_iff_mul_le (Or.inl hmR0) (Or.inl hmRt), mul_comm]
    exact hmw_le
  obtain ⟨t, ht⟩ :=
    exists_volume_cut_eq (hPmeas i) ((hPsub i).trans hDsub) hφ hwPi
  set C : Set (EuclideanSpace ℝ (Fin n)) := P i ∩ {z | φ z ≤ t} with hCdef
  have hC : IsSixteenthBall δ C := by
    refine ⟨(hPconv i).inter (convex_halfSpace_le (f := fun z => φ z)
        ⟨fun a b => φ.map_add a b, fun c a => φ.map_smul c a⟩ t),
      (hPmeas i).inter (measurableSet_le φ.continuous.measurable measurable_const),
      Set.Subset.trans Set.inter_subset_left ((hPsub i).trans hDsub), ?_⟩
    rw [ht]
    exact h16w
  have hCle : (∫⁻ y in x +ᵥ C, f y) ≤ ∫⁻ y in x +ᵥ P i, f y :=
    lintegral_mono' (Measure.restrict_mono
      (vadd_set_subset_vadd_set x Set.inter_subset_left) le_rfl) le_rfl
  have hsmooth : ballSmoothing16 f δ x * w ≤ ∫⁻ y in x +ᵥ P i, f y := by
    refine le_trans ?_ hCle
    have := ballSmoothing16_mul_volume_le (f := f) hδ x hC
    rwa [ht] at this
  calc ballSmoothing16 f δ x * vD
      ≤ ballSmoothing16 f δ x * (2 * ((m : ℝ≥0∞) * w)) := mul_le_mul_left' hvD_le _
    _ = 2 * ((m : ℝ≥0∞) * (ballSmoothing16 f δ x * w)) := by ring
    _ ≤ 2 * ((m : ℝ≥0∞) * (∫⁻ y in x +ᵥ P i, f y)) :=
        mul_le_mul_left' (mul_le_mul_left' hsmooth _) 2
    _ ≤ 2 * ∫⁻ y in x +ᵥ D, f y := mul_le_mul_left' hi 2

/-- **`f̂₁₆ ≤ 2 · f̂_{1/2}`.**  Lemma 6.1 applied to the half-volume sets of
Cousins–Vempala's transcription: their smoothing and Lovász–Vempala's differ by at most a
factor of `2` in this direction, so every upper bound proved for `ballSmoothing16` yields one
for `ballSmoothing` up to that factor. -/
theorem ballSmoothing16_le_two_mul_ballSmoothing (hn : 1 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {δ : ℝ} (hδ : 0 < δ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ballSmoothing16 f δ x ≤ 2 * ballSmoothing f δ x := by
  rw [ballSmoothing, ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  refine le_iInf fun D => ?_
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  refine le_iInf fun hD => ?_
  have hvol0 : volume D ≠ 0 := hD.volume_ne_zero hδ
  have hvolt : volume D ≠ ⊤ := hD.volume_ne_top
  have hDvol : volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) ≤ 16 * volume D := by
    rw [show (16 : ℝ≥0∞) = 8 * 2 by norm_num, mul_assoc, hD.two_mul_volume]
    calc volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ)
        = 1 * volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) := (one_mul _).symm
      _ ≤ 8 * volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) :=
          mul_le_mul_right' (by norm_num) _
  have hkey := ballSmoothing16_mul_volume_le_two_mul (f := f) hn hδ x hD.convex hD.measurableSet
    hD.subset_ball hDvol
  have hassoc : (2 : ℝ≥0∞) * ((∫⁻ y in x +ᵥ D, f y) / volume D)
      = (2 * ∫⁻ y in x +ᵥ D, f y) / volume D := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
  rw [hassoc, ENNReal.le_div_iff_mul_le (Or.inl hvol0) (Or.inl hvolt)]
  exact hkey

/-! ## 5. Lovász–Vempala Lemma 6.2: `f̂` is log-concave -/

/-- Log-concavity in `ℝ≥0∞` is preserved by precomposition with a linear map. -/
theorem isLogConcaveENN_comp_linearMap {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] {g : F → ℝ≥0∞} (hg : IsLogConcaveENN g) (L : E →ₗ[ℝ] F) :
    IsLogConcaveENN fun x => g (L x) := by
  intro x y a b ha hb hab
  have h := hg (L x) (L y) a b ha hb hab
  rwa [← LinearMap.map_smul, ← LinearMap.map_smul, ← map_add] at h

/-- Log-concavity in `ℝ≥0∞` is preserved by products. -/
theorem isLogConcaveENN_mul {E : Type*} [AddCommGroup E] [Module ℝ E] {g h : E → ℝ≥0∞}
    (hg : IsLogConcaveENN g) (hh : IsLogConcaveENN h) :
    IsLogConcaveENN fun x => g x * h x := by
  intro x y a b ha hb hab
  calc (g x * h x) ^ a * (g y * h y) ^ b
      = g x ^ a * g y ^ b * (h x ^ a * h y ^ b) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ ha, ENNReal.mul_rpow_of_nonneg _ _ hb]
        ring
    _ ≤ g (a • x + b • y) * h (a • x + b • y) :=
        mul_le_mul' (hg x y a b ha hb hab) (hh x y a b ha hb hab)

/-- Log-concavity in `ℝ≥0∞` is preserved by division by a positive finite constant. -/
theorem isLogConcaveENN_div_const {E : Type*} [AddCommGroup E] [Module ℝ E] {g : E → ℝ≥0∞}
    (hg : IsLogConcaveENN g) {c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    IsLogConcaveENN fun x => g x / c := by
  intro x y a b ha hb hab
  have hi0 : c⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hct
  have hit : c⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hc0
  simp only [div_eq_mul_inv]
  calc (g x * c⁻¹) ^ a * (g y * c⁻¹) ^ b
      = g x ^ a * g y ^ b * (c⁻¹ ^ a * c⁻¹ ^ b) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ ha, ENNReal.mul_rpow_of_nonneg _ _ hb]
        ring
    _ = g x ^ a * g y ^ b * c⁻¹ := by
        rw [← ENNReal.rpow_add _ _ hi0 hit, hab, ENNReal.rpow_one]
    _ ≤ g (a • x + b • y) * c⁻¹ := mul_le_mul_right' (hg x y a b ha hb hab) _

/-- Log-concavity in `ℝ≥0∞` is preserved by pointwise infima. -/
theorem isLogConcaveENN_iInf {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Sort*}
    {g : ι → E → ℝ≥0∞} (hg : ∀ i, IsLogConcaveENN (g i)) :
    IsLogConcaveENN fun x => ⨅ i, g i x := by
  intro x y a b ha hb hab
  refine le_iInf fun i => ?_
  refine le_trans (mul_le_mul' (ENNReal.rpow_le_rpow (iInf_le (fun i => g i x) i) ha)
    (ENNReal.rpow_le_rpow (iInf_le (fun i => g i y) i) hb)) ?_
  exact hg i x y a b ha hb hab

/-- **The ball convolution is log-concave.**  For log-concave measurable `f` and a convex
measurable `C`, the function `x ↦ ∫_{x+C} f` is log-concave.  This is Lovász–Vempala's
"`f_C(x) = ∫_C f(x+u) du` is the convolution of `f` with the characteristic function of the
convex set `−C`, and so it is log-concave by Theorem 5.1" — here obtained from the repository's
Prékopa–Leindler marginal lemma, after transporting `EuclideanSpace ℝ (Fin n)` to
`Fin n → ℝ` along the volume-preserving linear equivalence `WithLp.toLp`. -/
theorem isLogConcaveENN_setLIntegral_vadd {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : IsLogConcaveENN f) (hfm : Measurable f)
    {C : Set (EuclideanSpace ℝ (Fin n))} (hCconv : Convex ℝ C) (hCm : MeasurableSet C) :
    IsLogConcaveENN fun x : EuclideanSpace ℝ (Fin n) => ∫⁻ y in x +ᵥ C, f y := by
  set T : (Fin n → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap with hTdef
  have hTmeas : Measurable T := (PiLp.volume_preserving_toLp (Fin n)).measurable
  set G : EuclideanSpace ℝ (Fin n) × (Fin n → ℝ) → ℝ≥0∞ := fun p =>
    Set.indicator C (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (T p.2) * f (p.1 + T p.2) with hGdef
  have hGm : Measurable G := by
    refine Measurable.mul ?_ ?_
    · exact (measurable_one.indicator hCm).comp (hTmeas.comp measurable_snd)
    · exact hfm.comp (measurable_fst.add (hTmeas.comp measurable_snd))
  have hGlc : IsLogConcaveENN G := by
    have h1 : IsLogConcaveENN fun p : EuclideanSpace ℝ (Fin n) × (Fin n → ℝ) =>
        Set.indicator C (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (T p.2) :=
      isLogConcaveENN_comp_linearMap (isLogConcaveENN_indicator hCconv)
        (T ∘ₗ LinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (Fin n → ℝ))
    have h2 : IsLogConcaveENN fun p : EuclideanSpace ℝ (Fin n) × (Fin n → ℝ) =>
        f (p.1 + T p.2) :=
      isLogConcaveENN_comp_linearMap hf
        (LinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) (Fin n → ℝ)
          + T ∘ₗ LinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) (Fin n → ℝ))
    exact isLogConcaveENN_mul h1 h2
  have hrepr : (fun x : EuclideanSpace ℝ (Fin n) => ∫⁻ y in x +ᵥ C, f y)
      = fun x => ∫⁻ t, G (x, t) := by
    funext x
    have hmv : MeasurableSet (x +ᵥ C) := measurableSet_vadd_set hCm x
    have hmem : ∀ u : EuclideanSpace ℝ (Fin n), (x + u ∈ x +ᵥ C) ↔ u ∈ C := by
      intro u
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simp
    have hpt : ∀ u : EuclideanSpace ℝ (Fin n), (x +ᵥ C).indicator f (x + u)
        = Set.indicator C (1 : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) u * f (x + u) := by
      intro u
      by_cases hu : u ∈ C
      · rw [Set.indicator_of_mem ((hmem u).2 hu), Set.indicator_of_mem hu]
        simp
      · rw [Set.indicator_of_notMem (fun h => hu ((hmem u).1 h)),
          Set.indicator_of_notMem hu]
        simp
    calc (∫⁻ y in x +ᵥ C, f y)
        = ∫⁻ y, (x +ᵥ C).indicator f y := (lintegral_indicator hmv f).symm
      _ = ∫⁻ u, (x +ᵥ C).indicator f (x + u) :=
          ((measurePreserving_add_left (volume : Measure (EuclideanSpace ℝ (Fin n))) x).lintegral_comp
            (hfm.indicator hmv)).symm
      _ = ∫⁻ t, (x +ᵥ C).indicator f (x + T t) :=
          ((PiLp.volume_preserving_toLp (Fin n)).lintegral_comp
            ((hfm.indicator hmv).comp (measurable_const.add measurable_id))).symm
      _ = ∫⁻ t, G (x, t) := by
          refine lintegral_congr fun t => ?_
          exact hpt (T t)
  rw [hrepr]
  exact isLogConcaveENN_marginal_prod hGlc hGm

/-- **Lovász–Vempala Lemma 6.2: the function `f̂` is log-concave.**

"For a fixed convex set `C ⊆ rB`, the function `f_C(x) = ∫_C f(x+u) du` is the convolution of
`f` with the characteristic function of the convex set `−C`, and so it is log-concave by
Theorem 5.1.  Thus `f̂` is the infimum of a family `{f_C}` of log-concave functions, and so it
too is log-concave." -/
theorem isLogConcaveENN_ballSmoothing16 {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (hf : IsLogConcaveENN f) (hfm : Measurable f) {δ : ℝ} (hδ : 0 < δ) :
    IsLogConcaveENN (ballSmoothing16 f δ) := by
  have h : IsLogConcaveENN fun x : EuclideanSpace ℝ (Fin n) =>
      ⨅ D : Set (EuclideanSpace ℝ (Fin n)),
        ⨅ _ : D ∈ {D : Set (EuclideanSpace ℝ (Fin n)) | IsSixteenthBall δ D},
          (∫⁻ y in x +ᵥ D, f y) / volume D := by
    refine isLogConcaveENN_iInf fun D => isLogConcaveENN_iInf fun hD => ?_
    exact isLogConcaveENN_div_const
      (isLogConcaveENN_setLIntegral_vadd hf hfm hD.convex hD.measurableSet)
      (hD.volume_ne_zero hδ) hD.volume_ne_top
  exact h

/-! ## 6. Two proved instances of the sharp constant, and `lem:lambda-bound` -/

/-- **The sharp constant holds at every maximum point of `f`.**

If `f(y) ≤ f(x)` for all `y` — in particular at the mode of a log-concave density — then
*every* hyperplane through `x` separates `x` from the (empty) strict superlevel set, so one
may choose the half that carries at most half of `K`'s share of the proposal ball.  This
discharges the balance hypothesis of `ballSmoothing16_le_ell_mul_of_balanced` outright and
gives Cousins–Vempala's sharp

    `f̂(x) ≤ ℓ(x) · f(x)`.

It also shows the balance hypothesis is satisfiable, hence not vacuous. -/
theorem exists_balanced_dual_of_isMax (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (δ : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hmax : ∀ y, f y ≤ f x) :
    ∃ φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ, φ ≠ 0 ∧ (∀ y, f x < f y → φ x ≤ φ y) ∧
      2 * volume (ball x δ ∩ {y | φ y ≤ φ x} ∩ K) ≤ volume (ball x δ ∩ K) := by
  obtain ⟨φ, hφ0⟩ := exists_ne_zero_dual hn
  set Wm : ℝ≥0∞ := volume (ball x δ ∩ {y : EuclideanSpace ℝ (Fin n) | φ y ≤ φ x} ∩ K) with hWm
  set Wp : ℝ≥0∞ := volume (ball x δ ∩ {y : EuclideanSpace ℝ (Fin n) | φ x ≤ φ y} ∩ K) with hWp
  have hnosep : ∀ (ψ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (y : EuclideanSpace ℝ (Fin n)),
      f x < f y → ψ x ≤ ψ y := fun ψ y hy => absurd (hmax y) (not_le.2 hy)
  have hsum : Wm + Wp = volume (ball x δ ∩ K) := by
    set Sm : Set (EuclideanSpace ℝ (Fin n)) :=
      ball x δ ∩ {y : EuclideanSpace ℝ (Fin n) | φ y ≤ φ x} ∩ K with hSm
    set Sp : Set (EuclideanSpace ℝ (Fin n)) :=
      ball x δ ∩ {y : EuclideanSpace ℝ (Fin n) | φ x ≤ φ y} ∩ K with hSp
    have hmSp : MeasurableSet Sp :=
      (measurableSet_ball.inter
        (measurableSet_le measurable_const φ.continuous.measurable)).inter hK
    have hunion : Sm ∪ Sp = ball x δ ∩ K := by
      ext y
      simp only [hSm, hSp, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro (⟨⟨h1, -⟩, h3⟩ | ⟨⟨h1, -⟩, h3⟩) <;> exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        rcases le_total (φ y) (φ x) with hc | hc
        · exact Or.inl ⟨⟨h1, hc⟩, h2⟩
        · exact Or.inr ⟨⟨h1, hc⟩, h2⟩
    have hinter : volume (Sm ∩ Sp) = 0 := by
      refine measure_mono_null (fun y hy => ?_) (volume_setOf_eq_apply hφ0 x)
      exact le_antisymm hy.1.1.2 hy.2.1.2
    have h := measure_union_add_inter (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Sm hmSp
    rw [hunion, hinter, add_zero] at h
    exact h.symm
  rcases le_total Wm Wp with hcase | hcase
  · refine ⟨φ, hφ0, hnosep φ, ?_⟩
    rw [two_mul, ← hWm, ← hsum]
    exact add_le_add_left hcase Wm |>.trans_eq (add_comm Wp Wm)
  · have hset : {y : EuclideanSpace ℝ (Fin n) | (-φ) y ≤ (-φ) x}
        = {y : EuclideanSpace ℝ (Fin n) | φ x ≤ φ y} := by
      ext y
      simp only [Set.mem_setOf_eq, ContinuousLinearMap.neg_apply, neg_le_neg_iff]
    refine ⟨-φ, neg_ne_zero.2 hφ0, hnosep (-φ), ?_⟩
    rw [hset, ← hWp, two_mul, ← hsum]
    exact add_le_add_right hcase Wp |>.trans_eq (add_comm Wp Wm)

/-- **The sharp constant holds at every maximum point of `f`** — the corollary of
`exists_balanced_dual_of_isMax`. -/
theorem ballSmoothing16_le_ell_mul_of_isMax (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    {δ : ℝ} (hδ : 0 < δ) {x : EuclideanSpace ℝ (Fin n)} (hmax : ∀ y, f y ≤ f x) :
    ballSmoothing16 f δ x ≤ ell K δ x * f x := by
  obtain ⟨φ, hφ0, hsep, hb⟩ := exists_balanced_dual_of_isMax hn hK δ hmax
  exact ballSmoothing16_le_ell_mul_of_balanced hK hfK hδ hφ0 hsep hb

/-- **`lem:lambda-bound` (`vol3_journal.tex:853`) with the pointwise binder discharged, at the
cost of a factor `2`, and with the Lovász hypothesis now stated about the function
Lovász–Vempala's Lemma 6.3 is actually about.**

`Arlib.MarkovChains.avgLocalConductance_ge_half_of_lovasz` carries the same conclusion but
with `hLov` stated for `ballSmoothing`, the *half*-volume smoothing of Cousins–Vempala's
transcription — a function Lemma 6.3 says nothing about.  Here `hLov` is about
`ballSmoothing16`, which is Lovász–Vempala's `f̂` verbatim. -/
theorem avgLocalConductance_ge_half_of_lovasz16 (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hquasi : ∀ x : EuclideanSpace ℝ (Fin n), Convex ℝ {y | f x < f y})
    {c : ℝ}
    (hLov : ENNReal.ofReal c * ∫⁻ x in K, f x ≤ ∫⁻ x in K, ballSmoothing16 f δ x)
    (h0 : (∫⁻ x in K, f x) ≠ 0) (htop : (∫⁻ x in K, f x) ≠ ⊤) :
    ENNReal.ofReal c / 2 ≤ (∫⁻ x in K, ell K δ x * f x) / (∫⁻ x in K, f x) := by
  have hmono : (∫⁻ x in K, ballSmoothing16 f δ x) ≤ 2 * ∫⁻ x in K, ell K δ x * f x := by
    calc (∫⁻ x in K, ballSmoothing16 f δ x)
        ≤ ∫⁻ x in K, 2 * (ell K δ x * f x) := by
          refine lintegral_mono fun x => ?_
          have h := ballSmoothing16_le_two_mul_ell_mul hn hK hfK hδ (hquasi x)
          rwa [mul_assoc] at h
      _ = 2 * ∫⁻ x in K, ell K δ x * f x := lintegral_const_mul' 2 _ (by simp)
  have h2 : ENNReal.ofReal c * (∫⁻ x in K, f x) ≤ 2 * ∫⁻ x in K, ell K δ x * f x :=
    hLov.trans hmono
  rw [ENNReal.div_le_iff_le_mul (Or.inl two_ne_zero) (Or.inl (by simp)), mul_comm,
    ← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop)]
  exact h2

/-- **`lem:lambda-bound` with Cousins–Vempala's own constant**, under the balance condition of
`ballSmoothing16_le_ell_mul_of_balanced` holding at every point.  The balance condition is a
statement about `K`, `x` and a separating direction only; it is satisfied at every maximum
point of `f` (`ballSmoothing16_le_ell_mul_of_isMax`), so the hypothesis bundle is not
vacuous. -/
theorem avgLocalConductance_ge_of_lovasz16_balanced
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hbal : ∀ x ∈ K,
      ∃ φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ, φ ≠ 0 ∧ (∀ y, f x < f y → φ x ≤ φ y) ∧
        2 * volume (ball x δ ∩ {y | φ y ≤ φ x} ∩ K) ≤ volume (ball x δ ∩ K))
    {c : ℝ}
    (hLov : ENNReal.ofReal c * ∫⁻ x in K, f x ≤ ∫⁻ x in K, ballSmoothing16 f δ x)
    (h0 : (∫⁻ x in K, f x) ≠ 0) (htop : (∫⁻ x in K, f x) ≠ ⊤) :
    ENNReal.ofReal c ≤ (∫⁻ x in K, ell K δ x * f x) / (∫⁻ x in K, f x) := by
  have hmono : (∫⁻ x in K, ballSmoothing16 f δ x) ≤ ∫⁻ x in K, ell K δ x * f x := by
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict hK] with x hx
    obtain ⟨φ, hφ0, hsep, hb⟩ := hbal x hx
    exact ballSmoothing16_le_ell_mul_of_balanced hK hfK hδ hφ0 hsep hb
  rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop)]
  exact hLov.trans hmono

/-- **The `λ ≥ 1/2` corollary of `vol3_journal.tex:906`, obtained here as `λ ≥ 1/4`**, with
`hLov` about Lovász–Vempala's own `f̂`.  At the paper's step size `δ ≤ min{σ,1}/(4096√n)` the
Cousins–Vempala constant `1 − 32δ^{1/2}n^{1/4}/a^{1/2}` is at least `1/2`
(`cv_error_term_le_half`); the factor-`2` pointwise step then gives `1/4`. -/
theorem avgLocalConductance_ge_quarter_of_lovasz16 (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    {δ σ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hstep : δ ≤ min σ 1 / (4096 * Real.sqrt n))
    (hquasi : ∀ x : EuclideanSpace ℝ (Fin n), Convex ℝ {y | f x < f y})
    (hLov : ENNReal.ofReal
              (1 - 32 * Real.sqrt δ * Real.sqrt (Real.sqrt n) / Real.sqrt (min σ 1))
              * ∫⁻ x in K, f x ≤ ∫⁻ x in K, ballSmoothing16 f δ x)
    (h0 : (∫⁻ x in K, f x) ≠ 0) (htop : (∫⁻ x in K, f x) ≠ ⊤) :
    ENNReal.ofReal (1 / 4) ≤ (∫⁻ x in K, ell K δ x * f x) / (∫⁻ x in K, f x) := by
  have ha : (0 : ℝ) < min σ 1 := lt_min hσ one_pos
  have harith := cv_error_term_le_half (a := min σ 1) ha hn hstep
  refine le_trans ?_ (avgLocalConductance_ge_half_of_lovasz16 hn hK hfK hδ hquasi hLov h0 htop)
  rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl (by simp)),
    show ((2 : ℝ≥0∞)) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Cousins–Vempala's `λ(f) ≥ 1/2` itself** (`vol3_journal.tex:906`), under the balance
condition of `ballSmoothing16_le_ell_mul_of_balanced` and Lovász–Vempala's Lemma 6.3.  This is
the paper's claimed constant, not a weakened one; what it costs is the balance binder. -/
theorem avgLocalConductance_ge_half_of_lovasz16_balanced (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    {δ σ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hstep : δ ≤ min σ 1 / (4096 * Real.sqrt n))
    (hbal : ∀ x ∈ K,
      ∃ φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ, φ ≠ 0 ∧ (∀ y, f x < f y → φ x ≤ φ y) ∧
        2 * volume (ball x δ ∩ {y | φ y ≤ φ x} ∩ K) ≤ volume (ball x δ ∩ K))
    (hLov : ENNReal.ofReal
              (1 - 32 * Real.sqrt δ * Real.sqrt (Real.sqrt n) / Real.sqrt (min σ 1))
              * ∫⁻ x in K, f x ≤ ∫⁻ x in K, ballSmoothing16 f δ x)
    (h0 : (∫⁻ x in K, f x) ≠ 0) (htop : (∫⁻ x in K, f x) ≠ ⊤) :
    ENNReal.ofReal (1 / 2) ≤ (∫⁻ x in K, ell K δ x * f x) / (∫⁻ x in K, f x) := by
  have ha : (0 : ℝ) < min σ 1 := lt_min hσ one_pos
  have harith := cv_error_term_le_half (a := min σ 1) ha hn hstep
  refine le_trans (ENNReal.ofReal_le_ofReal (by linarith))
    (avgLocalConductance_ge_of_lovasz16_balanced hK hfK hδ hbal hLov h0 htop)

/-! ## 7. Non-vacuity: a witness whose Lovász hypothesis is proved, not assumed -/

/-- **The uniform density on the unit ball, smoothed at the `1/16` normalisation, is `1` well
inside the ball.**  For `‖x‖ < 1 − δ` every translate `x + D` of an admissible `D` stays
inside `B(0,1)`, so every term of the infimum is `vol(D)/vol(D) = 1`. -/
theorem one_le_ballSmoothing16_indicator_ball {δ : ℝ} (hδ : 0 < δ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1 - δ) :
    1 ≤ ballSmoothing16
      (Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞))) δ x := by
  refine le_ballSmoothing16 fun D hD => ?_
  have hsub : x +ᵥ D ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro y hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
    have h1 : ‖-x + y‖ < δ := by
      have h := hD.subset_ball hy
      simpa [vadd_eq_add, mem_ball, dist_zero_right] using h
    have h2 : ‖y‖ ≤ ‖-x + y‖ + ‖x‖ := by
      have hyx : (-x + y) + x = y := by abel
      calc ‖y‖ = ‖(-x + y) + x‖ := by rw [hyx]
        _ ≤ ‖-x + y‖ + ‖x‖ := norm_add_le _ _
    simp only [mem_ball, dist_zero_right]
    linarith
  have hEq : (∫⁻ y in x +ᵥ D,
      Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)) y)
      = volume D := by
    rw [setLIntegral_congr_fun (measurableSet_vadd_set hD.measurableSet x)
        (fun y hy => Set.indicator_of_mem (hsub hy) _), setLIntegral_one, volume_vadd_set]
  rw [hEq, ENNReal.div_self (hD.volume_ne_zero hδ) hD.volume_ne_top]

/-- **A proved instance of the conclusion of Lovász–Vempala Lemma 6.3, for the `1/16`
smoothing.**  For the uniform density on the unit ball and `0 < δ < 1`,
`∫_K f̂ ≥ (1−δ)ⁿ ∫_K f`, because `f̂ = 1` on the concentric ball of radius `1−δ`. -/
theorem lovasz16_bound_indicator_ball (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal ((1 - δ) ^ n)
        * (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
            Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)) x)
      ≤ ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          ballSmoothing16
            (Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞))) δ x := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have hball : volume (ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ))
      = ENNReal.ofReal ((1 - δ) ^ n) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    rw [Measure.addHaar_ball volume _ (by linarith), finrank_euclideanSpace_fin]
  rw [lintegral_indicator_ball_self, ← hball]
  calc volume (ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ))
      = ∫⁻ _ in ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ), 1 := (setLIntegral_one _).symm
    _ ≤ ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (1 - δ),
          ballSmoothing16
            (Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞))) δ x := by
        refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
        refine one_le_ballSmoothing16_indicator_ball hδ ?_
        simpa [mem_ball, dist_zero_right] using hy
    _ ≤ ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          ballSmoothing16
            (Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞))) δ x :=
        lintegral_mono' (Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl) le_rfl

/-- **Non-vacuity witness for `avgLocalConductance_ge_of_lovasz16_balanced`.**

Unit ball, uniform density, `δ = 1/2`, `c = (1/2)ⁿ > 0`.  Both nontrivial hypotheses are
*proved* for this instance, not assumed: the balance condition by
`exists_balanced_dual_of_isMax` (the density is constant on `K`, so every point of `K` is a
maximum), and the Lovász inequality by `lovasz16_bound_indicator_ball`.  In particular the
witness is not the tautology `f̂ = ℓ·f`, and the conclusion carries Cousins–Vempala's own
constant `c` rather than `c/2`. -/
theorem exists_lovasz16_balanced_instance (hn : 1 ≤ n) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
      (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (c : ℝ),
      0 < c ∧ 0 < δ ∧ MeasurableSet K ∧ (∀ y, y ∉ K → f y = 0) ∧
      (∀ x ∈ K, ∃ φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ, φ ≠ 0 ∧
        (∀ y, f x < f y → φ x ≤ φ y) ∧
        2 * volume (ball x δ ∩ {y | φ y ≤ φ x} ∩ K) ≤ volume (ball x δ ∩ K)) ∧
      (ENNReal.ofReal c * ∫⁻ x in K, f x ≤ ∫⁻ x in K, ballSmoothing16 f δ x) ∧
      (∫⁻ x in K, f x) ≠ 0 ∧ (∫⁻ x in K, f x) ≠ ⊤ ∧
      ENNReal.ofReal c ≤ (∫⁻ x in K, ell K δ x * f x) / (∫⁻ x in K, f x) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  set K : Set (EuclideanSpace ℝ (Fin n)) := ball 0 1 with hK
  set f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)) with hf
  have h0 : (∫⁻ x in K, f x) ≠ 0 := by
    rw [hK, hf, lintegral_indicator_ball_self]
    exact (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have htop : (∫⁻ x in K, f x) ≠ ⊤ := by
    rw [hK, hf, lintegral_indicator_ball_self]
    exact measure_ball_lt_top.ne
  have hbal : ∀ x ∈ K, ∃ φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ, φ ≠ 0 ∧
      (∀ y, f x < f y → φ x ≤ φ y) ∧
      2 * volume (ball x (1 / 2 : ℝ) ∩ {y | φ y ≤ φ x} ∩ K) ≤ volume (ball x (1 / 2 : ℝ) ∩ K) := by
    intro x hx
    refine exists_balanced_dual_of_isMax hn measurableSet_ball (1 / 2 : ℝ) fun y => ?_
    rw [hf, Set.indicator_of_mem hx]
    by_cases hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1
    · simp [Set.indicator_of_mem hy]
    · simp [Set.indicator_of_notMem hy]
  have hLov : ENNReal.ofReal ((1 - 1 / 2 : ℝ) ^ n) * (∫⁻ x in K, f x)
      ≤ ∫⁻ x in K, ballSmoothing16 f (1 / 2 : ℝ) x :=
    lovasz16_bound_indicator_ball hn (by norm_num) (by norm_num)
  refine ⟨K, 1 / 2, f, (1 - 1 / 2 : ℝ) ^ n, by positivity, by norm_num, measurableSet_ball,
    fun y hy => Set.indicator_of_notMem hy _, hbal, hLov, h0, htop, ?_⟩
  exact avgLocalConductance_ge_of_lovasz16_balanced measurableSet_ball
    (fun y hy => Set.indicator_of_notMem hy _) (by norm_num) hbal hLov h0 htop

/-- **Non-vacuity witness for `avgLocalConductance_ge_half_of_lovasz16`.**  Unit ball, uniform
density, `δ = 1/2`, `c = (1/2)ⁿ > 0`; the Lovász hypothesis is *proved* for this instance by
`lovasz16_bound_indicator_ball`, so no binder is discharged by fiat, and the witness is not
the tautology `f̂ = ℓ·f`. -/
theorem exists_lovasz16_instance (hn : 1 ≤ n) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
      (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (c : ℝ),
      0 < c ∧ 0 < δ ∧ MeasurableSet K ∧ (∀ y, y ∉ K → f y = 0) ∧
      (∀ x, Convex ℝ {y | f x < f y}) ∧
      (ENNReal.ofReal c * ∫⁻ x in K, f x ≤ ∫⁻ x in K, ballSmoothing16 f δ x) ∧
      (∫⁻ x in K, f x) ≠ 0 ∧ (∫⁻ x in K, f x) ≠ ⊤ ∧
      ENNReal.ofReal c / 2 ≤ (∫⁻ x in K, ell K δ x * f x) / (∫⁻ x in K, f x) := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  have h0 : (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)) x) ≠ 0 := by
    rw [lintegral_indicator_ball_self]
    exact (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) one_pos).ne'
  have htop : (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)) x) ≠ ⊤ := by
    rw [lintegral_indicator_ball_self]
    exact measure_ball_lt_top.ne
  refine ⟨ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1 / 2,
    Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)),
    (1 - 1 / 2 : ℝ) ^ n, by positivity, by norm_num, measurableSet_ball,
    fun y hy => Set.indicator_of_notMem hy _, convex_setOf_lt_indicator_ball,
    lovasz16_bound_indicator_ball hn (by norm_num) (by norm_num), h0, htop, ?_⟩
  exact avgLocalConductance_ge_half_of_lovasz16 hn measurableSet_ball
    (fun y hy => Set.indicator_of_notMem hy _) (by norm_num) convex_setOf_lt_indicator_ball
    (lovasz16_bound_indicator_ball hn (by norm_num) (by norm_num)) h0 htop

/-- **Non-vacuity witness for `avgLocalConductance_ge_quarter_of_lovasz16`** — the bundle whose
Lovász constant is forced to be at least `1/2`, so that a degenerate `c ≤ 0` cannot satisfy it.
Dimension `n = 2`, the unit disc, the uniform density, `σ = 1` and `δ = 1/(4096√2)`, which
makes `hstep` an *equality*; the Lovász hypothesis is discharged by the proved
`lovasz16_bound_indicator_ball` via `(1−δ)² ≥ 1/2`. -/
theorem exists_lovasz16_quarter_instance :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 2))) (δ σ : ℝ) (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞),
      0 < σ ∧ 0 < δ ∧ MeasurableSet K ∧ (∀ y, y ∉ K → f y = 0) ∧
      δ ≤ min σ 1 / (4096 * Real.sqrt ((2 : ℕ) : ℝ)) ∧
      (∀ x, Convex ℝ {y | f x < f y}) ∧
      (ENNReal.ofReal
          (1 - 32 * Real.sqrt δ * Real.sqrt (Real.sqrt ((2 : ℕ) : ℝ))
            / Real.sqrt (min σ 1)) * ∫⁻ x in K, f x ≤ ∫⁻ x in K, ballSmoothing16 f δ x) ∧
      (∫⁻ x in K, f x) ≠ 0 ∧ (∫⁻ x in K, f x) ≠ ⊤ := by
  have h2R : ((2 : ℕ) : ℝ) = 2 := by norm_num
  set r : ℝ := Real.sqrt ((2 : ℕ) : ℝ) with hrdef
  have hr1 : (1 : ℝ) ≤ r := by
    have h : Real.sqrt 1 ≤ Real.sqrt ((2 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by rw [h2R]; norm_num)
    rw [hrdef, ← Real.sqrt_one]
    exact h
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr1
  set q : ℝ := Real.sqrt r with hqdef
  have hq2 : q ^ 2 = r := Real.sq_sqrt hr0.le
  have hq1 : (1 : ℝ) ≤ q := by
    have h : Real.sqrt 1 ≤ Real.sqrt r := Real.sqrt_le_sqrt hr1
    rw [hqdef]; simpa using h
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq1
  set δ : ℝ := 1 / (4096 * q ^ 2) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδsmall : δ ≤ 1 / 4096 := by
    rw [hδdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hδ1 : δ < 1 := by linarith
  have hsd : Real.sqrt δ = 1 / (64 * q) := by
    have hsq : δ = (1 / (64 * q)) ^ 2 := by
      rw [hδdef, div_pow, mul_pow]
      norm_num
    rw [hsq]
    exact Real.sqrt_sq (by positivity)
  have hmin : min (1 : ℝ) 1 = 1 := min_self 1
  have hconst : 1 - 32 * Real.sqrt δ * q / Real.sqrt (min (1 : ℝ) 1) = 1 / 2 := by
    rw [hmin, Real.sqrt_one, hsd]
    field_simp
    ring
  have h0 : (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      Set.indicator (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) (fun _ => (1 : ℝ≥0∞)) x) ≠ 0 := by
    rw [lintegral_indicator_ball_self]
    exact (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin 2)) one_pos).ne'
  have htop : (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin 2)) 1,
      Set.indicator (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) (fun _ => (1 : ℝ≥0∞)) x) ≠ ⊤ := by
    rw [lintegral_indicator_ball_self]
    exact measure_ball_lt_top.ne
  refine ⟨ball (0 : EuclideanSpace ℝ (Fin 2)) 1, δ, 1,
    Set.indicator (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) (fun _ => (1 : ℝ≥0∞)),
    one_pos, hδ0, measurableSet_ball, fun y hy => Set.indicator_of_notMem hy _, ?_,
    convex_setOf_lt_indicator_ball, ?_, h0, htop⟩
  · rw [hmin, hδdef, hq2]
  · rw [hconst]
    refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
      (lovasz16_bound_indicator_ball (by norm_num) hδ0 hδ1)
    show (1 : ℝ) / 2 ≤ (1 - δ) ^ 2
    nlinarith [hδ0, hδsmall]

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.exists_apply_eq
#print axioms Arlib.MarkovChains.volume_setOf_apply_eq
#print axioms Arlib.MarkovChains.continuous_volume_cut
#print axioms Arlib.MarkovChains.exists_volume_cut_eq
#print axioms Arlib.MarkovChains.exists_convex_partition
#print axioms Arlib.MarkovChains.exists_nsmul_le_of_sum_le
#print axioms Arlib.MarkovChains.IsSixteenthBall.volume_ne_top
#print axioms Arlib.MarkovChains.IsSixteenthBall.volume_ne_zero
#print axioms Arlib.MarkovChains.ballSmoothing16_le
#print axioms Arlib.MarkovChains.le_ballSmoothing16
#print axioms Arlib.MarkovChains.ballSmoothing16_mul_volume_le
#print axioms Arlib.MarkovChains.exists_eight_sixteenthBalls
#print axioms Arlib.MarkovChains.exists_isSixteenthBall
#print axioms Arlib.MarkovChains.vadd_set_subset_vadd_set
#print axioms Arlib.MarkovChains.disjoint_vadd_set
#print axioms Arlib.MarkovChains.lintegral_le_of_sep
#print axioms Arlib.MarkovChains.exists_eight_pieces_at
#print axioms Arlib.MarkovChains.ballSmoothing16_le_self
#print axioms Arlib.MarkovChains.ballSmoothing16_le_two_mul_ell_mul
#print axioms Arlib.MarkovChains.ballSmoothing16_le_ell_mul_of_balanced
#print axioms Arlib.MarkovChains.ballSmoothing16_eq_zero_of_far_half_free
#print axioms Arlib.MarkovChains.exists_ne_zero_dual
#print axioms Arlib.MarkovChains.ballSmoothing16_mul_volume_le_two_mul
#print axioms Arlib.MarkovChains.ballSmoothing16_le_two_mul_ballSmoothing
#print axioms Arlib.MarkovChains.isLogConcaveENN_comp_linearMap
#print axioms Arlib.MarkovChains.isLogConcaveENN_mul
#print axioms Arlib.MarkovChains.isLogConcaveENN_div_const
#print axioms Arlib.MarkovChains.isLogConcaveENN_iInf
#print axioms Arlib.MarkovChains.isLogConcaveENN_setLIntegral_vadd
#print axioms Arlib.MarkovChains.isLogConcaveENN_ballSmoothing16
#print axioms Arlib.MarkovChains.exists_balanced_dual_of_isMax
#print axioms Arlib.MarkovChains.ballSmoothing16_le_ell_mul_of_isMax
#print axioms Arlib.MarkovChains.avgLocalConductance_ge_half_of_lovasz16
#print axioms Arlib.MarkovChains.avgLocalConductance_ge_of_lovasz16_balanced
#print axioms Arlib.MarkovChains.avgLocalConductance_ge_quarter_of_lovasz16
#print axioms Arlib.MarkovChains.avgLocalConductance_ge_half_of_lovasz16_balanced
#print axioms Arlib.MarkovChains.one_le_ballSmoothing16_indicator_ball
#print axioms Arlib.MarkovChains.lovasz16_bound_indicator_ball
#print axioms Arlib.MarkovChains.exists_lovasz16_balanced_instance
#print axioms Arlib.MarkovChains.exists_lovasz16_instance
#print axioms Arlib.MarkovChains.exists_lovasz16_quarter_instance
