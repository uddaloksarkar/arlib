/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFUpperShellProfile

/-!
# The support interval of a convex body's positive slices

This is the interval-support bridge needed by the upper-shell branch of the
Borell--KLS variational argument.  Sharp Brunn--Minkowski makes the set of heights with
positive slice volume convex.  Its `sInf` and `sSup` therefore span nonempty slices throughout
the open interval, exactly the domain on which the Brunn root can be endpoint-regularized.
-/

open Set MeasureTheory

namespace Arlib

variable {m : ℕ}

/-- Positive-volume slices of a convex measurable body form a convex set of heights. -/
theorem convex_positiveSliceSupport (hm : m ≠ 0)
    {K : Set (Fin (m + 1) → ℝ)} (hKconv : Convex ℝ K)
    (hKmeas : MeasurableSet K)
    (hfin : ∀ t : ℝ, volume (slice K t) ≠ ⊤) :
    Convex ℝ {t : ℝ | 0 < volume (slice K t)} := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hy
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  change 0 < volume (slice K x) at hx
  change 0 < volume (slice K y) at hy
  have hneX : (slice K x).Nonempty := by
    by_contra he
    rw [not_nonempty_iff_eq_empty.mp he, measure_empty] at hx
    exact lt_irrefl 0 hx
  have hneY : (slice K y).Nonempty := by
    by_contra he
    rw [not_nonempty_iff_eq_empty.mp he, measure_empty] at hy
    exact lt_irrefl 0 hy
  have hsharp := brunn_slice_sharp hm hKconv hKmeas ha (by linarith : a ≤ 1) hneX hneY
  have hrootX : 0 < volume (slice K x) ^ (1 / (m : ℝ)) :=
    ENNReal.rpow_pos hx (hfin x)
  have hterm : 0 < ENNReal.ofReal a * volume (slice K x) ^ (1 / (m : ℝ)) :=
    ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.2 ha')) (ne_of_gt hrootX)
  have hsum : 0 < ENNReal.ofReal a * volume (slice K x) ^ (1 / (m : ℝ)) +
      ENNReal.ofReal (1 - a) * volume (slice K y) ^ (1 / (m : ℝ)) :=
    hterm.trans_le (le_add_right (le_refl _))
  have hroot : 0 < volume (slice K (a * x + (1 - a) * y)) ^ (1 / (m : ℝ)) :=
    hsum.trans_le hsharp
  have hvol : 0 < volume (slice K (a * x + (1 - a) * y)) := by
    by_contra hn
    have hz : volume (slice K (a * x + (1 - a) * y)) = 0 :=
      le_antisymm (not_lt.mp hn) bot_le
    rw [hz, ENNReal.zero_rpow_of_pos (by positivity : (0 : ℝ) < 1 / (m : ℝ))] at hroot
    exact lt_irrefl 0 hroot
  have hb' : b = 1 - a := by linarith
  simpa [smul_eq_mul, hb'] using hvol

/-- Every slice of an affine upper shell has finite volume. -/
theorem volume_slice_affineUpperShell_ne_top {ψ : ℝ → ℝ}
    (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t) (u v t : ℝ) :
    volume (slice (affineUpperShell m ψ u v) t) ≠ ⊤ := by
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · have hsub : slice (affineUpperShell m ψ u v) t ⊆
        slice (profileBody (coordinateSimplex m) ψ) t := fun _y hy => hy.1
    refine ne_of_lt (lt_of_le_of_lt (measure_mono hsub) ?_)
    rw [volume_slice_profileBody ht (hψ0 t ht)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.2 volume_coordinateSimplex_ne_top)
  · have he : slice (affineUpperShell m ψ u v) t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro y hy
      exact ht ((mem_profileBody_coordinateSimplex_iff hψ0).mp hy.1).1
    rw [he, measure_empty]
    exact ENNReal.zero_ne_top

/-- The positive-slice support of an affine upper shell is convex. -/
theorem convex_affineUpperShell_positiveSliceSupport (hm : m ≠ 0)
    {ψ : ℝ → ℝ} (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hψm : Measurable ψ) (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    (u v : ℝ) :
    Convex ℝ {t : ℝ | 0 < volume (slice (affineUpperShell m ψ u v) t)} :=
  convex_positiveSliceSupport hm (convex_affineUpperShell hψ hψ0 u v)
    (measurableSet_affineUpperShell hψm hψ0 u v)
    (volume_slice_affineUpperShell_ne_top hψ0 u v)

/-- For a nonempty convex positive-slice support, every height strictly between its extremal
heights has a positive (hence nonempty) slice. -/
theorem Ioo_sInf_sSup_subset_positiveSliceSupport (hm : m ≠ 0)
    {K : Set (Fin (m + 1) → ℝ)} (hKconv : Convex ℝ K)
    (hKmeas : MeasurableSet K) (hfin : ∀ t : ℝ, volume (slice K t) ≠ ⊤)
    (hne : {t : ℝ | 0 < volume (slice K t)}.Nonempty)
    (hb : BddBelow {t : ℝ | 0 < volume (slice K t)})
    (ha : BddAbove {t : ℝ | 0 < volume (slice K t)}) :
    Ioo (sInf {t : ℝ | 0 < volume (slice K t)})
        (sSup {t : ℝ | 0 < volume (slice K t)}) ⊆
      {t : ℝ | 0 < volume (slice K t)} := by
  exact (convex_positiveSliceSupport hm hKconv hKmeas hfin).isConnected hne
    |>.Ioo_csInf_csSup_subset hb ha

/-- Endpoint-zero version of the Brunn root on the extremal positive-slice interval. -/
noncomputable def extremalSliceProfile (m : ℕ) (K : Set (Fin (m + 1) → ℝ)) (t : ℝ) : ℝ :=
  let S := {s : ℝ | 0 < volume (slice K s)}
  if t ∈ Ioo (sInf S) (sSup S) then
    (volume (slice K t)).toReal ^ (1 / (m : ℝ))
  else 0

theorem measurable_extremalSliceProfile {K : Set (Fin (m + 1) → ℝ)}
    (hKmeas : MeasurableSet K) : Measurable (extremalSliceProfile m K) := by
  unfold extremalSliceProfile
  exact ((measurable_volume_slice_toReal hKmeas).pow measurable_const).ite
    measurableSet_Ioo measurable_const

theorem extremalSliceProfile_nonneg (K : Set (Fin (m + 1) → ℝ)) (t : ℝ) :
    0 ≤ extremalSliceProfile m K t := by
  simp only [extremalSliceProfile]
  split_ifs <;> positivity

/-- Normalize a concave profile from an arbitrary interval to `[0,1]`. -/
theorem concaveOn_rescaledIntervalProfile {φ : ℝ → ℝ} {l u : ℝ}
    (hφ : ConcaveOn ℝ (Icc l u) φ) (hlu : l ≤ u) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (rescaledSubsegmentProfile φ l u) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hmap : ∀ z ∈ Icc (0 : ℝ) 1, l + (u - l) * z ∈ Icc l u := by
    intro z hz
    constructor <;> nlinarith [hz.1, hz.2]
  have hxy : a * x + b * y ∈ Icc (0 : ℝ) 1 :=
    (convex_Icc (0 : ℝ) 1) hx hy ha hb hab
  have hxy' : a • x + b • y ∈ Icc (0 : ℝ) 1 := by
    simpa only [smul_eq_mul] using hxy
  rw [rescaledSubsegmentProfile_of_mem hx, rescaledSubsegmentProfile_of_mem hy,
    rescaledSubsegmentProfile_of_mem hxy']
  have hc := hφ.2 (hmap x hx) (hmap y hy) ha hb hab
  dsimp only [smul_eq_mul] at hc ⊢
  convert hc using 1
  congr 1
  linear_combination -l * hab

/-- The extremal positive-slice profile is concave on the closed extremal interval. -/
theorem concaveOn_extremalSliceProfile (hm : m ≠ 0)
    {K : Set (Fin (m + 1) → ℝ)} (hKconv : Convex ℝ K)
    (hKmeas : MeasurableSet K) (hfin : ∀ t : ℝ, volume (slice K t) ≠ ⊤)
    (hne : {t : ℝ | 0 < volume (slice K t)}.Nonempty)
    (hb : BddBelow {t : ℝ | 0 < volume (slice K t)})
    (ha : BddAbove {t : ℝ | 0 < volume (slice K t)}) :
    ConcaveOn ℝ
      (Icc (sInf {t : ℝ | 0 < volume (slice K t)})
        (sSup {t : ℝ | 0 < volume (slice K t)}))
      (extremalSliceProfile m K) := by
  let S := {t : ℝ | 0 < volume (slice K t)}
  have hsub : Ioo (sInf S) (sSup S) ⊆ S :=
    Ioo_sInf_sSup_subset_positiveSliceSupport hm hKconv hKmeas hfin hne hb ha
  have hroot : ConcaveOn ℝ (Ioo (sInf S) (sSup S))
      (fun t => (volume (slice K t)).toReal ^ (1 / (m : ℝ))) := by
    apply brunn_slice_concaveOn hm hKconv hKmeas (convex_Ioo _ _)
    · intro t ht
      have hpos := hsub ht
      change 0 < volume (slice K t) at hpos
      by_contra he
      rw [not_nonempty_iff_eq_empty.mp he, measure_empty] at hpos
      exact lt_irrefl 0 hpos
    · intro t _ht
      exact hfin t
  have hzero : ∀ t ∈ Ioo (sInf S) (sSup S),
      0 ≤ (volume (slice K t)).toReal ^ (1 / (m : ℝ)) := by
    intro t ht
    positivity
  unfold extremalSliceProfile
  exact concaveOn_Icc_extendZero hroot hzero

/-- Away from the two extremal heights, the endpoint-regularized profile has exactly the
original slice volume as its `m`-th power. -/
theorem extremalSliceProfile_pow_eq_off_endpoints (hm : m ≠ 0)
    {K : Set (Fin (m + 1) → ℝ)}
    (hb : BddBelow {t : ℝ | 0 < volume (slice K t)})
    (ha : BddAbove {t : ℝ | 0 < volume (slice K t)})
    {t : ℝ}
    (htl : t ≠ sInf {s : ℝ | 0 < volume (slice K s)})
    (htu : t ≠ sSup {s : ℝ | 0 < volume (slice K s)}) :
    extremalSliceProfile m K t ^ m = (volume (slice K t)).toReal := by
  let S := {s : ℝ | 0 < volume (slice K s)}
  by_cases ht : t ∈ Ioo (sInf S) (sSup S)
  · rw [extremalSliceProfile]
    simp only [S, if_pos ht]
    simpa only [one_div] using
      (Real.rpow_inv_natCast_pow (x := (volume (slice K t)).toReal)
        ENNReal.toReal_nonneg hm)
  · have hvol : volume (slice K t) = 0 := by
      by_contra hne0
      have htpos : 0 < volume (slice K t) := (pos_iff_ne_zero).2 hne0
      have htS : t ∈ S := htpos
      have hlow : sInf S ≤ t := csInf_le hb htS
      have hupp : t ≤ sSup S := le_csSup ha htS
      have hlt : sInf S < t := lt_of_le_of_ne hlow (by
        intro h
        exact htl (h.symm.trans (by rfl)))
      have htu' : t < sSup S := lt_of_le_of_ne hupp (by
        intro h
        exact htu (h.trans (by rfl)))
      exact ht ⟨hlt, htu'⟩
    rw [extremalSliceProfile]
    simp only [S, if_neg ht, zero_pow hm, hvol, ENNReal.toReal_zero]

/-- Endpoint regularization changes none of the slice moments: the only possible discrepancies
are the two Lebesgue-null extremal heights. -/
theorem integral_extremalSliceProfile_pow_mul (hm : m ≠ 0)
    {K : Set (Fin (m + 1) → ℝ)}
    (hb : BddBelow {t : ℝ | 0 < volume (slice K t)})
    (ha : BddAbove {t : ℝ | 0 < volume (slice K t)}) (F : ℝ → ℝ) :
    (∫ t : ℝ, extremalSliceProfile m K t ^ m * F t) =
      ∫ t : ℝ, (volume (slice K t)).toReal * F t := by
  apply integral_congr_off_pair
  intro t htl htu
  rw [extremalSliceProfile_pow_eq_off_endpoints hm hb ha htl htu]

/-- One-sided positive-slice support gives a strict upper bound on the physical support width. -/
theorem extremalSliceEndpoints_lt_one_of_oneSided
    {K : Set (Fin (m + 1) → ℝ)} {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1)
    (hne : {t : ℝ | 0 < volume (slice K t)}.Nonempty)
    (hside : {t : ℝ | 0 < volume (slice K t)} ⊆ Ico 0 r ∨
      {t : ℝ | 0 < volume (slice K t)} ⊆ Ioc r 1) :
    sSup {t : ℝ | 0 < volume (slice K t)} -
        sInf {t : ℝ | 0 < volume (slice K t)} < 1 := by
  let S := {t : ℝ | 0 < volume (slice K t)}
  rcases hside with hleft | hright
  · have hl : 0 ≤ sInf S := le_csInf hne fun t ht => (hleft ht).1
    have hu : sSup S ≤ r := csSup_le hne fun t ht => (hleft ht).2.le
    dsimp [S] at hl hu
    linarith [hr.2]
  · have hl : r ≤ sInf S := le_csInf hne fun t ht => (hright ht).1.le
    have hu : sSup S ≤ 1 := csSup_le hne fun t ht => (hright ht).2
    dsimp [S] at hl hu
    linarith [hr.1]

/-- Positive total slice mass rules out a singleton positive-slice support. -/
theorem sInf_lt_sSup_positiveSliceSupport_of_integral_pos
    {K : Set (Fin (m + 1) → ℝ)}
    (hne : {t : ℝ | 0 < volume (slice K t)}.Nonempty)
    (hb : BddBelow {t : ℝ | 0 < volume (slice K t)})
    (ha : BddAbove {t : ℝ | 0 < volume (slice K t)})
    (hmass : 0 < ∫ t : ℝ, (volume (slice K t)).toReal) :
    sInf {t : ℝ | 0 < volume (slice K t)} <
      sSup {t : ℝ | 0 < volume (slice K t)} := by
  let S := {t : ℝ | 0 < volume (slice K t)}
  obtain ⟨x, hx⟩ := hne
  have hle : sInf S ≤ sSup S :=
    (csInf_le hb hx).trans (le_csSup ha hx)
  by_contra hnlt
  have heq : sInf S = sSup S := le_antisymm hle (not_lt.mp hnlt)
  have hzint : (∫ t : ℝ, (volume (slice K t)).toReal) = 0 := by
    rw [← integral_zero]
    apply integral_congr_off_pair (x := sInf S) (y := sSup S)
    intro t htl htu
    have hz : volume (slice K t) = 0 := by
      by_contra hne0
      have ht : t ∈ S := (pos_iff_ne_zero).2 hne0
      have htlow : sInf S ≤ t := csInf_le hb ht
      have htupp : t ≤ sSup S := le_csSup ha ht
      have : t = sInf S := by linarith
      exact htl this
    simp [hz]
  linarith

/-! ## Direct support-minimality consumer -/

/-- **Convex-slice support shrink contradicts a support-minimizing BF candidate.**

This consumes the three exact Fubini moments of a convex selected body `D`.  Its extremal Brunn
profile is endpoint-regularized, affinely pulled back to `[0,1]`, and used to construct a literal
`BFMovingRawCandidate` on the shorter physical subsegment.  Thus the upper-shell branch no
longer needs an abstract "selected profile" premise. -/
theorem BFMovingCandidate.not_feasible_convexSliceBody_of_eq_sInf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hKconv : Convex ℝ K) {g h : E → ℝ}
    (c : BFMovingCandidate K g h m)
    (hmin : c.supportLength = sInf (Set.range
      (fun q : BFMovingCandidate K g h m => q.supportLength)))
    (hcne : c.left ≠ c.right) (hm : m ≠ 0)
    {D : Set (Fin (m + 1) → ℝ)} (hDconv : Convex ℝ D)
    (hDmeas : MeasurableSet D) (hfin : ∀ t : ℝ, volume (slice D t) ≠ ⊤)
    (hSne : {t : ℝ | 0 < volume (slice D t)}.Nonempty)
    (hb : BddBelow {t : ℝ | 0 < volume (slice D t)})
    (ha : BddAbove {t : ℝ | 0 < volume (slice D t)})
    (hl : 0 ≤ sInf {t : ℝ | 0 < volume (slice D t)})
    (hlu : sInf {t : ℝ | 0 < volume (slice D t)} <
      sSup {t : ℝ | 0 < volume (slice D t)})
    (hu : sSup {t : ℝ | 0 < volume (slice D t)} ≤ 1)
    (hwidth : sSup {t : ℝ | 0 < volume (slice D t)} -
      sInf {t : ℝ | 0 < volume (slice D t)} < 1)
    (hmass : 0 < ∫ t : ℝ, (volume (slice D t)).toReal)
    (hgzero : (∫ t : ℝ, (volume (slice D t)).toReal *
      g (bfSegmentPoint c.left c.right t)) = 0)
    (hhpos : 0 ≤ ∫ t : ℝ, (volume (slice D t)).toReal *
      h (bfSegmentPoint c.left c.right t)) : False := by
  let S := {t : ℝ | 0 < volume (slice D t)}
  let l := sInf S
  let u := sSup S
  let φ := extremalSliceProfile m D
  have hφconc : ConcaveOn ℝ (Icc l u) φ :=
    concaveOn_extremalSliceProfile hm hDconv hDmeas hfin hSne hb ha
  have hmassφ : 0 < ∫ t : ℝ, φ t ^ m := by
    change 0 < ∫ t : ℝ, extremalSliceProfile m D t ^ m
    have heq := integral_extremalSliceProfile_pow_mul hm hb ha (fun _ => 1)
    simp only [mul_one] at heq
    rw [heq]
    exact hmass
  have hgφ : (∫ t : ℝ, φ t ^ m *
      g (bfSegmentPoint c.left c.right t)) = 0 := by
    rw [integral_extremalSliceProfile_pow_mul hm hb ha
      (fun t => g (bfSegmentPoint c.left c.right t))]
    exact hgzero
  have hhφ : 0 ≤ ∫ t : ℝ, φ t ^ m *
      h (bfSegmentPoint c.left c.right t) := by
    rw [integral_extremalSliceProfile_pow_mul hm hb ha
      (fun t => h (bfSegmentPoint c.left c.right t))]
    exact hhpos
  have hmassRescaled : 0 < ∫ s : ℝ, rescaledSubsegmentProfile φ l u s ^ m := by
    have hres := integral_rescaledSubsegmentProfile_pow_mul (ψ := φ) (l := l) (u := u)
      (F := fun _ => 1) hm hlu
    simp only [mul_one] at hres
    rw [hres]
    have hrestrict : (∫ t in Icc l u, φ t ^ m) = ∫ t : ℝ, φ t ^ m := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ Icc l u
      · simp [ht]
      · have hzero : φ t = 0 := by
          unfold φ extremalSliceProfile
          exact if_neg (fun h => ht (Ioo_subset_Icc_self h))
        simp [ht, hzero, hm]
    rw [hrestrict]
    exact mul_pos (inv_pos.mpr (sub_pos.mpr hlu)) hmassφ
  have hgRescaled : (∫ s : ℝ, rescaledSubsegmentProfile φ l u s ^ m *
      g (bfSegmentPoint c.left c.right (l + (u - l) * s))) = 0 := by
    rw [integral_rescaledSubsegmentProfile_pow_mul (ψ := φ) (l := l) (u := u)
      (F := fun t => g (bfSegmentPoint c.left c.right t)) hm hlu]
    have hrestrict : (∫ t in Icc l u, φ t ^ m *
        g (bfSegmentPoint c.left c.right t)) =
        ∫ t : ℝ, φ t ^ m * g (bfSegmentPoint c.left c.right t) := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ Icc l u
      · simp [ht]
      · have hzero : φ t = 0 := by
          unfold φ extremalSliceProfile
          exact if_neg (fun h => ht (Ioo_subset_Icc_self h))
        simp [ht, hzero, hm]
    rw [hrestrict, hgφ, mul_zero]
  have hhRescaled : 0 ≤ ∫ s : ℝ, rescaledSubsegmentProfile φ l u s ^ m *
      h (bfSegmentPoint c.left c.right (l + (u - l) * s)) := by
    rw [integral_rescaledSubsegmentProfile_pow_mul (ψ := φ) (l := l) (u := u)
      (F := fun t => h (bfSegmentPoint c.left c.right t)) hm hlu]
    have hrestrict : (∫ t in Icc l u, φ t ^ m *
        h (bfSegmentPoint c.left c.right t)) =
        ∫ t : ℝ, φ t ^ m * h (bfSegmentPoint c.left c.right t) := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun t => ?_
      by_cases ht : t ∈ Icc l u
      · simp [ht]
      · have hzero : φ t = 0 := by
          unfold φ extremalSliceProfile
          exact if_neg (fun h => ht (Ioo_subset_Icc_self h))
        simp [ht, hzero, hm]
    rw [hrestrict]
    exact mul_nonneg (inv_pos.mpr (sub_pos.mpr hlu)).le hhφ
  let q : BFMovingRawCandidate K g h m := {
    left := bfSegmentPoint c.left c.right l
    right := bfSegmentPoint c.left c.right u
    left_mem := hKconv c.left_mem c.right_mem (sub_nonneg.mpr (hlu.le.trans hu)) hl (by ring)
    right_mem := hKconv c.left_mem c.right_mem (sub_nonneg.mpr hu) (hl.trans hlu.le) (by ring)
    profile := rescaledSubsegmentProfile φ l u
    profile_concave := concaveOn_rescaledIntervalProfile hφconc hlu.le
    profile_nonneg := fun s => by
      by_cases hs : s ∈ Icc (0 : ℝ) 1
      · rw [rescaledSubsegmentProfile_of_mem hs]
        exact extremalSliceProfile_nonneg D _
      · rw [rescaledSubsegmentProfile_of_notMem hs]
    profile_off := fun s hs => rescaledSubsegmentProfile_of_notMem hs
    profile_measurable := measurable_rescaledSubsegmentProfile
      (measurable_extremalSliceProfile hDmeas) l u
    mass_pos := hmassRescaled
    g_zero := by simpa only [bfSegmentPoint_subsegment] using hgRescaled
    h_nonneg := by simpa only [bfSegmentPoint_subsegment] using hhRescaled }
  have hle := c.supportLength_le_raw_of_eq_sInf hm hmin q
  rw [BFMovingCandidate.supportLength,
    show q.left = bfSegmentPoint c.left c.right l from rfl,
    show q.right = bfSegmentPoint c.left c.right u from rfl,
    dist_bfSegmentPoint_subsegment, abs_of_nonneg (sub_nonneg.mpr hlu.le)] at hle
  have hdpos : 0 < dist c.left c.right := dist_pos.mpr hcne
  exact (not_lt_of_ge hle) (by
    change (u - l) * dist c.left c.right < dist c.left c.right
    nlinarith [hwidth])

/-- **Upper-shell alternative eliminated by support minimality.**  An affine roof touching the
profile at an interior height produces a strictly shorter feasible candidate, provided the
selected shell carries the selector's mass and two moments.  All geometry, slice concavity,
endpoint regularization, and support arithmetic are discharged here. -/
theorem BFMovingCandidate.not_feasible_affineUpperShell_of_eq_sInf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hKconv : Convex ℝ K) {g h : E → ℝ}
    (c : BFMovingCandidate K g h m)
    (hmin : c.supportLength = sInf (Set.range
      (fun q : BFMovingCandidate K g h m => q.supportLength)))
    (hcne : c.left ≠ c.right) (hm : m ≠ 0)
    {ψ : ℝ → ℝ} (hψ : ConcaveOn ℝ (Icc (0 : ℝ) 1) ψ)
    (hψmeas : Measurable ψ) (hψ0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ψ t)
    {u v r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) (htouch : u * r + v = ψ r)
    (hSne : {t : ℝ | 0 < volume (slice (affineUpperShell m ψ u v) t)}.Nonempty)
    (hmass : 0 < ∫ t : ℝ,
      (volume (slice (affineUpperShell m ψ u v) t)).toReal)
    (hgzero : (∫ t : ℝ, (volume (slice (affineUpperShell m ψ u v) t)).toReal *
      g (bfSegmentPoint c.left c.right t)) = 0)
    (hhpos : 0 ≤ ∫ t : ℝ,
      (volume (slice (affineUpperShell m ψ u v) t)).toReal *
      h (bfSegmentPoint c.left c.right t)) : False := by
  let D := affineUpperShell m ψ u v
  let S := {t : ℝ | 0 < volume (slice D t)}
  have hmem : ∀ t ∈ S, t ∈ Icc (0 : ℝ) 1 := by
    intro t ht
    exact (affineUpperShell_slice_volume_pos_imp hψ0 ht).1
  have hb : BddBelow S := ⟨0, fun t ht => (hmem t ht).1⟩
  have ha : BddAbove S := ⟨1, fun t ht => (hmem t ht).2⟩
  have hl : 0 ≤ sInf S := le_csInf hSne fun t ht => (hmem t ht).1
  have hu : sSup S ≤ 1 := csSup_le hSne fun t ht => (hmem t ht).2
  have hlu : sInf S < sSup S :=
    sInf_lt_sSup_positiveSliceSupport_of_integral_pos hSne hb ha hmass
  have hside : S ⊆ Ico 0 r ∨ S ⊆ Ioc r 1 :=
    affineUpperShell_positiveSliceSupport_shrinks hψ hψ0 hr htouch
  have hwidth : sSup S - sInf S < 1 :=
    extremalSliceEndpoints_lt_one_of_oneSided hr hSne hside
  exact c.not_feasible_convexSliceBody_of_eq_sInf hKconv hmin hcne hm
    (convex_affineUpperShell hψ hψ0 u v)
    (measurableSet_affineUpperShell hψmeas hψ0 u v)
    (volume_slice_affineUpperShell_ne_top hψ0 u v) hSne hb ha hl hlu hu hwidth
    hmass hgzero hhpos

end Arlib

#print axioms Arlib.convex_positiveSliceSupport
#print axioms Arlib.volume_slice_affineUpperShell_ne_top
#print axioms Arlib.convex_affineUpperShell_positiveSliceSupport
#print axioms Arlib.Ioo_sInf_sSup_subset_positiveSliceSupport
#print axioms Arlib.concaveOn_extremalSliceProfile
#print axioms Arlib.extremalSliceProfile_pow_eq_off_endpoints
#print axioms Arlib.integral_extremalSliceProfile_pow_mul
#print axioms Arlib.extremalSliceEndpoints_lt_one_of_oneSided
#print axioms Arlib.sInf_lt_sSup_positiveSliceSupport_of_integral_pos
#print axioms Arlib.concaveOn_rescaledIntervalProfile
#print axioms Arlib.BFMovingCandidate.not_feasible_convexSliceBody_of_eq_sInf
#print axioms Arlib.BFMovingCandidate.not_feasible_affineUpperShell_of_eq_sInf
