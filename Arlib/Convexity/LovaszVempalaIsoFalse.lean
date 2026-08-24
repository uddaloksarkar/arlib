/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.Convexity.LovaszVempalaIso
import Arlib.Convexity.LocalizationTransport
import Arlib.Probability.UniformOn

/-!
# Lovász–Vempala Theorem 2.1 is false as stated — machine-checked

> L. Lovász and S. Vempala, *Hit-and-Run from a Corner*, STOC 2004 / SIAM J. Comput. **35**
> (2006) 985–1005, **Theorem 2.1**.

`Arlib.Convexity.LovaszVempalaIso` records, in prose, that Theorem 2.1 is false as printed, and
proves the geometric core of the counterexample (`Arlib.chord_le_of_corner_boxes`).  This file
completes the refutation: the five box volumes, the `∫⁻` of the weight, and the `uniformOn`
arithmetic.

## The headline

`Arlib.not_hIso_two` is the **negation of the `hIso` binder of
`Arlib.MarkovChains.conductance_hitAndRun_ge` as that binder stood before the repair of this
date**, written out verbatim at `n = 2` and `K = cexK`.  A reader can confirm the refutation
from the statement alone.

The binder now carries an extra clause `∀ x ∈ K, h x ≤ 1/3`, inserted *because of* this
refutation; `Arlib.cexH_not_le_third` is the check that the new clause is exactly what the
counterexample violates, and `Arlib.not_hIso_two_measurable` is the check that adding
`Measurable h` would not have been a repair.

## The data, and why `[0,4]²` rather than `[0,1]²`

* `Arlib.cexK   = [0,4]²`         — the body.
* `Arlib.cexT₁  = [0,1/2]²`       — one corner box.
* `Arlib.cexT₂  = [7/2,4]×[0,1/2]`— the opposite bottom corner box.
* `Arlib.cexN   = [0,4]×[4/3,4]`  — the region no cross chord reaches.
* `Arlib.cexH   = 1000·1_N`       — the weight.

The dilation factor `4` is not cosmetic.  Theorem 2.1 itself is refuted just as well on the
unit square, but `conductance_hitAndRun_ge` additionally asks that `K` **contain a unit ball**,
and `[0,1]²` does not.  `[0,4]²` does, at its centre `(2,2)`, so
`Arlib.cexK_hitAndRun_hypotheses` discharges *every other* geometric hypothesis of that theorem
at the very instance where `Arlib.not_hIso_two` refutes `hIso`.  The conclusion is therefore not
merely "Theorem 2.1 is false somewhere" but "`conductance_hitAndRun_ge`'s guarantee is empty at
a body satisfying all of its other hypotheses".  (It says nothing about `n = 1`, where every
chord is all of `K` and the chord hypothesis does constrain `h` everywhere.)

## The numbers

`vol K = 16`, `vol T₁ = vol T₂ = 1/4`, `vol N = 32/3`, so under `π = uniformOn volume K`

    π T₁ = π T₂ = 1/64,     π N = 2/3,     E_π(cexH) = 1000 · 2/3,

and the left-hand side of Theorem 2.1's conclusion is `1000 · (2/3) · (1/64) = 125/12 > 1`,
while the right-hand side is a probability, hence `≤ 1`.  Any constant `> 96` in place of `1000`
does; `1000` leaves room.

Every hypothesis of Theorem 2.1 holds.  The only non-obvious one is the chord bound, and it
holds because `cexH` is *identically zero* on every cross chord: by `Arlib.chord_le_of_cex` such
a chord never rises above height `7/6 < 4/3`, so it misses `cexN`.  The right-hand side
`min(1, d_K(u,v))/3` is nonnegative by `Arlib.crossRatioDist_nonneg`, so `0 ≤` it.

## What this does **not** say

It does not say the conductance bound of Lovász–Vempala is wrong.  The repair —
`∀ x ∈ K, h x ≤ 1/3`, which the paper's own §4 application verifies and which
`Arlib.MarkovChains.stepRadius_le_two_mul_diam` proves in the stronger form `1/(24√n)` — costs
the argument nothing, and the repaired theorem is `Arlib.needle_iso` /
`Arlib.needle_iso_of_chord`, both unconditional.  `Arlib.cexH_not_le_third` checks that the
repair is what kills this counterexample, i.e. that the extra clause is doing real work rather
than making the hypothesis vacuous.

## Provenance of the transport

The volume computations go through `Arlib.volume_preimage_toLp` and
`Arlib.measurableSet_preimage_toLp_iff` of `Arlib.Convexity.LocalizationTransport`
(`PiLp.volume_preserving_toLp`), since `EuclideanSpace ℝ (Fin 2)` is `WithLp 2 (Fin 2 → ℝ)` and
`WithLp` is a structure, not a definitional synonym.
-/

namespace Arlib

open MeasureTheory Set
open scoped ENNReal

/-! ### Coordinate boxes in the Euclidean plane -/

section PlaneBox

/-- A closed coordinate box `[a,b] × [c,d]` in `EuclideanSpace ℝ (Fin 2)`.  A plain explicit
definition; every property of it below is proved. -/
def planeBox (a b c d : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | x 0 ∈ Set.Icc a b ∧ x 1 ∈ Set.Icc c d}

theorem mem_planeBox {a b c d : ℝ} {x : EuclideanSpace ℝ (Fin 2)} :
    x ∈ planeBox a b c d ↔ (a ≤ x 0 ∧ x 0 ≤ b) ∧ (c ≤ x 1 ∧ x 1 ≤ d) := Iff.rfl

/-- Read through the `WithLp` transport, a plane box is a product of intervals. -/
theorem preimage_toLp_planeBox (a b c d : ℝ) :
    (WithLp.toLp 2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2)) ⁻¹' planeBox a b c d
      = Set.univ.pi ![Set.Icc a b, Set.Icc c d] := by
  ext y
  simp [planeBox, Fin.forall_fin_two]

theorem measurableSet_planeBox (a b c d : ℝ) : MeasurableSet (planeBox a b c d) := by
  rw [← measurableSet_preimage_toLp_iff, preimage_toLp_planeBox]
  exact MeasurableSet.univ_pi fun i => by fin_cases i <;> simp [measurableSet_Icc]

theorem isCompact_planeBox (a b c d : ℝ) : IsCompact (planeBox a b c d) := by
  rw [← isCompact_preimage_toLp_iff, preimage_toLp_planeBox]
  exact isCompact_univ_pi fun i => by fin_cases i <;> simp [isCompact_Icc]

theorem convex_planeBox (a b c d : ℝ) : Convex ℝ (planeBox a b c d) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hx
  obtain ⟨⟨g1, g2⟩, g3, g4⟩ := hy
  have htv : t = 1 - s := by linarith
  subst htv
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] <;>
    nlinarith [mul_nonneg hs (sub_nonneg.2 h1), mul_nonneg ht (sub_nonneg.2 g1),
      mul_nonneg hs (sub_nonneg.2 h2), mul_nonneg ht (sub_nonneg.2 g2),
      mul_nonneg hs (sub_nonneg.2 h3), mul_nonneg ht (sub_nonneg.2 g3),
      mul_nonneg hs (sub_nonneg.2 h4), mul_nonneg ht (sub_nonneg.2 g4)]

/-- **The volume of a plane box** is the product of its side lengths. -/
theorem volume_planeBox {a b c d : ℝ} (hab : a ≤ b) :
    volume (planeBox a b c d) = ENNReal.ofReal ((b - a) * (d - c)) := by
  rw [← volume_preimage_toLp (measurableSet_planeBox a b c d).nullMeasurableSet,
    preimage_toLp_planeBox, volume_pi_pi]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Real.volume_Icc]
  rw [← ENNReal.ofReal_mul (by linarith)]

end PlaneBox

/-! ### The counterexample data -/

section Data

/-- `K = [0,4]²`.  The dilation by `4` of the unit square of the module docstring of
`Arlib.Convexity.LovaszVempalaIso`; the factor `4` is there only so that `K` contains a unit
ball (at its centre `(2,2)`) and therefore satisfies the *other* hypotheses of
`Arlib.MarkovChains.conductance_hitAndRun_ge`. -/
def cexK : Set (EuclideanSpace ℝ (Fin 2)) := planeBox 0 4 0 4

/-- `S₁ = [0,1/2]²`, the corner box at the origin. -/
def cexT₁ : Set (EuclideanSpace ℝ (Fin 2)) := planeBox 0 (1 / 2) 0 (1 / 2)

/-- `S₂ = [7/2,4] × [0,1/2]`, the corner box at the opposite bottom corner. -/
def cexT₂ : Set (EuclideanSpace ℝ (Fin 2)) := planeBox (7 / 2) 4 0 (1 / 2)

/-- `N = [0,4] × [4/3,4]`, the upper part of `K`, which **no chord through `cexT₁` and `cexT₂`
ever reaches**.  This is where the unconstrained weight lives. -/
def cexN : Set (EuclideanSpace ℝ (Fin 2)) := planeBox 0 4 (4 / 3) 4

/-- The weight: `1000` on `N` and `0` elsewhere.  Any constant `> 96` does; `1000` leaves room. -/
noncomputable def cexH : EuclideanSpace ℝ (Fin 2) → ℝ := cexN.indicator fun _ => 1000

theorem measurableSet_cexK : MeasurableSet cexK := measurableSet_planeBox 0 4 0 4

theorem measurableSet_cexT₁ : MeasurableSet cexT₁ := measurableSet_planeBox _ _ _ _

theorem measurableSet_cexT₂ : MeasurableSet cexT₂ := measurableSet_planeBox _ _ _ _

theorem measurableSet_cexN : MeasurableSet cexN := measurableSet_planeBox _ _ _ _

theorem cexT₁_subset : cexT₁ ⊆ cexK := by
  rintro x ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, by linarith⟩, h3, by linarith⟩

theorem cexT₂_subset : cexT₂ ⊆ cexK := by
  rintro x ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, h2⟩, h3, by linarith⟩

theorem cexN_subset : cexN ⊆ cexK := by
  rintro x ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h2⟩, by linarith, h4⟩

theorem cexT₁_disjoint : Disjoint cexT₁ cexT₂ :=
  Set.disjoint_left.mpr fun x hx hx' => by
    have := hx.1.2; have := hx'.1.1; linarith

theorem volume_cexK : volume cexK = ENNReal.ofReal 16 := by
  rw [cexK, volume_planeBox (by norm_num)]; norm_num

/-- The uniform measure of a sub-box of `K`, as an explicit real. -/
theorem uniformOn_cexK_planeBox {a b c d : ℝ} (hab : a ≤ b)
    (hsub : planeBox a b c d ⊆ cexK) :
    uniformOn volume cexK (planeBox a b c d) = ENNReal.ofReal ((b - a) * (d - c) / 16) := by
  rw [uniformOn_apply volume measurableSet_cexK (measurableSet_planeBox a b c d),
    Set.inter_eq_self_of_subset_left hsub, volume_planeBox hab, volume_cexK,
    ← ENNReal.ofReal_div_of_pos (by norm_num)]

theorem uniformOn_cexT₁ : uniformOn volume cexK cexT₁ = ENNReal.ofReal (1 / 64) := by
  rw [cexT₁, uniformOn_cexK_planeBox (by norm_num) cexT₁_subset]; norm_num

theorem uniformOn_cexT₂ : uniformOn volume cexK cexT₂ = ENNReal.ofReal (1 / 64) := by
  rw [cexT₂, uniformOn_cexK_planeBox (by norm_num) cexT₂_subset]; norm_num

theorem uniformOn_cexN : uniformOn volume cexK cexN = ENNReal.ofReal (2 / 3) := by
  rw [cexN, uniformOn_cexK_planeBox (by norm_num) cexN_subset]; norm_num

theorem isCompact_cexK : IsCompact cexK := isCompact_planeBox 0 4 0 4

end Data

/-! ### No chord through the two corner boxes reaches `cexN` -/

section Chord

/-- **The dilation by `4` of `Arlib.chord_le_of_corner_boxes`.**  For `u ∈ [0,1/2]²`,
`v ∈ [7/2,4]×[0,1/2]` and `x ∈ [0,4]²` on the chord through `u` and `v`, `x₁ ≤ 7/6`.

Proved *from* the unit-square lemma by scaling all three points by `4⁻¹`; `AffineMap.lineMap`
commutes with a scalar multiple, and every box hypothesis scales. -/
theorem chord_le_of_cex {u v x : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hu : u ∈ cexT₁) (hv : v ∈ cexT₂) (hx : x ∈ cexK)
    (hxr : x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin 2)) r) :
    x 1 ≤ 7 / 6 := by
  obtain ⟨⟨hu0a, hu0b⟩, hu1a, hu1b⟩ := hu
  obtain ⟨⟨hv0a, hv0b⟩, hv1a, hv1b⟩ := hv
  obtain ⟨⟨hx0a, hx0b⟩, -⟩ := hx
  have hsmul : ∀ (w : EuclideanSpace ℝ (Fin 2)) (i : Fin 2),
      ((4 : ℝ)⁻¹ • w) i = 4⁻¹ * w i := fun w i => by simp
  have hlm : ((4 : ℝ)⁻¹ • x)
      = (AffineMap.lineMap ((4 : ℝ)⁻¹ • u) ((4 : ℝ)⁻¹ • v) :
          ℝ → EuclideanSpace ℝ (Fin 2)) r := by
    rw [hxr, lineMap_apply', lineMap_apply']
    module
  have key := chord_le_of_corner_boxes (u := (4 : ℝ)⁻¹ • u) (v := (4 : ℝ)⁻¹ • v)
    (x := (4 : ℝ)⁻¹ • x) (r := r)
    (by constructor <;> (rw [hsmul]; linarith)) (by constructor <;> (rw [hsmul]; linarith))
    (by constructor <;> (rw [hsmul]; linarith)) (by constructor <;> (rw [hsmul]; linarith))
    (by constructor <;> (rw [hsmul]; linarith)) hlm
  rw [hsmul] at key
  linarith

/-- Hence the weight vanishes on every such chord. -/
theorem cexH_eq_zero_of_chord {u v x : EuclideanSpace ℝ (Fin 2)} {r : ℝ}
    (hu : u ∈ cexT₁) (hv : v ∈ cexT₂) (hx : x ∈ cexK)
    (hxr : x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin 2)) r) :
    cexH x = 0 := by
  have h := chord_le_of_cex hu hv hx hxr
  rw [cexH, Set.indicator_of_notMem]
  rintro ⟨-, h1, -⟩
  linarith

/-- **The hypothesis of Theorem 2.1 holds for `cexH`.**  On a cross chord `cexH` is `0`, and the
right-hand side is nonnegative because `Arlib.crossRatioDist` is. -/
theorem cexH_chord : ∀ u ∈ cexT₁, ∀ v ∈ cexT₂, ∀ x ∈ cexK,
    (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin 2)) t) →
    cexH x ≤ min 1 (crossRatioDist cexK u v) / 3 := by
  rintro u hu v hv x hx ⟨r, hr⟩
  rw [cexH_eq_zero_of_chord hu hv hx hr]
  have hne : u ≠ v := by
    intro hq
    have h1 : u 0 ≤ 1 / 2 := hu.1.2
    have h2 : (7 : ℝ) / 2 ≤ v 0 := hv.1.1
    rw [hq] at h1
    linarith
  have hd : 0 ≤ crossRatioDist cexK u v :=
    crossRatioDist_nonneg isCompact_cexK.isBounded hne (cexT₁_subset hu) (cexT₂_subset hv)
  have hmin : 0 ≤ min 1 (crossRatioDist cexK u v) := le_min zero_le_one hd
  linarith

theorem cexH_nonneg (x : EuclideanSpace ℝ (Fin 2)) : 0 ≤ cexH x :=
  Set.indicator_nonneg (fun _ _ => by norm_num) x

/-- The whole mass of `cexH`, read against the uniform measure on `K`. -/
theorem lintegral_cexH :
    (∫⁻ x, ENNReal.ofReal (cexH x) ∂(uniformOn volume cexK))
      = ENNReal.ofReal 1000 * ENNReal.ofReal (2 / 3) := by
  have hfun : (fun x => ENNReal.ofReal (cexH x))
      = cexN.indicator fun _ => ENNReal.ofReal 1000 := by
    funext x
    by_cases hx : x ∈ cexN
    · rw [Set.indicator_of_mem hx, cexH, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, cexH, Set.indicator_of_notMem hx, ENNReal.ofReal_zero]
  rw [hfun, lintegral_indicator measurableSet_cexN, setLIntegral_const, uniformOn_cexN]

end Chord

/-! ### The refutation -/

section Refutation

theorem volume_cexK_ne_zero : volume cexK ≠ 0 := by
  rw [volume_cexK, Ne, ENNReal.ofReal_eq_zero]; norm_num

theorem volume_cexK_ne_top : volume cexK ≠ ⊤ := by
  rw [volume_cexK]; exact ENNReal.ofReal_ne_top

instance isProbabilityMeasure_uniformOn_cexK :
    IsProbabilityMeasure (uniformOn volume cexK) :=
  isProbabilityMeasure_uniformOn volume volume_cexK_ne_zero volume_cexK_ne_top

/-- `E(h)·min{π T₁, π T₂} = 125/12 > 1` for the counterexample data. -/
theorem one_lt_cex_lhs :
    (1 : ℝ≥0∞) < (∫⁻ x, ENNReal.ofReal (cexH x) ∂(uniformOn volume cexK)) *
      min (uniformOn volume cexK cexT₁) (uniformOn volume cexK cexT₂) := by
  rw [lintegral_cexH, uniformOn_cexT₁, uniformOn_cexT₂, min_self,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

/-- **The `hIso` binder of `Arlib.MarkovChains.conductance_hitAndRun_ge` is false.**

The statement below is that binder verbatim **as it stood before the repair of this date** —
i.e. without the clause `∀ x ∈ K, h x ≤ 1/3` that `conductance_hitAndRun_ge` now carries — at
`n = 2` and `K = cexK = [0,4]²`, a convex, compact, measurable body containing a unit ball, so
that every *other* hypothesis of `conductance_hitAndRun_ge` is simultaneously satisfiable
(`Arlib.cexK_hitAndRun_hypotheses`).

The witness is `h = 1000·1_N`, `T₁ = [0,1/2]²`, `T₂ = [7/2,4]×[0,1/2]`,
`N = [0,4]×[4/3,4]`.  Every hypothesis holds: `h ≥ 0` (`Arlib.cexH_nonneg`), the two sets are
measurable, contained in `K` and disjoint, and the chord bound holds because no chord through
`T₁` and `T₂` rises above height `7/6 < 4/3` (`Arlib.chord_le_of_cex`), so `h` vanishes on all
of them (`Arlib.cexH_chord`).  But the conclusion asks for `125/12 ≤ π(K ∖ T₁ ∖ T₂) ≤ 1`.

This is Lovász–Vempala's **Theorem 2.1** for the uniform density; the theorem is therefore
false as printed, and the repair — a global bound `h ≤ 1/3` on `K`, which the paper's own
application verifies — is `Arlib.needle_iso` and `Arlib.needle_iso_of_chord`. -/
theorem not_hIso_two :
    ¬ ∀ (h : EuclideanSpace ℝ (Fin 2) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin 2))), (∀ x, 0 ≤ h x) →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ cexK → T₂ ⊆ cexK → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ cexK,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin 2)) t) →
        h x ≤ min 1 (crossRatioDist cexK u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume cexK)) *
          min (uniformOn volume cexK T₁) (uniformOn volume cexK T₂)
        ≤ uniformOn volume cexK ((cexK \ T₁) \ T₂) := by
  intro hIso
  have key := hIso cexH cexT₁ cexT₂ cexH_nonneg measurableSet_cexT₁ measurableSet_cexT₂
    cexT₁_subset cexT₂_subset cexT₁_disjoint cexH_chord
  have hRHS : uniformOn volume cexK ((cexK \ cexT₁) \ cexT₂) ≤ 1 := prob_le_one
  exact absurd (one_lt_cex_lhs.trans_le (key.trans hRHS)) (lt_irrefl 1)

theorem measurable_cexH : Measurable cexH :=
  measurable_const.indicator measurableSet_cexN

/-- **Adding `Measurable h` to the binder does not repair it.**

The counterexample weight is an indicator of a box times a constant, hence measurable, so the
binder is false even when restricted to measurable `h`.  Measurability is therefore *not* part
of the repair — the global bound `h ≤ 1/3` is (`Arlib.cexH_not_le_third`) — and a measurability
hypothesis should be added only by whoever proves `hIso` and finds they need it. -/
theorem not_hIso_two_measurable :
    ¬ ∀ (h : EuclideanSpace ℝ (Fin 2) → ℝ)
        (T₁ T₂ : Set (EuclideanSpace ℝ (Fin 2))), (∀ x, 0 ≤ h x) → Measurable h →
      MeasurableSet T₁ → MeasurableSet T₂ → T₁ ⊆ cexK → T₂ ⊆ cexK → Disjoint T₁ T₂ →
      (∀ u ∈ T₁, ∀ v ∈ T₂, ∀ x ∈ cexK,
        (∃ t : ℝ, x = (AffineMap.lineMap u v : ℝ → EuclideanSpace ℝ (Fin 2)) t) →
        h x ≤ min 1 (crossRatioDist cexK u v) / 3) →
      (∫⁻ x, ENNReal.ofReal (h x) ∂(uniformOn volume cexK)) *
          min (uniformOn volume cexK T₁) (uniformOn volume cexK T₂)
        ≤ uniformOn volume cexK ((cexK \ T₁) \ T₂) := by
  intro hIso
  have key := hIso cexH cexT₁ cexT₂ cexH_nonneg measurable_cexH measurableSet_cexT₁
    measurableSet_cexT₂ cexT₁_subset cexT₂_subset cexT₁_disjoint cexH_chord
  have hRHS : uniformOn volume cexK ((cexK \ cexT₁) \ cexT₂) ≤ 1 := prob_le_one
  exact absurd (one_lt_cex_lhs.trans_le (key.trans hRHS)) (lt_irrefl 1)

/-- The centre `(2,2)` of `cexK`. -/
def cexZ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![2, 2]

theorem closedBall_cexZ_subset : Metric.closedBall cexZ 1 ⊆ cexK := by
  intro x hx
  rw [Metric.mem_closedBall] at hx
  have h0 : dist (x 0) (cexZ 0) ≤ 1 := le_trans (PiLp.dist_apply_le x cexZ 0) hx
  have h1 : dist (x 1) (cexZ 1) ≤ 1 := le_trans (PiLp.dist_apply_le x cexZ 1) hx
  have e0 : cexZ 0 = 2 := by simp [cexZ]
  have e1 : cexZ 1 = 2 := by simp [cexZ]
  rw [Real.dist_eq, e0, abs_le] at h0
  rw [Real.dist_eq, e1, abs_le] at h1
  exact ⟨⟨by linarith [h0.1], by linarith [h0.2]⟩, by linarith [h1.1], by linarith [h1.2]⟩

/-- **`cexK` satisfies every geometric hypothesis of
`Arlib.MarkovChains.conductance_hitAndRun_ge`** — it is a convex, closed, measurable, bounded
body containing a unit ball.  Together with `Arlib.not_hIso_two` this says that the theorem's
`hIso` binder is *not* satisfiable at an instance where everything else is: the guarantee is
empty there. -/
theorem cexK_hitAndRun_hypotheses :
    Convex ℝ cexK ∧ IsClosed cexK ∧ MeasurableSet cexK ∧ Bornology.IsBounded cexK ∧
      Metric.closedBall cexZ 1 ⊆ cexK :=
  ⟨convex_planeBox 0 4 0 4, isCompact_cexK.isClosed, measurableSet_cexK,
    isCompact_cexK.isBounded, closedBall_cexZ_subset⟩

/-- **The repaired binder is satisfiable at the same data**, so the repair is not a way of
making the hypothesis vacuous: `cexH` fails it — `cexH = 1000` somewhere on `K` — and that is
exactly the clause that blocks the counterexample.  The `1/3` bound is what the consumer of
`hIso` supplies (`h = s/(48·D·√n) ≤ 1/(24√n)`). -/
theorem cexH_not_le_third : ¬ ∀ x ∈ cexK, cexH x ≤ 1 / 3 := by
  intro hcon
  have hmem : WithLp.toLp 2 ![2, 2] ∈ cexN := by
    refine ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩
  have h := hcon _ (cexN_subset hmem)
  rw [cexH, Set.indicator_of_mem hmem] at h
  norm_num at h

end Refutation

end Arlib

/-! ### Axiom audit -/

section AxiomCheck

#print axioms Arlib.measurableSet_planeBox
#print axioms Arlib.isCompact_planeBox
#print axioms Arlib.convex_planeBox
#print axioms Arlib.volume_planeBox
#print axioms Arlib.volume_cexK
#print axioms Arlib.uniformOn_cexK_planeBox
#print axioms Arlib.uniformOn_cexT₁
#print axioms Arlib.uniformOn_cexT₂
#print axioms Arlib.uniformOn_cexN
#print axioms Arlib.chord_le_of_cex
#print axioms Arlib.cexH_eq_zero_of_chord
#print axioms Arlib.cexH_chord
#print axioms Arlib.lintegral_cexH
#print axioms Arlib.one_lt_cex_lhs
#print axioms Arlib.not_hIso_two
#print axioms Arlib.not_hIso_two_measurable
#print axioms Arlib.closedBall_cexZ_subset
#print axioms Arlib.cexK_hitAndRun_hypotheses
#print axioms Arlib.cexH_not_le_third

end AxiomCheck
