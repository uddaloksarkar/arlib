/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
import Arlib.MarkovChains.Continuous.LambdaBoundSharp

/-!
# The ball smoothing `f̂`, and the pointwise binder of `lem:lambda-bound`

`Arlib.MarkovChains.Continuous.LambdaBoundSharp` proves `lem:sigma-roundness` outright but
leaves Cousins–Vempala's `lem:lambda-bound` (`1409.6011/vol3_journal.tex:853`) conditional on
**two** hypotheses about an entirely unconstrained function `fhat`:

1. `hpt : ∀ x, fhat x ≤ ell K δ x * f x` — the pointwise step at `:869`;
2. `hLov : ofReal c * ∫_K f ≤ ∫_K fhat` — **Lovász 2007, Lemma 6.3**.

This file **defines the smoothing `f̂` that Cousins–Vempala actually mean** and **proves a
pointwise step for it**, so that the surviving statements carry exactly one hypothesis, about
a concrete function, instead of two hypotheses about an arbitrary one.

## PROVED, unconditionally

**`exists_dual_le_on_of_notMem`** — separation of a point from a convex set in `ℝⁿ`, with no
openness, closedness or nonempty-interior assumption on the set (the empty-interior case goes
through the affine span, on which the separating functional is forced to be constant).

**`two_mul_volume_ball_inter_halfSpace`** — a closed half-space through the centre cuts `δBₙ`
into two pieces of exactly half the volume each.  Proof: `z ↦ -z` swaps them, and the
bounding hyperplane is a proper subspace, hence Lebesgue-null.

**`ballSmoothing`** (`def`) — the ball convolution
`f̂(x) = ⨅_D (∫_{x+D} f)/vol(D)` over convex measurable `D ⊆ δBₙ` with `2·vol(D) = vol(δBₙ)`.

**`exists_isHalfBall_lintegral_le`** — the geometric crux.  If the strict superlevel set
`{y : f(x) < f(y)}` is convex (implied by, and strictly weaker than, logconcavity of `f`),
there is a convex half `D` of `δBₙ` with `∫_{x+D} f ≤ vol((x+D) ∩ K)·f(x)`: take the half cut
off by a hyperplane through `x` separating `x` from that superlevel set.

**`ballSmoothing_le_self`** — `f̂(x) ≤ f(x)`.  Sharp; the `ℓ ≡ 1` case of the pointwise step.

**`ballSmoothing_le_two_mul_ell_mul`** — the pointwise step, `f̂(x) ≤ 2·ℓ(x)·f(x)`.
Cousins–Vempala assert this with constant `1`; see the paper-oracle note below.

**`lovasz_bound_indicator_ball`** — a genuine, proved instance of the *conclusion* of
Lovász 2007 Lemma 6.3: for the uniform density on the unit ball and `0 < δ < 1`,
`∫_K f̂ ≥ (1−δ)ⁿ ∫_K f`, because `f̂ = 1` on the concentric ball of radius `1−δ`.

## ASSUMED — exactly one binder, and it is the deep one

`avgLocalConductance_ge_half_of_lovasz` and `avgLocalConductance_ge_quarter_of_lovasz` carry
**one** unproved hypothesis, `hLov`, i.e. **Lovász 2007, Lemma 6.3**
(`∫_K f̂ ≥ 1 − 32·δ^{1/2}n^{1/4}/a^{1/2}` for an `a`-rounded logconcave `f`).  That lemma is
not proved here and its source is not in this repository — of the three PDFs at the
repository root, `vol5.pdf` is Kannan–Lovász–Simonovits, *Random walks and an O\*(n⁵) volume
algorithm* (whose §4.2 treats the average local conductance only for the **uniform** density,
by a surface-area argument, giving `λ ≥ 1 − δ√n/(2r)`); `BF02574061.pdf` is
Kannan–Lovász–Simonovits, *Isoperimetric problems for convex bodies and a localization
lemma*; `258533.258665.pdf` is Kannan–Vempala, *Sampling lattice points*.  None is
Lovász–Vempala 2007.  The statement of `hLov` here is transcribed from Cousins–Vempala's
citation of it and has **not** been checked against the source.

Because of the factor `2` in the pointwise step, the conclusions are
`λ(f) ≥ c/2` and — at the paper's step size `δ ≤ min{σ,1}/(4096√n)` — `λ(f) ≥ 1/4`,
where Cousins–Vempala claim `λ(f) ≥ c` and `λ(f) ≥ 1/2`.  A constant is a constant, and
`lem:speedy-to-ball` consumes only a constant, but this is **weaker than the paper's claim**
and is not presented as a proof of it.

Both hypothesis bundles come with a **non-vacuity witness whose `hLov` is proved, not
assumed** (`exists_lovasz_instance`, `exists_lovasz_quarter_instance`): the unit ball with
the uniform density, where `lovasz_bound_indicator_ball` supplies the Lovász inequality
outright.  In particular neither witness is the tautology `fhat = ℓ·f`.

## Paper-oracle note: where the factor `2` comes from, and why it is not removable here

The route is: pick the half `D₁` of `δBₙ` cut off by a hyperplane through `x` separating `x`
from the convex superlevel set `A = {y : f(y) > f(x)}`.  On `x+D₁` one has `f ≤ f(x)`, so

    `∫_{x+D₁} f ≤ f(x)·vol((x+D₁) ∩ K) ≤ f(x)·vol(B(x,δ) ∩ K) = f(x)·ℓ(x)·vol(δBₙ)`,

and dividing by `vol(D₁) = vol(δBₙ)/2` gives `2·ℓ(x)·f(x)`.  The sharp constant would need
`vol((x+D₁) ∩ K) ≤ vol(B(x,δ) ∩ K)/2`, i.e. the *forced* separating half to carry at most
half of `K`'s share of the ball.  **It need not.**  Concretely, in `ℝ²` with `δ = 1`, `x = 0`,

    `K = {y : |y₁| ≤ h, −1 ≤ y₂ ≤ b}`,   `f = e^{α y₂}·1_K`,

the superlevel set is `A = K ∩ {y₂ > 0}`, and as `h → 0` the only direction separating `0`
from `A` is `e₂`, forcing `D₁` to be the *lower* half-disc.  As `α → 0⁺` and `b → 0⁺`,

    `∫_{D₁} f / vol(D₁) → 2h/(π/2) = 4h/π`,  while  `ℓ(0)·f(0) → 2h/π`,

so this route loses exactly the factor `2`, and does so in the limit — it is not slack in the
estimates.  The sharp inequality nevertheless survives at that instance, via the *upper*
half-disc (`∫ → 2hb → 0`), which does **not** avoid `A`.  So a proof of the sharp constant
must use a `D` on which `f` exceeds `f(x)` somewhere, hence must use logconcavity
quantitatively (`f(x+z)f(x−z) ≤ f(x)²`) and not merely convexity of superlevel sets.  That
argument is not in Cousins–Vempala's three displayed lines and is not formalised here.

This is on top of the defect already recorded in `LambdaBoundSharp`: the printed chain at
`:869` does not compose as written (line 1's numerator is missing `∩ K`; line 2's denominator
must be `vol(δBₙ)`).

## Scope

The only `def` is `ballSmoothing` and the only `structure` is `IsHalfBall`; neither name
asserts an identity that is not either definitional or proved.  `ballSmoothing`'s index set
is the paper's, further restricted to **measurable** `D`; that restriction makes
`ballSmoothing ≥` the paper's `f̂`, so the upper bounds proved here hold a fortiori for the
paper's `f̂`, and a lower bound on `∫_K` of the paper's `f̂` is a fortiori one for
`∫_K ballSmoothing`.  Both directions therefore compose in the safe direction.

Nothing here is a conductance, mixing-time or polynomial-time statement.
-/

namespace Arlib.MarkovChains

open MeasureTheory Metric Set
open scoped ENNReal Pointwise

variable {n : ℕ}

/-! ## 1. Separating a point from a convex set -/

/-- **Separation of a point from a convex set in `ℝⁿ`.** -/
theorem exists_dual_le_on_of_notMem (hn : 1 ≤ n)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : Convex ℝ A)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ A) :
    ∃ φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ, φ ≠ 0 ∧ ∀ y ∈ A, φ x ≤ φ y := by
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  by_cases hint : (interior A).Nonempty
  · obtain ⟨φ, hφ0, hφ⟩ :=
      geometric_hahn_banach_of_nonempty_interior_point hA (fun h => hx (interior_subset h)) hint
    refine ⟨-φ, neg_ne_zero.2 hφ0, fun y hy => ?_⟩
    simpa using hφ y hy
  · rcases A.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · obtain ⟨v, hv⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
      obtain ⟨φ, hφ1, -⟩ := exists_dual_vector ℝ v (by simpa using hv)
      refine ⟨φ, ?_, by simp⟩
      intro h
      rw [h] at hφ1
      simp at hφ1
    · have hspan : affineSpan ℝ A ≠ ⊤ := fun h =>
        hint (hA.interior_nonempty_iff_affineSpan_eq_top.2 h)
      obtain ⟨p, hp⟩ : ∃ p, p ∉ (affineSpan ℝ A : Set (EuclideanSpace ℝ (Fin n))) := by
        by_contra h
        push Not at h
        exact hspan (SetLike.ext fun q => ⟨fun _ => AffineSubspace.mem_top ℝ _ q, fun _ => h q⟩)
      obtain ⟨φ, u, hlt, hu⟩ :=
        geometric_hahn_banach_closed_point (AffineSubspace.convex (affineSpan ℝ A))
          (AffineSubspace.closed_of_finiteDimensional _) hp
      have hsub : A ⊆ (affineSpan ℝ A : Set (EuclideanSpace ℝ (Fin n))) := subset_affineSpan ℝ A
      -- `φ` is constant on the affine span of `A`
      have hconst : ∀ b ∈ (affineSpan ℝ A : Set (EuclideanSpace ℝ (Fin n))), φ b = φ a := by
        intro b hb
        by_contra hne
        set d : ℝ := φ b - φ a with hd
        have hd0 : d ≠ 0 := sub_ne_zero.2 hne
        set t : ℝ := (u - φ a + 1) / d with ht
        have hmem : t • (b - a) + a ∈ (affineSpan ℝ A : Set (EuclideanSpace ℝ (Fin n))) := by
          simpa [vsub_eq_sub, vadd_eq_add] using
            (affineSpan ℝ A).smul_vsub_vadd_mem t hb (hsub ha) (hsub ha)
        have hval : φ (t • (b - a) + a) = φ a + (u - φ a + 1) := by
          rw [map_add, map_smul, map_sub, smul_eq_mul, ht, div_mul_cancel₀ _ hd0]
          ring
        have := hlt _ hmem
        rw [hval] at this
        linarith
      have hφ0 : φ ≠ 0 := by
        intro h
        have h1 := hlt a (hsub ha)
        rw [h] at h1 hu
        simp at h1 hu
        linarith
      rcases le_or_gt (φ x) (φ a) with hcase | hcase
      · exact ⟨φ, hφ0, fun y hy => by rw [hconst y (hsub hy)]; exact hcase⟩
      · refine ⟨-φ, neg_ne_zero.2 hφ0, fun y hy => ?_⟩
        have : φ y = φ a := hconst y (hsub hy)
        simp only [neg_apply, this]
        linarith

/-! ## 2. Convex half-volume subsets of the ball -/

/-- `IsHalfBall δ D` says `D` is a convex measurable subset of `δBₙ` of exactly half its
volume — the index set of Cousins–Vempala's minimum at `vol3_journal.tex:864`. -/
structure IsHalfBall (δ : ℝ) (D : Set (EuclideanSpace ℝ (Fin n))) : Prop where
  convex : Convex ℝ D
  measurableSet : MeasurableSet D
  subset_ball : D ⊆ ball 0 δ
  two_mul_volume : 2 * volume D = volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ)

/-- A closed half-space through the origin, cut down to `δBₙ`, has exactly half the volume of
the ball: the reflection `z ↦ -z` swaps the two halves, and the bounding hyperplane
`ker φ` is Lebesgue-null. -/
theorem two_mul_volume_ball_inter_halfSpace {δ : ℝ}
    {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0) :
    2 * volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ ∩ {z | φ z ≤ 0})
      = volume (ball (0 : EuclideanSpace ℝ (Fin n)) δ) := by
  set Hm : Set (EuclideanSpace ℝ (Fin n)) := ball 0 δ ∩ {z | φ z ≤ 0} with hHm
  set Hp : Set (EuclideanSpace ℝ (Fin n)) := ball 0 δ ∩ {z | 0 ≤ φ z} with hHp
  have hmHm : MeasurableSet Hm :=
    measurableSet_ball.inter (measurableSet_le φ.continuous.measurable measurable_const)
  have hmHp : MeasurableSet Hp :=
    measurableSet_ball.inter (measurableSet_le measurable_const φ.continuous.measurable)
  have hpre : Hp = (fun z : EuclideanSpace ℝ (Fin n) => -z) ⁻¹' Hm := by
    ext z
    simp [hHm, hHp, mem_ball, dist_zero_right]
  have hvol : volume Hp = volume Hm := by
    rw [hpre]
    exact (Measure.measurePreserving_neg (volume : Measure (EuclideanSpace ℝ (Fin n)))).measure_preimage
      hmHm.nullMeasurableSet
  have hunion : Hm ∪ Hp = ball (0 : EuclideanSpace ℝ (Fin n)) δ := by
    ext z
    simp only [hHm, hHp, mem_union, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases le_total (φ z) 0 with hc | hc
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr ⟨h, hc⟩
  have hlin : (φ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) ≠ 0 := fun h =>
    hφ (ContinuousLinearMap.coe_injective h)
  have hker : volume (Hm ∩ Hp) = 0 := by
    refine measure_mono_null (fun z hz => ?_)
      (Measure.addHaar_submodule (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (LinearMap.ker (φ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ))
        (by simpa [LinearMap.ker_eq_top] using hlin))
    have h1 : φ z ≤ 0 := hz.1.2
    have h2 : (0 : ℝ) ≤ φ z := hz.2.2
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    exact le_antisymm h1 h2
  have hadd := measure_union_add_inter (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) Hm hmHp
  rw [hunion, hker, add_zero, hvol] at hadd
  rw [two_mul]
  exact hadd.symm

/-- Every nonzero functional gives an inhabitant of `IsHalfBall`. -/
theorem isHalfBall_ball_inter_halfSpace {δ : ℝ}
    {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0) :
    IsHalfBall δ (ball (0 : EuclideanSpace ℝ (Fin n)) δ ∩ {z | φ z ≤ 0}) where
  convex := (convex_ball _ _).inter
    (convex_halfSpace_le (f := fun z => φ z) ⟨fun a b => φ.map_add a b, fun c a => φ.map_smul c a⟩ 0)
  measurableSet :=
    measurableSet_ball.inter (measurableSet_le φ.continuous.measurable measurable_const)
  subset_ball := inter_subset_left
  two_mul_volume := two_mul_volume_ball_inter_halfSpace hφ

/-! ## 3. The ball smoothing `f̂` -/

/-- **The ball smoothing of Cousins–Vempala** (`1409.6011/vol3_journal.tex:864`),

    `f̂(x) = min_D (∫_{y ∈ x+D} f(y) dy) / vol(D)`,

the minimum taken over convex subsets `D ⊆ δBₙ` of half the ball's volume.

Two deliberate deviations from the printed formula, both recorded here rather than hidden in
a name:

* the `min` is a `⨅` — the paper asserts the minimum is attained; nothing below needs that;
* the index set additionally requires `D` to be **measurable**, without which `∫_{x+D} f` and
  `vol(D)` are not the quantities the paper means.  This *shrinks* the index set, so
  `ballSmoothing f δ x ≥` the paper's `f̂(x)`.  Both consumers still compose: an upper bound
  proved here is a fortiori an upper bound for the paper's `f̂` (§4), and a lower bound on
  `∫_K f̂` (Lovász 2007 Lemma 6.3, assumed) is a fortiori a lower bound on `∫_K ballSmoothing`
  so both consumers compose in the safe direction: an upper bound proved here is a fortiori
  an upper bound for the paper's `f̂`, and a lower bound on `∫_K` of the paper's `f̂` is a
  fortiori a lower bound on `∫_K ballSmoothing`. -/
noncomputable def ballSmoothing (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (δ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨅ D ∈ {D : Set (EuclideanSpace ℝ (Fin n)) | IsHalfBall δ D}, (∫⁻ y in x +ᵥ D, f y) / volume D

/-- Any single admissible `D` bounds `ballSmoothing` from above. -/
theorem ballSmoothing_le {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {δ : ℝ}
    (x : EuclideanSpace ℝ (Fin n)) {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsHalfBall δ D) :
    ballSmoothing f δ x ≤ (∫⁻ y in x +ᵥ D, f y) / volume D :=
  iInf₂_le (f := fun D (_ : D ∈ {D : Set (EuclideanSpace ℝ (Fin n)) | IsHalfBall δ D}) =>
    (∫⁻ y in x +ᵥ D, f y) / volume D) D hD

/-- `ballSmoothing` is bounded below by `c` as soon as every admissible `D` is. -/
theorem le_ballSmoothing {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} {δ : ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {c : ℝ≥0∞}
    (h : ∀ D : Set (EuclideanSpace ℝ (Fin n)), IsHalfBall δ D →
      c ≤ (∫⁻ y in x +ᵥ D, f y) / volume D) :
    c ≤ ballSmoothing f δ x :=
  le_iInf₂ h

/-! ## 3b. Translation bookkeeping -/

/-- A translated set is a preimage under a translation. -/
theorem vadd_set_eq_preimage (x : EuclideanSpace ℝ (Fin n))
    (D : Set (EuclideanSpace ℝ (Fin n))) : x +ᵥ D = (fun y => -x + y) ⁻¹' D := by
  ext y
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simp

/-- Lebesgue measure is translation invariant, in `+ᵥ` form. -/
theorem volume_vadd_set (x : EuclideanSpace ℝ (Fin n)) (D : Set (EuclideanSpace ℝ (Fin n))) :
    volume (x +ᵥ D) = volume D := by
  rw [vadd_set_eq_preimage]
  exact measure_preimage_add volume (-x) D

/-- Translates of measurable sets are measurable. -/
theorem measurableSet_vadd_set {D : Set (EuclideanSpace ℝ (Fin n))} (hD : MeasurableSet D)
    (x : EuclideanSpace ℝ (Fin n)) : MeasurableSet (x +ᵥ D) := by
  rw [vadd_set_eq_preimage]
  exact hD.preimage (measurable_id.const_add (-x))

/-! ## 4. The pointwise step, with a factor `2` -/

/-- The translate of a half-ball by `x` is the corresponding half of `B(x,δ)`. -/
theorem vadd_ball_inter_halfSpace {δ : ℝ} {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ}
    (x : EuclideanSpace ℝ (Fin n)) :
    x +ᵥ (ball (0 : EuclideanSpace ℝ (Fin n)) δ ∩ {z | φ z ≤ 0})
      = ball x δ ∩ {y | φ y ≤ φ x} := by
  ext y
  have h1 : y ∈ x +ᵥ (ball (0 : EuclideanSpace ℝ (Fin n)) δ ∩ {z | φ z ≤ 0})
      ↔ (y - x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) δ ∧ φ (y - x) ≤ 0) := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [vadd_eq_add, neg_add_eq_sub, mem_inter_iff, mem_setOf_eq]
  rw [h1]
  simp only [mem_inter_iff, mem_ball, mem_setOf_eq, dist_eq_norm, map_sub, sub_zero]
  constructor <;> rintro ⟨a, b⟩ <;> exact ⟨a, by linarith⟩

/-- The hyperplane `{y : φ y = φ x}` is Lebesgue-null when `φ ≠ 0`. -/
theorem volume_setOf_eq_apply {φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} (hφ : φ ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) :
    volume {y : EuclideanSpace ℝ (Fin n) | φ y = φ x} = 0 := by
  have hlin : (φ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) ≠ 0 := fun h =>
    hφ (ContinuousLinearMap.coe_injective h)
  have hpre : (fun h : EuclideanSpace ℝ (Fin n) => x + h) ⁻¹'
      {y : EuclideanSpace ℝ (Fin n) | φ y = φ x}
      = (LinearMap.ker (φ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) : Set (EuclideanSpace ℝ (Fin n))) := by
    ext h
    simp only [mem_preimage, mem_setOf_eq, map_add, SetLike.mem_coe, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe]
    constructor <;> intro hh <;> linarith
  rw [← measure_preimage_add volume x _, hpre]
  exact Measure.addHaar_submodule _ _ (by simpa [LinearMap.ker_eq_top] using hlin)

/-- **The good half-ball.**  If the strict superlevel set `{y : f(x) < f(y)}` is convex —
which is implied by (and is all that is used of) logconcavity of `f` — then some convex
half `D` of `δBₙ` satisfies

    `∫_{x+D} f  ≤  vol((x+D) ∩ K) · f(x)`,

i.e. `f` is bounded by `f(x)` throughout `x+D`, up to the Lebesgue-null bounding hyperplane
and up to the set where `f` vanishes anyway.

`D` is the half of `δBₙ` cut off by a hyperplane through `x` separating `x` from the convex
superlevel set — the only geometric input, and the reason the sharp constant is out of reach
(see the module docstring). -/
theorem exists_isHalfBall_lintegral_le (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    (δ : ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hquasi : Convex ℝ {y : EuclideanSpace ℝ (Fin n) | f x < f y}) :
    ∃ D : Set (EuclideanSpace ℝ (Fin n)), IsHalfBall δ D ∧
      (∫⁻ y in x +ᵥ D, f y) ≤ volume ((x +ᵥ D) ∩ K) * f x := by
  obtain ⟨φ, hφ0, hφ⟩ := exists_dual_le_on_of_notMem hn hquasi (x := x) (by simp)
  refine ⟨ball 0 δ ∩ {z | φ z ≤ 0}, isHalfBall_ball_inter_halfSpace hφ0, ?_⟩
  set S : Set (EuclideanSpace ℝ (Fin n)) := ball x δ ∩ {y | φ y ≤ φ x} with hSdef
  set S' : Set (EuclideanSpace ℝ (Fin n)) := ball x δ ∩ {y | φ y < φ x} with hS'def
  have hSD : x +ᵥ (ball (0 : EuclideanSpace ℝ (Fin n)) δ ∩ {z | φ z ≤ 0}) = S :=
    vadd_ball_inter_halfSpace x
  have hmS : MeasurableSet S :=
    measurableSet_ball.inter (measurableSet_le φ.continuous.measurable measurable_const)
  have hmS' : MeasurableSet S' :=
    measurableSet_ball.inter (measurableSet_lt φ.continuous.measurable measurable_const)
  have hae : S =ᵐ[volume] S' := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null (fun y hy => ?_) (volume_setOf_eq_apply hφ0 x)
      have h1 : φ y ≤ φ x := hy.1.2
      have h2 : ¬ (y ∈ ball x δ ∧ φ y < φ x) := hy.2
      simp only [mem_setOf_eq]
      by_contra hne
      exact h2 ⟨hy.1.1, lt_of_le_of_ne h1 hne⟩
    · have hemp : S' \ S = ∅ := by
        rw [Set.sdiff_eq_empty]
        intro y hy
        refine ⟨hy.1, ?_⟩
        show φ y ≤ φ x
        exact le_of_lt hy.2
      rw [hemp]
      exact measure_empty
  have hmSK : MeasurableSet (S ∩ K) := hmS.inter hK
  rw [hSD, Measure.restrict_congr_set hae]
  calc ∫⁻ y in S', f y
      = ∫⁻ y, S'.indicator f y := (lintegral_indicator hmS' f).symm
    _ ≤ ∫⁻ y, (S ∩ K).indicator (fun _ => f x) y := by
        refine lintegral_mono fun y => ?_
        by_cases hy : y ∈ S'
        · rw [Set.indicator_of_mem hy]
          by_cases hyK : y ∈ K
          · have hyS : y ∈ S := ⟨hy.1, show φ y ≤ φ x from le_of_lt hy.2⟩
            rw [Set.indicator_of_mem (Set.mem_inter hyS hyK)]
            by_contra hcon
            push Not at hcon
            exact absurd (hφ y hcon) (not_le.2 hy.2)
          · rw [hfK y hyK]; simp
        · rw [Set.indicator_of_notMem hy]; simp
    _ = volume (S ∩ K) * f x := by
        rw [lintegral_indicator hmSK, setLIntegral_const, mul_comm]

/-- **`f̂ ≤ f` — the ball smoothing really smooths.**  This is sharp, and is the `ℓ ≡ 1`
(interior) case of the Cousins–Vempala pointwise step. -/
theorem ballSmoothing_le_self (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    (δ : ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hquasi : Convex ℝ {y : EuclideanSpace ℝ (Fin n) | f x < f y}) :
    ballSmoothing f δ x ≤ f x := by
  obtain ⟨D, hD, hle⟩ := exists_isHalfBall_lintegral_le hn hK hfK δ hquasi
  refine (ballSmoothing_le x hD).trans (ENNReal.div_le_of_le_mul ?_)
  calc (∫⁻ y in x +ᵥ D, f y) ≤ volume ((x +ᵥ D) ∩ K) * f x := hle
    _ ≤ volume (x +ᵥ D) * f x := mul_le_mul' (measure_mono inter_subset_left) le_rfl
    _ = f x * volume D := by rw [volume_vadd_set, mul_comm]

/-- **The pointwise step of `lem:lambda-bound`, with a factor `2`.**

For a function `f` vanishing off `K` whose strict superlevel set at `x` is convex — which is
implied by (and is all that is used of) logconcavity of `f` —

    `f̂(x) ≤ 2 · ℓ(x) · f(x)`.

Cousins–Vempala claim this without the factor `2` (`vol3_journal.tex:869`); see the module
docstring for why the factor `2` is exactly the price of the halfspace route, and why the
printed three-line proof does not establish the sharp form. -/
theorem ballSmoothing_le_two_mul_ell_mul (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    {δ : ℝ} (hδ : 0 < δ) {x : EuclideanSpace ℝ (Fin n)}
    (hquasi : Convex ℝ {y : EuclideanSpace ℝ (Fin n) | f x < f y}) :
    ballSmoothing f δ x ≤ 2 * ell K δ x * f x := by
  obtain ⟨D, hD, hle⟩ := exists_isHalfBall_lintegral_le hn hK hfK δ hquasi
  have hbt : volume (ball x δ) ≠ ⊤ := measure_ball_lt_top.ne
  have hb0 : volume (ball x δ) ≠ 0 := (Metric.measure_ball_pos volume x hδ).ne'
  have hsubball : (x +ᵥ D) ⊆ ball x δ := by
    intro y hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
    have h := hD.subset_ball hy
    simp only [vadd_eq_add, mem_ball, dist_zero_right] at h
    simp only [mem_ball, dist_eq_norm, ← neg_add_eq_sub]
    exact h
  have hdd : 2 * volume D = volume (ball x δ) := by
    rw [hD.two_mul_volume]
    exact (volume_ball_eq x δ).symm
  refine (ballSmoothing_le x hD).trans (ENNReal.div_le_of_le_mul ?_)
  calc (∫⁻ y in x +ᵥ D, f y) ≤ volume ((x +ᵥ D) ∩ K) * f x := hle
    _ ≤ volume (ball x δ ∩ K) * f x :=
        mul_le_mul' (measure_mono (Set.inter_subset_inter_left _ hsubball)) le_rfl
    _ = ell K δ x * volume (ball x δ) * f x := by
        rw [ell_apply, ENNReal.div_mul_cancel hb0 hbt]
    _ = 2 * ell K δ x * f x * volume D := by rw [← hdd]; ring

/-! ## 5. `lem:lambda-bound` with only the Lovász binder left -/

/-- **`lem:lambda-bound` (`vol3_journal.tex:853`) with the pointwise binder discharged, at the
cost of a factor `2`.**

The only remaining hypothesis is `hLov`, **Lovász 2007 Lemma 6.3**, stated about the concrete
`ballSmoothing` of §3 rather than about an arbitrary `fhat`.  Compare
`avgLocalConductance_ge_of_smoothing` in `LambdaBoundSharp`, which carries *two* hypotheses
about an unconstrained `fhat`.

`hLov` is **not** proved in this repository, and the source is not in it either. -/
theorem avgLocalConductance_ge_half_of_lovasz (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hquasi : ∀ x : EuclideanSpace ℝ (Fin n), Convex ℝ {y | f x < f y})
    {c : ℝ}
    (hLov : ENNReal.ofReal c * ∫⁻ x in K, f x ≤ ∫⁻ x in K, ballSmoothing f δ x)
    (h0 : (∫⁻ x in K, f x) ≠ 0) (htop : (∫⁻ x in K, f x) ≠ ⊤) :
    ENNReal.ofReal c / 2 ≤ (∫⁻ x in K, ell K δ x * f x) / (∫⁻ x in K, f x) := by
  have hmono : (∫⁻ x in K, ballSmoothing f δ x) ≤ 2 * ∫⁻ x in K, ell K δ x * f x := by
    calc (∫⁻ x in K, ballSmoothing f δ x)
        ≤ ∫⁻ x in K, 2 * (ell K δ x * f x) := by
          refine lintegral_mono fun x => ?_
          have h := ballSmoothing_le_two_mul_ell_mul hn hK hfK hδ (hquasi x)
          rwa [mul_assoc] at h
      _ = 2 * ∫⁻ x in K, ell K δ x * f x := lintegral_const_mul' 2 _ (by simp)
  have h2 : ENNReal.ofReal c * (∫⁻ x in K, f x) ≤ 2 * ∫⁻ x in K, ell K δ x * f x :=
    hLov.trans hmono
  rw [ENNReal.div_le_iff_le_mul (Or.inl two_ne_zero) (Or.inl (by simp)), mul_comm,
    ← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl htop)]
  exact h2

/-- **The `λ ≥ 1/2` corollary of `vol3_journal.tex:906`, obtained here as `λ ≥ 1/4`.**

At the paper's step size `δ ≤ min{σ,1}/(4096√n)` the Cousins–Vempala constant
`1 − 32δ^{1/2}n^{1/4}/a^{1/2}` is at least `1/2` (`cv_error_term_le_half`).  Feeding that
through §4's factor-`2` pointwise step gives `λ(f) ≥ 1/4` rather than the paper's `1/2`.

The one hypothesis carried unproved is `hLov` = Lovász 2007 Lemma 6.3. -/
theorem avgLocalConductance_ge_quarter_of_lovasz (hn : 1 ≤ n)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : MeasurableSet K)
    {f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hfK : ∀ y, y ∉ K → f y = 0)
    {δ σ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ)
    (hstep : δ ≤ min σ 1 / (4096 * Real.sqrt n))
    (hquasi : ∀ x : EuclideanSpace ℝ (Fin n), Convex ℝ {y | f x < f y})
    (hLov : ENNReal.ofReal
              (1 - 32 * Real.sqrt δ * Real.sqrt (Real.sqrt n) / Real.sqrt (min σ 1))
              * ∫⁻ x in K, f x ≤ ∫⁻ x in K, ballSmoothing f δ x)
    (h0 : (∫⁻ x in K, f x) ≠ 0) (htop : (∫⁻ x in K, f x) ≠ ⊤) :
    ENNReal.ofReal (1 / 4) ≤ (∫⁻ x in K, ell K δ x * f x) / (∫⁻ x in K, f x) := by
  have ha : (0 : ℝ) < min σ 1 := lt_min hσ one_pos
  have harith := cv_error_term_le_half (a := min σ 1) ha hn hstep
  refine le_trans ?_ (avgLocalConductance_ge_half_of_lovasz hn hK hfK hδ hquasi hLov h0 htop)
  rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl (by simp)),
    show ((2 : ℝ≥0∞)) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ## 6. Non-vacuity: a witness that is not `fhat = ℓ·f` -/

/-- A half-ball of `IsHalfBall` has strictly positive, finite volume. -/
theorem IsHalfBall.volume_ne_zero {δ : ℝ} (hδ : 0 < δ) {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsHalfBall δ D) : volume D ≠ 0 := by
  intro h
  have := hD.two_mul_volume
  rw [h, mul_zero] at this
  exact (Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin n)) hδ).ne' this.symm

theorem IsHalfBall.volume_ne_top {δ : ℝ} {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsHalfBall δ D) : volume D ≠ ⊤ :=
  ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono hD.subset_ball)

/-- **The uniform density on the unit ball, smoothed, is `1` well inside the ball.**  For
`‖x‖ < 1 − δ` every translate `x + D` of an admissible `D` stays inside `B(0,1)`, so every
term of the infimum is `vol(D)/vol(D) = 1`. -/
theorem one_le_ballSmoothing_indicator_ball {δ : ℝ} (hδ : 0 < δ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1 - δ) :
    1 ≤ ballSmoothing
      (Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞))) δ x := by
  refine le_ballSmoothing fun D hD => ?_
  have hsub : x +ᵥ D ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro y hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
    have h1 : ‖-x + y‖ < δ := by
      have := hD.subset_ball hy
      simpa [vadd_eq_add, mem_ball, dist_zero_right] using this
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

/-- The uniform density on the unit ball has convex strict superlevel sets. -/
theorem convex_setOf_lt_indicator_ball (x : EuclideanSpace ℝ (Fin n)) :
    Convex ℝ {y : EuclideanSpace ℝ (Fin n) |
      Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)) x
        < Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)) y} := by
  by_cases hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1
  · have : {y : EuclideanSpace ℝ (Fin n) |
        Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)) x
          < Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)) y}
        = ∅ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt,
        Set.indicator_of_mem hx]
      by_cases hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 <;>
        simp [hy]
    rw [this]
    exact convex_empty
  · have : {y : EuclideanSpace ℝ (Fin n) |
        Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)) x
          < Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)) y}
        = ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      ext y
      simp only [Set.mem_setOf_eq, Set.indicator_of_notMem hx]
      by_cases hy : y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 <;>
        simp [hy]
    rw [this]
    exact convex_ball _ _

/-- The mass of the uniform density on the unit ball is the volume of the ball. -/
theorem lintegral_indicator_ball_self :
    (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
        Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)) x)
      = volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [setLIntegral_congr_fun measurableSet_ball (fun y hy => Set.indicator_of_mem hy _),
    setLIntegral_one]

/-- **The Lovász binder is genuinely satisfiable for the concrete `ballSmoothing`.**  For the
unit ball with the *uniform* density and any `0 < δ < 1`,

    `∫_K f̂ ≥ (1−δ)ⁿ · ∫_K f`,

because `f̂ = 1` on the concentric ball of radius `1−δ`.  This is a real instance of
Lovász 2007 Lemma 6.3's conclusion, proved outright — not the tautology `fhat = ℓ·f`. -/
theorem lovasz_bound_indicator_ball (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal ((1 - δ) ^ n)
        * (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
            Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞)) x)
      ≤ ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          ballSmoothing
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
          ballSmoothing
            (Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞))) δ x := by
        refine setLIntegral_mono' measurableSet_ball fun y hy => ?_
        refine one_le_ballSmoothing_indicator_ball hδ ?_
        simpa [mem_ball, dist_zero_right] using hy
    _ ≤ ∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          ballSmoothing
            (Set.indicator (ball (0 : EuclideanSpace ℝ (Fin n)) 1) (fun _ => (1 : ℝ≥0∞))) δ x :=
        lintegral_mono' (Measure.restrict_mono (Metric.ball_subset_ball (by linarith)) le_rfl) le_rfl

/-- **Non-vacuity witness for `avgLocalConductance_ge_half_of_lovasz`.**  Unit ball, uniform
density, `δ = 1/2`, `c = (1/2)ⁿ > 0`; the Lovász hypothesis is *proved* for this instance by
`lovasz_bound_indicator_ball`, so no binder is discharged by fiat. -/
theorem exists_lovasz_instance (hn : 1 ≤ n) :
    ∃ (K : Set (EuclideanSpace ℝ (Fin n))) (δ : ℝ)
      (f : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (c : ℝ),
      0 < c ∧ 0 < δ ∧ MeasurableSet K ∧ (∀ y, y ∉ K → f y = 0) ∧
      (∀ x, Convex ℝ {y | f x < f y}) ∧
      (ENNReal.ofReal c * ∫⁻ x in K, f x ≤ ∫⁻ x in K, ballSmoothing f δ x) ∧
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
    lovasz_bound_indicator_ball hn (by norm_num) (by norm_num), h0, htop, ?_⟩
  exact avgLocalConductance_ge_half_of_lovasz hn measurableSet_ball
    (fun y hy => Set.indicator_of_notMem hy _) (by norm_num) convex_setOf_lt_indicator_ball
    (lovasz_bound_indicator_ball hn (by norm_num) (by norm_num)) h0 htop

/-- **Non-vacuity witness for `avgLocalConductance_ge_quarter_of_lovasz`** — the bundle whose
Lovász constant is forced to be at least `1/2`, so that a degenerate `c ≤ 0` cannot satisfy it.

Dimension `n = 2`, the unit disc, the uniform density, `σ = 1` and `δ = 1/(4096√2)`, which
makes `hstep` an *equality*.  There the Cousins–Vempala constant is exactly `1/2`, and the
Lovász hypothesis is discharged by the proved `lovasz_bound_indicator_ball` via
`(1−δ)² ≥ 1/2`. -/
theorem exists_lovasz_quarter_instance :
    ∃ (K : Set (EuclideanSpace ℝ (Fin 2))) (δ σ : ℝ) (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞),
      0 < σ ∧ 0 < δ ∧ MeasurableSet K ∧ (∀ y, y ∉ K → f y = 0) ∧
      δ ≤ min σ 1 / (4096 * Real.sqrt ((2 : ℕ) : ℝ)) ∧
      (∀ x, Convex ℝ {y | f x < f y}) ∧
      (ENNReal.ofReal
          (1 - 32 * Real.sqrt δ * Real.sqrt (Real.sqrt ((2 : ℕ) : ℝ))
            / Real.sqrt (min σ 1)) * ∫⁻ x in K, f x ≤ ∫⁻ x in K, ballSmoothing f δ x) ∧
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
      (lovasz_bound_indicator_ball (by norm_num) hδ0 hδ1)
    show (1 : ℝ) / 2 ≤ (1 - δ) ^ 2
    nlinarith [hδ0, hδsmall]

end Arlib.MarkovChains

/-! ### Axiom audit -/

#print axioms Arlib.MarkovChains.exists_dual_le_on_of_notMem
#print axioms Arlib.MarkovChains.two_mul_volume_ball_inter_halfSpace
#print axioms Arlib.MarkovChains.isHalfBall_ball_inter_halfSpace
#print axioms Arlib.MarkovChains.ballSmoothing_le
#print axioms Arlib.MarkovChains.le_ballSmoothing
#print axioms Arlib.MarkovChains.vadd_set_eq_preimage
#print axioms Arlib.MarkovChains.volume_vadd_set
#print axioms Arlib.MarkovChains.measurableSet_vadd_set
#print axioms Arlib.MarkovChains.vadd_ball_inter_halfSpace
#print axioms Arlib.MarkovChains.volume_setOf_eq_apply
#print axioms Arlib.MarkovChains.exists_isHalfBall_lintegral_le
#print axioms Arlib.MarkovChains.ballSmoothing_le_self
#print axioms Arlib.MarkovChains.ballSmoothing_le_two_mul_ell_mul
#print axioms Arlib.MarkovChains.avgLocalConductance_ge_half_of_lovasz
#print axioms Arlib.MarkovChains.avgLocalConductance_ge_quarter_of_lovasz
#print axioms Arlib.MarkovChains.IsHalfBall.volume_ne_zero
#print axioms Arlib.MarkovChains.IsHalfBall.volume_ne_top
#print axioms Arlib.MarkovChains.one_le_ballSmoothing_indicator_ball
#print axioms Arlib.MarkovChains.convex_setOf_lt_indicator_ball
#print axioms Arlib.MarkovChains.lintegral_indicator_ball_self
#print axioms Arlib.MarkovChains.lovasz_bound_indicator_ball
#print axioms Arlib.MarkovChains.exists_lovasz_instance
#print axioms Arlib.MarkovChains.exists_lovasz_quarter_instance
