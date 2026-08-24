/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.LocalizationLimit

/-!
# Transverse cuts which preserve an affine needle profile

The affine-power conclusion of the Kannan--Lovasz--Simonovits localization lemma cannot be
recovered merely from concavity of a limiting slice profile: a bipyramid gives a formal
counterexample in `Arlib.exists_convex_slice_profile_not_affine`.  This file records a genuinely
affine finite-step invariant instead.

If a generalized cone has slices `g(t) • A` and it is cut by a homogeneous half-space in the
transverse coordinates, then every slice becomes `g(t) • (A ∩ H)`.  Thus the *same* profile `g`
survives exactly.  In particular, when `g(t) = (1-t)p+tq`, its slice volumes retain the exact
needle weight `((1-t)p+tq)^m`.

The remaining constructive localization problem is now explicit: choose enough
constraint-preserving cuts from this profile-preserving class (and the corresponding oblique
classes) to make the transverse base degenerate.  The theorem below proves the shape invariant;
it does not posit that missing choice theorem.
-/

open Set MeasureTheory
open scoped Pointwise

namespace Arlib

variable {m : ℕ}

/-- The closed homogeneous half-space in the transverse `Fin m` coordinates. -/
def transverseHalfSpace (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) : Set (Fin (m + 1) → ℝ) :=
  {x | L (Fin.tail x) ≤ 0}

/-- The corresponding half-space in the base of a generalized cone. -/
def baseHalfSpace (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) : Set (Fin m → ℝ) :=
  {y | L y ≤ 0}

@[simp] theorem mem_transverseHalfSpace {L : (Fin m → ℝ) →ₗ[ℝ] ℝ}
    {x : Fin (m + 1) → ℝ} : x ∈ transverseHalfSpace L ↔ L (Fin.tail x) ≤ 0 := Iff.rfl

@[simp] theorem mem_baseHalfSpace {L : (Fin m → ℝ) →ₗ[ℝ] ℝ} {y : Fin m → ℝ} :
    y ∈ baseHalfSpace L ↔ L y ≤ 0 := Iff.rfl

/-- Scaling by a nonnegative number commutes with cutting a set containing zero by a
homogeneous half-space.  The `r = 0` case is why `0 ∈ A` is needed. -/
theorem smul_inter_baseHalfSpace {A : Set (Fin m → ℝ)} (hA0 : (0 : Fin m → ℝ) ∈ A)
    (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) {r : ℝ} (hr : 0 ≤ r) :
    r • (A ∩ baseHalfSpace L) = (r • A) ∩ baseHalfSpace L := by
  ext z
  constructor
  · rintro ⟨y, ⟨hyA, hyL⟩, rfl⟩
    refine ⟨⟨y, hyA, rfl⟩, ?_⟩
    simp only [mem_baseHalfSpace, map_smul]
    exact mul_nonpos_of_nonneg_of_nonpos hr hyL
  · rintro ⟨⟨y, hyA, hyz⟩, hzL⟩
    rcases hr.eq_or_lt with rfl | hrpos
    · refine ⟨0, ⟨hA0, ?_⟩, ?_⟩
      · simp [baseHalfSpace]
      · simpa using hyz
    · refine ⟨y, ⟨hyA, ?_⟩, hyz⟩
      simp only [mem_baseHalfSpace] at hzL ⊢
      rw [← hyz, map_smul] at hzL
      simp only [smul_eq_mul] at hzL
      nlinarith

/-- A homogeneous transverse cut of a generalized cone is exactly the generalized cone over
the cut base, with the original profile unchanged. -/
theorem profileBody_inter_transverseHalfSpace {A : Set (Fin m → ℝ)}
    (hA0 : (0 : Fin m → ℝ) ∈ A) {g : ℝ → ℝ}
    (hg0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ g t) (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) :
    profileBody A g ∩ transverseHalfSpace L = profileBody (A ∩ baseHalfSpace L) g := by
  ext x
  simp only [mem_inter_iff, mem_profileBody, mem_transverseHalfSpace]
  constructor
  · rintro ⟨⟨hxt, htail⟩, hL⟩
    refine ⟨hxt, ?_⟩
    rw [smul_inter_baseHalfSpace hA0 L (hg0 _ hxt)]
    exact ⟨htail, hL⟩
  · rintro ⟨hxt, htail⟩
    rw [smul_inter_baseHalfSpace hA0 L (hg0 _ hxt)] at htail
    exact ⟨⟨hxt, htail.1⟩, htail.2⟩

/-- The cut base remains convex and contains zero. -/
theorem convex_inter_baseHalfSpace {A : Set (Fin m → ℝ)} (hA : Convex ℝ A)
    (hA0 : (0 : Fin m → ℝ) ∈ A) (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) :
    Convex ℝ (A ∩ baseHalfSpace L) ∧ (0 : Fin m → ℝ) ∈ A ∩ baseHalfSpace L := by
  constructor
  · unfold baseHalfSpace
    exact hA.inter (convex_halfSpace_le (LinearMap.isLinear L) 0)
  · exact ⟨hA0, by simp [baseHalfSpace]⟩

/-- Consequently, a nonnegative concave-profile cone remains convex after a homogeneous
transverse cut, without weakening or changing its profile. -/
theorem convex_profileBody_inter_transverseHalfSpace {A : Set (Fin m → ℝ)}
    (hA : Convex ℝ A) (hA0 : (0 : Fin m → ℝ) ∈ A) {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ (Icc (0 : ℝ) 1) g) (hg0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ g t)
    (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) :
    Convex ℝ (profileBody A g ∩ transverseHalfSpace L) := by
  rw [profileBody_inter_transverseHalfSpace hA0 hg0 L]
  obtain ⟨hcut, hzero⟩ := convex_inter_baseHalfSpace hA hA0 L
  exact convex_profileBody hcut hzero hg hg0

/-- Slice volumes after a transverse cut retain the same power of the original profile; only
the base-volume factor changes. -/
theorem volume_slice_profileBody_inter_transverseHalfSpace {A : Set (Fin m → ℝ)}
    (hA0 : (0 : Fin m → ℝ) ∈ A) {g : ℝ → ℝ}
    (hg0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ g t) (L : (Fin m → ℝ) →ₗ[ℝ] ℝ)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    volume (slice (profileBody A g ∩ transverseHalfSpace L) t) =
      ENNReal.ofReal (g t ^ m) * volume (A ∩ baseHalfSpace L) := by
  rw [profileBody_inter_transverseHalfSpace hA0 hg0 L]
  exact volume_slice_profileBody ht (hg0 t ht)

/-- The affine special case: the exact KLS needle weight survives a homogeneous transverse
cut. -/
theorem volume_slice_affineProfile_inter_transverseHalfSpace {A : Set (Fin m → ℝ)}
    (hA0 : (0 : Fin m → ℝ) ∈ A) {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    volume (slice
        (profileBody A (fun s => (1 - s) * p + s * q) ∩ transverseHalfSpace L) t) =
      ENNReal.ofReal (needleWeight p q m t) * volume (A ∩ baseHalfSpace L) := by
  simpa only [needleWeight_apply] using
    volume_slice_profileBody_inter_transverseHalfSpace hA0
      (fun s hs => affine_interp_nonneg hp hq hs) L ht

/-! ## Oblique cuts adapted to an affine profile -/

/-- A base half-space with an arbitrary nonnegative level. -/
def baseHalfSpaceAt (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) : Set (Fin m → ℝ) :=
  {y | L y ≤ c}

/-- The corresponding cut in the full generalized cone.  When `g` is affine this is an
ordinary affine half-space in `Fin (m+1) → ℝ`. -/
def profileHalfSpace (g : ℝ → ℝ) (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) (c : ℝ) :
    Set (Fin (m + 1) → ℝ) :=
  {x | L (Fin.tail x) ≤ c * g (x 0)}

@[simp] theorem mem_baseHalfSpaceAt {L : (Fin m → ℝ) →ₗ[ℝ] ℝ} {c : ℝ}
    {y : Fin m → ℝ} : y ∈ baseHalfSpaceAt L c ↔ L y ≤ c := Iff.rfl

@[simp] theorem mem_profileHalfSpace {g : ℝ → ℝ} {L : (Fin m → ℝ) →ₗ[ℝ] ℝ} {c : ℝ}
    {x : Fin (m + 1) → ℝ} :
    x ∈ profileHalfSpace g L c ↔ L (Fin.tail x) ≤ c * g (x 0) := Iff.rfl

/-- For an affine profile, an adapted profile cut really is an ordinary affine half-space in
the ambient space. -/
theorem convex_profileHalfSpace_affine (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) (c p q : ℝ) :
    Convex ℝ (profileHalfSpace (fun t => (1 - t) * p + t * q) L c) := by
  let phi : (Fin (m + 1) → ℝ) → ℝ :=
    fun x => L (Fin.tail x) - c * (q - p) * x 0
  have hphi : IsLinearMap ℝ phi := by
    constructor
    · intro x y
      dsimp [phi]
      rw [show Fin.tail (x + y) = Fin.tail x + Fin.tail y by ext i; simp [Fin.tail], map_add]
      ring
    · intro r x
      dsimp [phi]
      rw [show Fin.tail (r • x) = r • Fin.tail x by ext i; simp [Fin.tail], map_smul]
      simp only [smul_eq_mul]
      ring
  have hconv := convex_halfSpace_le hphi (c * p)
  have heq : profileHalfSpace (fun t => (1 - t) * p + t * q) L c =
      {x | phi x ≤ c * p} := by
    ext x
    dsimp [phi, profileHalfSpace]
    constructor <;> intro h <;> nlinarith
  rw [heq]
  exact hconv

/-- Scaling commutes with a half-space when its level is scaled by the same nonnegative
factor. -/
theorem smul_inter_baseHalfSpaceAt {A : Set (Fin m → ℝ)} (hA0 : (0 : Fin m → ℝ) ∈ A)
    (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r) :
    r • (A ∩ baseHalfSpaceAt L c) =
      (r • A) ∩ {z : Fin m → ℝ | L z ≤ r * c} := by
  ext z
  constructor
  · rintro ⟨y, ⟨hyA, hyL⟩, rfl⟩
    refine ⟨⟨y, hyA, rfl⟩, ?_⟩
    change L (r • y) ≤ r * c
    rw [map_smul]
    simp only [smul_eq_mul]
    exact mul_le_mul_of_nonneg_left hyL hr
  · rintro ⟨⟨y, hyA, hyz⟩, hzL⟩
    rcases hr.eq_or_lt with rfl | hrpos
    · refine ⟨0, ⟨hA0, ?_⟩, ?_⟩
      · simp [baseHalfSpaceAt, hc]
      · simpa using hyz
    · refine ⟨y, ⟨hyA, ?_⟩, hyz⟩
      simp only [mem_baseHalfSpaceAt]
      change L z ≤ r * c at hzL
      rw [← hyz, map_smul] at hzL
      simp only [smul_eq_mul] at hzL
      nlinarith

/-- An adapted oblique cut preserves an arbitrary nonnegative profile exactly.  For an affine
profile the adapted cut itself is an ordinary affine half-space. -/
theorem profileBody_inter_profileHalfSpace {A : Set (Fin m → ℝ)}
    (hA0 : (0 : Fin m → ℝ) ∈ A) {g : ℝ → ℝ}
    (hg0 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ g t) (L : (Fin m → ℝ) →ₗ[ℝ] ℝ)
    {c : ℝ} (hc : 0 ≤ c) :
    profileBody A g ∩ profileHalfSpace g L c =
      profileBody (A ∩ baseHalfSpaceAt L c) g := by
  ext x
  simp only [mem_inter_iff, mem_profileBody, mem_profileHalfSpace]
  constructor
  · rintro ⟨⟨hxt, htail⟩, hcut⟩
    refine ⟨hxt, ?_⟩
    rw [smul_inter_baseHalfSpaceAt hA0 L hc (hg0 _ hxt)]
    simpa [mul_comm] using And.intro htail hcut
  · rintro ⟨hxt, htail⟩
    rw [smul_inter_baseHalfSpaceAt hA0 L hc (hg0 _ hxt)] at htail
    exact ⟨⟨hxt, htail.1⟩, by simpa [mul_comm] using htail.2⟩

/-- An adapted oblique cut is an honest convex-body cut when the base is convex and the profile
is affine and nonnegative. -/
theorem convex_affineProfile_inter_profileHalfSpace {A : Set (Fin m → ℝ)}
    (hA : Convex ℝ A) (hA0 : (0 : Fin m → ℝ) ∈ A) {p q c : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (_hc : 0 ≤ c)
    (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) :
    Convex ℝ
      (profileBody A (fun s => (1 - s) * p + s * q) ∩
        profileHalfSpace (fun s => (1 - s) * p + s * q) L c) :=
  (convex_profileBody hA hA0 (concaveOn_affine_interp p q)
    (fun _ hs => affine_interp_nonneg hp hq hs)).inter
      (convex_profileHalfSpace_affine L c p q)

/-- The exact affine needle-weight slice formula after an adapted oblique half-space cut. -/
theorem volume_slice_affineProfile_inter_profileHalfSpace {A : Set (Fin m → ℝ)}
    (hA0 : (0 : Fin m → ℝ) ∈ A) {p q c : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hc : 0 ≤ c) (L : (Fin m → ℝ) →ₗ[ℝ] ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    volume (slice
        (profileBody A (fun s => (1 - s) * p + s * q) ∩
          profileHalfSpace (fun s => (1 - s) * p + s * q) L c) t) =
      ENNReal.ofReal (needleWeight p q m t) * volume (A ∩ baseHalfSpaceAt L c) := by
  rw [profileBody_inter_profileHalfSpace hA0
    (fun s hs => affine_interp_nonneg hp hq hs) L hc]
  simpa only [needleWeight_apply] using
    volume_slice_profileBody (A := A ∩ baseHalfSpaceAt L c) ht
      (affine_interp_nonneg hp hq ht)

end Arlib

#print axioms Arlib.smul_inter_baseHalfSpace
#print axioms Arlib.profileBody_inter_transverseHalfSpace
#print axioms Arlib.convex_profileBody_inter_transverseHalfSpace
#print axioms Arlib.volume_slice_affineProfile_inter_transverseHalfSpace
#print axioms Arlib.smul_inter_baseHalfSpaceAt
#print axioms Arlib.convex_profileHalfSpace_affine
#print axioms Arlib.profileBody_inter_profileHalfSpace
#print axioms Arlib.convex_affineProfile_inter_profileHalfSpace
#print axioms Arlib.volume_slice_affineProfile_inter_profileHalfSpace
