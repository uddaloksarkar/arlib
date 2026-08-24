/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.AdaptedProfileSelection
import Arlib.Convexity.LocalizationClosed
import Arlib.Convexity.LocalizationTransport

/-!
# A nested adapted-profile localization chain

The rational-flat localization chain can be run on the transverse base of a strictly positive
affine-profile body.  Its ordinary Euclidean half-space cuts pull back to the adapted base cuts
of `Arlib.AdaptedProfileSelection`; consequently every finite stage still has the same exact
affine profile.  The existing exhaustion theorem makes the limiting transverse base collinear,
equivalently its vector-span has dimension at most one.

This is the compact nested/dimension-collapse part of the affine-profile construction.  Notice
that it is a statement about the *transverse* dimension: adjoining the profile coordinate can
still produce a two-dimensional ambient limit.  The final BF extremality argument is what must
remove that last transverse direction.
-/

open Set MeasureTheory

namespace Arlib

variable {m : ℕ}

/-- Inclusion of bases induces inclusion of their profile bodies. -/
theorem profileBody_mono_base {A B : Set (Fin m → ℝ)} {g : ℝ → ℝ} (hAB : A ⊆ B) :
    profileBody A g ⊆ profileBody B g := by
  intro x hx
  exact ⟨hx.1, Set.smul_set_mono hAB hx.2⟩

/-- Preimages under `toLp` commute with the intersection of a sequence of transverse bases. -/
theorem iInter_preimage_toLp (D : ℕ → Set (EuclideanSpace ℝ (Fin m))) :
    (⋂ k, (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) ⁻¹' D k) =
      (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) ⁻¹' (⋂ k, D k) := by
  ext y
  simp

/-- **Nested adapted-profile chain with transverse dimension at most one.**

At every finite stage the two signed constraints survive on the compact convex Euclidean base,
and the associated profile body has the original affine needle weight on every slice.  The bases
are nested and their intersection, both before and after transport to ordinary coordinates, is
collinear. -/
theorem exists_affineProfile_chain_transverse_finrank_le_one (h2 : 2 ≤ m)
    {G H : EuclideanSpace ℝ (Fin m) → ℝ} (hG : Integrable G) (hH : Integrable H)
    {A : Set (EuclideanSpace ℝ (Fin m))} (hA : IsCompact A) (hAconv : Convex ℝ A)
    (hG0 : ∫ y in A, G y = 0) (hHpos : 0 < ∫ y in A, H y)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    ∃ D : ℕ → Set (EuclideanSpace ℝ (Fin m)),
      D 0 = A ∧
      (∀ k, D (k + 1) ⊆ D k) ∧
      (∀ k, IsCompact (D k) ∧ Convex ℝ (D k) ∧ D k ⊆ A ∧
        0 < volume (D k) ∧ (∫ y in D k, G y) = 0 ∧ 0 < ∫ y in D k, H y) ∧
      Collinear ℝ (⋂ k, D k) ∧
      Collinear ℝ
        (⋂ k, (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) ⁻¹' D k) ∧
      Module.finrank ℝ (vectorSpan ℝ
        (⋂ k, (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) ⁻¹' D k)) ≤ 1 ∧
      (∀ k,
        profileBody ((WithLp.toLp 2) ⁻¹' D (k + 1))
            (fun t => (1 - t) * p + t * q) ⊆
          profileBody ((WithLp.toLp 2) ⁻¹' D k)
            (fun t => (1 - t) * p + t * q)) ∧
      (∀ k t, t ∈ Icc (0 : ℝ) 1 →
        volume (slice
          (profileBody ((WithLp.toLp 2) ⁻¹' D k)
            (fun s => (1 - s) * p + s * q)) t) =
          ENNReal.ofReal (needleWeight p q m t) *
            volume ((WithLp.toLp 2) ⁻¹' D k)) := by
  obtain ⟨D, hD0, hDmono, hDinv, hDcol⟩ :=
    exists_flat_cut_chain_collinear_compact h2 hG hH hA hAconv hG0 hHpos
  have hprecol : Collinear ℝ
      (⋂ k, (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) ⁻¹' D k) := by
    rw [iInter_preimage_toLp]
    exact collinear_preimage_toLp_iff.mpr hDcol
  refine ⟨D, hD0, hDmono, hDinv, hDcol, hprecol, hprecol.finrank_le_one,
    fun k => profileBody_mono_base (preimage_mono (hDmono k)), ?_⟩
  intro k t ht
  simpa only [needleWeight_apply] using
    volume_slice_profileBody
      (A := (WithLp.toLp 2 : (Fin m → ℝ) → EuclideanSpace ℝ (Fin m)) ⁻¹' D k)
      ht (affine_interp_nonneg hp.le hq.le ht)

end Arlib

#print axioms Arlib.profileBody_mono_base
#print axioms Arlib.iInter_preimage_toLp
#print axioms Arlib.exists_affineProfile_chain_transverse_finrank_le_one
