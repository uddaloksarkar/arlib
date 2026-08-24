/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Data.Set.Card

/-!
# The integer lattice, the refined lattice, and the dilation between them

Lattice-point counting arguments (Kannan–Vempala and friends) are stated for the
*integer* lattice `ℤⁿ ⊆ ℝⁿ`. An algorithm that counts to precision `10^(−ρ)`
instead counts points of the *refined* lattice

```
𝕃ⁿ = c⁻¹ · ℤⁿ,   c = 10^ρ.
```

This file supplies the transport between the two: the dilation `x ↦ c • x`
restricts, for every `c > 0` and every set `S`, to a bijection

```
S ∩ 𝕃ⁿ  ≃  (c • S) ∩ ℤⁿ
```

so that any statement about integer points of a dilate is a statement about
fine-lattice points of the original set, with the *same* count. This is the
"canonical isomorphism `φ`" of the lattice lemma.

## Main definitions

* `Arlib.Lattice.intLattice n` — the integer lattice `ℤⁿ` inside
  `EuclideanSpace ℝ (Fin n)`.
* `Arlib.Lattice.fineLattice n c` — the refined lattice `c⁻¹ · ℤⁿ`.
* `Arlib.Lattice.latticeScale ρ` — the dilation factor `10 ^ ρ`.

## Main results

* `Arlib.Lattice.smul_mem_intLattice_iff` — pointwise form of the transport:
  `c • x` is an integer point iff `x` is a fine-lattice point.
* `Arlib.Lattice.image_smul_inter_fineLattice` — the set form:
  `(c • ·) '' (S ∩ fineLattice n c) = (c • S) ∩ intLattice n`.
* `Arlib.Lattice.injOn_smul_inter_fineLattice` — the dilation is injective, so
  the previous item is a genuine bijection.
* `Arlib.Lattice.ncard_inter_fineLattice` — consequently the two counts agree.
  Since both sides of a lattice-count guarantee are normalised by the count, the
  transport changes neither side.

Nothing here needs `S` to be convex, measurable, or bounded: the transport is
purely set-theoretic.
-/

namespace Arlib.Lattice

open Set Pointwise

variable {n : ℕ}

/-! ## The two lattices -/

/-- The integer lattice `ℤⁿ` inside `ℝⁿ`: the points all of whose coordinates
are integers. -/
def intLattice (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) := {x | ∀ i, ∃ k : ℤ, x i = (k : ℝ)}

/-- The refined lattice `𝕃ⁿ = c⁻¹ · ℤⁿ`, of spacing `c⁻¹`. The intended value is
`c = 10 ^ ρ`, giving spacing `10 ^ (−ρ)`. -/
def fineLattice (n : ℕ) (c : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, ∃ k : ℤ, x i = c⁻¹ * (k : ℝ)}

/-- Membership in the integer lattice, unfolded. -/
@[simp]
theorem mem_intLattice {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ intLattice n ↔ ∀ i, ∃ k : ℤ, x i = (k : ℝ) := Iff.rfl

/-- Membership in the refined lattice, unfolded. -/
@[simp]
theorem mem_fineLattice {c : ℝ} {x : EuclideanSpace ℝ (Fin n)} :
    x ∈ fineLattice n c ↔ ∀ i, ∃ k : ℤ, x i = c⁻¹ * (k : ℝ) := Iff.rfl

/-- At spacing `1` the refined lattice *is* the integer lattice. -/
@[simp]
theorem fineLattice_one (n : ℕ) : fineLattice n 1 = intLattice n := by
  ext x
  simp

/-! ## The dilation transport

The four statements of this section are the isomorphism `φ`: pointwise, on
lattices, on intersections, and on counts.
-/

/-- **Pointwise transport.** For a positive dilation factor `c`, the dilate
`c • x` is an integer point exactly when `x` is a point of the refined lattice of
spacing `c⁻¹`. -/
theorem smul_mem_intLattice_iff {c : ℝ} (hc : 0 < c) {x : EuclideanSpace ℝ (Fin n)} :
    c • x ∈ intLattice n ↔ x ∈ fineLattice n c := by
  have hc' : c ≠ 0 := hc.ne'
  simp only [mem_intLattice, mem_fineLattice, PiLp.smul_apply, smul_eq_mul]
  constructor
  · intro h i
    obtain ⟨k, hk⟩ := h i
    exact ⟨k, by rw [← hk]; field_simp⟩
  · intro h i
    obtain ⟨k, hk⟩ := h i
    exact ⟨k, by rw [hk]; field_simp⟩

/-- **Transport of the lattices themselves.** Dilating by `c ≠ 0` carries the
refined lattice of spacing `c⁻¹` onto the integer lattice. -/
theorem smul_fineLattice {c : ℝ} (hc : c ≠ 0) : c • fineLattice n c = intLattice n := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    obtain ⟨k, hk⟩ := hy i
    exact ⟨k, by simp [hk, mul_inv_cancel_left₀ hc]⟩
  · intro hx
    refine ⟨c⁻¹ • x, fun i => ?_, ?_⟩
    · obtain ⟨k, hk⟩ := hx i
      exact ⟨k, by simp [hk]⟩
    · show c • c⁻¹ • x = x
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- Dilation commutes with cutting a set down to the respective lattice. -/
theorem smul_inter_fineLattice {c : ℝ} (hc : c ≠ 0) (S : Set (EuclideanSpace ℝ (Fin n))) :
    c • (S ∩ fineLattice n c) = (c • S) ∩ intLattice n := by
  rw [smul_set_inter₀ hc, smul_fineLattice hc]

/-- **The transport, as an image.** The dilation `x ↦ c • x` maps the
fine-lattice points of `S` exactly onto the integer points of the dilate
`c • S`. -/
theorem image_smul_inter_fineLattice {c : ℝ} (hc : 0 < c)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    (fun x => c • x) '' (S ∩ fineLattice n c) = (c • S) ∩ intLattice n := by
  rw [Set.image_smul, smul_inter_fineLattice hc.ne']

/-- The dilation is injective, hence injective on any set: the image of the
previous lemma is attained bijectively. -/
theorem injOn_smul_inter_fineLattice {c : ℝ} (hc : 0 < c)
    (S : Set (EuclideanSpace ℝ (Fin n))) :
    Set.InjOn (fun x => c • x) (S ∩ fineLattice n c) :=
  (smul_right_injective (EuclideanSpace ℝ (Fin n)) hc.ne').injOn

/-- **The counting form of the transport.** The number of fine-lattice points of
`S` equals the number of integer points of the dilate `c • S`.

Both sides of a lattice-count guarantee are normalised by this count, so
transporting along `φ` changes neither side. No finiteness hypothesis is needed:
the two `ncard`s are equal because the underlying sets are in bijection, and
`Set.ncard` of an infinite set is `0` on both sides. -/
theorem ncard_inter_fineLattice {c : ℝ} (hc : 0 < c) (S : Set (EuclideanSpace ℝ (Fin n))) :
    (S ∩ fineLattice n c).ncard = ((c • S) ∩ intLattice n).ncard := by
  rw [← image_smul_inter_fineLattice hc S]
  exact ((injOn_smul_inter_fineLattice hc S).ncard_image).symm

/-! ## The dilation factor `10 ^ ρ` -/

/-- The dilation `10 ^ ρ` carrying `𝕃ⁿ = 10^(−ρ)·ℤⁿ` onto `ℤⁿ`. -/
noncomputable def latticeScale (ρ : ℤ) : ℝ := (10 : ℝ) ^ ρ

/-- The dilation factor is positive. -/
theorem latticeScale_pos (ρ : ℤ) : 0 < latticeScale ρ := zpow_pos (by norm_num) ρ

/-- The dilation factor is nonzero — the hypothesis every cancellation below
needs, given Mathlib's `x / 0 = 0` convention. -/
theorem latticeScale_ne_zero (ρ : ℤ) : latticeScale ρ ≠ 0 := (latticeScale_pos ρ).ne'

/-! ## Structure of the lattices

Standard facts, needed as soon as one wants the lattice-point count of a bounded
region to be an honest finite number (`Set.ncard` is `0` on infinite sets, so
finiteness is what makes the count meaningful).
-/

/-- The integer lattice is the range of the coordinatewise cast `ℤⁿ → ℝⁿ`. -/
theorem intLattice_eq_range (n : ℕ) :
    intLattice n
      = Set.range (fun k : Fin n → ℤ =>
          (WithLp.toLp 2 (fun i => (k i : ℝ)) : EuclideanSpace ℝ (Fin n))) := by
  ext x
  constructor
  · intro hx
    choose k hk using hx
    exact ⟨k, by ext i; rw [PiLp.toLp_apply]; exact (hk i).symm⟩
  · rintro ⟨k, rfl⟩ i
    exact ⟨k i, rfl⟩

/-- The integer lattice is countable. -/
theorem countable_intLattice (n : ℕ) : (intLattice n).Countable := by
  rw [intLattice_eq_range]
  exact Set.countable_range _

/-- The refined lattice is countable: it is a dilate of the integer lattice. -/
theorem countable_fineLattice (n : ℕ) {c : ℝ} (hc : c ≠ 0) : (fineLattice n c).Countable := by
  have : fineLattice n c = c⁻¹ • intLattice n := by
    rw [← smul_fineLattice hc, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [this]
  exact (countable_intLattice n).image _

/-- The integer lattice is closed: each coordinate is constrained to the closed
set `ℤ ⊆ ℝ`. -/
theorem isClosed_intLattice (n : ℕ) : IsClosed (intLattice n) := by
  have hrw : intLattice n
      = ⋂ i : Fin n, (fun x : EuclideanSpace ℝ (Fin n) => x i) ⁻¹' Set.range ((↑) : ℤ → ℝ) := by
    ext x
    simp [intLattice, eq_comm]
  rw [hrw]
  exact isClosed_iInter fun i =>
    Real.isClosed_range_intCast.preimage (PiLp.continuous_apply _ _ i)

/-- The integer lattice has empty interior once there is at least one coordinate
to move in: perturbing a lattice point by less than one unit in coordinate `i`
leaves the lattice. (For `n = 0` the space is a single point and
`intLattice 0 = univ`, so the hypothesis `0 < n` is necessary.) -/
theorem interior_intLattice (n : ℕ) (hn : 0 < n) : interior (intLattice n) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  set i : Fin n := ⟨0, hn⟩ with hi
  set δ : ℝ := min (ε / 2) (1 / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set y : EuclideanSpace ℝ (Fin n) := x + δ • PiLp.single 2 i (1 : ℝ) with hy
  have hdist : dist y x < ε := by
    rw [dist_eq_norm]
    have : y - x = δ • PiLp.single 2 i (1 : ℝ) := by rw [hy]; abel
    rw [this, norm_smul, PiLp.norm_single]
    simpa [abs_of_pos hδ0] using hδε
  have hyL : y ∈ intLattice n := interior_subset (hball (Metric.mem_ball.2 hdist))
  obtain ⟨k, hk⟩ := (interior_subset hx : x ∈ intLattice n) i
  obtain ⟨m, hm⟩ := hyL i
  have hyi : y i = x i + δ := by simp [hy]
  have hmk : ((m - k : ℤ) : ℝ) = δ := by
    push_cast
    rw [← hm, ← hk, hyi]
    ring
  have h0 : (0 : ℤ) < m - k := by exact_mod_cast hmk ▸ hδ0
  have h1 : (m - k : ℤ) < 1 := by exact_mod_cast hmk ▸ hδ1
  omega

/-! ## Finiteness of the count on a bounded region -/

/-- Coordinatewise floor. On `intLattice n` it inverts the cast `ℤⁿ → ℝⁿ`, which
is what makes the integer points of a bounded region finite in number. -/
noncomputable def toIntTuple (x : EuclideanSpace ℝ (Fin n)) : Fin n → ℤ := fun i => ⌊x i⌋

/-- On the integer lattice, casting the coordinatewise floor back to `ℝ` recovers
the point. -/
theorem cast_toIntTuple {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ intLattice n) (i : Fin n) :
    ((toIntTuple x i : ℤ) : ℝ) = x i := by
  obtain ⟨k, hk⟩ := hx i
  simp [toIntTuple, hk]

/-- The coordinatewise floor is injective on the integer lattice. -/
theorem injOn_toIntTuple (n : ℕ) : Set.InjOn toIntTuple (intLattice n) := by
  intro x hx y hy h
  ext i
  rw [← cast_toIntTuple hx i, ← cast_toIntTuple hy i, h]

/-- A bounded region contains only finitely many integer points. -/
theorem finite_inter_intLattice {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : Bornology.IsBounded S) : (S ∩ intLattice n).Finite := by
  obtain ⟨R, hR⟩ := hS.subset_closedBall 0
  refine Set.Finite.of_finite_image ?_ ((injOn_toIntTuple n).mono Set.inter_subset_right)
  refine (Set.Finite.pi fun _ : Fin n => Set.finite_Icc (-⌈R⌉) ⌈R⌉).subset ?_
  rintro _ ⟨x, ⟨hxS, hxL⟩, rfl⟩
  intro i _
  have hxR : ‖x‖ ≤ R := by simpa using mem_closedBall_zero_iff.1 (hR hxS)
  have hi : |x i| ≤ R := le_trans (by simpa using PiLp.norm_apply_le x i) hxR
  have habs : |((toIntTuple x i : ℤ) : ℝ)| ≤ ((⌈R⌉ : ℤ) : ℝ) :=
    le_trans (by rw [cast_toIntTuple hxL i]; exact hi) (Int.le_ceil R)
  rw [← Int.cast_abs, Int.cast_le] at habs
  exact Set.mem_Icc.2 (abs_le.1 habs |>.imp id id)

/-- A bounded region contains only finitely many points of the refined lattice —
the transport of `Arlib.Lattice.finite_inter_intLattice` along the dilation. -/
theorem finite_inter_fineLattice {c : ℝ} (hc : 0 < c) {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS : Bornology.IsBounded S) : (S ∩ fineLattice n c).Finite := by
  have himg : ((fun x => c • x) '' (S ∩ fineLattice n c)).Finite := by
    rw [image_smul_inter_fineLattice hc S]
    exact finite_inter_intLattice (hS.smul₀ c)
  exact himg.of_finite_image (injOn_smul_inter_fineLattice hc S)

end Arlib.Lattice
