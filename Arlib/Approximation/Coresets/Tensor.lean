/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Tensor products of weighted point sets, and the composition of reductions

The engine of every bottom-up domain reduction.  Two weighted point sets over
disjoint sets of variables are combined by taking the Cartesian product of their
index sets, multiplying the weights, and computing the combined feature vector
**bilinearly** from the children's:

`Φ(u, v) a = ∑_{p,q} M a p q · Φ₁(u) p · Φ₂(v) q`.

That bilinearity is the mathematical content of decomposability: a gate whose
scope splits as a disjoint union computes the *product* of its children, and a
layer of sum gates above it takes linear combinations — jointly, a bilinear
form.  The Hadamard (coordinatewise) product, which is what a mixture of product
distributions needs, is the special case where `M` is the diagonal tensor.

## Main results

* `WPS.tensor M A B` — the Cartesian-product weighted point set.
* `WPS.E_tensor_right` / `E_tensor_left` — the two **Fubini identities**: the
  functional of a tensor product is a weighted sum, over the assignments of
  *one* factor, of the functional of the *other* factor at a query which depends
  on the first factor's feature vector.  A linear test on the product is, for
  each fixed assignment of one side, a linear test on the other.
* `Embeds.tensor` — **the composition theorem**.  Reducing each factor reduces
  the product, the windows multiplying.  Proved by replacing one factor at a
  time, each replacement licensed by one of the two Fubini identities.
* `WPS.hadamard` and `hadamard_feat` — the coordinatewise special case.

Note that `Embeds.tensor` is *not* about sparsifying the product: it says the
product of the reduced factors already approximates the product of the exact
factors.  Sparsifying the (still quadratically large) product is a further,
separate application of `Embeds.trans`.

No `sorry`.
-/
import Arlib.Approximation.Coresets.Embedding
import Mathlib.Data.Fintype.Prod

namespace Arlib.Approximation

open scoped BigOperators
open Finset

variable {ι₁ ι₂ d d₁ d₂ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype d] [Fintype d₁] [Fintype d₂]

/-! ## The bilinear combination of feature vectors -/

/-- The feature vector obtained from two children's feature vectors by the
bilinear structure tensor `M`: coordinate `a` of the result is
`∑_{p,q} M a p q · v₁ p · v₂ q`. -/
def tensorFeat (M : d → d₁ → d₂ → ℝ) (v₁ : d₁ → ℝ) (v₂ : d₂ → ℝ) : d → ℝ :=
  fun a => ∑ p, ∑ q, M a p q * v₁ p * v₂ q

/-- The query induced on the **right** factor by a query `y` on the product and
a fixed left feature vector `v₁`. -/
def rightQuery (M : d → d₁ → d₂ → ℝ) (y : d → ℝ) (v₁ : d₁ → ℝ) : d₂ → ℝ :=
  fun q => ∑ p, (∑ a, y a * M a p q) * v₁ p

/-- The query induced on the **left** factor by a query `y` on the product and a
fixed right feature vector `v₂`. -/
def leftQuery (M : d → d₁ → d₂ → ℝ) (y : d → ℝ) (v₂ : d₂ → ℝ) : d₁ → ℝ :=
  fun p => ∑ q, (∑ a, y a * M a p q) * v₂ q

/-- Rotating a triple sum: `∑ₐ∑_b∑_c = ∑_b∑_c∑ₐ`. -/
private theorem sum3_rot {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (F : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ b, ∑ c, ∑ a, F a b c := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- Reversing a triple sum: `∑ₐ∑_b∑_c = ∑_c∑_b∑ₐ`. -/
private theorem sum3_rev {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (F : α → β → γ → ℝ) :
    (∑ a, ∑ b, ∑ c, F a b c) = ∑ c, ∑ b, ∑ a, F a b c := by
  rw [sum3_rot]; exact Finset.sum_comm

/-- The linear test on a tensor-combined feature vector, written out as a triple
sum. -/
private theorem dot_tensorFeat_expand (M : d → d₁ → d₂ → ℝ) (y : d → ℝ)
    (v₁ : d₁ → ℝ) (v₂ : d₂ → ℝ) :
    dot y (tensorFeat M v₁ v₂) = ∑ a, ∑ p, ∑ q, y a * M a p q * v₁ p * v₂ q := by
  simp only [dot, tensorFeat, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/-- The linear test against a `rightQuery`, as the same triple sum. -/
private theorem dot_rightQuery_expand (M : d → d₁ → d₂ → ℝ) (y : d → ℝ)
    (v₁ : d₁ → ℝ) (v₂ : d₂ → ℝ) :
    dot (rightQuery M y v₁) v₂ = ∑ q, ∑ p, ∑ a, y a * M a p q * v₁ p * v₂ q := by
  simp only [dot, rightQuery]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]

/-- The linear test against a `leftQuery`, as the same triple sum. -/
private theorem dot_leftQuery_expand (M : d → d₁ → d₂ → ℝ) (y : d → ℝ)
    (v₁ : d₁ → ℝ) (v₂ : d₂ → ℝ) :
    dot (leftQuery M y v₂) v₁ = ∑ p, ∑ q, ∑ a, y a * M a p q * v₁ p * v₂ q := by
  simp only [dot, leftQuery]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **A linear test on the product is a linear test on the right factor.** -/
theorem dot_tensorFeat_right (M : d → d₁ → d₂ → ℝ) (y : d → ℝ)
    (v₁ : d₁ → ℝ) (v₂ : d₂ → ℝ) :
    dot y (tensorFeat M v₁ v₂) = dot (rightQuery M y v₁) v₂ := by
  rw [dot_tensorFeat_expand, dot_rightQuery_expand]
  exact sum3_rev _

/-- **A linear test on the product is a linear test on the left factor.** -/
theorem dot_tensorFeat_left (M : d → d₁ → d₂ → ℝ) (y : d → ℝ)
    (v₁ : d₁ → ℝ) (v₂ : d₂ → ℝ) :
    dot y (tensorFeat M v₁ v₂) = dot (leftQuery M y v₂) v₁ := by
  rw [dot_tensorFeat_expand, dot_leftQuery_expand]
  exact sum3_rot _

/-! ## The tensor product of weighted point sets -/

namespace WPS

/-- The **tensor (Cartesian) product** of two weighted point sets: indices pair
up, weights multiply, features combine through the structure tensor `M`. -/
def tensor (M : d → d₁ → d₂ → ℝ) (A : WPS ι₁ d₁) (B : WPS ι₂ d₂) : WPS (ι₁ × ι₂) d where
  wt := fun ij => A.wt ij.1 * B.wt ij.2
  wt_nonneg := fun ij => mul_nonneg (A.wt_nonneg ij.1) (B.wt_nonneg ij.2)
  feat := fun ij => tensorFeat M (A.feat ij.1) (B.feat ij.2)

omit [Fintype ι₁] [Fintype ι₂] [Fintype d] in
@[simp] theorem tensor_wt (M : d → d₁ → d₂ → ℝ) (A : WPS ι₁ d₁) (B : WPS ι₂ d₂)
    (ij : ι₁ × ι₂) : (tensor M A B).wt ij = A.wt ij.1 * B.wt ij.2 := rfl

omit [Fintype ι₁] [Fintype ι₂] [Fintype d] in
@[simp] theorem tensor_feat (M : d → d₁ → d₂ → ℝ) (A : WPS ι₁ d₁) (B : WPS ι₂ d₂)
    (ij : ι₁ × ι₂) :
    (tensor M A B).feat ij = tensorFeat M (A.feat ij.1) (B.feat ij.2) := rfl

/-- **Fubini, right factor inside.**  The functional of a tensor product is the
`A`-weighted sum of `B`'s functional at the induced right queries. -/
theorem E_tensor_right (M : d → d₁ → d₂ → ℝ) (A : WPS ι₁ d₁) (B : WPS ι₂ d₂)
    (y : d → ℝ) :
    (tensor M A B).E y = ∑ i, A.wt i * B.E (rightQuery M y (A.feat i)) := by
  rw [E_apply, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [E_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tensor_wt, tensor_feat, dot_tensorFeat_right]
  ring

/-- **Fubini, left factor inside.**  The mirror image of `E_tensor_right`. -/
theorem E_tensor_left (M : d → d₁ → d₂ → ℝ) (A : WPS ι₁ d₁) (B : WPS ι₂ d₂)
    (y : d → ℝ) :
    (tensor M A B).E y = ∑ j, B.wt j * A.E (leftQuery M y (B.feat j)) := by
  rw [E_apply, ← Finset.univ_product_univ, Finset.sum_product_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [E_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tensor_wt, tensor_feat, dot_tensorFeat_left]
  ring

end WPS

/-! ## The composition theorem -/

/-- **Reducing each factor reduces the product.**

The proof replaces one factor at a time.  Replacing `B` by `B'` is licensed by
`E_tensor_right`, which exhibits both sides as an `A`-weighted sum of `B`'s
(resp. `B'`'s) functional at the *same* family of queries; replacing `A` by `A'`
is licensed by `E_tensor_left` in the same way, now against the already-reduced
`B'`.  Nonnegativity of the left window is what lets the two windows chain. -/
theorem Embeds.tensor {lo₁ hi₁ lo₂ hi₂ : ℝ} (M : d → d₁ → d₂ → ℝ)
    (hlo₁ : 0 ≤ lo₁) (hhi₁ : 0 ≤ hi₁)
    {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    {A : WPS κ₁ d₁} {A' : WPS ι₁ d₁} {B : WPS κ₂ d₂} {B' : WPS ι₂ d₂}
    (hA : Embeds lo₁ hi₁ A A') (hB : Embeds lo₂ hi₂ B B') :
    Embeds (lo₁ * lo₂) (hi₁ * hi₂) (WPS.tensor M A B) (WPS.tensor M A' B') := by
  intro y
  -- Step 1: replace the right factor.
  have step1 : Between lo₂ hi₂ ((WPS.tensor M A B').E y) ((WPS.tensor M A B).E y) := by
    rw [WPS.E_tensor_right, WPS.E_tensor_right]
    exact hB.sum_queries Finset.univ _ _ A.wt_nonneg
  -- Step 2: replace the left factor, against the already-reduced right factor.
  have step2 : Between lo₁ hi₁ ((WPS.tensor M A' B').E y) ((WPS.tensor M A B').E y) := by
    rw [WPS.E_tensor_left, WPS.E_tensor_left]
    exact hA.sum_queries Finset.univ _ _ B'.wt_nonneg
  exact Between.trans hlo₁ hhi₁ step2 step1

/-! ## The Hadamard (coordinatewise) special case -/

/-- The diagonal structure tensor: it makes `tensorFeat` the coordinatewise
product of the two feature vectors. -/
def diagTensor (d : Type*) [DecidableEq d] : d → d → d → ℝ :=
  fun a p q => if p = a ∧ q = a then 1 else 0

/-- The **Hadamard product** of two weighted point sets over the same feature
index: indices pair up, weights multiply, features multiply coordinatewise.

This is the extension step of a dynamic program over coordinates: a surviving
prefix with accumulated feature `v` is extended by a domain element with local
feature `r`, and the extended feature is `v ⊙ r`. -/
def WPS.hadamard [DecidableEq d] (A : WPS ι₁ d) (B : WPS ι₂ d) : WPS (ι₁ × ι₂) d :=
  WPS.tensor (diagTensor d) A B

@[simp] theorem tensorFeat_diag [DecidableEq d] (v₁ v₂ : d → ℝ) :
    tensorFeat (diagTensor d) v₁ v₂ = fun a => v₁ a * v₂ a := by
  funext a
  simp only [tensorFeat, diagTensor]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single a]
    · simp
    · intro q _ hq; simp [hq]
    · intro h; exact absurd (Finset.mem_univ a) h
  · intro p _ hp
    refine Finset.sum_eq_zero fun q _ => ?_
    simp [hp]
  · intro h; exact absurd (Finset.mem_univ a) h

omit [Fintype ι₁] [Fintype ι₂] in
@[simp] theorem WPS.hadamard_feat [DecidableEq d] (A : WPS ι₁ d) (B : WPS ι₂ d)
    (ij : ι₁ × ι₂) (a : d) :
    (WPS.hadamard A B).feat ij a = A.feat ij.1 a * B.feat ij.2 a := by
  simp [WPS.hadamard]

omit [Fintype ι₁] [Fintype ι₂] in
@[simp] theorem WPS.hadamard_wt [DecidableEq d] (A : WPS ι₁ d) (B : WPS ι₂ d) (ij : ι₁ × ι₂) :
    (WPS.hadamard A B).wt ij = A.wt ij.1 * B.wt ij.2 := rfl

/-- The composition theorem, Hadamard case. -/
theorem Embeds.hadamard [DecidableEq d] {lo₁ hi₁ lo₂ hi₂ : ℝ}
    (hlo₁ : 0 ≤ lo₁) (hhi₁ : 0 ≤ hi₁)
    {κ₁ κ₂ : Type*} [Fintype κ₁] [Fintype κ₂]
    {A : WPS κ₁ d} {A' : WPS ι₁ d} {B : WPS κ₂ d} {B' : WPS ι₂ d}
    (hA : Embeds lo₁ hi₁ A A') (hB : Embeds lo₂ hi₂ B B') :
    Embeds (lo₁ * lo₂) (hi₁ * hi₂) (WPS.hadamard A B) (WPS.hadamard A' B') :=
  Embeds.tensor _ hlo₁ hhi₁ hA hB

end Arlib.Approximation
