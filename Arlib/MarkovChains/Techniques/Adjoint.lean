/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Mutually adjoint kernels

Reversibility says a chain is self-adjoint in `L²(μ)`.  The local-to-global
machinery needs the same statement for a *pair* of kernels moving between two
different spaces: the up operator `U_k : 𝒫_k → 𝒫_{k+1}` and the down operator
`D_k : 𝒫_{k+1} → 𝒫_k` of the up/down walks satisfy

  `π_k(τ) · U_k(τ, η) = π_{k+1}(η) · D_k(η, τ)`,

and the monograph (§5.1) observes that this single identity is what makes the
up-down and down-up walks reversible *and* positive semidefinite.  This module
isolates that observation.

* `Adjoint μ ν K L` — the relation `μ x · K x y = ν y · L y x` for
  `K : α → β` and `L : β → α`.  `Reversible μ P` is exactly `Adjoint μ μ P P`
  (`adjoint_self_iff`).
* `Adjoint.ip_act` — the `L²` form: `⟪f, K g⟫_μ = ⟪L f, g⟫_ν`.
* `Adjoint.push_left`, `Adjoint.push_right` — adjointness already forces the two
  distributions to be each other's pushforwards; neither is free data.
* `Adjoint.comp_reversible`, `Adjoint.comp_nonnegDefinite` — **the payoff**:
  `K ∘ₖ L` is reversible with respect to `μ` and positive semidefinite, and
  symmetrically for `L ∘ₖ K` with respect to `ν`.  Both proofs are one line, and
  the PSD proof in particular is the elementary replacement for "the nonzero
  spectra of `AB` and `BA` agree, and `A A*` has nonnegative eigenvalues".
* `Adjoint.dirichlet_comp` — `ℰ_{K∘ₖL}(f) = ⟪f,f⟫_μ - ⟪L f, L f⟫_ν`, the form in
  which the Dirichlet form of an up-down walk enters the local-to-global
  induction.

The significance for this library is that positive semidefiniteness is exactly
the hypothesis `Techniques.SpectralGap` needs in order to turn a Poincaré
inequality into decay of variance.  `Techniques.Lazy` obtains it by averaging
with the identity; here it comes for free from the structure of the walk, at no
cost in the gap.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.Dirichlet

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {α β : Type*} [Fintype α] [Fintype β]

/-! ## The adjointness relation -/

/-- `K : α → β` and `L : β → α` are **mutually adjoint** with respect to `μ` on
`α` and `ν` on `β` when `μ(x) K(x, y) = ν(y) L(y, x)` for all `x, y`.

This is detailed balance for a pair of kernels between different spaces.  Taking
`α = β`, `μ = ν` and `K = L` recovers `Reversible` exactly. -/
def Adjoint (μ : FinDist α) (ν : FinDist β) (K : FinKernel α β) (L : FinKernel β α) : Prop :=
  ∀ x y, μ x * K x y = ν y * L y x

/-- Adjointness is symmetric in the two kernels. -/
theorem Adjoint.symm {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β} {L : FinKernel β α}
    (h : Adjoint μ ν K L) : Adjoint ν μ L K := fun y x => (h x y).symm

/-- `Reversible` is the self-adjoint case. -/
theorem adjoint_self_iff {Ω : Type*} [Fintype Ω] (μ : FinDist Ω) (P : FinChain Ω) :
    Adjoint μ μ P P ↔ Reversible μ P := Iff.rfl

/-! ## Adjointness composes

Note the asymmetry: the forward operators compose in the order they are applied,
the adjoints in the opposite order, exactly as for a composite of linear maps and
its adjoint. -/

section Comp

variable {γ : Type*} [Fintype γ]

/-- **Adjointness composes.**  If `K : α → β` and `L : β → α` are mutually
adjoint for `μ, ν`, and `K' : β → γ` and `L' : γ → β` are mutually adjoint for
`ν, ρ`, then `K ∘ₖ K'` and `L' ∘ₖ L` are mutually adjoint for `μ, ρ`.

The order is **reversed** on the right: the adjoint of a composite is the
composite of the adjoints in the opposite order, and here that is visible in the
matrices rather than in an abstract `L²` argument.  The proof is one chain of
rewrites inside a sum over the intermediate space: `μ(x)K(x,y)` becomes
`ν(y)L(y,x)`, then `ν(y)K'(y,z)` becomes `ρ(z)L'(z,y)`, and the two `L`s are
left over in the right order. -/
theorem Adjoint.comp {μ : FinDist α} {ν : FinDist β} {ρ : FinDist γ}
    {K : FinKernel α β} {L : FinKernel β α} {K' : FinKernel β γ} {L' : FinKernel γ β}
    (h : Adjoint μ ν K L) (h' : Adjoint ν ρ K' L') :
    Adjoint μ ρ (K ∘ₖ K') (L' ∘ₖ L) := by
  intro x z
  rw [FinKernel.comp_apply, FinKernel.comp_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  calc μ x * (K x y * K' y z) = μ x * K x y * K' y z := by ring
    _ = ν y * L y x * K' y z := by rw [h x y]
    _ = ν y * K' y z * L y x := by ring
    _ = ρ z * L' z y * L y x := by rw [h' y z]
    _ = ρ z * (L' z y * L y x) := by ring

end Comp

section Id

variable [DecidableEq α]

/-- The unit of `Adjoint.comp`: the identity kernel is self-adjoint with respect
to every distribution. -/
theorem adjoint_id (μ : FinDist α) : Adjoint μ μ (FinKernel.id α) (FinKernel.id α) := by
  intro x y
  by_cases h : x = y
  · rw [h]
  · simp only [FinKernel.id]
    rw [if_neg h, if_neg (Ne.symm h), mul_zero, mul_zero]

end Id

/-! ## Consequences for the distributions

Mutual adjointness is a strong relation: it pins down each distribution as the
pushforward of the other, so `μ` and `ν` cannot be chosen independently. -/

/-- Adjointness forces `ν` to be the pushforward of `μ` along `K`. -/
theorem Adjoint.push_left {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β}
    {L : FinKernel β α} (h : Adjoint μ ν K L) : K.push μ = ν := by
  refine FinDist.ext fun y => ?_
  rw [FinKernel.push_apply]
  calc ∑ x, μ x * K x y = ∑ x, ν y * L y x := Finset.sum_congr rfl fun x _ => h x y
    _ = ν y := by rw [← Finset.mul_sum, L.sum_coe y, mul_one]

/-- Adjointness forces `μ` to be the pushforward of `ν` along `L`. -/
theorem Adjoint.push_right {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β}
    {L : FinKernel β α} (h : Adjoint μ ν K L) : L.push ν = μ := h.symm.push_left

/-! ## The `L²` form of adjointness -/

/-- **Adjointness in `L²`**: `⟪f, K g⟫_μ = ⟪L f, g⟫_ν`.

Every result below is a corollary of this identity. -/
theorem Adjoint.ip_act {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β} {L : FinKernel β α}
    (h : Adjoint μ ν K L) (f : α → ℝ) (g : β → ℝ) :
    ip μ f (K.act g) = ip ν (L.act f) g := by
  have hL : ∀ x : α, ∀ y : β, μ x * K x y * (f x * g y) = ν y * L y x * (f x * g y) :=
    fun x y => by rw [h x y]
  calc ip μ f (K.act g)
      = ∑ x, ∑ y, μ x * K x y * (f x * g y) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [FinKernel.act, Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ x, ∑ y, ν y * L y x * (f x * g y) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hL x y
    _ = ∑ y, ∑ x, ν y * L y x * (f x * g y) := Finset.sum_comm
    _ = ip ν (L.act f) g := by
        refine Finset.sum_congr rfl fun y _ => ?_
        show ∑ x, ν y * L y x * (f x * g y) = ν y * (∑ x, L y x * f x) * g y
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring

/-! ## Reversibility and positive semidefiniteness of the composites

`K ∘ₖ L` is a chain on `α` and `L ∘ₖ K` a chain on `β`.  For the up/down
operators these are the up-down and down-up walks. -/

/-- **`K ∘ₖ L` is reversible with respect to `μ`.**

The proof is the whole argument in one calculation: pushing `μ(x) K(x,y)` through
adjointness turns the composite into `∑ y, ν y * L y x * L y x'`, which is
visibly symmetric in `x` and `x'`. -/
theorem Adjoint.comp_reversible {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β}
    {L : FinKernel β α} (h : Adjoint μ ν K L) : Reversible μ (K ∘ₖ L) := by
  have key : ∀ x x' : α, μ x * (K ∘ₖ L) x x' = ∑ y, ν y * L y x * L y x' := by
    intro x x'
    rw [FinKernel.comp_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by rw [← mul_assoc, h x y]
  intro x x'
  rw [key x x', key x' x]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- `L ∘ₖ K` is reversible with respect to `ν`. -/
theorem Adjoint.comp_reversible' {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β}
    {L : FinKernel β α} (h : Adjoint μ ν K L) : Reversible ν (L ∘ₖ K) :=
  h.symm.comp_reversible

/-- `μ` is stationary for `K ∘ₖ L`. -/
theorem Adjoint.comp_stationary {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β}
    {L : FinKernel β α} (h : Adjoint μ ν K L) : Stationary μ (K ∘ₖ L) :=
  h.comp_reversible.stationary

/-- **`K ∘ₖ L` is positive semidefinite.**

`⟪f, K(L f)⟫_μ = ⟪L f, L f⟫_ν ≥ 0`: one application of `Adjoint.ip_act`.  This is the
elementary substitute for the spectral argument that a composite `A A*` has
nonnegative eigenvalues, and it is what lets `Techniques.SpectralGap` convert a
Poincaré inequality for an up-down walk into decay of variance without ever
halving the gap by passing to the lazy chain. -/
theorem Adjoint.comp_nonnegDefinite {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β}
    {L : FinKernel β α} (h : Adjoint μ ν K L) : NonnegDefinite μ (K ∘ₖ L) := by
  intro f
  rw [show (K ∘ₖ L).act f = K.act (L.act f) from FinKernel.act_comp K L f, h.ip_act f (L.act f)]
  exact ip_self_nonneg ν (L.act f)

/-- `L ∘ₖ K` is positive semidefinite with respect to `ν`. -/
theorem Adjoint.comp_nonnegDefinite' {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β}
    {L : FinKernel β α} (h : Adjoint μ ν K L) : NonnegDefinite ν (L ∘ₖ K) :=
  h.symm.comp_nonnegDefinite

/-! ## The self-adjoint case

Specialising to `K = L = P` says something about ordinary reversible chains that is
worth recording separately: their *squares* are always positive semidefinite. -/

/-- **The square of a reversible chain is positive semidefinite.**

This is a fourth source of PSD-ness, alongside laziness, adjointness of a genuine
pair, and self-adjoint idempotence.  It costs nothing in the gap but doubles the
time scale, so `Techniques.Lazy` is usually the better trade — but it is the only
one available when the chain is given and cannot be modified. -/
theorem Reversible.sq_nonnegDefinite {Ω : Type*} [Fintype Ω] {μ : FinDist Ω}
    {P : FinChain Ω} (h : Reversible μ P) : NonnegDefinite μ (P ∘ₖ P) :=
  ((adjoint_self_iff μ P).mpr h).comp_nonnegDefinite

/-- The square of a reversible chain is reversible. -/
theorem Reversible.sq_reversible {Ω : Type*} [Fintype Ω] {μ : FinDist Ω}
    {P : FinChain Ω} (h : Reversible μ P) : Reversible μ (P ∘ₖ P) :=
  ((adjoint_self_iff μ P).mpr h).comp_reversible

/-! ## The Dirichlet form of a composite -/

/-- The Dirichlet form of `K ∘ₖ L` measures how much `L` contracts:
`ℰ_{K∘ₖL}(f) = ⟪f, f⟫_μ - ⟪L f, L f⟫_ν`.

This is the shape in which the Dirichlet form of an up-down walk enters the
local-to-global induction: the loss in norm on passing to the level below. -/
theorem Adjoint.dirichlet_comp {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β}
    {L : FinKernel β α} (h : Adjoint μ ν K L) (f : α → ℝ) :
    dirichlet μ (K ∘ₖ L) f f = ip μ f f - ip ν (L.act f) (L.act f) := by
  rw [dirichlet_apply,
    show (K ∘ₖ L).act f = K.act (L.act f) from FinKernel.act_comp K L f, h.ip_act f (L.act f)]

/-- Consequently `⟪L f, L f⟫_ν ≤ ⟪f, f⟫_μ`: the down operator is a contraction. -/
theorem Adjoint.ip_act_le {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β}
    {L : FinKernel β α} (h : Adjoint μ ν K L) (f : α → ℝ) :
    ip ν (L.act f) (L.act f) ≤ ip μ f f := by
  have h1 := dirichlet_self_nonneg h.comp_stationary f
  rw [h.dirichlet_comp f] at h1
  linarith

end Arlib.MarkovChains
