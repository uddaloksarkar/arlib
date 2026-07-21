/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The two composites of an adjoint pair have the same spectral gap

`lem:updown-downup` of the source monograph asserts `γ(P^∧∨_{k-1}) = γ(P^∨∧_k)`:
the up-down walk on level `k` and the down-up walk on level `k + 1` have the same
spectral gap.  The monograph proves it by "the nonzero spectrum of `AB` equals the
nonzero spectrum of `BA`", which is exactly the route the design principles of
this area forbid.  This module supplies the elementary replacement, and supplies
it at the right generality: nothing about the two composites of a *mutually
adjoint pair* `Adjoint μ ν K L` is special to the up and down operators of a
weighted complex.

The argument is Cauchy–Schwarz applied twice, once in each direction, and it
never leaves the world of squared norms — no `Real.sqrt` appears.  Writing
`γ · Var ≤ ℰ` in the equivalent "norm" form `‖L f‖² ≤ (1 - γ)‖f‖²` on mean-zero
`f`, adjointness gives

  `‖K g‖²_μ = ⟪g, L (K g)⟫_ν ≤ ‖g‖_ν · ‖L (K g)‖_ν`  and  `‖L (K g)‖²_ν ≤ (1-γ)‖K g‖²_μ`,

so `‖K g‖⁴ ≤ ‖g‖² (1-γ) ‖K g‖²`, and dividing by `‖K g‖²` (or observing that the
conclusion is trivial when it vanishes) gives `‖K g‖² ≤ (1-γ)‖g‖²`.

* `Adjoint.Ex_act_left` — `μ(K g) = ν(g)`: the functional form of
  `Adjoint.push_left`, which is what keeps "mean-zero" mean-zero across `K`.
* `Adjoint.spectralGapAtLeast_comp_iff_norm` — **the translation**, both
  directions: `SpectralGapAtLeast μ (K ∘ₖ L) γ` holds iff
  `⟪L f, L f⟫_ν ≤ (1 - γ)⟪f, f⟫_μ` for every mean-zero `f`.  Centering is handled
  once and for all here, by `Var_sub_const` and `dirichlet_self_sub_const`.
* `Adjoint.spectralGapAtLeast_comp_swap` — **the headline**: for `γ ≤ 1`, a gap
  of `γ` for `K ∘ₖ L` on `α` transfers to `L ∘ₖ K` on `β`.
* `Adjoint.spectralGapAtLeast_comp_iff` — the resulting equivalence, and
  `Adjoint.spectralGapAtLeast_comp_swap_min` the sharpest unconditional form.
* `upDown_spectralGapAtLeast_iff` — `lem:updown-downup` itself, obtained from
  `Levels.up_down_adjoint` in one line.

## The hypothesis `γ ≤ 1` is not decoration

The equivalence is **false** without it, and the failure is not an artefact of
the proof.  `SpectralGapAtLeast` is a Poincaré inequality, so it is vacuously
true for *every* `γ` when every function on `α` has zero variance, while the
composite on the other side can be a genuine chain with gap exactly `1`.
`exists_adjoint_gap_not_swap` exhibits this for an arbitrary pair of spaces: take
`μ` a point mass, `K` the independent sampler onto `ν`, and `L` the constant
kernel back to that point.  Since `γ ≤ 1` is automatic for any composite with a
non-degenerate stationary measure (`gap_le_one_of_var_pos`, and every composite
here is positive semidefinite for free), the hypothesis costs nothing in
practice — but it must be stated.

Everything here is proved from first principles with no `sorry`, and with no
eigenvalue, spectrum or spectral theorem anywhere.
-/
import Arlib.MarkovChains.Techniques.Levels

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## A Poincaré constant is at most `1` unless the chain is degenerate

Recorded first because it is what makes the hypothesis `γ ≤ 1` below harmless:
for a positive semidefinite chain the Dirichlet form is bounded above by the
variance, so no `γ > 1` can satisfy the Poincaré inequality unless *every*
function has zero variance. -/

section GapLeOne

variable {Ω : Type*} [Fintype Ω]

/-- **A positive semidefinite chain has Poincaré constant at most `1`**, as soon
as some function has positive variance.

`ℰ_P(f) = ⟪f,f⟫ - ⟪f, P f⟫ ≤ ⟪f,f⟫ = Var(f)` on a mean-zero `f`, so
`γ · Var(f) ≤ Var(f)`.  No stationarity is needed: `dirichlet` is defined without
it, and centering is available unconditionally. -/
theorem gap_le_one_of_var_pos {μ : FinDist Ω} {P : FinChain Ω} {γ : ℝ}
    (hpsd : NonnegDefinite μ P) (hgap : SpectralGapAtLeast μ P γ)
    {f : Ω → ℝ} (hf : 0 < Var μ f) : γ ≤ 1 := by
  have hg0 : Ex μ (fun x => f x - Ex μ f) = 0 := Ex_center μ f
  have hVar : Var μ (fun x => f x - Ex μ f) = Var μ f := Var_sub_const μ f _
  have hip : Var μ (fun x => f x - Ex μ f)
      = ip μ (fun x => f x - Ex μ f) (fun x => f x - Ex μ f) :=
    Var_eq_ip_self_of_mean_zero hg0
  have hd := hgap (fun x => f x - Ex μ f)
  rw [dirichlet_apply, hVar] at hd
  rw [hVar] at hip
  have hnn := hpsd (fun x => f x - Ex μ f)
  nlinarith [hd, hip, hnn, hf]

end GapLeOne

/-! ## The gap of a composite, in norm form -/

section AdjointPair

variable {α β : Type*} [Fintype α] [Fintype β]
variable {μ : FinDist α} {ν : FinDist β} {K : FinKernel α β} {L : FinKernel β α}

/-- **Adjointness preserves expectations**: `μ(K g) = ν(g)`.

This is `Adjoint.push_left` (`ν` *is* the pushforward of `μ` along `K`) read on
functions, and it is the reason the mean-zero subspace of `L²(ν)` is carried into
the mean-zero subspace of `L²(μ)` by `K` — without which the norm form of the
Poincaré inequality could not be transported at all. -/
theorem Adjoint.Ex_act_left (h : Adjoint μ ν K L) (g : β → ℝ) :
    Ex μ (K.act g) = Ex ν g := by
  have h1 : ip μ (fun _ => (1 : ℝ)) (K.act g) = ip ν (L.act fun _ => (1 : ℝ)) g :=
    h.ip_act _ g
  rw [FinKernel.act_const] at h1
  rw [← ip_one_right μ (K.act g), ip_comm μ (K.act g) (fun _ => (1 : ℝ)), h1,
    ip_comm ν (fun _ => (1 : ℝ)) g, ip_one_right]

/-- **The Poincaré inequality for `K ∘ₖ L`, in norm form.**

`SpectralGapAtLeast μ (K ∘ₖ L) γ` is equivalent to the statement that `L`
contracts mean-zero functions by `√(1 - γ)` in `L²`, written here — deliberately —
as the squared inequality `⟪L f, L f⟫_ν ≤ (1 - γ)⟪f, f⟫_μ`, so that no square root
ever has to be introduced.

Both directions are needed downstream, and both are elementary: `→` is
`Adjoint.dirichlet_comp` on a mean-zero function, where `Var` *is* `⟪f,f⟫`, and
`←` is the same computation after centering, using that `Var` and the Dirichlet
form are alike insensitive to adding a constant. -/
theorem Adjoint.spectralGapAtLeast_comp_iff_norm (h : Adjoint μ ν K L) (γ : ℝ) :
    SpectralGapAtLeast μ (K ∘ₖ L) γ ↔
      ∀ f : α → ℝ, Ex μ f = 0 → ip ν (L.act f) (L.act f) ≤ (1 - γ) * ip μ f f := by
  constructor
  · intro hgap f hf
    have hd := hgap f
    rw [Var_eq_ip_self_of_mean_zero hf, h.dirichlet_comp f] at hd
    linarith
  · intro hnorm f
    have hg0 : Ex μ (fun x => f x - Ex μ f) = 0 := Ex_center μ f
    have hVar : Var μ (fun x => f x - Ex μ f) = Var μ f := Var_sub_const μ f _
    have hip : Var μ (fun x => f x - Ex μ f)
        = ip μ (fun x => f x - Ex μ f) (fun x => f x - Ex μ f) :=
      Var_eq_ip_self_of_mean_zero hg0
    have hdir : dirichlet μ (K ∘ₖ L) (fun x => f x - Ex μ f) (fun x => f x - Ex μ f)
        = dirichlet μ (K ∘ₖ L) f f :=
      dirichlet_self_sub_const h.comp_stationary f _
    have hdc := h.dirichlet_comp (fun x => f x - Ex μ f)
    have hn := hnorm _ hg0
    rw [← hVar, hip, ← hdir, hdc]
    linarith

/-! ## The transfer

The whole content of `lem:updown-downup`, with Cauchy–Schwarz in place of the
spectrum of `AB` versus `BA`. -/

/-- **The two composites have the same spectral gap** (transfer direction).

If `K ∘ₖ L` has spectral gap at least `γ ≤ 1` with respect to `μ`, then `L ∘ₖ K`
has spectral gap at least `γ` with respect to `ν`.

Write `u = K g` for a mean-zero `g : β → ℝ`; `u` is mean-zero by
`Adjoint.Ex_act_left`.  Adjointness turns `⟪u, u⟫_μ` into `⟪g, L u⟫_ν`, Cauchy–
Schwarz (`ip_sq_le`) bounds its square by `⟪g,g⟫_ν ⟪L u, L u⟫_ν`, and the
hypothesis in norm form bounds `⟪L u, L u⟫_ν` by `(1-γ)⟪u,u⟫_μ`.  The result is
`⟪u,u⟫² ≤ (1-γ)⟪g,g⟫⟪u,u⟫`, which divides through.  Everything stays squared;
`Real.sqrt` is never needed. -/
theorem Adjoint.spectralGapAtLeast_comp_swap (h : Adjoint μ ν K L) {γ : ℝ} (hγ : γ ≤ 1)
    (hgap : SpectralGapAtLeast μ (K ∘ₖ L) γ) : SpectralGapAtLeast ν (L ∘ₖ K) γ := by
  rw [h.symm.spectralGapAtLeast_comp_iff_norm γ]
  intro g hg
  have hnorm := (h.spectralGapAtLeast_comp_iff_norm γ).mp hgap
  have hu0 : Ex μ (K.act g) = 0 := by rw [h.Ex_act_left g, hg]
  -- `⟪K g, K g⟫_μ = ⟪g, L (K g)⟫_ν`, by adjointness.
  have hA : ip μ (K.act g) (K.act g) = ip ν g (L.act (K.act g)) := by
    rw [ip_comm ν g (L.act (K.act g)), ← h.ip_act (K.act g) g]
  have hCS : ip ν g (L.act (K.act g)) ^ 2
      ≤ ip ν g g * ip ν (L.act (K.act g)) (L.act (K.act g)) := ip_sq_le ν _ _
  have hD := hnorm (K.act g) hu0
  have hB : 0 ≤ ip ν g g := ip_self_nonneg ν g
  have hAnn : 0 ≤ ip μ (K.act g) (K.act g) := ip_self_nonneg μ _
  have hc : 0 ≤ 1 - γ := by linarith
  rcases eq_or_lt_of_le hAnn with hA0 | hApos
  · rw [← hA0]
    exact mul_nonneg hc hB
  · have h1 : ip ν g g * ip ν (L.act (K.act g)) (L.act (K.act g))
        ≤ ip ν g g * ((1 - γ) * ip μ (K.act g) (K.act g)) :=
      mul_le_mul_of_nonneg_left hD hB
    have h2 : ip μ (K.act g) (K.act g) ^ 2
        ≤ ip ν g g * ((1 - γ) * ip μ (K.act g) (K.act g)) :=
      calc ip μ (K.act g) (K.act g) ^ 2 = ip ν g (L.act (K.act g)) ^ 2 := by rw [hA]
        _ ≤ ip ν g g * ((1 - γ) * ip μ (K.act g) (K.act g)) := le_trans hCS h1
    have key : ip μ (K.act g) (K.act g) * ip μ (K.act g) (K.act g)
        ≤ ((1 - γ) * ip ν g g) * ip μ (K.act g) (K.act g) := by nlinarith [h2]
    exact le_of_mul_le_mul_right key hApos

/-- **`lem:updown-downup` for an arbitrary adjoint pair.**

For `γ ≤ 1`, `K ∘ₖ L` has spectral gap at least `γ` with respect to `μ` if and
only if `L ∘ₖ K` has spectral gap at least `γ` with respect to `ν`.  Since the
spectral gap is by definition the largest such `γ`, this is exactly the statement
that the two walks have the same gap. -/
theorem Adjoint.spectralGapAtLeast_comp_iff (h : Adjoint μ ν K L) {γ : ℝ} (hγ : γ ≤ 1) :
    SpectralGapAtLeast μ (K ∘ₖ L) γ ↔ SpectralGapAtLeast ν (L ∘ₖ K) γ :=
  ⟨h.spectralGapAtLeast_comp_swap hγ, h.symm.spectralGapAtLeast_comp_swap hγ⟩

/-- The sharpest hypothesis-free form of the transfer: a gap of `γ` for `K ∘ₖ L`
gives a gap of `min γ 1` for `L ∘ₖ K`.  For the values of `γ` that occur in
practice (`γ ≤ 1`, by `gap_le_one_of_var_pos`) this is the full statement. -/
theorem Adjoint.spectralGapAtLeast_comp_swap_min (h : Adjoint μ ν K L) {γ : ℝ}
    (hgap : SpectralGapAtLeast μ (K ∘ₖ L) γ) : SpectralGapAtLeast ν (L ∘ₖ K) (min γ 1) :=
  h.spectralGapAtLeast_comp_swap (min_le_right γ 1) (hgap.mono (min_le_left γ 1))

end AdjointPair

/-! ## Sharpness: the hypothesis `γ ≤ 1` cannot be dropped

The transfer above is *not* an unconditional equivalence, and the counterexample
is as simple as it could be.  A Poincaré inequality says nothing at all when
every function has zero variance, so a point mass on `α` satisfies
`SpectralGapAtLeast μ (K ∘ₖ L) γ` for every real `γ`, however large — while the
companion composite on `β` may be a perfectly ordinary chain whose gap is exactly
`1`.  Nothing here is special to a particular state space: the construction takes
any `ν` on any `β` and any point `a : α`. -/

section Sharpness

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

/-- **The transfer fails for `γ > 1`.**

For any point `a : α`, any `ν` on `β` admitting a function of positive variance,
and any `γ > 1`, there is a mutually adjoint pair `K`, `L` such that `K ∘ₖ L` has
spectral gap at least `γ` while `L ∘ₖ K` does not.

The witness: `μ = δ_a`, `K x y = ν y` (jump to equilibrium), `L y x = [x = a]`
(jump back to `a`).  Then `L ∘ₖ K` is the independent sampler on `ν`, whose
Dirichlet form *is* the variance, so its Poincaré constant is exactly `1`; and
`K ∘ₖ L` lives over a distribution on which every variance vanishes, so it
satisfies every Poincaré inequality vacuously. -/
theorem exists_adjoint_gap_not_swap (a : α) (ν : FinDist β) {γ : ℝ} (hγ : 1 < γ)
    {g : β → ℝ} (hg : 0 < Var ν g) :
    ∃ (μ : FinDist α) (K : FinKernel α β) (L : FinKernel β α),
      Adjoint μ ν K L ∧ SpectralGapAtLeast μ (K ∘ₖ L) γ ∧
        ¬ SpectralGapAtLeast ν (L ∘ₖ K) γ := by
  -- The three kernels, produced together with their defining equations so that
  -- the proofs below never have to look inside a structure instance.
  obtain ⟨μ, hμ⟩ : ∃ μ : FinDist α, ∀ x, μ x = if x = a then 1 else 0 :=
    ⟨⟨fun x => if x = a then 1 else 0, fun x => by by_cases hx : x = a <;> simp [hx], by simp⟩,
      fun _ => rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : FinKernel α β, ∀ x y, K x y = ν y :=
    ⟨⟨fun _ y => ν y, fun _ y => ν.coe_nonneg y, fun _ => ν.sum_coe⟩, fun _ _ => rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : FinKernel β α, ∀ y x, L y x = if x = a then 1 else 0 :=
    ⟨⟨fun _ x => if x = a then 1 else 0, fun _ x => by by_cases hx : x = a <;> simp [hx],
      fun _ => by simp⟩, fun _ _ => rfl⟩
  have hadj : Adjoint μ ν K L := by
    intro x y
    rw [hμ, hK, hL]
    ring
  refine ⟨μ, K, L, hadj, ?_, ?_⟩
  · -- Every function has zero variance over a point mass, so *every* `γ` works.
    intro f
    have hEx : Ex μ f = f a := by simp [Ex_apply, hμ]
    have hVar : Var μ f = 0 := by simp [Var_apply, hEx, hμ]
    rw [hVar, mul_zero]
    exact dirichlet_self_nonneg hadj.comp_stationary f
  · -- The other composite is the independent sampler, whose Poincaré constant is `1`.
    intro hgap
    have hcomp : ∀ y y' : β, (L ∘ₖ K) y y' = ν y' := by
      intro y y'
      rw [FinKernel.comp_apply]
      simp [hL, hK]
    have hact : (L ∘ₖ K).act g = fun _ => Ex ν g := by
      funext y
      rw [FinKernel.act_apply]
      simp only [hcomp]
      rw [← Ex_apply]
    have hip : ip ν g (fun _ => Ex ν g) = Ex ν g ^ 2 := by
      simp only [ip_apply]
      rw [← Finset.sum_mul, ← Ex_apply]
      ring
    have hd := hgap g
    rw [dirichlet_apply, hact, hip, ← Var_eq_ip_sub_sq] at hd
    nlinarith [hd, hg, hγ]

end Sharpness

/-! ## `lem:updown-downup` -/

section Levels

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **The up-down and down-up walks have the same spectral gap** —
`lem:updown-downup` of the monograph, `γ(P^∧∨_k) = γ(P^∨∧_{k+1})` in the
indexing of `Techniques.Levels`.

The monograph deduces this from the equality of the nonzero spectra of `AB` and
`BA`; here it is `Adjoint.spectralGapAtLeast_comp_iff` applied to
`Levels.up_down_adjoint`, and the only analytic input is Cauchy–Schwarz.

The hypothesis `γ ≤ 1` is harmless: by `gap_le_one_of_var_pos` together with
`upDown_nonnegDefinite` it is implied by the gap statement itself whenever `π_k`
is non-degenerate. -/
theorem upDown_spectralGapAtLeast_iff (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) {γ : ℝ} (hγ : γ ≤ 1) :
    SpectralGapAtLeast (pi w n k hw hsupp hsum hk.le) (upDown w n k hw hsupp hk) γ ↔
      SpectralGapAtLeast (pi w n (k + 1) hw hsupp hsum hk) (downUp w n k hw hsupp hk) γ :=
  (up_down_adjoint w n k hw hsupp hsum hk).spectralGapAtLeast_comp_iff hγ

/-- The transfer in the direction the local-to-global induction consumes: a gap
for the up-down walk on level `k` is a gap for the down-up walk on level `k+1`. -/
theorem downUp_spectralGapAtLeast_of_upDown (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) {γ : ℝ} (hγ : γ ≤ 1)
    (hgap : SpectralGapAtLeast (pi w n k hw hsupp hsum hk.le) (upDown w n k hw hsupp hk) γ) :
    SpectralGapAtLeast (pi w n (k + 1) hw hsupp hsum hk) (downUp w n k hw hsupp hk) γ :=
  (upDown_spectralGapAtLeast_iff w n k hw hsupp hsum hk hγ).mp hgap

/-- The converse direction: a gap for the down-up walk on level `k+1` is a gap
for the up-down walk on level `k`. -/
theorem upDown_spectralGapAtLeast_of_downUp (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (hk : k < n) {γ : ℝ} (hγ : γ ≤ 1)
    (hgap : SpectralGapAtLeast (pi w n (k + 1) hw hsupp hsum hk)
      (downUp w n k hw hsupp hk) γ) :
    SpectralGapAtLeast (pi w n k hw hsupp hsum hk.le) (upDown w n k hw hsupp hk) γ :=
  (upDown_spectralGapAtLeast_iff w n k hw hsupp hsum hk hγ).mpr hgap

end Levels

end Arlib.MarkovChains

