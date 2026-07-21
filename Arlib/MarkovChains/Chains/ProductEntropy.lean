/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Tensorization of entropy for a product measure, and the modified log-Sobolev inequality

`Chains/ProductMeasure.lean` proves approximate tensorization of *variance* for a
product measure, and hence a spectral gap of `1/n` for its Gibbs sampler.  That
route pays a factor `log(1/μ_min) = Θ(n)` when it is converted into a mixing
time, so the monograph replaces variance by **entropy** everywhere.  This module
carries out the entropy half of the programme for the one measure where it can be
done from first principles: for `μ` a product measure and every `f > 0`,

  `Ent_μ(f) ≤ ∑_v μ[Ent_v(f)]`,

subadditivity of entropy — classically Han's inequality, or the tensorization
property of relative entropy — with the optimal constant `1`.  Combined with the
local comparison `μ[Ent_v(f)] ≤ ℰ_{P_v}(f, log f)` proved below, this gives a
**modified log-Sobolev inequality with constant `1/n`** for the Glauber dynamics
of a product measure, against `Techniques/Entropy.lean`'s `ModLogSobolev` — the
*correct* one, paired with the entropy production, not the vacuous
`NaiveModLogSobolev`.

## Homogeneity

Every inequality stated here is `1`-homogeneous on both sides, which is the test
`Techniques/Entropy.lean` records as `naiveModLogSobolev_le_zero`.  `Ent` is
`1`-homogeneous (`Ent_smul`); so is `localEnt`, being a `μ`-average of entropies;
and so is `entropyProduction` (`entropyProduction_smul`).  Nothing below pairs
`Ent` with the quadratic form `ℰ(f, f)`.

## How the proof works

The skeleton is the one that worked for the variance in `Chains/ProductMeasure.lean`
and it transfers without change: the projection kernels `Q_Λ` of that module are
reused verbatim, the statement proved by induction is uniform in `Λ`, and plain
`Finset.induction_on` closes it with **no ordering of the sites** and no
martingale filtration.  Only the functional changes, and with it the two analytic
ingredients:

* the quantity that telescopes is `Ent_μ(f) − Ent_μ(Q_Λ f)` rather than
  `‖f‖² − ‖Q_Λ f‖²`;
* the monotonicity of the increment, which for the variance was the statement
  that `Q_Λ` is an `L²(μ)`-contraction, is here the **log-sum inequality**
  `(∑ a) log((∑ a)/(∑ b)) ≤ ∑ a log(a/b)`, i.e. the data-processing inequality
  for the relative entropy of a *pair of functions* along a common kernel.

The bridge between the two is the identity `Ent_μ(g) − Ent_μ(Q g) = μ[g log(g/Qg)]`,
valid whenever `Q` is self-adjoint and `log(Q g)` is `Q`-invariant — for the
resampling kernels the latter holds because `Q_Λ g` does not depend on the spins
inside `Λ` at all (`act_prodProj_fix`).

## Main declarations

Two layers of general machinery sit below this module.  The log-sum inequality
`mul_log_sub_log_sum_le`, its kernel form `Ex_mul_log_sub_log_act_le`, and the
mean conditional entropy `localEnt` with **`localEnt_le_entropyProduction`**
(valid for *any* reversible chain) are in `Techniques/Entropy.lean`; the
spin-system instances `siteEnt`, `ApproxTensorizationEnt` and
**`modLogSobolev_glauber_of_approxTensorizationEnt`** are in
`Chains/GlauberTensorization.lean`, beside their variance counterparts.  Nothing
in either layer is specific to a product measure.

* `act_prodProj_congr`, **`act_prodProj_fix`** — `Q_Λ f` ignores the spins in `Λ`,
  hence every function of `Q_Λ f` is `Q_Λ`-invariant.
* **`Ent_sub_Ent_act_prodProj`** — the relative-entropy form of the increment.
* **`Ent_sub_Ent_act_prodProj_le`** — the crux: passing a function through `Q_Λ`
  can only decrease the entropy destroyed by resampling a site.
* **`Ent_sub_Ent_act_prodProj_le_sum`** — the induction on `Λ`.
* **`approxTensorizationEnt_prodWeight`** — the headline:
  `Ent_μ(f) ≤ ∑_v μ[Ent_v(f)]` for a product measure.
* **`modLogSobolev_glauber_prodWeight`** — hence the Glauber dynamics of a
  product measure satisfies a modified log-Sobolev inequality with constant
  `1/n`.

Everything here is proved from first principles with no `sorry`; in particular no
eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Chains.ProductMeasure
import Arlib.MarkovChains.Techniques.Entropy

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset


/-! ## Transport across null rows

The single-site heat-bath update and the one-site resampling kernel of a product
measure differ off the support of the Gibbs measure, exactly as in
`Chains/ProductMeasure.lean`; `localEnt` weights the row at `σ` by `μ(σ)`, so it
does not see the difference. -/

section TransportLocalEnt

variable {Ω : Type*} [Fintype Ω] {μ : FinDist Ω} {P Q : FinChain Ω}

/-- The mean conditional entropy only depends on the rows the measure charges. -/
theorem EqOnSupport.localEnt_eq (h : EqOnSupport μ P Q) (f : Ω → ℝ) :
    localEnt μ P f = localEnt μ Q f := by
  simp only [localEnt_apply, Ex_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : μ x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [show P.row x = Q.row x from FinDist.ext fun y => h x hx y]

end TransportLocalEnt

/-! ## The resampling kernels ignore the resampled spins

The one structural fact about `Q_Λ` that the variance proof did not need.  `Q_Λ f`
depends only on the spins *off* `Λ`, so it is constant along the rows of `Q_Λ`,
and therefore *any* function of `Q_Λ f` — in particular `log (Q_Λ f)` — is
`Q_Λ`-invariant.  That is exactly the hypothesis of
`Ent_sub_Ent_act_of_invariant`. -/

section Invariance

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ}

/-- The matrix of `Q_Λ` depends on the source configuration only through the
spins off `Λ`. -/
theorem prodProjMat_congr_left (Λ : Finset V) {σ σ' : V → S} (h : ∀ v, v ∉ Λ → σ v = σ' v)
    (τ : V → S) : prodProjMat φ Λ σ τ = prodProjMat φ Λ σ' τ := by
  simp only [prodProjMat_apply]
  refine Finset.prod_congr rfl fun v _ => ?_
  by_cases hv : v ∈ Λ
  · rw [if_pos hv, if_pos hv]
  · rw [if_neg hv, if_neg hv, h v hv]

variable (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)

/-- A transition of `Q_Λ` of positive probability changes no spin off `Λ`. -/
theorem agree_of_prodProj_ne_zero (Λ : Finset V) {σ τ : V → S}
    (h : prodProj hφ hc Λ σ τ ≠ 0) {v : V} (hv : v ∉ Λ) : τ v = σ v := by
  by_contra hne
  refine h ?_
  rw [prodProj_apply, prodProjMat_apply]
  exact Finset.prod_eq_zero (mem_univ v) (by rw [if_neg hv, if_neg hne])

/-- **`Q_Λ f` ignores the spins inside `Λ`.**  Two configurations agreeing off
`Λ` give the same value. -/
theorem act_prodProj_congr (Λ : Finset V) (u : (V → S) → ℝ) {σ σ' : V → S}
    (h : ∀ v, v ∉ Λ → σ v = σ' v) :
    (prodProj hφ hc Λ).act u σ = (prodProj hφ hc Λ).act u σ' := by
  simp only [FinKernel.act_apply, prodProj_apply]
  exact Finset.sum_congr rfl fun τ _ => by rw [prodProjMat_congr_left Λ h τ]

/-- **Every function of `Q_Λ u` is `Q_Λ`-invariant.**  In particular
`Q_Λ (log (Q_Λ u)) = log (Q_Λ u)`, which is the hypothesis of
`Ent_sub_Ent_act_of_invariant` and hence the reason the entropy drop of a
resampling kernel is a relative entropy.

This is strictly stronger than idempotence of `Q_Λ` — which only gives
`Q_Λ (Q_Λ u) = Q_Λ u` — and it is where "resampling" rather than merely
"projection" is used. -/
theorem act_prodProj_fix (Λ : Finset V) (F : ℝ → ℝ) (u : (V → S) → ℝ) :
    (prodProj hφ hc Λ).act (fun τ => F ((prodProj hφ hc Λ).act u τ))
      = fun σ => F ((prodProj hφ hc Λ).act u σ) := by
  funext σ
  have key : ∀ τ : V → S,
      prodProj hφ hc Λ σ τ * F ((prodProj hφ hc Λ).act u τ)
        = prodProj hφ hc Λ σ τ * F ((prodProj hφ hc Λ).act u σ) := by
    intro τ
    by_cases hz : prodProj hφ hc Λ σ τ = 0
    · rw [hz, zero_mul, zero_mul]
    · rw [act_prodProj_congr hφ hc Λ u fun v hv => agree_of_prodProj_ne_zero hφ hc Λ hz hv]
  rw [FinKernel.act_apply, Finset.sum_congr rfl fun τ _ => key τ, ← Finset.sum_mul,
    (prodProj hφ hc Λ).sum_coe σ, one_mul]

end Invariance

/-! ## The telescoping induction

Exactly the shape of `ip_sub_act_prodProj_le_sum` in `Chains/ProductMeasure.lean`:
the quantity `Ent_μ(f) − Ent_μ(Q_Λ f)` is `0` at `Λ = ∅` and `Ent_μ(f)` at
`Λ = univ`, adding a site `a` to `Λ` increases it by the local entropy of
`Q_Λ f` at `a`, and that is at most the local entropy of `f` at `a`.  The
statement is uniform in `Λ`, so `Finset.induction_on` closes it with no ordering
of the sites. -/

section Induction

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ} (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)

/-- **The entropy drop of a resampling kernel is a relative entropy**:

  `Ent_μ(f) − Ent_μ(Q_Λ f) = μ[f · (log f − log (Q_Λ f))]`.

`Ent_sub_Ent_act_of_invariant` with its hypothesis discharged by
`act_prodProj_fix`.  No positivity of `f` is needed for the identity itself. -/
theorem Ent_sub_Ent_act_prodProj (Λ : Finset V) (f : (V → S) → ℝ) :
    Ent (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) f
        - Ent (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
            ((prodProj hφ hc Λ).act f)
      = Ex (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
          (fun σ => f σ * (Real.log (f σ) - Real.log ((prodProj hφ hc Λ).act f σ))) :=
  Ent_sub_Ent_act_of_invariant (prodProj_reversible hφ hc Λ)
    (act_prodProj_fix hφ hc Λ Real.log f)

/-- **The error term of the induction is monotone**:

  `μ[Ent_a(Q_Λ f)] ≤ μ[Ent_a(f)]`.

The variance proof got this from the contraction property of `Q_Λ` in `L²(μ)`;
here it is the data-processing inequality for relative entropy.  Writing both
sides as divergences by `Ent_sub_Ent_act_prodProj`, the left-hand side is the
divergence of the pair `(Q_Λ f, Q_Λ (Q_a f))` — using that `Q_Λ` and `Q_a`
commute — and the right-hand side that of `(f, Q_a f)`, so
`Ex_mul_log_sub_log_act_le` applies verbatim.  This is the only inequality in the
whole argument. -/
theorem Ent_sub_Ent_act_prodProj_le (a : V) (Λ : Finset V) {f : (V → S) → ℝ}
    (hf : ∀ σ, 0 < f σ) :
    Ent (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
          ((prodProj hφ hc Λ).act f)
        - Ent (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
            ((prodProj hφ hc {a}).act ((prodProj hφ hc Λ).act f))
      ≤ Ent (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) f
        - Ent (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
            ((prodProj hφ hc {a}).act f) := by
  have hcomm : (prodProj hφ hc {a}).act ((prodProj hφ hc Λ).act f)
      = (prodProj hφ hc Λ).act ((prodProj hφ hc {a}).act f) :=
    (act_prodProj_comm hφ hc a Λ f).symm
  rw [Ent_sub_Ent_act_prodProj hφ hc {a} ((prodProj hφ hc Λ).act f),
    Ent_sub_Ent_act_prodProj hφ hc {a} f, hcomm]
  exact Ex_mul_log_sub_log_act_le (prodProj_stationary hφ hc Λ) hf
    (fun σ => act_pos (prodProj hφ hc {a}) hf σ)

/-- The local entropy of a product measure at a site, in terms of the resampling
kernel: `μ[Ent_v(f)] = Ent_μ(f) − Ent_μ(Q_v f)`.  The analogue of
`siteVar_prodWeight`, and it goes through the same `EqOnSupport` identification
`siteChain_eqOnSupport_prodProj`. -/
theorem siteEnt_prodWeight (v : V) (f : (V → S) → ℝ) :
    siteEnt (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) v f
      = Ent (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) f
        - Ent (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
            ((prodProj hφ hc {v}).act f) := by
  rw [siteEnt_apply, (siteChain_eqOnSupport_prodProj hφ hc v).localEnt_eq f,
    localEnt_eq_Ent_sub_Ent (prodProj_stationary hφ hc {v}) f]

/-- **The induction.**  For every set `Λ` of sites and every `f > 0`,

  `Ent_μ(f) − Ent_μ(Q_Λ f) ≤ ∑_{v ∈ Λ} μ[Ent_v(f)]`.

The base case `Λ = ∅` is `Q_∅ = id`.  For the step, the increment on adding a
site `a` is `Ent_μ(Q_Λ f) − Ent_μ(Q_a Q_Λ f)`, which is
`μ[Ent_a(Q_Λ f)]` by `siteEnt_prodWeight`, and `Ent_sub_Ent_act_prodProj_le`
bounds it by `μ[Ent_a(f)]`.  As in the variance proof, no ordering of the sites
appears. -/
theorem Ent_sub_Ent_act_prodProj_le_sum {f : (V → S) → ℝ} (hf : ∀ σ, 0 < f σ)
    (Λ : Finset V) :
    Ent (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc)) f
        - Ent (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
            ((prodProj hφ hc Λ).act f)
      ≤ ∑ v ∈ Λ, siteEnt (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) v f := by
  refine Finset.induction_on Λ ?_ ?_
  · rw [Finset.sum_empty, act_prodProj_empty hφ hc f]
    simp
  · intro a T ha ih
    have hstep : (prodProj hφ hc (insert a T)).act f
        = (prodProj hφ hc {a}).act ((prodProj hφ hc T).act f) := by
      rw [act_prodProj_comp hφ hc {a} T f, ← Finset.insert_eq]
    have h2 := Ent_sub_Ent_act_prodProj_le hφ hc a T hf
    have h3 := siteEnt_prodWeight hφ hc a f
    rw [Finset.sum_insert ha, hstep]
    linarith

end Induction

/-! ## The payoff

Tensorization of entropy with the optimal constant `C = 1`, and the modified
log-Sobolev inequality it produces. -/

section Payoff

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ} (hφ : ∀ v s, 0 ≤ φ v s) (hc : ∀ v, 0 < ∑ s, φ v s)

/-- **Tensorization of entropy for a product measure.**

  `Ent_μ(f) ≤ ∑_v μ[Ent_v(f)]`

for `μ` the Gibbs measure of a product weight and every `f > 0` — that is,
`ApproxTensorizationEnt` holds with the optimal constant `C = 1`.  This is
subadditivity of entropy (Han's inequality; the tensorization property of
relative entropy), and it is the entropy analogue of
`approxTensorization_prodWeight`.

Both sides are `1`-homogeneous in `f`, as they must be.

The proof is `Ent_sub_Ent_act_prodProj_le_sum` at `Λ = univ`, where `Q_univ f` is
the constant `μ(f)` and `Ent_μ` of a constant vanishes; so the left-hand side is
`Ent_μ(f)` on the nose. -/
theorem approxTensorizationEnt_prodWeight :
    ApproxTensorizationEnt (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc) 1 := by
  intro f hf
  have h := Ent_sub_Ent_act_prodProj_le_sum hφ hc hf univ
  rw [act_prodProj_univ hφ hc f, Ent_const] at h
  rw [one_mul]
  linarith

section Dynamics

variable [Nonempty V]

/-- **The Glauber dynamics of a product measure satisfies a modified log-Sobolev
inequality with constant `1/n`.**

For every strictly positive `f`,

  `(1/n) · Ent_μ(f) ≤ ℰ_{P_GD}(f, log f)`.

This is the entropy counterpart of `spectralGapAtLeast_glauber_prodWeight`, and —
as there — it is the exact answer: `n` steps are needed just to touch every site.

Two homogeneity checks, in the spirit of `naiveModLogSobolev_le_zero`.  `Ent` is
`1`-homogeneous (`Ent_smul`) and so is `entropyProduction`
(`entropyProduction_smul`), so the statement is scale-invariant and not vacuous;
and the tensorization inequality it comes from is `1`-homogeneous on both sides
as well.  Had we paired `Ent` with the quadratic form `ℰ(f, f)` — the
`NaiveModLogSobolev` of `Techniques/Entropy.lean` — the conclusion would have
been empty. -/
theorem modLogSobolev_glauber_prodWeight :
    ModLogSobolev (gibbs (prodWeight φ) (prodWeight_nonneg hφ) (Z_prodWeight_pos hc))
      (glauber (prodWeight φ) (prodWeight_nonneg hφ)) (1 / (Fintype.card V : ℝ)) := by
  have h := modLogSobolev_glauber_of_approxTensorizationEnt (C := 1) one_pos
    (approxTensorizationEnt_prodWeight hφ hc)
  rwa [one_mul] at h

end Dynamics

end Payoff

end Arlib.MarkovChains

