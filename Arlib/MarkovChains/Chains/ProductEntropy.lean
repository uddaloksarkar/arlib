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

* `mul_log_sub_log_sum_le` — **the log-sum inequality**, in the weighted form.
  It is `mul_log_le_mul_log_add_sub` of `Techniques/Entropy.lean` evaluated at
  `t = a/b`, `m = (∑ p a)/(∑ p b)`; no new analytic input is needed.
  `Ex_mul_log_sub_log_act_le` is its kernel form: relative entropy of a pair of
  positive functions decreases along a stationary kernel.
* `localEnt μ P f` — the **mean conditional entropy** `μ[Ent_{P(σ,·)}(f)]`, the
  exact entropy analogue of `siteVar`, with `localEnt_eq_Ent_sub_Ent`
  (`= Ent_μ(f) − Ent_μ(P f)`), `localEnt_nonneg`, and `localEnt_smul` — the
  homogeneity audit, proved rather than asserted.
* **`localEnt_le_entropyProduction`** — for *any* reversible chain,
  `μ[Ent_P(f)] ≤ ℰ_P(f, log f)`.  This is what makes entropy tensorization
  produce a modified log-Sobolev inequality, and it is proved by the log-sum
  inequality applied to the pair `(P f, f)`, whose `μ`-means agree.
* `siteEnt`, `ApproxTensorizationEnt` — the spin-system instances, mirroring
  `siteVar` and `ApproxTensorization` of `Chains/GlauberTensorization.lean`.
* **`modLogSobolev_glauber_of_approxTensorizationEnt`** — `C`-approximate
  tensorization of entropy implies `ModLogSobolev` for the Glauber dynamics with
  constant `1/(Cn)`.  The entropy analogue of
  `spectralGapAtLeast_glauber_of_approxTensorization`.
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

/-! ## The log-sum inequality

The single analytic ingredient the variance proof did not need.  It is *not* a
new inequality: it is `mul_log_le_mul_log_add_sub` — the `t log m ≤ t log t + (m − t)`
of `Techniques/Entropy.lean` — evaluated at `t = a/b` and `m = (∑ p a)/(∑ p b)`
and summed against the weights `p b`.  Everything else in this module is
algebra on top of it.

The convention throughout is to write `log a − log b` rather than `log (a/b)`,
which keeps the `Real.log_div` side conditions in one place. -/

section LogSum

variable {Ω : Type*} [Fintype Ω]

/-- A strictly positive function has strictly positive average against a
probability weight vector.  (`Ex_pos_of_pos` in
`Techniques/EntropyVariational.lean` is the `FinDist` version; this one is
needed for the rows of a kernel as well.) -/
theorem sum_mul_pos {p a : Ω → ℝ} (hp : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1)
    (ha : ∀ y, 0 < a y) : 0 < ∑ y, p y * a y := by
  obtain ⟨y₀, -, hy₀⟩ : ∃ y ∈ univ, p y ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hp1]; exact one_ne_zero)
  have h0 : 0 < p y₀ * a y₀ := mul_pos (lt_of_le_of_ne (hp y₀) (Ne.symm hy₀)) (ha y₀)
  exact lt_of_lt_of_le h0
    (Finset.single_le_sum (f := fun y => p y * a y)
      (fun y _ => mul_nonneg (hp y) (ha y).le) (mem_univ y₀))

/-- **The log-sum inequality.**  For a probability weight vector `p` and
strictly positive `a`, `b`,

  `(∑ p a) · (log (∑ p a) − log (∑ p b)) ≤ ∑ p · a · (log a − log b)`.

Equivalently `A log (A/B) ≤ ∑ pᵢ aᵢ log (aᵢ/bᵢ)`: the relative entropy of the
aggregated pair is at most the aggregate of the pointwise relative entropies.
This is the convexity fact that entropy tensorization needs and variance
tensorization does not; taking `b ≡ 1` recovers `mul_log_sum_le_sum_mul_log`.

The proof is the pointwise bound `mul_log_le_mul_log_add_sub` at `t = aᵢ/bᵢ`,
`m = A/B`, multiplied by `pᵢ bᵢ ≥ 0`; the linear correction sums to
`(A/B)·B − A = 0`. -/
theorem mul_log_sub_log_sum_le {p a b : Ω → ℝ} (hp : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1)
    (ha : ∀ y, 0 < a y) (hb : ∀ y, 0 < b y) :
    (∑ y, p y * a y) * (Real.log (∑ y, p y * a y) - Real.log (∑ y, p y * b y))
      ≤ ∑ y, p y * (a y * (Real.log (a y) - Real.log (b y))) := by
  set A := ∑ y, p y * a y with hA
  set B := ∑ y, p y * b y with hB
  have hApos : 0 < A := sum_mul_pos hp hp1 ha
  have hBpos : 0 < B := sum_mul_pos hp hp1 hb
  have key : ∀ y : Ω, p y * a y * (Real.log A - Real.log B)
      ≤ p y * (a y * (Real.log (a y) - Real.log (b y)))
        + ((A / B) * (p y * b y) - p y * a y) := by
    intro y
    have h := mul_log_le_mul_log_add_sub (div_pos hApos hBpos)
      (div_nonneg (ha y).le (hb y).le)
    have h2 := mul_le_mul_of_nonneg_left h (mul_nonneg (hp y) (hb y).le)
    rw [Real.log_div hApos.ne' hBpos.ne', Real.log_div (ha y).ne' (hb y).ne'] at h2
    have hbne : b y ≠ 0 := (hb y).ne'
    have hcan : a y / b y * b y = a y := by field_simp
    have e0 : p y * b y * (a y / b y) = p y * a y := by
      calc p y * b y * (a y / b y) = p y * (a y / b y * b y) := by ring
        _ = p y * a y := by rw [hcan]
    have e1 : p y * b y * (a y / b y * (Real.log A - Real.log B))
        = p y * a y * (Real.log A - Real.log B) := by
      rw [show p y * b y * (a y / b y * (Real.log A - Real.log B))
        = p y * b y * (a y / b y) * (Real.log A - Real.log B) by ring, e0]
    have e2 : p y * b y * (a y / b y * (Real.log (a y) - Real.log (b y))
          + (A / B - a y / b y))
        = p y * a y * (Real.log (a y) - Real.log (b y))
          + ((A / B) * (p y * b y) - p y * a y) := by
      rw [show p y * b y * (a y / b y * (Real.log (a y) - Real.log (b y))
            + (A / B - a y / b y))
          = p y * b y * (a y / b y) * (Real.log (a y) - Real.log (b y))
            + ((A / B) * (p y * b y) - p y * b y * (a y / b y)) by ring, e0]
    rw [e1, e2] at h2
    linarith
  have hsum1 : ∑ y : Ω, p y * a y * (Real.log A - Real.log B)
      = A * (Real.log A - Real.log B) := by
    rw [← Finset.sum_mul, ← hA]
  have hAB : (A / B) * B = A := by field_simp
  have hsum2 : ∑ y : Ω, ((A / B) * (p y * b y) - p y * a y) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hA, ← hB, hAB, sub_self]
  calc A * (Real.log A - Real.log B)
      = ∑ y : Ω, p y * a y * (Real.log A - Real.log B) := hsum1.symm
    _ ≤ ∑ y : Ω, (p y * (a y * (Real.log (a y) - Real.log (b y)))
          + ((A / B) * (p y * b y) - p y * a y)) := Finset.sum_le_sum fun y _ => key y
    _ = ∑ y : Ω, p y * (a y * (Real.log (a y) - Real.log (b y))) := by
        rw [Finset.sum_add_distrib, hsum2, add_zero]

/-- The action of a kernel on a strictly positive function is strictly
positive. -/
theorem act_pos (P : FinChain Ω) {f : Ω → ℝ} (hf : ∀ y, 0 < f y) (x : Ω) : 0 < P.act f x :=
  sum_mul_pos (P.coe_nonneg x) (P.sum_coe x) hf

/-- **The log-sum inequality along a kernel row.**  For strictly positive `g`, `h`,

  `(P g)(x) · (log (P g)(x) − log (P h)(x)) ≤ (P (g · (log g − log h)))(x)`.

This is the pointwise data-processing inequality for relative entropy: averaging
a pair of positive functions over a row of `P` can only decrease their
divergence. -/
theorem mul_log_sub_log_act_le (P : FinChain Ω) {g h : Ω → ℝ} (hg : ∀ y, 0 < g y)
    (hh : ∀ y, 0 < h y) (x : Ω) :
    P.act g x * (Real.log (P.act g x) - Real.log (P.act h x))
      ≤ P.act (fun y => g y * (Real.log (g y) - Real.log (h y))) x :=
  mul_log_sub_log_sum_le (P.coe_nonneg x) (P.sum_coe x) hg hh

/-- **Data processing for the relative entropy of a pair of functions.**  If `μ`
is stationary for `P` then

  `μ[(P g) · (log (P g) − log (P h))] ≤ μ[g · (log g − log h)]`.

Both sides are `1`-homogeneous under the simultaneous scaling `(g, h) ↦ (cg, ch)`.
This is the inequality that replaces "`Q_Λ` is an `L²(μ)`-contraction" in the
entropy version of the tensorization argument, and the only inequality used in
the induction below. -/
theorem Ex_mul_log_sub_log_act_le {μ : FinDist Ω} {P : FinChain Ω} (hst : Stationary μ P)
    {g h : Ω → ℝ} (hg : ∀ y, 0 < g y) (hh : ∀ y, 0 < h y) :
    Ex μ (fun x => P.act g x * (Real.log (P.act g x) - Real.log (P.act h x)))
      ≤ Ex μ (fun y => g y * (Real.log (g y) - Real.log (h y))) :=
  le_trans (Ex_mono fun x => mul_log_sub_log_act_le P hg hh x)
    (le_of_eq (Ex_act_of_stationary hst _))

end LogSum

/-! ## The mean conditional entropy

`localEnt μ P f` is the entropy analogue of `siteVar`: draw `σ` from `μ`, take the
entropy of `f` with respect to the *row* `P(σ, ·)`, and average.  Where
`Chains/GlauberTensorization.lean` can define its mean conditional variance as a
Dirichlet form, we cannot — entropy is not a quadratic form — so the definition is
the average of row entropies, and `localEnt_eq_Ent_sub_Ent` shows it collapses to
the difference `Ent_μ(f) − Ent_μ(P f)` exactly as `siteVar` collapses to
`⟪f,f⟫ − ⟪Pf, Pf⟫`. -/

section LocalEntropy

variable {Ω : Type*} [Fintype Ω]

/-- The **mean conditional entropy** `μ[Ent_{P(σ,·)}(f)]`: the entropy of `f`
under the row distribution of `P` at `σ`, averaged over `σ ∼ μ`.

This is the exact analogue of `siteVar` in `Chains/GlauberTensorization.lean`,
and the normalisation is the same one: no division by anything, and the average
is against `μ` itself. -/
noncomputable def localEnt (μ : FinDist Ω) (P : FinChain Ω) (f : Ω → ℝ) : ℝ :=
  Ex μ (fun x => Ent (P.row x) f)

theorem localEnt_apply (μ : FinDist Ω) (P : FinChain Ω) (f : Ω → ℝ) :
    localEnt μ P f = Ex μ (fun x => Ent (P.row x) f) := rfl

/-- Averaging against a row of a kernel is the action of the kernel. -/
theorem Ex_row_eq_act (P : FinChain Ω) (f : Ω → ℝ) (x : Ω) : Ex (P.row x) f = P.act f x := rfl

/-- The mean conditional entropy is nonnegative, being an average of
entropies. -/
theorem localEnt_nonneg (μ : FinDist Ω) (P : FinChain Ω) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ localEnt μ P f :=
  Ex_nonneg fun x => Ent_nonneg (P.row x) hf

/-- **The mean conditional entropy is linearly homogeneous**,
`μ[Ent_P(c f)] = c · μ[Ent_P(f)]`, being an average of entropies (`Ent_smul`).

This is the homogeneity audit that `naiveModLogSobolev_le_zero` demands, carried
out on the right-hand side of the tensorization inequality: `Ent` is
`1`-homogeneous and so is `∑_v μ[Ent_v(·)]`, so the two sides of
`ApproxTensorizationEnt` scale together and the condition has content.  Contrast
`dirichlet_smul_self`, which is quadratic. -/
theorem localEnt_smul (μ : FinDist Ω) (P : FinChain Ω) {c : ℝ} (hc : 0 ≤ c) {f : Ω → ℝ}
    (hf : ∀ x, 0 ≤ f x) : localEnt μ P (fun x => c * f x) = c * localEnt μ P f := by
  rw [localEnt_apply, localEnt_apply, ← Ex_smul]
  refine Finset.sum_congr rfl fun x _ => ?_
  show μ x * Ent (P.row x) (fun y => c * f y) = μ x * (c * Ent (P.row x) f)
  rw [Ent_smul (P.row x) hc hf]

/-- **The mean conditional entropy collapses to an entropy difference**:

  `μ[Ent_P(f)] = Ent_μ(f) − Ent_μ(P f)`.

The `μ`-average of the row terms `P(f log f)` is `μ(f log f)` by stationarity,
and the two `μ(f) log μ(f)` terms of the right-hand side cancel for the same
reason.  Compare `siteVar_eq_ip_sub`. -/
theorem localEnt_eq_Ent_sub_Ent {μ : FinDist Ω} {P : FinChain Ω} (hst : Stationary μ P)
    (f : Ω → ℝ) : localEnt μ P f = Ent μ f - Ent μ (P.act f) := by
  have hrow : (fun x => Ent (P.row x) f)
      = fun x => P.act (fun y => f y * Real.log (f y)) x
          - P.act f x * Real.log (P.act f x) := by
    funext x
    rw [Ent_apply, Ex_row_eq_act, Ex_row_eq_act]
  rw [localEnt_apply, hrow, Ex_sub, Ex_act_of_stationary hst]
  simp only [Ent_apply]
  rw [Ex_act_of_stationary hst f]
  ring

/-- **The mean conditional entropy is at most the entropy production**:

  `μ[Ent_P(f)] ≤ ℰ_P(f, log f)`

for every reversible chain and every strictly positive `f`.  Both sides are
`1`-homogeneous in `f`.

This is the local half of a modified log-Sobolev inequality, and it is where the
log-sum inequality earns its keep.  Self-adjointness turns
`ℰ_P(f, log f) − μ[Ent_P(f)]` into `μ[(P f) · (log (P f) − log f)]`, which is the
relative entropy of the pair `(P f, f)`; stationarity says the two have the same
`μ`-mean, so the log-sum inequality bounds it below by `μ(f) · log 1 = 0`.

Note what is *not* needed: no idempotence, no product structure, no
positive-semidefiniteness — only detailed balance. -/
theorem localEnt_le_entropyProduction {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P)
    {f : Ω → ℝ} (hf : ∀ x, 0 < f x) : localEnt μ P f ≤ entropyProduction μ P f := by
  have hst := hrev.stationary
  have hPf : ∀ x, 0 < P.act f x := fun x => act_pos P hf x
  -- The entropy production, with the second argument moved across by self-adjointness.
  have hEP : entropyProduction μ P f
      = Ex μ (fun x => f x * Real.log (f x))
        - Ex μ (fun x => P.act f x * Real.log (f x)) := by
    rw [entropyProduction_apply, dirichlet_apply, ip_eq_Ex_mul,
      ip_act_comm hrev f (fun x => Real.log (f x))]
    congr 1
    exact Finset.sum_congr rfl fun x _ => by ring
  -- The mean conditional entropy, unfolded the same way.
  have hloc : localEnt μ P f
      = Ex μ (fun x => f x * Real.log (f x))
        - Ex μ (fun x => P.act f x * Real.log (P.act f x)) := by
    rw [localEnt_eq_Ent_sub_Ent hst f]
    simp only [Ent_apply]
    rw [Ex_act_of_stationary hst f]
    ring
  -- The difference is a relative entropy between two functions of equal mean.
  have hkey : 0 ≤ Ex μ (fun x => P.act f x * (Real.log (P.act f x) - Real.log (f x))) := by
    have h := mul_log_sub_log_sum_le (p := fun x => μ x) (a := P.act f) (b := f)
      μ.coe_nonneg μ.sum_coe hPf hf
    have hmean : ∑ x, μ x * P.act f x = ∑ x, μ x * f x := Ex_act_of_stationary hst f
    rw [hmean, sub_self, mul_zero] at h
    exact h
  have hsplit : Ex μ (fun x => P.act f x * (Real.log (P.act f x) - Real.log (f x)))
      = Ex μ (fun x => P.act f x * Real.log (P.act f x))
        - Ex μ (fun x => P.act f x * Real.log (f x)) := by
    simp only [Ex_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  linarith

/-- **The relative-entropy form of the entropy drop.**  If `P` is reversible and
`log (P g)` is `P`-invariant then

  `Ent_μ(g) − Ent_μ(P g) = μ[g · (log g − log (P g))]`.

The invariance hypothesis is genuine and is not implied by idempotence: it says
`P g` is constant along the rows of `P`, which for a resampling kernel holds
because `P g` does not depend on the resampled coordinates at all
(`act_prodProj_fix`).  Given it, self-adjointness moves the weight from `P g` to
`g` in the term `μ[(P g) log (P g)]`, which is precisely what turns a difference
of entropies into a divergence, and hence what makes the data-processing
inequality applicable. -/
theorem Ent_sub_Ent_act_of_invariant {μ : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P)
    {g : Ω → ℝ}
    (hinv : P.act (fun x => Real.log (P.act g x)) = fun x => Real.log (P.act g x)) :
    Ent μ g - Ent μ (P.act g)
      = Ex μ (fun x => g x * (Real.log (g x) - Real.log (P.act g x))) := by
  have hmean : Ex μ (P.act g) = Ex μ g := Ex_act_of_stationary hrev.stationary g
  have h2 := ip_act_comm hrev g (fun x => Real.log (P.act g x))
  rw [hinv] at h2
  have hself : Ex μ (fun x => P.act g x * Real.log (P.act g x))
      = Ex μ (fun x => g x * Real.log (P.act g x)) := by
    calc Ex μ (fun x => P.act g x * Real.log (P.act g x))
        = ip μ (fun x => Real.log (P.act g x)) (P.act g) :=
          Finset.sum_congr rfl fun x _ => by ring
      _ = ip μ g (fun x => Real.log (P.act g x)) := h2.symm
      _ = Ex μ (fun x => g x * Real.log (P.act g x)) :=
          Finset.sum_congr rfl fun x _ => by ring
  have hRHS : Ex μ (fun x => g x * (Real.log (g x) - Real.log (P.act g x)))
      = Ex μ (fun x => g x * Real.log (g x))
        - Ex μ (fun x => g x * Real.log (P.act g x)) := by
    simp only [Ex_apply, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  simp only [Ent_apply]
  rw [hmean, hRHS, ← hself]
  ring

end LocalEntropy

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

/-! ## Entropy tensorization for a spin system, and the Glauber dynamics

The definitions mirror `Chains/GlauberTensorization.lean` one for one:
`siteEnt` is `siteVar` with `Ent` in place of `Var`, and `ApproxTensorizationEnt`
is `ApproxTensorization` with the same substitution.  The one theorem of this
section, `modLogSobolev_glauber_of_approxTensorizationEnt`, is the entropy
analogue of `spectralGapAtLeast_glauber_of_approxTensorization`; note that it
does *not* have a converse here, because `localEnt_le_entropyProduction` is an
inequality and not an identity. -/

section SiteEntropy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The **mean conditional entropy at a site** `μ[Ent_v(f)]`: resample the spin
at `v` from its conditional Gibbs law and take the entropy of `f` under that law,
averaged over the configuration off `v`.

The normalisation mirrors `siteVar` exactly, so the two are directly comparable:
`siteVar` is `ℰ_{P_v}(f, f) = ⟪f,f⟫ − ⟪P_v f, P_v f⟫`, and `siteEnt` is
`Ent_μ(f) − Ent_μ(P_v f)` (`siteEnt_eq_Ent_sub_Ent`). -/
noncomputable def siteEnt (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) : ℝ :=
  localEnt (gibbs w hw hZ) (siteChain w hw v) f

theorem siteEnt_apply (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) :
    siteEnt w hw hZ v f = localEnt (gibbs w hw hZ) (siteChain w hw v) f := rfl

/-- The mean conditional entropy at a site is nonnegative. -/
theorem siteEnt_nonneg (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) {f : (V → S) → ℝ} (hf : ∀ σ, 0 ≤ f σ) : 0 ≤ siteEnt w hw hZ v f :=
  localEnt_nonneg _ _ hf

/-- `μ[Ent_v(f)] = Ent_μ(f) − Ent_μ(P_v f)`, the analogue of
`siteVar_eq_ip_sub`. -/
theorem siteEnt_eq_Ent_sub_Ent (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) (f : (V → S) → ℝ) :
    siteEnt w hw hZ v f
      = Ent (gibbs w hw hZ) f - Ent (gibbs w hw hZ) ((siteChain w hw v).act f) :=
  localEnt_eq_Ent_sub_Ent (siteChain_stationary w hw hZ v) f

/-- The local entropy at a site is dominated by the local entropy production,
`μ[Ent_v(f)] ≤ ℰ_{P_v}(f, log f)`. -/
theorem siteEnt_le_entropyProduction (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (v : V) {f : (V → S) → ℝ} (hf : ∀ σ, 0 < f σ) :
    siteEnt w hw hZ v f ≤ entropyProduction (gibbs w hw hZ) (siteChain w hw v) f :=
  localEnt_le_entropyProduction (siteChain_reversible w hw hZ v) hf

section Glauber

variable [Nonempty V]

/-- The bilinear form of the Glauber dynamics is the average of those of the
single-site updates.  This is `ip_act_glauber` of `Chains/Glauber.lean` with the
two arguments allowed to differ, which is what the entropy production — a
Dirichlet form evaluated at `(f, log f)` — requires.  (It belongs in
`Chains/Glauber.lean`, replacing the quadratic version; it is proved here to
avoid a concurrent edit.) -/
theorem ip_act_glauber_two (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (f g : (V → S) → ℝ) :
    ip (gibbs w hw hZ) f ((glauber w hw).act g)
      = ∑ v, (1 / (Fintype.card V : ℝ)) * ip (gibbs w hw hZ) f ((siteChain w hw v).act g) := by
  have hact : ∀ σ : V → S, (glauber w hw).act g σ
      = ∑ v, (1 / (Fintype.card V : ℝ)) * (siteChain w hw v).act g σ := by
    intro σ
    simp only [FinKernel.act_apply, glauber_apply]
    have step : ∀ τ : V → S,
        (1 / (Fintype.card V : ℝ)) * (∑ v, siteChain w hw v σ τ) * g τ
          = ∑ v, (1 / (Fintype.card V : ℝ)) * (siteChain w hw v σ τ * g τ) := by
      intro τ
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun v _ => by ring
    rw [Finset.sum_congr rfl fun τ _ => step τ, Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => by rw [Finset.mul_sum]
  simp only [ip_apply]
  have step : ∀ σ : V → S, gibbs w hw hZ σ * f σ * ((glauber w hw).act g σ)
      = ∑ v, (1 / (Fintype.card V : ℝ)) *
          (gibbs w hw hZ σ * f σ * ((siteChain w hw v).act g σ)) := by
    intro σ
    rw [hact σ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [Finset.sum_congr rfl fun σ _ => step σ, Finset.sum_comm]
  exact Finset.sum_congr rfl fun v _ => by rw [← Finset.mul_sum]

/-- The Dirichlet form of the Glauber dynamics is the average of the single-site
Dirichlet forms, in both arguments:
`ℰ_{P_GD}(f, g) = (1/n) ∑_v ℰ_{P_v}(f, g)`. -/
theorem dirichlet_glauber_two (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (f g : (V → S) → ℝ) :
    dirichlet (gibbs w hw hZ) (glauber w hw) f g
      = (1 / (Fintype.card V : ℝ))
        * ∑ v, dirichlet (gibbs w hw hZ) (siteChain w hw v) f g := by
  have hc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have step : ∀ v : V,
      (1 / (Fintype.card V : ℝ)) * ip (gibbs w hw hZ) f ((siteChain w hw v).act g)
        = (1 / (Fintype.card V : ℝ)) * ip (gibbs w hw hZ) f g
          - (1 / (Fintype.card V : ℝ))
              * dirichlet (gibbs w hw hZ) (siteChain w hw v) f g := by
    intro v
    rw [dirichlet_apply]
    ring
  have hA : ∑ _v : V, (1 / (Fintype.card V : ℝ)) * ip (gibbs w hw hZ) f g
      = ip (gibbs w hw hZ) f g := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, mul_one_div,
      div_self hc, one_mul]
  rw [dirichlet_apply, ip_act_glauber_two w hw hZ f g,
    Finset.sum_congr rfl fun v _ => step v, Finset.sum_sub_distrib, hA, ← Finset.mul_sum]
  ring

/-- `∑_v ℰ_{P_v}(f, log f) = n · ℰ_{P_GD}(f, log f)`: the entropy production of
the Glauber dynamics is the average of the local entropy productions. -/
theorem sum_entropyProduction_siteChain (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (f : (V → S) → ℝ) :
    ∑ v, entropyProduction (gibbs w hw hZ) (siteChain w hw v) f
      = (Fintype.card V : ℝ) * entropyProduction (gibbs w hw hZ) (glauber w hw) f := by
  have hc : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp only [entropyProduction_apply]
  rw [dirichlet_glauber_two w hw hZ f (fun x => Real.log (f x)), ← mul_assoc, mul_one_div,
    div_self hc, one_mul]

/-- **The local entropies sum to at most `n` times the entropy production.**
This is the step that converts tensorization of entropy into a modified
log-Sobolev inequality; it is `siteEnt_le_entropyProduction` summed over the
sites. -/
theorem sum_siteEnt_le (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    {f : (V → S) → ℝ} (hf : ∀ σ, 0 < f σ) :
    ∑ v, siteEnt w hw hZ v f
      ≤ (Fintype.card V : ℝ) * entropyProduction (gibbs w hw hZ) (glauber w hw) f := by
  rw [← sum_entropyProduction_siteChain w hw hZ f]
  exact Finset.sum_le_sum fun v _ => siteEnt_le_entropyProduction w hw hZ v hf

end Glauber

/-- **`C`-approximate tensorization of entropy**: for every strictly positive `f`,

  `Ent_μ(f) ≤ C ∑_v μ[Ent_v(f)]`.

The exact analogue of `ApproxTensorization`, with `Ent` in place of `Var`.  Both
sides are `1`-homogeneous in `f`, so — unlike an inequality pairing `Ent` with a
quadratic Dirichlet form (`naiveModLogSobolev_le_zero`) — the condition is not
vacuous.  As with the variance, `C ≥ 1` always, and `C = 1` is attained by a
product measure (`approxTensorizationEnt_prodWeight`).

The restriction to strictly positive `f` is the same one `ModLogSobolev` makes;
for `f` with zeros the statement remains true by continuity but the logarithms in
the proof do not. -/
def ApproxTensorizationEnt (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (C : ℝ) : Prop :=
  ∀ f : (V → S) → ℝ, (∀ σ, 0 < f σ) →
    Ent (gibbs w hw hZ) f ≤ C * ∑ v, siteEnt w hw hZ v f

/-- **Approximate tensorization of entropy implies a modified log-Sobolev
inequality.**  If the Gibbs distribution satisfies `C`-approximate tensorization
of entropy with `C > 0`, then the Glauber dynamics satisfies `ModLogSobolev` with
constant `1/(Cn)`.

This is the entropy analogue of
`spectralGapAtLeast_glauber_of_approxTensorization`, and the reason the
tensorization statement is worth proving.  Note the right-hand side is the
entropy production `ℰ(f, log f)`, not the Dirichlet form `ℰ(f, f)`: with the
latter the conclusion would be vacuous by `naiveModLogSobolev_le_zero`.

Unlike the variance case there is no converse: `localEnt_le_entropyProduction` is
an inequality, so a modified log-Sobolev inequality does not obviously return
tensorization. -/
theorem modLogSobolev_glauber_of_approxTensorizationEnt [Nonempty V] {w : (V → S) → ℝ}
    {hw : ∀ σ, 0 ≤ w σ} {hZ : 0 < Z w} {C : ℝ} (hC : 0 < C)
    (hAT : ApproxTensorizationEnt w hw hZ C) :
    ModLogSobolev (gibbs w hw hZ) (glauber w hw) (1 / (C * (Fintype.card V : ℝ))) := by
  have hn : (0 : ℝ) < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  intro f hf
  have h3 : Ent (gibbs w hw hZ) f
      ≤ C * ((Fintype.card V : ℝ) * entropyProduction (gibbs w hw hZ) (glauber w hw) f) :=
    le_trans (hAT f hf) (mul_le_mul_of_nonneg_left (sum_siteEnt_le w hw hZ hf) hC.le)
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  linarith

end SiteEntropy

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

