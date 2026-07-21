/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Glauber dynamics (Gibbs sampler)

This is the chain the source monograph is about.  Everything in
`Arlib/MarkovChains/Techniques/` — Dirichlet forms, Poincaré inequalities,
positive semidefiniteness, variance decay — exists in order to say something
about it, so until it is defined the general theory has nothing to bite on.

The chain is the one of the monograph's §1.3.  From a configuration `σ` of a
spin system, pick a site `v` uniformly at random, keep the spins everywhere
else, and resample the spin at `v` from the conditional Gibbs distribution given
the rest of the configuration.  We build it in two stages: the *single-site
heat-bath update* `siteChain w hw v` at a fixed site, and then the Glauber
dynamics `glauber w hw` as the uniform average of these over `v`.

Two features of the construction deserve comment.

*The degenerate branch.*  The conditional distribution at `v` is only defined
when the local partition function `Zloc w σ v` is nonzero, so `siteUpdate` holds
still when it vanishes.  This is invisible to the theory: `w σ ≤ Zloc w σ v`
(`w_le_Zloc`), so `Zloc w σ v = 0` forces `w σ = 0` and hence
`gibbs w hw hZ σ = 0`.  It is a device for making the matrix row-stochastic on
the junk states, and nothing else.

*Why detailed balance holds.*  On the branch that matters both sides of
`μ(σ) P(σ, τ) = μ(τ) P(τ, σ)` equal `w(σ) w(τ) / (Z · Zloc)`, because the
normaliser `Zloc` depends only on the configuration off `v` and `σ`, `τ` agree
there (`Zloc_congr_of_agreeOff`).  The symmetry is then visible on the nose.

* `siteUpdate`, `siteChain` — the single-site heat-bath update at a site `v`,
  as a `FinChain (V → S)`.
* **`siteChain_reversible`** — the Gibbs distribution satisfies detailed balance
  for the single-site update.
* `siteUpdate_congr_left`, `sum_siteUpdate_mul`, `act_siteChain_idem` — the
  single-site update is an **idempotent**: `P ∘ P = P`, because after one update
  at `v` the state is already distributed as the conditional law at `v`.
* **`siteChain_nonnegDefinite`** — hence `⟪f, P f⟫ = ⟪P f, P f⟫ ≥ 0`.  This is
  the elementary route to positive semidefiniteness: a self-adjoint idempotent
  is PSD, no eigenvalue required.
* `glauber` — the **Glauber dynamics**, `FinKernel.avg (siteChain w hw)`.
* **`glauber_reversible`**, `glauber_stationary`, **`glauber_nonnegDefinite`** —
  detailed balance, stationarity and PSD-ness are all preserved by the average,
  and each is one application of the corresponding `avg_*` lemma of
  `Techniques/Mixture.lean`.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Chains.SpinSystem
import Arlib.MarkovChains.Techniques.Mixture

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## The single-site heat-bath update -/

/-- The **single-site heat-bath update** at the site `v`: from `σ`, keep the
spins off `v` and draw the spin at `v` from the conditional Gibbs distribution,
which assigns the configuration `τ` (agreeing with `σ` off `v`) probability
`w τ / Zloc w σ v`.

Where the local partition function vanishes there is no conditional
distribution to draw from, and the chain holds still; by `w_le_Zloc` this
happens only at configurations of weight `0`, which the Gibbs distribution does
not charge. -/
noncomputable def siteUpdate (w : (V → S) → ℝ) (v : V) (σ τ : V → S) : ℝ :=
  if Zloc w σ v = 0 then (if τ = σ then 1 else 0)
  else if AgreeOff v σ τ then w τ / Zloc w σ v else 0

/-- On the degenerate branch the update is the identity row. -/
theorem siteUpdate_of_Zloc_eq_zero {w : (V → S) → ℝ} {v : V} {σ : V → S}
    (h : Zloc w σ v = 0) (τ : V → S) :
    siteUpdate w v σ τ = if τ = σ then 1 else 0 := by
  rw [siteUpdate, if_pos h]

/-- On the branch that matters the update is the conditional Gibbs
distribution at `v`. -/
theorem siteUpdate_of_Zloc_ne_zero {w : (V → S) → ℝ} {v : V} {σ : V → S}
    (h : Zloc w σ v ≠ 0) (τ : V → S) :
    siteUpdate w v σ τ = if AgreeOff v σ τ then w τ / Zloc w σ v else 0 := by
  rw [siteUpdate, if_neg h]

theorem siteUpdate_nonneg {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (v : V) (σ τ : V → S) :
    0 ≤ siteUpdate w v σ τ := by
  rw [siteUpdate]
  split
  · split
    · exact zero_le_one
    · exact le_rfl
  · split
    · exact div_nonneg (hw τ) (Zloc_nonneg hw σ v)
    · exact le_rfl

/-- Each row of the single-site update is a probability distribution.  On the
main branch this is exactly the statement that `Zloc` normalises the
conditional law: the neighbours of `σ` at `v` are the updates `update σ v s`,
and their weights sum to `Zloc w σ v`. -/
theorem sum_siteUpdate (w : (V → S) → ℝ) (v : V) (σ : V → S) :
    ∑ τ, siteUpdate w v σ τ = 1 := by
  by_cases hz : Zloc w σ v = 0
  · simp [siteUpdate_of_Zloc_eq_zero hz]
  · simp only [siteUpdate_of_Zloc_ne_zero hz]
    rw [sum_ite_agreeOff v σ fun τ => w τ / Zloc w σ v, ← Finset.sum_div]
    exact div_self hz

/-- The **single-site heat-bath chain** at the site `v`. -/
noncomputable def siteChain (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (v : V) :
    FinChain (V → S) where
  P := siteUpdate w v
  P_nonneg := siteUpdate_nonneg hw v
  P_sum := sum_siteUpdate w v

@[simp] theorem siteChain_apply (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (v : V) (σ τ : V → S) :
    siteChain w hw v σ τ = siteUpdate w v σ τ := rfl

/-! ## Detailed balance -/

/-- **The single-site heat-bath update is reversible with respect to the Gibbs
distribution.**

On the branch where the local partition function is positive and `σ`, `τ` agree
off `v`, both sides of the detailed-balance identity equal
`w σ · w τ / (Z w · Zloc w σ v)`; the two denominators agree because `Zloc` only
depends on the configuration off `v` (`Zloc_congr_of_agreeOff`).  If `σ` and `τ`
do not agree off `v` both sides vanish, and if a local partition function
vanishes then so does the corresponding weight, hence the corresponding Gibbs
mass. -/
theorem siteChain_reversible (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (v : V) :
    Reversible (gibbs w hw hZ) (siteChain w hw v) := by
  intro σ τ
  rw [siteChain_apply, siteChain_apply]
  by_cases hzσ : Zloc w σ v = 0
  · have hσ : w σ = 0 := w_eq_zero_of_Zloc_eq_zero hw hzσ
    rw [gibbs_eq_zero hw hZ hσ, zero_mul]
    by_cases hzτ : Zloc w τ v = 0
    · rw [gibbs_eq_zero hw hZ (w_eq_zero_of_Zloc_eq_zero hw hzτ), zero_mul]
    · rw [siteUpdate_of_Zloc_ne_zero hzτ, hσ]
      simp
  · by_cases hzτ : Zloc w τ v = 0
    · have hτ : w τ = 0 := w_eq_zero_of_Zloc_eq_zero hw hzτ
      rw [gibbs_eq_zero hw hZ hτ, zero_mul, siteUpdate_of_Zloc_ne_zero hzσ, hτ]
      simp
    · rw [siteUpdate_of_Zloc_ne_zero hzσ, siteUpdate_of_Zloc_ne_zero hzτ]
      by_cases hA : AgreeOff v σ τ
      · rw [if_pos hA, if_pos hA.symm, Zloc_congr_of_agreeOff w hA, gibbs_apply, gibbs_apply]
        ring
      · rw [if_neg hA, if_neg fun k => hA k.symm]
        simp

/-- The Gibbs distribution is stationary for the single-site update. -/
theorem siteChain_stationary (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (v : V) :
    Stationary (gibbs w hw hZ) (siteChain w hw v) :=
  (siteChain_reversible w hw hZ v).stationary

/-! ## The single-site update is a projection

After a heat-bath update at `v` the spin at `v` is already distributed according
to the conditional law, so updating again changes nothing.  Formally: the rows
of `siteUpdate` at configurations agreeing off `v` are *identical*, whence
`P ∘ P = P`.  Combined with self-adjointness (reversibility) this gives positive
semidefiniteness in one line, with no eigenvalue anywhere. -/

/-- **Rows at configurations agreeing off `v` coincide.**  This is the reason
the single-site update is idempotent. -/
theorem siteUpdate_congr_left {w : (V → S) → ℝ} {v : V} {σ ρ : V → S}
    (h : AgreeOff v σ ρ) (hz : Zloc w σ v ≠ 0) (τ : V → S) :
    siteUpdate w v ρ τ = siteUpdate w v σ τ := by
  have hzr : Zloc w ρ v = Zloc w σ v := (Zloc_congr_of_agreeOff w h).symm
  rw [siteUpdate_of_Zloc_ne_zero (by rw [hzr]; exact hz), siteUpdate_of_Zloc_ne_zero hz, hzr]
  by_cases hA : AgreeOff v σ τ
  · rw [if_pos (h.symm.trans hA), if_pos hA]
  · rw [if_neg fun k => hA (h.trans k), if_neg hA]

/-- **The single-site update is idempotent**, entrywise. -/
theorem sum_siteUpdate_mul (w : (V → S) → ℝ) (v : V) (σ τ : V → S) :
    ∑ ρ, siteUpdate w v σ ρ * siteUpdate w v ρ τ = siteUpdate w v σ τ := by
  by_cases hz : Zloc w σ v = 0
  · simp only [siteUpdate_of_Zloc_eq_zero hz, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq' univ σ fun ρ => siteUpdate w v ρ τ, if_pos (mem_univ σ)]
    exact siteUpdate_of_Zloc_eq_zero hz τ
  · have key : ∀ ρ : V → S, siteUpdate w v σ ρ * siteUpdate w v ρ τ
        = siteUpdate w v σ ρ * siteUpdate w v σ τ := by
      intro ρ
      by_cases hA : AgreeOff v σ ρ
      · rw [siteUpdate_congr_left hA hz]
      · have h0 : siteUpdate w v σ ρ = 0 := by
          rw [siteUpdate_of_Zloc_ne_zero hz, if_neg hA]
        rw [h0, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl fun ρ _ => key ρ, ← Finset.sum_mul, sum_siteUpdate w v σ, one_mul]

/-- The action of the single-site update on functions is idempotent:
`P (P f) = P f`. -/
theorem act_siteChain_idem (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (v : V) (f : (V → S) → ℝ) :
    (siteChain w hw v).act ((siteChain w hw v).act f) = (siteChain w hw v).act f := by
  funext σ
  simp only [FinKernel.act_apply, siteChain_apply]
  calc ∑ ρ, siteUpdate w v σ ρ * ∑ τ, siteUpdate w v ρ τ * f τ
      = ∑ ρ, ∑ τ, siteUpdate w v σ ρ * siteUpdate w v ρ τ * f τ := by
        refine Finset.sum_congr rfl fun ρ _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun τ _ => by ring
    _ = ∑ τ, ∑ ρ, siteUpdate w v σ ρ * siteUpdate w v ρ τ * f τ := Finset.sum_comm
    _ = ∑ τ, siteUpdate w v σ τ * f τ := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [← Finset.sum_mul, sum_siteUpdate_mul w v σ τ]

/-- **The single-site heat-bath update is positive semidefinite.**

It is a self-adjoint idempotent in `L²(μ)`: reversibility gives
`⟪f, P (P f)⟫ = ⟪P f, P f⟫`, and idempotence rewrites the left-hand side as
`⟪f, P f⟫`.  So `⟪f, P f⟫ = ⟪P f, P f⟫ ≥ 0`.  No eigenvalue is used. -/
theorem siteChain_nonnegDefinite (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (v : V) :
    NonnegDefinite (gibbs w hw hZ) (siteChain w hw v) := by
  intro f
  have h := ip_act_comm (siteChain_reversible w hw hZ v) f ((siteChain w hw v).act f)
  rw [act_siteChain_idem w hw v f] at h
  rw [h]
  exact ip_self_nonneg _ _

/-! ## The Glauber dynamics

Pick a site uniformly at random and perform the heat-bath update there.  That is
literally `FinKernel.avg` of `Techniques/Mixture.lean` applied to the family of
single-site updates, so the definition is one line and reversibility,
stationarity and positive semidefiniteness are each inherited in one line
more. -/

section Glauber

variable [Nonempty V]

/-- The **Glauber dynamics** of a spin system: the uniform average over sites of
the single-site heat-bath updates.  This is the chain of the monograph's §1.3,
also known as the Gibbs sampler.

Built as `FinKernel.avg (siteChain w hw)`, which needs no hypotheses at all and
so carries none; every structural property below is then the corresponding
`avg_*` lemma applied to `siteChain`. -/
noncomputable def glauber (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) : FinChain (V → S) :=
  FinKernel.avg (siteChain w hw)

theorem glauber_apply (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (σ τ : V → S) :
    glauber w hw σ τ = (1 / (Fintype.card V : ℝ)) * ∑ v, siteChain w hw v σ τ := rfl

/-- **The Glauber dynamics is reversible with respect to the Gibbs
distribution.**  Detailed balance is a linear condition, so it survives the
average over sites; the content is `siteChain_reversible`. -/
theorem glauber_reversible (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) :
    Reversible (gibbs w hw hZ) (glauber w hw) :=
  avg_reversible fun v => siteChain_reversible w hw hZ v

/-- **The Gibbs distribution is stationary for the Glauber dynamics.** -/
theorem glauber_stationary (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) :
    Stationary (gibbs w hw hZ) (glauber w hw) :=
  (glauber_reversible w hw hZ).stationary

/-- The `L²(μ)` bilinear form of the Glauber dynamics is the average of those of
the single-site updates.

Stated for two arguments, not just for `(f, f)`: the entropy production is a
Dirichlet form evaluated at `(f, log f)`, so `Chains/ProductEntropy.lean` needs
the general shape.  The quadratic case is the specialisation `g = f`. -/
theorem ip_act_glauber (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
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

/-- **The Glauber dynamics is positive semidefinite.**

An average of positive semidefinite chains is positive semidefinite, and each
single-site heat-bath update is a self-adjoint idempotent
(`siteChain_nonnegDefinite`).  Together with a Poincaré inequality this is what
turns the spectral gap into the *absolute* spectral gap, and hence what makes
the gap control the decay of variance. -/
theorem glauber_nonnegDefinite (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) :
    NonnegDefinite (gibbs w hw hZ) (glauber w hw) :=
  avg_nonnegDefinite fun v => siteChain_nonnegDefinite w hw hZ v

end Glauber

end Arlib.MarkovChains
