/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Glauber dynamics through the level machinery

`Chains.LevelEncoding` proves that the down-up walk at the top level of the
weighted complex induced by a spin system *is* the Glauber dynamics
(`spinDownUp_apply_graph`).  That identification is an equality of matrix
entries between two chains on two different state spaces, so on its own it
transfers nothing: `Techniques.Levels` proves `downUp_nonnegDefinite` about a
chain on `Finset (V × S)`, and the Gibbs sampler lives on `V → S`.

This module closes the gap, using `Techniques.Transport`.  The encoding is
`graph : (V → S) → Finset (V × S)`, which is injective (`graph_injective`), and
the top-level distribution of the induced complex is the Gibbs measure
(`spinTop_graph`) — provided the weight is normalised, which is where the one
piece of genuine bookkeeping lives:

**Normalisation.**  `Techniques.Levels` builds `pi w n k` only from a weight of
total mass `1`, whereas a spin system carries an unnormalised weight `w` with
partition function `Z w`.  So the complex must be built from `gibbsWeight w =
w / Z w`, not from `w`.  This costs nothing, because the Glauber dynamics is
scale-invariant (`glauber_gibbsWeight`): rescaling the weight rescales every
local partition function by the same factor and leaves every transition
probability unchanged.

The pay-off is threefold.

* `glauber_nonnegDefinite_via_levels` — positive semidefiniteness of the Gibbs
  sampler, for the **third** time in this development and by a third route:
  after self-adjoint idempotence (`Chains.Glauber`) and the mixture argument
  (`Chains.BlockDynamics`), now from the adjointness of the up and down
  operators.  Still no eigenvalue anywhere.
* `glauber_reversible_via_levels` — likewise for detailed balance.
* **`spectralGapAtLeast_glauber_iff`** — the point of the whole exercise: a
  Poincaré inequality for the down-up walk of the induced complex *is* a
  Poincaré inequality for the Gibbs sampler, with the same constant.  Any
  future local-to-global theorem proved in `Techniques.Levels` reaches the Gibbs
  sampler through this equivalence.

Main declarations:

* `gibbsWeight`, `glauber_gibbsWeight` — the normalised weight and the
  scale-invariance of the Glauber dynamics.
* `spinTop`, `spinPin`, `spinUp`, `spinTopDownUp` — the induced complex's top
  level, the level below, the up operator, and the down-up walk.
* `spinTop_graph` — **the top-level distribution is the Gibbs measure**.
* `transport_graph`, `encodes_spinTopDownUp` — the transport data.
* **`spectralGapAtLeast_glauber_iff`**, `glauber_nonnegDefinite_via_levels`,
  `glauber_reversible_via_levels`, `dirichlet_glauber_eq`,
  **`dirichlet_glauber_eq_norm_loss`**.

Everything here is proved from first principles with no `sorry`; in particular
no eigenvalue, and no spectral theorem, appears anywhere.
-/
import Arlib.MarkovChains.Chains.LevelEncoding
import Arlib.MarkovChains.Techniques.Transport

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## Normalising the weight

`Techniques.Levels` insists on a top-level weight of total mass `1`; a spin
system supplies an arbitrary nonnegative `w`.  The bridge is `gibbsWeight`, and
the reason the bridge is free is that the Glauber dynamics does not see the
scale of `w` at all. -/

section Normalisation

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S]

/-- The **normalised weight** `w / Z w`.  As a function it *is* the Gibbs
distribution; giving it a name lets it be fed to `Techniques.Levels`, which
wants a bare weight function rather than a `FinDist`. -/
noncomputable def gibbsWeight (w : (V → S) → ℝ) : (V → S) → ℝ := fun σ => w σ / Z w

theorem gibbsWeight_apply (w : (V → S) → ℝ) (σ : V → S) : gibbsWeight w σ = w σ / Z w := rfl

/-- The normalised weight is the Gibbs distribution, on the nose. -/
theorem gibbs_eq_gibbsWeight (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (σ : V → S) :
    gibbs w hw hZ σ = gibbsWeight w σ := rfl

theorem gibbsWeight_nonneg {w : (V → S) → ℝ} (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) (σ : V → S) :
    0 ≤ gibbsWeight w σ := div_nonneg (hw σ) hZ.le

/-- The normalised weight has total mass `1` — the hypothesis
`Techniques.Levels` requires of a top-level weight. -/
theorem gibbsWeight_sum {w : (V → S) → ℝ} (hZ : 0 < Z w) : ∑ σ, gibbsWeight w σ = 1 := by
  simp only [gibbsWeight]
  rw [← Finset.sum_div, ← Z_apply, div_self hZ.ne']

/-- Normalising rescales the local partition function by the same factor. -/
theorem Zloc_gibbsWeight (w : (V → S) → ℝ) (σ : V → S) (v : V) :
    Zloc (gibbsWeight w) σ v = Zloc w σ v / Z w := by
  simp only [Zloc_apply, gibbsWeight]
  rw [Finset.sum_div]

end Normalisation

section NormalisationChain

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]

/-- **The single-site heat-bath update is scale-invariant.**  Both the numerator
and the normaliser are homogeneous of degree one in the weight, so the
conditional distribution is unchanged. -/
theorem siteUpdate_gibbsWeight (w : (V → S) → ℝ) (hZ : 0 < Z w) (v : V) (σ τ : V → S) :
    siteUpdate (gibbsWeight w) v σ τ = siteUpdate w v σ τ := by
  have hZ' : Z w ≠ 0 := hZ.ne'
  have hZl : Zloc (gibbsWeight w) σ v = Zloc w σ v / Z w := Zloc_gibbsWeight w σ v
  by_cases h : Zloc w σ v = 0
  · rw [siteUpdate_of_Zloc_eq_zero (by rw [hZl, h, zero_div]), siteUpdate_of_Zloc_eq_zero h]
  · rw [siteUpdate_of_Zloc_ne_zero (by rw [hZl]; exact div_ne_zero h hZ'),
      siteUpdate_of_Zloc_ne_zero h, hZl]
    by_cases hA : AgreeOff v σ τ
    · rw [if_pos hA, if_pos hA]
      simp only [gibbsWeight]
      field_simp
    · rw [if_neg hA, if_neg hA]

/-- **The Glauber dynamics is scale-invariant**: it is the same chain for `w` and
for the normalised weight `w / Z w`.  This is what lets the level machinery,
which needs a normalised weight, speak about the Gibbs sampler of an arbitrary
spin system. -/
theorem glauber_gibbsWeight [Nonempty V] (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)
    (σ τ : V → S) :
    glauber (gibbsWeight w) (gibbsWeight_nonneg hw hZ) σ τ = glauber w hw σ τ := by
  simp only [glauber_apply, siteChain_apply]
  exact congrArg _ (Finset.sum_congr rfl fun v _ => siteUpdate_gibbsWeight w hZ v σ τ)

end NormalisationChain

/-! ## The induced complex, its top level, and its down-up walk -/

section Complex

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {m : ℕ}
variable (hm : Fintype.card V = m + 1)

/-- The **top-level distribution** of the complex induced by a spin system:
`π_{m+1}` for the normalised weight. -/
noncomputable def spinTop : FinDist (Finset (V × S)) :=
  pi (graphWeight (gibbsWeight w)) (m + 1) (m + 1)
    (graphWeight_nonneg (gibbsWeight_nonneg hw hZ))
    (graphWeight_supp' (gibbsWeight w) hm)
    (by rw [graphWeight_sum]; exact gibbsWeight_sum hZ) le_rfl

/-- The **level below the top**: `π_m`, the distribution on pinnings of all but
one site. -/
noncomputable def spinPin : FinDist (Finset (V × S)) :=
  pi (graphWeight (gibbsWeight w)) (m + 1) m
    (graphWeight_nonneg (gibbsWeight_nonneg hw hZ))
    (graphWeight_supp' (gibbsWeight w) hm)
    (by rw [graphWeight_sum]; exact gibbsWeight_sum hZ) (Nat.le_succ m)

/-- The **up operator** from the level of pinnings to the top level: fill in the
missing site with probability proportional to the resulting weight.  This is the
single-site heat-bath update seen from below. -/
noncomputable def spinUp : FinChain (Finset (V × S)) :=
  up (graphWeight (gibbsWeight w)) (m + 1) m
    (graphWeight_nonneg (gibbsWeight_nonneg hw hZ))
    (graphWeight_supp' (gibbsWeight w) hm) (Nat.lt_succ_self m)

/-- The **down-up walk at the top level** of the induced complex: erase a
uniformly random pair, then fill the missing site back in.  By
`Chains.LevelEncoding` this is the Glauber dynamics, `π`-almost everywhere. -/
noncomputable def spinTopDownUp : FinChain (Finset (V × S)) :=
  spinDownUp (gibbsWeight w) (gibbsWeight_nonneg hw hZ) hm

/-- The up and down operators of the induced complex are mutually adjoint —
`Techniques.Levels` in the form this module consumes it. -/
theorem spinUp_down_adjoint :
    Adjoint (spinPin w hw hZ hm) (spinTop w hw hZ hm) (spinUp w hw hZ hm) (down m) :=
  up_down_adjoint (graphWeight (gibbsWeight w)) (m + 1) m
    (graphWeight_nonneg (gibbsWeight_nonneg hw hZ))
    (graphWeight_supp' (gibbsWeight w) hm)
    (by rw [graphWeight_sum]; exact gibbsWeight_sum hZ) (Nat.lt_succ_self m)

/-- **The top-level distribution of the induced complex is the Gibbs measure.**

The two normalising constants both disappear: at the top level `mu` is the
weight itself (`mu_graphWeight_graph`), and `(m+1).choose (m+1) = 1`. -/
theorem spinTop_graph (σ : V → S) : spinTop w hw hZ hm (graph σ) = gibbs w hw hZ σ := by
  rw [spinTop, pi_apply, if_pos (by rw [graph_card, hm]), mu_graphWeight_graph,
    Nat.choose_self, Nat.cast_one, div_one]
  rfl

/-- **The transport data**: `graph` is injective and carries the Gibbs measure to
the top-level distribution of the induced complex. -/
theorem transport_graph :
    Transport (graph : (V → S) → Finset (V × S)) (gibbs w hw hZ) (spinTop w hw hZ hm) where
  inj := graph_injective
  dist_apply σ := spinTop_graph w hw hZ hm σ

/-- Positive semidefiniteness of the down-up walk, from adjointness of the up and
down operators — `Techniques.Levels`, unchanged. -/
theorem spinTopDownUp_nonnegDefinite :
    NonnegDefinite (spinTop w hw hZ hm) (spinTopDownUp w hw hZ hm) :=
  (spinUp_down_adjoint w hw hZ hm).comp_nonnegDefinite'

/-- Reversibility of the down-up walk with respect to the top-level
distribution. -/
theorem spinTopDownUp_reversible :
    Reversible (spinTop w hw hZ hm) (spinTopDownUp w hw hZ hm) :=
  (spinUp_down_adjoint w hw hZ hm).comp_reversible'

end Complex

/-! ## Transport along `graph`

The encoding is `graph`, which `Chains.LevelEncoding` already proved injective.
The two chains agree only on rows of positive weight, which is exactly the slack
`Techniques.Transport` allows in `Encodes`. -/

section Transport

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {S : Type*} [Fintype S] [DecidableEq S]
variable (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w) {m : ℕ}
variable (hm : Fintype.card V = m + 1)

/-- **The down-up walk encodes the Glauber dynamics along `graph`.**

This is `spinDownUp_apply_graph` of `Chains.LevelEncoding`, stated in the form
`Techniques.Transport` consumes: on every row the Gibbs measure charges, the two
chains have the same entries.  Rows of weight zero are excluded — there the two
constructions genuinely differ. -/
theorem encodes_spinTopDownUp :
    Encodes graph (gibbs w hw hZ) (spinTopDownUp w hw hZ hm) (glauber w hw) := by
  intro σ hσ τ
  have hwσ : 0 < w σ :=
    lt_of_le_of_ne (hw σ) (Ne.symm fun hc => hσ (gibbs_eq_zero hw hZ hc))
  have hw'σ : 0 < gibbsWeight w σ := div_pos hwσ hZ
  rw [spinTopDownUp,
    spinDownUp_apply_graph (gibbsWeight w) (gibbsWeight_nonneg hw hZ) hm hw'σ τ]
  exact glauber_gibbsWeight w hw hZ σ τ

/-! ## The transported conclusions -/

/-- **The Poincaré inequality transports.**

A spectral gap for the down-up walk of the induced complex *is* a spectral gap
for the Gibbs sampler, with the same constant and in both directions.  This is
the mechanism by which any future local-to-global theorem proved in
`Techniques.Levels` reaches the Glauber dynamics. -/
theorem spectralGapAtLeast_glauber_iff (γ : ℝ) :
    SpectralGapAtLeast (spinTop w hw hZ hm) (spinTopDownUp w hw hZ hm) γ
      ↔ SpectralGapAtLeast (gibbs w hw hZ) (glauber w hw) γ :=
  (transport_graph w hw hZ hm).spectralGapAtLeast_iff (encodes_spinTopDownUp w hw hZ hm) γ

/-- **The Dirichlet forms agree.**  A function on the top level of the complex
restricts along `graph` to a function on configurations, and the two Dirichlet
forms of the corresponding chains coincide. -/
theorem dirichlet_glauber_eq (F G : Finset (V × S) → ℝ) :
    dirichlet (spinTop w hw hZ hm) (spinTopDownUp w hw hZ hm) F G
      = dirichlet (gibbs w hw hZ) (glauber w hw) (F ∘ graph) (G ∘ graph) :=
  (transport_graph w hw hZ hm).dirichlet_eq (encodes_spinTopDownUp w hw hZ hm) F G

/-- **The Dirichlet form of the Gibbs sampler is a loss of `L²` norm under the up
operator.**

`ℰ_{P_GD}(F ∘ graph) = ⟪F, F⟫_{π_top} − ⟪U F, U F⟫_{π_pin}`.  This is the shape
in which the Dirichlet form enters the local-to-global induction of §5.1, now
available for the Glauber dynamics itself; compare `dirichlet_glauber` of
`Chains.GlauberTensorization`, which expresses the same quantity as an average of
conditional variances. -/
theorem dirichlet_glauber_eq_norm_loss (F : Finset (V × S) → ℝ) :
    dirichlet (gibbs w hw hZ) (glauber w hw) (F ∘ graph) (F ∘ graph)
      = ip (spinTop w hw hZ hm) F F
        - ip (spinPin w hw hZ hm) ((spinUp w hw hZ hm).act F) ((spinUp w hw hZ hm).act F) := by
  rw [← dirichlet_glauber_eq w hw hZ hm F F]
  exact (spinUp_down_adjoint w hw hZ hm).symm.dirichlet_comp F

end Transport

/-! ## The Gibbs sampler, seen from the level machinery

These are the conclusions in the form the rest of the development uses them:
statements about `glauber` alone, with the complex, its levels and its walks
appearing only inside the proofs.  The dimension hypothesis `hm` is carried
explicitly because the statements themselves do not mention it. -/

section Conclusions

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {S : Type*} [Fintype S] [DecidableEq S]
variable (w : (V → S) → ℝ) (hw : ∀ σ, 0 ≤ w σ) (hZ : 0 < Z w)

/-- **The Glauber dynamics is positive semidefinite — third proof.**

After self-adjoint idempotence of a single-site update (`Chains.Glauber`) and
the mixture argument (`Chains.BlockDynamics`), this derivation goes through the
adjointness of the up and down operators of the induced weighted complex and the
transport of `⟪f, P f⟫` along `graph`.  No eigenvalue is used in any of the
three. -/
theorem glauber_nonnegDefinite_via_levels {m : ℕ} (hm : Fintype.card V = m + 1) :
    NonnegDefinite (gibbs w hw hZ) (glauber w hw) :=
  ((transport_graph w hw hZ hm).nonnegDefinite_iff
    (encodes_spinTopDownUp w hw hZ hm)).mp (spinTopDownUp_nonnegDefinite w hw hZ hm)

/-- **The Glauber dynamics is reversible with respect to the Gibbs
distribution — second proof**, from the detailed balance of the down-up walk. -/
theorem glauber_reversible_via_levels {m : ℕ} (hm : Fintype.card V = m + 1) :
    Reversible (gibbs w hw hZ) (glauber w hw) :=
  ((transport_graph w hw hZ hm).reversible_iff
    (encodes_spinTopDownUp w hw hZ hm)).mp (spinTopDownUp_reversible w hw hZ hm)

/-- The Gibbs distribution is stationary for the Glauber dynamics, transported
from the level machinery. -/
theorem glauber_stationary_via_levels {m : ℕ} (hm : Fintype.card V = m + 1) :
    Stationary (gibbs w hw hZ) (glauber w hw) :=
  (glauber_reversible_via_levels w hw hZ hm).stationary

end Conclusions

end Arlib.MarkovChains
