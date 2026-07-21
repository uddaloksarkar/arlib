/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Links of faces, and the local walk

The local-to-global technique (§5.1 of the monograph) is an induction on the
levels of a weighted complex in which the inductive step is applied not to the
complex itself but to the *link* of a face: the complex obtained by conditioning
on containing a fixed face `τ`.  This module makes that step available.

The point of the module is a triviality that is worth stating precisely, because
it is what removes all the work: the link of `τ` is *again a weighted complex on
the same ground set and of the same dimension*, with top-level weight
`linkWeight w τ = fun σ => if τ ⊆ σ then w σ else 0`.  This is exactly what
`Chains.Pinning` found for conditional Gibbs measures — **conditioning does not
leave the category** — so no new theory is needed and every result of
`Techniques.Levels` applies to the link verbatim.  The only bookkeeping is a
normalisation: `linkWeight w τ` sums to `mu w τ` rather than to `1`, so the
distributions of the link are built from the normalised weight
`linkWeightNorm w τ = linkWeight w τ / mu w τ`.  The operators `up`, `down`,
`upDown`, `downUp` need no normalisation at all, since `Levels` never asks them
for `hsum`.

The workhorse is `mu_linkWeight`: the derived weights of the link are the
derived weights of the original complex, shifted by `τ`.  Together with
`linkWeight_union` — links compose — it is what lets the local-to-global
induction descend one level at a time.

* `linkWeight`, `linkWeight_nonneg`, `linkWeight_supp`, `linkWeight_empty`,
  `linkWeight_top`, `sum_linkWeight` — the link weight and its elementary
  properties.  `sum_linkWeight` is the partition function of the link:
  `∑ σ, linkWeight w τ σ = mu w τ`.
* `mu_linkWeight` — **the workhorse**: `mu (linkWeight w τ) ρ = mu w (τ ∪ ρ)`.
  Both sides are `∑ σ, if τ ∪ ρ ⊆ σ then w σ else 0` by `Finset.union_subset_iff`.
* `linkWeight_union` — **links compose**:
  `linkWeight (linkWeight w τ) ρ = linkWeight w (τ ∪ ρ)`.
* `linkWeightNorm` and `linkWeightNorm_nonneg`, `linkWeightNorm_supp`,
  `sum_linkWeightNorm`, `mu_linkWeightNorm` — the normalised link weight
  satisfies *all three* hypotheses of `Levels`.
* `linkPi`, `linkUp`, `linkDown`, `linkUpDown`, `linkDownUp` — the level
  distributions and the four operators of the link, together with
  `link_up_down_adjoint`, `linkUpDown_reversible`, `linkUpDown_nonnegDefinite`,
  `linkDownUp_reversible`, `linkDownUp_nonnegDefinite`, … .  **This is the real
  deliverable**: the local-to-global inductive step is "apply `Levels` to the
  link", and each of these is one line.
* `linkDist` — the paper's `π_{τ,1}`, the distribution one level above `τ` on
  ground-set elements: mass `mu w (insert e τ) / ((n - k) · mu w τ)` at `e ∉ τ`.
  It is a distribution by `Levels.sum_insert_mu`, which exists for exactly this
  purpose.  The monograph only ever uses `j = 1`, so no general `π_{τ,j}` is
  built.
* `localWalk` — the local walk `Q_τ` on ground-set elements, which from `e`
  jumps to `e' ∉ τ ∪ {e}` with probability proportional to
  `mu w (τ ∪ {e, e'})`, with `linkDist_mul_localWalk` and
  **`localWalk_reversible`**, `localWalk_stationary`.

**Two deliberate choices.**  First, `localWalk` is defined directly rather than
as a walk of the link complex.  The tempting route — "`Q_τ` is `downUp` of the
link at the bottom level" — is not available: `downUp _ n 0` first steps
deterministically down to `∅` and then goes up, so it is the *independent
sampler* for the level-`1` distribution and does not depend on its current
state, whereas `Q_τ` does.  The walk that is genuinely built from the operators
is `upDown` at level `1`, and the monograph's own computation (`rem:local-downup`)
shows that this is `(Q_τ + I)/(k+1)`-shaped, not `Q_τ`.  Second, `Q_τ` is *not*
asserted to be positive semidefinite, and indeed it is not: it is the
non-backtracking walk, and the monograph records `-1/(n-k-1)` in its spectrum.
Positive semidefiniteness in this development belongs to the up-down and down-up
walks, where `Techniques.Adjoint` supplies it for free.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.Levels

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {E : Type*} [DecidableEq E]

/-! ## The weight of a link

Conditioning a weighted complex on containing a face `τ` restricts the top-level
weight to the star of `τ`.  The result is a weight on the same ground set,
supported on the same level `n`; only the normalisation changes. -/

/-- The **link weight** of a face `τ`: the top-level weight `w` restricted to the
faces containing `τ`.  This is the top-level weight of the link complex, which
lives on the same ground set and has the same dimension as the original. -/
def linkWeight (w : Finset E → ℝ) (τ : Finset E) : Finset E → ℝ :=
  fun σ => if τ ⊆ σ then w σ else 0

/-- The defining formula for `linkWeight`. -/
theorem linkWeight_apply (w : Finset E → ℝ) (τ σ : Finset E) :
    linkWeight w τ σ = if τ ⊆ σ then w σ else 0 := rfl

/-- The link weight is nonnegative: hypothesis `hw` of `Levels` survives. -/
theorem linkWeight_nonneg {w : Finset E → ℝ} (hw : ∀ σ : Finset E, 0 ≤ w σ) (τ : Finset E) :
    ∀ σ : Finset E, 0 ≤ linkWeight w τ σ := by
  intro σ
  rw [linkWeight_apply]
  split
  exacts [hw σ, le_rfl]

/-- The link weight is still supported on the top level: hypothesis `hsupp` of
`Levels` survives, with the *same* dimension `n`. -/
theorem linkWeight_supp {w : Finset E → ℝ} {n : ℕ}
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (τ : Finset E) :
    ∀ σ : Finset E, σ.card ≠ n → linkWeight w τ σ = 0 := by
  intro σ hσ
  rw [linkWeight_apply]
  split
  exacts [hsupp σ hσ, rfl]

/-- The link of the empty face is the complex itself. -/
theorem linkWeight_empty (w : Finset E → ℝ) : linkWeight w ∅ = w := by
  funext σ
  rw [linkWeight_apply, if_pos (Finset.empty_subset σ)]

/-- **Links compose**: the link of `ρ` inside the link of `τ` is the link of
`τ ∪ ρ`.  This is what lets the local-to-global induction descend one level at a
time without ever leaving the category of weighted complexes. -/
theorem linkWeight_union (w : Finset E → ℝ) (τ ρ : Finset E) :
    linkWeight (linkWeight w τ) ρ = linkWeight w (τ ∪ ρ) := by
  funext σ
  simp only [linkWeight_apply, Finset.union_subset_iff]
  by_cases hτ : τ ⊆ σ <;> by_cases hρ : ρ ⊆ σ <;> simp [hτ, hρ]

/-- The link of a *top-level* face is a point mass at that face: conditioning on
a full assignment leaves nothing to be random. -/
theorem linkWeight_top {w : Finset E → ℝ} {n : ℕ}
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) {τ : Finset E} (hτ : τ.card = n)
    (σ : Finset E) : linkWeight w τ σ = if σ = τ then w τ else 0 := by
  rw [linkWeight_apply]
  by_cases h : σ = τ
  · subst h
    rw [if_pos Finset.Subset.rfl, if_pos rfl]
  · rw [if_neg h]
    by_cases hsub : τ ⊆ σ
    · rw [if_pos hsub]
      refine hsupp σ fun hcard => h ?_
      exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
    · rw [if_neg hsub]

section Fintype

variable [Fintype E]

/-- **The derived weights of a link are the derived weights of the complex,
shifted by `τ`**: `mu (linkWeight w τ) ρ = mu w (τ ∪ ρ)`.

Both sides are `∑ σ, if τ ∪ ρ ⊆ σ then w σ else 0`, by `Finset.union_subset_iff`.
Every quantitative statement about the link is obtained from this one identity. -/
theorem mu_linkWeight (w : Finset E → ℝ) (τ ρ : Finset E) :
    mu (linkWeight w τ) ρ = mu w (τ ∪ ρ) := by
  simp only [mu_apply, linkWeight_apply, Finset.union_subset_iff]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hτ : τ ⊆ σ <;> by_cases hρ : ρ ⊆ σ <;> simp [hτ, hρ]

/-- The partition function of the link is the derived weight of `τ`:
`∑ σ, linkWeight w τ σ = mu w τ`.  This is the only thing that stops
`linkWeight` from being a weight in the sense of `Levels`, and the reason for
`linkWeightNorm` below. -/
theorem sum_linkWeight (w : Finset E → ℝ) (τ : Finset E) :
    ∑ σ : Finset E, linkWeight w τ σ = mu w τ := rfl

/-! ## The normalised link weight

`Levels.pi` needs a weight of total mass `1`; dividing by `mu w τ` supplies it.
The operators `up`, `down`, `upDown`, `downUp` do not need the normalisation,
but it costs nothing to use the same weight throughout. -/

/-- The **normalised link weight**, `linkWeight w τ / mu w τ`.  This is the
top-level weight of the link as a *probability*-weighted complex: it satisfies
all three hypotheses `hw`, `hsupp`, `hsum` of `Techniques.Levels`. -/
noncomputable def linkWeightNorm (w : Finset E → ℝ) (τ : Finset E) : Finset E → ℝ :=
  fun σ => linkWeight w τ σ / mu w τ

/-- The defining formula for `linkWeightNorm`. -/
theorem linkWeightNorm_apply (w : Finset E → ℝ) (τ σ : Finset E) :
    linkWeightNorm w τ σ = linkWeight w τ σ / mu w τ := rfl

/-- Hypothesis `hw` for the link. -/
theorem linkWeightNorm_nonneg {w : Finset E → ℝ} (hw : ∀ σ : Finset E, 0 ≤ w σ) (τ : Finset E) :
    ∀ σ : Finset E, 0 ≤ linkWeightNorm w τ σ :=
  fun σ => div_nonneg (linkWeight_nonneg hw τ σ) (mu_nonneg hw τ)

/-- Hypothesis `hsupp` for the link: the link has the same dimension `n`. -/
theorem linkWeightNorm_supp {w : Finset E → ℝ} {n : ℕ}
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0) (τ : Finset E) :
    ∀ σ : Finset E, σ.card ≠ n → linkWeightNorm w τ σ = 0 := by
  intro σ hσ
  rw [linkWeightNorm_apply, linkWeight_supp hsupp τ σ hσ, zero_div]

/-- Hypothesis `hsum` for the link: the normalised link weight is a probability
weight, provided `τ` is not a null face. -/
theorem sum_linkWeightNorm (w : Finset E → ℝ) (τ : Finset E) (hpos : 0 < mu w τ) :
    ∑ σ : Finset E, linkWeightNorm w τ σ = 1 := by
  have h : ∀ σ : Finset E, linkWeightNorm w τ σ = linkWeight w τ σ / mu w τ :=
    fun σ => rfl
  rw [Finset.sum_congr rfl fun σ _ => h σ, ← Finset.sum_div, sum_linkWeight,
    div_self hpos.ne']

/-- `mu_linkWeight` in normalised form: `mu (linkWeightNorm w τ) ρ` is the
conditional derived weight `mu w (τ ∪ ρ) / mu w τ`. -/
theorem mu_linkWeightNorm (w : Finset E → ℝ) (τ ρ : Finset E) :
    mu (linkWeightNorm w τ) ρ = mu w (τ ∪ ρ) / mu w τ := by
  have hstep : ∀ σ : Finset E,
      (if ρ ⊆ σ then linkWeightNorm w τ σ else 0)
        = (if ρ ⊆ σ then linkWeight w τ σ else 0) / mu w τ := by
    intro σ
    rw [linkWeightNorm_apply]
    split
    · rfl
    · rw [zero_div]
  rw [mu_apply, Finset.sum_congr rfl fun σ _ => hstep σ, ← Finset.sum_div,
    show (∑ σ : Finset E, if ρ ⊆ σ then linkWeight w τ σ else 0) = mu w (τ ∪ ρ) from
      mu_linkWeight w τ ρ]

/-! ## The link is a weighted complex

Every definition of `Techniques.Levels` instantiates at the link with no work at
all.  The definitions below are named purely for readability downstream: each is
the corresponding `Levels` notion applied to `linkWeightNorm w τ`, and each
theorem is the corresponding `Levels` theorem, verbatim. -/

/-- The **level-`k` distribution of the link of `τ`**: `Levels.pi` applied to the
normalised link weight. -/
noncomputable def linkPi (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k ≤ n) : FinDist (Finset E) :=
  pi (linkWeightNorm w τ) n k (linkWeightNorm_nonneg hw τ) (linkWeightNorm_supp hsupp τ)
    (sum_linkWeightNorm w τ hpos) hk

/-- The level distributions of the link in closed form: mass
`mu w (τ ∪ ρ) / (mu w τ · binom n k)` on the faces of cardinality `k`. -/
theorem linkPi_apply (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k ≤ n) (ρ : Finset E) :
    linkPi w n k τ hw hsupp hpos hk ρ =
      if ρ.card = k then mu w (τ ∪ ρ) / (mu w τ * (n.choose k : ℝ)) else 0 := by
  rw [linkPi, pi_apply]
  split
  · rw [mu_linkWeightNorm, div_div]
  · rfl

/-- The **up operator of the link**. -/
noncomputable def linkUp (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk : k < n) : FinChain (Finset E) :=
  up (linkWeightNorm w τ) n k (linkWeightNorm_nonneg hw τ) (linkWeightNorm_supp hsupp τ) hk

/-- The **down operator of the link**.  It is literally `Levels.down`: the down
operator deletes a uniformly random element and never looks at the weight, so
conditioning cannot change it. -/
noncomputable def linkDown (k : ℕ) : FinChain (Finset E) := down k

/-- The **up-down walk of the link** on level `k`. -/
noncomputable def linkUpDown (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk : k < n) : FinChain (Finset E) :=
  upDown (linkWeightNorm w τ) n k (linkWeightNorm_nonneg hw τ) (linkWeightNorm_supp hsupp τ) hk

/-- The **down-up walk of the link** on level `k + 1`. -/
noncomputable def linkDownUp (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk : k < n) : FinChain (Finset E) :=
  downUp (linkWeightNorm w τ) n k (linkWeightNorm_nonneg hw τ) (linkWeightNorm_supp hsupp τ) hk

/-- **The up and down operators of the link are mutually adjoint.**  This is
`Levels.up_down_adjoint` applied to the link, and it is the entire inductive step
of the local-to-global argument: everything below follows from it. -/
theorem link_up_down_adjoint (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    Adjoint (linkPi w n k τ hw hsupp hpos hk.le) (linkPi w n (k + 1) τ hw hsupp hpos hk)
      (linkUp w n k τ hw hsupp hk) (linkDown k) :=
  up_down_adjoint (linkWeightNorm w τ) n k (linkWeightNorm_nonneg hw τ)
    (linkWeightNorm_supp hsupp τ) (sum_linkWeightNorm w τ hpos) hk

/-- The up-down walk of the link is reversible with respect to the link's
level-`k` distribution. -/
theorem linkUpDown_reversible (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    Reversible (linkPi w n k τ hw hsupp hpos hk.le) (linkUpDown w n k τ hw hsupp hk) :=
  (link_up_down_adjoint w n k τ hw hsupp hpos hk).comp_reversible

/-- The link's level-`k` distribution is stationary for the link's up-down walk. -/
theorem linkUpDown_stationary (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    Stationary (linkPi w n k τ hw hsupp hpos hk.le) (linkUpDown w n k τ hw hsupp hk) :=
  (link_up_down_adjoint w n k τ hw hsupp hpos hk).comp_stationary

/-- **The up-down walk of the link is positive semidefinite**, for the same
structural reason as in the ambient complex and with no eigenvalue argument. -/
theorem linkUpDown_nonnegDefinite (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    NonnegDefinite (linkPi w n k τ hw hsupp hpos hk.le) (linkUpDown w n k τ hw hsupp hk) :=
  (link_up_down_adjoint w n k τ hw hsupp hpos hk).comp_nonnegDefinite

/-- The down-up walk of the link is reversible with respect to the link's
level-`(k+1)` distribution. -/
theorem linkDownUp_reversible (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    Reversible (linkPi w n (k + 1) τ hw hsupp hpos hk) (linkDownUp w n k τ hw hsupp hk) :=
  (link_up_down_adjoint w n k τ hw hsupp hpos hk).comp_reversible'

/-- The link's level-`(k+1)` distribution is stationary for the link's down-up
walk.  For `k + 1 = n` this is the Glauber dynamics of the conditioned system. -/
theorem linkDownUp_stationary (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    Stationary (linkPi w n (k + 1) τ hw hsupp hpos hk) (linkDownUp w n k τ hw hsupp hk) :=
  (link_up_down_adjoint w n k τ hw hsupp hpos hk).comp_reversible'.stationary

/-- **The down-up walk of the link is positive semidefinite.** -/
theorem linkDownUp_nonnegDefinite (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) :
    NonnegDefinite (linkPi w n (k + 1) τ hw hsupp hpos hk) (linkDownUp w n k τ hw hsupp hk) :=
  (link_up_down_adjoint w n k τ hw hsupp hpos hk).comp_nonnegDefinite'

/-- The Dirichlet form of the link's up-down walk, in the shape in which it
enters the local-to-global induction. -/
theorem linkUpDown_dirichlet (w : Finset E → ℝ) (n k : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : k < n) (f : Finset E → ℝ) :
    dirichlet (linkPi w n k τ hw hsupp hpos hk.le) (linkUpDown w n k τ hw hsupp hk) f f
      = ip (linkPi w n k τ hw hsupp hpos hk.le) f f
        - ip (linkPi w n (k + 1) τ hw hsupp hpos hk) ((linkDown k).act f) ((linkDown k).act f) :=
  (link_up_down_adjoint w n k τ hw hsupp hpos hk).dirichlet_comp f

/-! ## The distribution one level above a face

This is the monograph's `π_{τ,1}`, carried on ground-set *elements* rather than
on faces: from a face `τ` of cardinality `k < n`, the element `e ∉ τ` is drawn
with probability proportional to `mu w (insert e τ)`.  That this is a
distribution is exactly `Levels.sum_insert_mu`.  Only the case `j = 1` is ever
used in the monograph, and only that case is built here. -/

/-- The **one-level-up distribution** `π_{τ,1}` of a face `τ` of cardinality
`k < n`: mass `mu w (insert e τ) / ((n - k) · mu w τ)` at `e ∉ τ`, and `0` at
`e ∈ τ`.

The hypotheses are carried in the data, as they are for `Levels.up`, whose row
at `τ` this distribution is (transported along `e ↦ insert e τ`). -/
noncomputable def linkDist (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card < n) : FinDist E where
  p e := if e ∈ τ then 0 else mu w (insert e τ) / (((n - τ.card : ℕ) : ℝ) * mu w τ)
  p_nonneg e := by
    dsimp only
    split
    · exact le_rfl
    · exact div_nonneg (mu_nonneg hw _) (mul_nonneg (Nat.cast_nonneg _) (mu_nonneg hw τ))
  p_sum := by
    have hD : ((n - τ.card : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hm : mu w τ ≠ 0 := hpos.ne'
    have hstep : ∀ e : E,
        (if e ∈ τ then (0 : ℝ) else mu w (insert e τ) / (((n - τ.card : ℕ) : ℝ) * mu w τ))
          = (if e ∈ τᶜ then mu w (insert e τ) else 0)
              / (((n - τ.card : ℕ) : ℝ) * mu w τ) := by
      intro e
      by_cases h : e ∈ τ
      · rw [if_pos h, if_neg (Finset.not_mem_compl.mpr h), zero_div]
      · rw [if_neg h, if_pos (Finset.mem_compl.mpr h)]
    rw [Finset.sum_congr rfl fun e _ => hstep e, ← Finset.sum_div, Finset.sum_ite_mem,
      Finset.univ_inter, sum_insert_mu w n τ.card hsupp rfl, div_self (mul_ne_zero hD hm)]

/-- The defining formula for `linkDist`. -/
theorem linkDist_apply (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card < n) (e : E) :
    linkDist w n τ hw hsupp hpos hk e =
      if e ∈ τ then 0 else mu w (insert e τ) / (((n - τ.card : ℕ) : ℝ) * mu w τ) := rfl

/-- The one-level-up distribution ignores the elements of `τ` itself. -/
theorem linkDist_of_mem (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card < n) {e : E} (he : e ∈ τ) :
    linkDist w n τ hw hsupp hpos hk e = 0 := by
  rw [linkDist_apply, if_pos he]

/-- Off `τ`, the one-level-up distribution is proportional to `mu w (insert e τ)`. -/
theorem linkDist_of_not_mem (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card < n) {e : E} (he : e ∉ τ) :
    linkDist w n τ hw hsupp hpos hk e
      = mu w (insert e τ) / (((n - τ.card : ℕ) : ℝ) * mu w τ) := by
  rw [linkDist_apply, if_neg he]

/-! ## The local walk

The local walk `Q_τ` is the non-backtracking walk one level above `τ`: from
`e ∉ τ` it jumps to `e' ∉ τ ∪ {e}` with probability proportional to
`mu w (τ ∪ {e, e'})`.  Its guard structure mirrors `Levels.up` exactly: the two
degenerate branches (a null face, or an element of `τ`) hold in place, purely so
that the matrix is stochastic on all of `E`. -/

/-- The **local walk** `Q_τ` at a face `τ` with `τ.card + 1 < n`:

`Q_τ(e, e') = mu w (τ ∪ {e, e'}) / ((n - k - 1) · mu w (τ ∪ {e}))`

for `e ∉ τ` with `mu w (insert e τ) > 0` and `e' ∉ τ ∪ {e}`, and `0` for
`e' ∈ τ ∪ {e}` — in particular the diagonal vanishes, which is what
"non-backtracking" means.  The row sum is `Levels.sum_insert_mu` applied to the
face `insert e τ`, of cardinality `k + 1`. -/
noncomputable def localWalk (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk : τ.card + 1 < n) : FinChain E where
  P e e' :=
    if e ∉ τ ∧ 0 < mu w (insert e τ) then
      (if e' ∉ insert e τ then
        mu w (insert e' (insert e τ))
          / (((n - (τ.card + 1) : ℕ) : ℝ) * mu w (insert e τ))
      else 0)
    else (if e' = e then 1 else 0)
  P_nonneg e e' := by
    dsimp only
    split
    · split
      · exact div_nonneg (mu_nonneg hw _) (mul_nonneg (Nat.cast_nonneg _) (mu_nonneg hw _))
      · exact le_rfl
    · split
      · exact zero_le_one
      · exact le_rfl
  P_sum e := by
    by_cases h : e ∉ τ ∧ 0 < mu w (insert e τ)
    · simp only [if_pos h]
      have hcard : (insert e τ).card = τ.card + 1 := Finset.card_insert_of_not_mem h.1
      have hD : ((n - (τ.card + 1) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hm : mu w (insert e τ) ≠ 0 := h.2.ne'
      have hstep : ∀ e' : E,
          (if e' ∉ insert e τ then
              mu w (insert e' (insert e τ))
                / (((n - (τ.card + 1) : ℕ) : ℝ) * mu w (insert e τ))
            else 0)
            = (if e' ∈ (insert e τ)ᶜ then mu w (insert e' (insert e τ)) else 0)
                / (((n - (τ.card + 1) : ℕ) : ℝ) * mu w (insert e τ)) := by
        intro e'
        by_cases h' : e' ∈ insert e τ
        · rw [if_neg (not_not_intro h'), if_neg (Finset.not_mem_compl.mpr h'), zero_div]
        · rw [if_pos h', if_pos (Finset.mem_compl.mpr h')]
      rw [Finset.sum_congr rfl fun e' _ => hstep e', ← Finset.sum_div, Finset.sum_ite_mem,
        Finset.univ_inter, sum_insert_mu w n (τ.card + 1) hsupp hcard,
        div_self (mul_ne_zero hD hm)]
    · simp only [if_neg h]
      simp

/-- The defining formula for `localWalk`. -/
theorem localWalk_apply (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk : τ.card + 1 < n) (e e' : E) :
    localWalk w n τ hw hsupp hk e e' =
      if e ∉ τ ∧ 0 < mu w (insert e τ) then
        (if e' ∉ insert e τ then
          mu w (insert e' (insert e τ))
            / (((n - (τ.card + 1) : ℕ) : ℝ) * mu w (insert e τ))
        else 0)
      else (if e' = e then 1 else 0) := rfl

/-- **The detailed-balance cell of the local walk.**  For all `e, e'`,

`π_{τ,1}(e) · Q_τ(e, e') = mu w (τ ∪ {e, e'}) / ((n-k)(n-k-1) · mu w τ)`

when `e, e' ∉ τ` are distinct, and `0` otherwise.  Every degenerate branch
collapses: if `e ∈ τ` or `mu w (insert e τ) = 0` then `π_{τ,1}(e) = 0`; if
`e' ∈ insert e τ` — in particular on the diagonal — then `Q_τ(e, e') = 0`; and
if the guard is off because `mu w (insert e τ) = 0`, the numerator on the right
vanishes too, by `Levels.mu_eq_zero_of_subset`.

Reversibility is read off from this by swapping `e` and `e'`. -/
theorem linkDist_mul_localWalk (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card + 1 < n) (e e' : E) :
    linkDist w n τ hw hsupp hpos (Nat.lt_of_succ_lt hk) e * localWalk w n τ hw hsupp hk e e'
      = if e ∉ τ ∧ e' ∉ τ ∧ e ≠ e' then
          mu w (insert e' (insert e τ))
            / (((n - τ.card : ℕ) : ℝ) * ((n - (τ.card + 1) : ℕ) : ℝ) * mu w τ)
        else 0 := by
  have hD1 : ((n - τ.card : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hD2 : ((n - (τ.card + 1) : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hM : mu w τ ≠ 0 := hpos.ne'
  -- the two ways in which the left-hand side degenerates
  have hnull : ¬ (0 < mu w (insert e τ)) →
      linkDist w n τ hw hsupp hpos (Nat.lt_of_succ_lt hk) e = 0 := by
    intro hA
    have hA0 : mu w (insert e τ) = 0 := le_antisymm (not_lt.mp hA) (mu_nonneg hw _)
    rw [linkDist_apply]
    split
    · rfl
    · rw [hA0, zero_div]
  by_cases he : e ∈ τ
  · rw [linkDist_apply, if_pos he, zero_mul, if_neg fun h => h.1 he]
  · by_cases he' : e' ∈ τ
    · rw [if_neg fun h => h.2.1 he']
      by_cases hA : 0 < mu w (insert e τ)
      · have hz : localWalk w n τ hw hsupp hk e e' = 0 := by
          rw [localWalk_apply, if_pos ⟨he, hA⟩,
            if_neg (fun hc => hc (Finset.mem_insert_of_mem he'))]
        rw [hz, mul_zero]
      · rw [hnull hA, zero_mul]
    · by_cases hee : e = e'
      · subst hee
        rw [if_neg fun h => h.2.2 rfl]
        by_cases hA : 0 < mu w (insert e τ)
        · have hz : localWalk w n τ hw hsupp hk e e = 0 := by
            rw [localWalk_apply, if_pos ⟨he, hA⟩,
              if_neg (fun hc => hc (Finset.mem_insert_self e τ))]
          rw [hz, mul_zero]
        · rw [hnull hA, zero_mul]
      · rw [if_pos ⟨he, he', hee⟩]
        have hnm : e' ∉ insert e τ :=
          fun hc => (Finset.mem_insert.mp hc).elim (fun h => hee h.symm) he'
        by_cases hA : 0 < mu w (insert e τ)
        · have hA' : mu w (insert e τ) ≠ 0 := hA.ne'
          rw [linkDist_apply, if_neg he, localWalk_apply, if_pos ⟨he, hA⟩, if_pos hnm]
          field_simp
          ring
        · have hA0 : mu w (insert e τ) = 0 := le_antisymm (not_lt.mp hA) (mu_nonneg hw _)
          have hX : mu w (insert e' (insert e τ)) = 0 :=
            mu_eq_zero_of_subset hw (Finset.subset_insert e' (insert e τ)) hA0
          rw [hnull hA, zero_mul, hX, zero_div]

/-- **The local walk is reversible with respect to `π_{τ,1}`.**

The detailed-balance cell computed above is symmetric under `e ↔ e'`: the
denominator does not mention `e` or `e'` at all, and the numerator is symmetric
because `insert e' (insert e τ) = insert e (insert e' τ)`. -/
theorem localWalk_reversible (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card + 1 < n) :
    Reversible (linkDist w n τ hw hsupp hpos (Nat.lt_of_succ_lt hk))
      (localWalk w n τ hw hsupp hk) := by
  intro e e'
  rw [linkDist_mul_localWalk w n τ hw hsupp hpos hk e e',
    linkDist_mul_localWalk w n τ hw hsupp hpos hk e' e]
  by_cases h : e ∉ τ ∧ e' ∉ τ ∧ e ≠ e'
  · rw [if_pos h, if_pos ⟨h.2.1, h.1, h.2.2.symm⟩, Finset.insert_comm]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.2.1, h'.1, h'.2.2.symm⟩]

/-- `π_{τ,1}` is stationary for the local walk. -/
theorem localWalk_stationary (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hpos : 0 < mu w τ) (hk : τ.card + 1 < n) :
    Stationary (linkDist w n τ hw hsupp hpos (Nat.lt_of_succ_lt hk))
      (localWalk w n τ hw hsupp hk) :=
  (localWalk_reversible w n τ hw hsupp hpos hk).stationary

/-- The local walk is non-backtracking: it never stays where it is, unless the
row is one of the two degenerate ones. -/
theorem localWalk_diag (w : Finset E → ℝ) (n : ℕ) (τ : Finset E)
    (hw : ∀ σ : Finset E, 0 ≤ w σ) (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hk : τ.card + 1 < n) {e : E} (he : e ∉ τ) (hA : 0 < mu w (insert e τ)) :
    localWalk w n τ hw hsupp hk e e = 0 := by
  rw [localWalk_apply, if_pos ⟨he, hA⟩, if_neg (fun hc => hc (Finset.mem_insert_self e τ))]

/-- The link of the empty face changes nothing at the level of derived weights:
`linkWeight w ∅ = w`, so no conditioning has taken place.  Recorded here because
it is the base case of the local-to-global induction. -/
theorem mu_linkWeight_empty (w : Finset E → ℝ) (ρ : Finset E) :
    mu (linkWeight w ∅) ρ = mu w ρ := by
  rw [mu_linkWeight, Finset.empty_union]

end Fintype

end Arlib.MarkovChains
