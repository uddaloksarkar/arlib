/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The Improved Random Walk Theorem, and `lem:improved-technical`

The Random Walk Theorem of §6.4 rests on the comparison
`ℰ_{P^∧∨_k}(f) ≥ (k/(k+1))·γ_{k-1}·ℰ_{P^∨∧_k}(f)`, which loses a factor `k/(k+1)`
at every level and hence a factor `1/n` overall.  §6.6 of the source monograph
replaces it by a *lossless* comparison between two consecutive down-up energies,

  `ℰ_{P^∨∧_{k+1}}(f^{(k+2)}) ≥ (2γ_k - 1)·ℰ_{P^∨∧_k}(f^{(k+1)})`,

and this is the whole content of the improvement: the telescoping that follows it
gives `γ(P^∨∧_n) ≥ Γ_{n-1}/∑_i Γ_i` with `Γ_i = ∏_{j<i}(2γ_j - 1)`, in place of
the `(1/n)∏γ_j` of §6.4.  This module proves that comparison — the monograph's
`lem:improved-technical`, its `eqn:NEW-D` — and then the induction it powers,
`eqn:RW-one-improved`.

Everything except one inequality was already in place.  The two averaged
identities

  `𝔼_{τ ∼ π_k}[Var_{π_{τ,2}}(f_τ^{(2)})] = ℰ_{P^∨∧_{k+1}}(f^{(k+2)}) + ℰ_{P^∨∧_k}(f^{(k+1)})`
  `𝔼_{τ ∼ π_k}[Var_{π_{τ,1}}(f_τ^{(1)})] = ℰ_{P^∨∧_k}(f^{(k+1)})`

are `Techniques.FirstStep.Ex_Var_linkShiftPiOf_eq_levelEnergy_add` (=
`claim:first-step`) and `Techniques.FirstStep.Ex_pi_Var_linkShiftPiOf_one_eq_levelEnergy`
(= `claim:DDD`).  Subtracting, `eqn:NEW-D` is exactly the statement that the
first average dominates `2γ_k` times the second, and *that* is proved face by
face from a Poincaré inequality inside the link of `τ`.

**The per-face step, and why it needs no division.**  Inside the link of a face
`τ`, `LinkRestriction.Var_linkShiftPi_two_eq` (`lem:diff-var` at `i = 2, j = 1`)
says `Var_{π_{τ,2}}(g) = Var_{π_{τ,1}}(U^τ_1 g) + ℰ_{P^∨∧_{τ,1}}(g)`.  With
`ℰ_{P^∨∧_{τ,1}}(g) ≥ (γ/2)·Var_{π_{τ,2}}(g)` this gives
`Var_{π_{τ,1}}(U^τ_1 g) ≤ (1 - γ/2)·Var_{π_{τ,2}}(g)`, and then

  `2γ·Var_{π_{τ,1}} ≤ 2γ(1 - γ/2)·Var_{π_{τ,2}} = (2γ - γ²)·Var_{π_{τ,2}} ≤ Var_{π_{τ,2}}`,

the last step being `(γ - 1)² ≥ 0`.  The monograph instead divides by
`1 - γ_{k-1}/2` and so tacitly assumes `γ_{k-1} < 2`; the route above needs only
`0 ≤ γ`, and in particular is not vacuous at `γ = 2`.

**Where the gap hypothesis comes from, and where it stops.**  The monograph's
chain is `γ(Q_τ) ≥ γ_k` ⟹ `γ(P^∧∨_{τ,1}) ≥ γ_k/2` ⟹ `γ(P^∨∧_{τ,2}) ≥ γ_k/2`,
the first step because `P^∧∨_{τ,1} = (Q_τ + I)/2` and the second by
`lem:updown-downup` — which is `Techniques.UpDownDownUp`.  The second step is
supplied here; the first is *not* available in this development, because no
lemma yet identifies `Techniques.LocalWalk.localWalk` with the level-`1` up-down
walk of the honest link `LinkRestriction.linkShiftNorm`.  Accordingly the
headline below is stated with the up-down hypothesis `γ(P^∧∨_{τ,1}) ≥ γ/2`,
which is as close to `γ(Q_τ) ≥ γ` as can currently be written down, and the
down-up form is kept as the primitive.

**The side condition of `lem:updown-downup` propagates as `γ ≤ 2`.**  The
transfer `Adjoint.spectralGapAtLeast_comp_iff` needs its gap to be at most `1`,
and the gap being transferred here is `γ/2`; so the up-down form of the
hypothesis carries `γ ≤ 2`, which is strictly weaker than the `γ ≤ 1` that
holds for any genuine local walk.  The down-up form carries no side condition at
all.

**Main declarations.**

* `two_mul_Var_pi_succ_le` — the per-level inequality in an arbitrary weighted
  complex: `2γ·Var_{π_k}(U_k g) ≤ Var_{π_{k+1}}(g)` from
  `γ(P^∨∧_k) ≥ γ/2`.  This is `missing-step` of the monograph, stated where it
  belongs.
* `two_mul_Var_linkShiftPiOf_one_le` — the same inequality inside the link of a
  face, in the guarded-total language that the `π_k`-average requires.
* **`levelEnergy_ge_of_downUp_gap`** — `lem:improved-technical`
  (`eqn:NEW-D`) with the down-up form of the local hypothesis.
* **`levelEnergy_ge_of_upDown_gap`** — `lem:improved-technical` with the up-down
  form, the shape the monograph writes; `lem:updown-downup` is what connects the
  two, at the cost of the side condition `γ ≤ 2`.
* `improvedFactor` with `improvedFactor_zero`, `improvedFactor_succ`,
  `improvedFactor_nonneg`, `one_le_sum_improvedFactor` — the monograph's
  `Γ_i = ∏_{j<i}(2γ_j - 1)`.
* `improvedFactor_mul_levelVar_le` — `induct:simpler`, the induction over levels
  that `lem:improved-technical` powers.
* **`downUp_top_spectralGapAtLeast`** — the **Improved Random Walk Theorem**
  `eqn:RW-one-improved`: `γ(P^∨∧_{m+1}) ≥ Γ_m / ∑_{i≤m} Γ_i`.
* **`downUp_top_spectralGapAtLeast_of_upDown_gap`** — the same with the up-down
  form of the local hypothesis.

There is no `sorry` in this file, and no eigenvalue anywhere in its proofs.
-/
import Arlib.MarkovChains.Techniques.FirstStep
import Arlib.MarkovChains.Techniques.UpDownDownUp

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## Averaging on the support only

`Ex_mono` asks for a pointwise inequality everywhere.  Every guarded-total
construction in this development (`LocalWalk.linkDistOf`,
`LinkRestriction.linkShiftPiOf`, `LinkRestriction.linkLevelFun`) takes a junk
value off the support of the averaging distribution, and there the pointwise
inequality is simply false — at a face `τ` with `|τ| ≠ k` the level-`2` guard
fails while the level-`1` guard may not, so the left-hand side of the per-face
bound can be positive and the right-hand side zero.  Multiplying by the face
weight is what kills that branch, so every averaging step below is done with
`Functional.Ex_mono_of_ne_zero`, the mass-aware form, and not with `Ex_mono`. -/

variable {E : Type*} [Fintype E] [DecidableEq E]

/-! ## `missing-step`, in an arbitrary weighted complex

The monograph proves its per-face inequality inside the link of a face, but
nothing in the argument is about links: it is a statement about two consecutive
levels of *any* weighted complex, and the link is a weighted complex.  Proving it
there costs nothing and makes the instantiation a one-liner. -/

/-- **The one-level variance comparison** (`missing-step` of the monograph).  If
the down-up walk from level `k + 1` to level `k` has spectral gap at least
`γ / 2`, then for every `g` on level `k + 1`

  **`2γ · Var_{π_k}(U_k g) ≤ Var_{π_{k+1}}(g)`.**

`LevelVariance.Var_pi_succ_eq` splits `Var_{π_{k+1}}(g)` as
`Var_{π_k}(U_k g) + ℰ_{P^∨∧_k}(g)`; the hypothesis bounds the second summand
below by `(γ/2)·Var_{π_{k+1}}(g)`, so `Var_{π_k}(U_k g) ≤ (1 - γ/2)·Var_{π_{k+1}}(g)`,
and multiplying by `2γ ≥ 0` finishes because `2γ(1 - γ/2) = 1 - (γ-1)² ≤ 1`.

Only `0 ≤ γ` is needed.  The monograph reaches the same bound by dividing by
`1 - γ/2` and therefore needs `γ < 2`; the multiplicative route does not. -/
theorem two_mul_Var_pi_succ_le (v : Finset E → ℝ) (m k : ℕ)
    (hv : ∀ σ : Finset E, 0 ≤ v σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ m → v σ = 0)
    (hsum : ∑ σ : Finset E, v σ = 1) (hk : k < m) {γ : ℝ} (hγ : 0 ≤ γ)
    (hgap : SpectralGapAtLeast (pi v m (k + 1) hv hsupp hsum hk)
      (downUp v m k hv hsupp hk) (γ / 2)) (g : Finset E → ℝ) :
    2 * γ * Var (pi v m k hv hsupp hsum hk.le) ((up v m k hv hsupp hk).act g)
      ≤ Var (pi v m (k + 1) hv hsupp hsum hk) g := by
  set A := Var (pi v m k hv hsupp hsum hk.le) ((up v m k hv hsupp hk).act g) with hA
  set B := Var (pi v m (k + 1) hv hsupp hsum hk) g with hB
  have hsplit : B = A + dirichlet (pi v m (k + 1) hv hsupp hsum hk)
      (downUp v m k hv hsupp hk) g g := Var_pi_succ_eq v m k hv hsupp hsum hk g
  have hpoin := hgap g
  have hBnn : 0 ≤ B := Var_nonneg _ _
  -- `A ≤ (1 - γ/2)·B`
  have hupper : A ≤ (1 - γ / 2) * B := by
    rw [← hB] at hpoin
    linarith [hsplit, hpoin]
  have hstep : 2 * γ * A ≤ 2 * γ * ((1 - γ / 2) * B) :=
    mul_le_mul_of_nonneg_left hupper (by linarith)
  have hfin : 2 * γ * ((1 - γ / 2) * B) ≤ B := by
    nlinarith [mul_nonneg hBnn (sq_nonneg (γ - 1))]
  linarith

/-! ## The per-face inequality, in the guarded-total language

`FirstStep`'s two averaged identities are stated with the guarded-total
`linkShiftPiOf` and `linkLevelFun`, so the per-face bound must be too.  At a
face of positive derived weight with room for two more levels the guards are
invisible, and the statement is `two_mul_Var_pi_succ_le` inside the link. -/

/-- **The per-face inequality of `lem:improved-technical`.**  For a face `τ` of
size `k` and positive derived weight, with `k + 1 < n`, and given that the
level-`1` down-up walk *of the link of `τ`* has spectral gap at least `γ/2`,

  **`2γ · Var_{π_{τ,1}}(f_τ^{(1)}) ≤ Var_{π_{τ,2}}(f_τ^{(2)})`.**

This is the monograph's `missing-step`, and it is `two_mul_Var_pi_succ_le`
applied to the weighted complex `LinkRestriction.linkShiftNorm w τ` of dimension
`n - |τ|` at `k = 1`, together with the observation that the link projection
`f_τ^{(1)}` *is* `U^τ_1 f_τ^{(2)}` — which holds by definition of
`FirstStep.linkLevelFun` as a `levelFun` in the link, and `levelFun_succ`. -/
theorem two_mul_Var_linkShiftPiOf_one_le (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    {γ : ℝ} (hγ : 0 ≤ γ) (f : Finset E → ℝ) {τ : Finset E}
    (hcard : τ.card = k) (hpos : 0 < mu w τ) (hk2 : k + 1 < n)
    (hgap : SpectralGapAtLeast
      (linkShiftPi w n 2 τ hw hsupp (by omega) hpos (by omega))
      (downUp (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
        (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ / 2)) :
    2 * γ * Var (linkShiftPiOf w n 1 τ hw hsupp) (linkLevelFun w n 1 τ hw hsupp f)
      ≤ Var (linkShiftPiOf w n 2 τ hw hsupp) (linkLevelFun w n 2 τ hw hsupp f) := by
  have hτn : τ.card ≤ n := by omega
  have h1 : 1 < n - τ.card := by omega
  have h2 : 2 ≤ n - τ.card := by omega
  -- the link projection one level down is the up-action of the one two levels down
  have hproj : linkLevelFun w n 1 τ hw hsupp f
      = (up (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp hτn) h1).act (linkLevelFun w n 2 τ hw hsupp f) := by
    rw [linkLevelFun_apply w n 1 τ hw hsupp f hτn, linkLevelFun_apply w n 2 τ hw hsupp f hτn,
      levelFun_succ (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
        (linkShiftNorm_supp hsupp hτn) (fun σ => f (τ ∪ σ)) h1]
  rw [linkShiftPiOf_eq_linkShiftPi w n 1 τ hw hsupp hτn hpos (by omega),
    linkShiftPiOf_eq_linkShiftPi w n 2 τ hw hsupp hτn hpos h2, hproj]
  exact two_mul_Var_pi_succ_le (linkShiftNorm w τ) (n - τ.card) 1
    (linkShiftNorm_nonneg hw τ) (linkShiftNorm_supp hsupp hτn)
    (sum_linkShiftNorm w hpos) h1 hγ hgap (linkLevelFun w n 2 τ hw hsupp f)

/-! ## `lem:improved-technical`

The averaging step.  Both sides are `π_k`-averages of per-face quantities and
both are already identified with level energies in `Techniques.FirstStep`, so
all that is left is to feed the per-face bound to `Ex_mono_of_ne_zero` and
rearrange. -/

/-- **`lem:improved-technical` (`eqn:NEW-D`), down-up form.**  If for every face
`τ` of size `k` and positive derived weight the level-`1` down-up walk of the
link of `τ` has spectral gap at least `γ/2`, then for every `f` on the top level

  **`(2γ - 1)·ℰ_{P^∨∧_k}(f^{(k+1)}) ≤ ℰ_{P^∨∧_{k+1}}(f^{(k+2)})`.**

(The monograph indexes this as `ℰ_{P^∨∧_{k+1}}(f^{(k+1)}) ≥ (2γ_{k-1}-1)·ℰ_{P^∨∧_k}(f^{(k)})`;
here, as throughout `Techniques.LocalToGlobal`, `levelEnergy … k` is the down-up
energy *from* level `k+1`, and the faces averaged over have size `k`.)

Proof: `claim:first-step` and `claim:DDD` express the two averages
`𝔼_{π_k}[Var_{π_{τ,2}}(f_τ^{(2)})]` and `𝔼_{π_k}[Var_{π_{τ,1}}(f_τ^{(1)})]` as
`ℰ_{k+1} + ℰ_k` and `ℰ_k`; the per-face bound
`two_mul_Var_linkShiftPiOf_one_le` says the first dominates `2γ` times the
second, so `2γ·ℰ_k ≤ ℰ_{k+1} + ℰ_k`.

The averaging uses `Ex_mono_of_ne_zero`, not `Ex_mono`: a face of `π_k`-mass
zero need not satisfy the per-face bound, because the two guarded distributions
`linkShiftPiOf … 1 τ` and `linkShiftPiOf … 2 τ` can degenerate independently
there.  Only the face weight kills that branch. -/
theorem levelEnergy_ge_of_downUp_gap (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) {γ : ℝ} (hγ : 0 ≤ γ) (hk2 : k + 1 < n)
    (hgap : ∀ (τ : Finset E) (hcard : τ.card = k) (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w n 2 τ hw hsupp (by omega) hpos (by omega))
        (downUp (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ / 2))
    (f : Finset E → ℝ) :
    (2 * γ - 1) * levelEnergy w n hw hsupp hsum f k
      ≤ levelEnergy w n hw hsupp hsum f (k + 1) := by
  have hk1 : k < n := by omega
  -- the two averaged identities
  have hAdd := Ex_Var_linkShiftPiOf_eq_levelEnergy_add w n k hw hsupp hsum f hk2
  have hOne := Ex_pi_Var_linkShiftPiOf_one_eq_levelEnergy w n k hw hsupp hsum f hk1
  -- the averaged inequality
  have hmono : Ex (pi w n k hw hsupp hsum hk1.le)
        (fun τ => 2 * γ * Var (linkShiftPiOf w n 1 τ hw hsupp)
          (linkLevelFun w n 1 τ hw hsupp f))
      ≤ Ex (pi w n k hw hsupp hsum hk1.le)
        (fun τ => Var (linkShiftPiOf w n 2 τ hw hsupp)
          (linkLevelFun w n 2 τ hw hsupp f)) := by
    refine Ex_mono_of_ne_zero _ fun τ hz => ?_
    have hcard : τ.card = k := by
      by_contra hc
      exact hz (by rw [pi_apply, if_neg hc])
    have hmu : 0 < mu w τ := by
      rcases lt_or_eq_of_le (mu_nonneg hw τ) with h | h
      · exact h
      · exact absurd (by rw [pi_apply, if_pos hcard, ← h, zero_div]) hz
    exact two_mul_Var_linkShiftPiOf_one_le w n k hw hsupp hγ f hcard hmu hk2
      (hgap τ hcard hmu)
  rw [Ex_smul (pi w n k hw hsupp hsum hk1.le) (2 * γ)
    (fun τ => Var (linkShiftPiOf w n 1 τ hw hsupp) (linkLevelFun w n 1 τ hw hsupp f)),
    hOne, hAdd] at hmono
  linarith

/-- **`lem:improved-technical` (`eqn:NEW-D`), up-down form** — the shape the
monograph writes.  The local hypothesis is now that the level-`1` *up-down* walk
of the link of `τ` has spectral gap at least `γ/2`, which is the monograph's
`γ(P^∧∨_{τ,1}) ≥ γ_{k-1}/2`; the conclusion is unchanged:

  **`(2γ - 1)·ℰ_{P^∨∧_k}(f^{(k+1)}) ≤ ℰ_{P^∨∧_{k+1}}(f^{(k+2)})`.**

The two hypotheses are connected by `lem:updown-downup`
(`UpDownDownUp.downUp_spectralGapAtLeast_of_upDown`), applied inside the link,
and that transfer needs its gap to be at most `1` — which here is the side
condition `γ ≤ 2`.  It is not an artefact: `UpDownDownUp.exists_adjoint_gap_not_swap`
shows the transfer genuinely fails above `1`.  For a local walk it is harmless,
since a Poincaré constant of a positive semidefinite chain is at most `1`
(`UpDownDownUp.gap_le_one_of_var_pos`) whenever some function on the link has
positive variance, so the honest hypothesis on `γ` is `γ ≤ 1`, and `γ ≤ 2` is
weaker still.

What is *not* supplied here is the monograph's first step
`γ(Q_τ) ≥ γ ⟹ γ(P^∧∨_{τ,1}) ≥ γ/2`, which rests on the identity
`P^∧∨_{τ,1} = (Q_τ + I)/2` (`rem:local-downup`).  That identity is not yet
available: `LocalWalk.localWalk` has not been related to the up-down walk of the
honest link `LinkRestriction.linkShiftNorm`. -/
theorem levelEnergy_ge_of_upDown_gap (w : Finset E → ℝ) (n k : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) {γ : ℝ} (hγ : 0 ≤ γ) (hγ2 : γ ≤ 2) (hk2 : k + 1 < n)
    (hgap : ∀ (τ : Finset E) (hcard : τ.card = k) (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w n 1 τ hw hsupp (by omega) hpos (by omega))
        (upDown (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ / 2))
    (f : Finset E → ℝ) :
    (2 * γ - 1) * levelEnergy w n hw hsupp hsum f k
      ≤ levelEnergy w n hw hsupp hsum f (k + 1) := by
  refine levelEnergy_ge_of_downUp_gap w n k hw hsupp hsum hγ hk2 ?_ f
  intro τ hcard hpos
  exact downUp_spectralGapAtLeast_of_upDown (linkShiftNorm w τ) (n - τ.card) 1
    (linkShiftNorm_nonneg hw τ) (linkShiftNorm_supp hsupp (by omega))
    (sum_linkShiftNorm w hpos) (by omega) (by linarith) (hgap τ hcard hpos)

/-! ## The Improved Random Walk Theorem

`lem:improved-technical` is the whole of the improvement; what follows it in the
monograph is bookkeeping, and it is reproduced here.  `eqn:RW-one-improved` says

  `γ(P^∨∧_n) ≥ Γ_{n-1} / ∑_{i<n} Γ_i`,  `Γ_i = ∏_{j<i}(2γ_j - 1)`,

to be compared with the `(1/n)·∏_j γ_j` of `thm:RW`.  For a genuine local walk
`γ_j ≤ 1`, so `Γ_i ≤ 1` and the sum is at most `n`, and the improved bound is
never worse than `thm:RW`'s; when every `γ_j` is close
to `1` the `Γ_i` stay close to `1` and the bound is `≈ 1/n` — the optimal
relaxation time — whereas `∏_j γ_j` can decay geometrically.

**A hypothesis the monograph does not state.**  Its induction multiplies the
inductive hypothesis by `2γ_{k-1} - 1` and multiplies `eqn:NEW-D` by
`∑_{i<k} Γ_i`, so both quantities must be nonnegative.  That is not automatic:
for `γ_j < 1/2` the factor `2γ_j - 1` is negative and both steps reverse.  We
therefore assume `1/2 ≤ γ_j` — equivalently `0 ≤ 2γ_j - 1` — which is exactly
the regime in which the improved theorem says anything (for `γ_j < 1/2` the
bound `Γ_{n-1}/∑Γ_i` is not a lower bound on a spectral gap in any useful
sense).

**A typo in the monograph.**  The penultimate line of the proof of
`lem:impr-RW-thm` justifies a step by "`Γ_k = γ_{k-1}Γ_{k-1}`"; with the stated
definition `Γ_i = ∏_{j<i}(2γ_j - 1)` the correct recursion is
`Γ_k = (2γ_{k-1} - 1)·Γ_{k-1}`, which is what the step actually uses and what
`improvedFactor_succ` records. -/

/-- The monograph's `Γ_i = ∏_{j<i} (2γ_j - 1)`, for a sequence `γ` of local
spectral gaps indexed by level. -/
def improvedFactor (γ : ℕ → ℝ) (i : ℕ) : ℝ := ∏ j ∈ Finset.range i, (2 * γ j - 1)

/-- `Γ_0` is the empty product, `1`. -/
@[simp] theorem improvedFactor_zero (γ : ℕ → ℝ) : improvedFactor γ 0 = 1 :=
  Finset.prod_range_zero _

/-- **The recursion `Γ_{i+1} = Γ_i · (2γ_i - 1)`.**  The monograph's proof of
`lem:impr-RW-thm` cites this step as "`Γ_k = γ_{k-1}Γ_{k-1}`", which is a typo:
the factor is `2γ_{k-1} - 1`, as the definition of `Γ` requires. -/
theorem improvedFactor_succ (γ : ℕ → ℝ) (i : ℕ) :
    improvedFactor γ (i + 1) = improvedFactor γ i * (2 * γ i - 1) :=
  Finset.prod_range_succ _ _

/-- Every `Γ_i` is nonnegative as soon as every local gap is at least `1/2`.
This is the hypothesis the monograph's induction needs and does not state. -/
theorem improvedFactor_nonneg {γ : ℕ → ℝ} (h : ∀ j, 0 ≤ 2 * γ j - 1) (i : ℕ) :
    0 ≤ improvedFactor γ i :=
  Finset.prod_nonneg fun j _ => h j

/-- The partial sums `∑_{i≤m} Γ_i` are at least `1`, since `Γ_0 = 1` and the
remaining terms are nonnegative.  This is what lets the final bound be divided
through by the sum. -/
theorem one_le_sum_improvedFactor {γ : ℕ → ℝ} (h : ∀ j, 0 ≤ 2 * γ j - 1) (m : ℕ) :
    1 ≤ ∑ i ∈ Finset.range (m + 1), improvedFactor γ i := by
  rw [Finset.sum_range_succ' (improvedFactor γ) m, improvedFactor_zero]
  have : 0 ≤ ∑ i ∈ Finset.range m, improvedFactor γ (i + 1) :=
    Finset.sum_nonneg fun i _ => improvedFactor_nonneg h (i + 1)
  linarith

/-- **`induct:simpler`, the inductive heart of the Improved Random Walk
Theorem.**  For every `m < n`,

  **`Γ_m · Var_{π_{m+1}}(f^{(m+1)}) ≤ (∑_{i≤m} Γ_i) · ℰ_{P^∨∧_m}(f^{(m+1)})`.**

The base case `m = 0` is an equality: `Var_{π_0} = 0`, so the one-step identity
`levelVar_succ` reads `Var_{π_1}(f^{(1)}) = ℰ_{P^∨∧_0}(f^{(1)})`.

The step is the monograph's display.  Split the sum as `(∑_{i≤m} Γ_i) + Γ_{m+1}`;
apply `lem:improved-technical` (`levelEnergy_ge_of_downUp_gap`) to the first
part, multiplied by `∑_{i≤m} Γ_i ≥ 0`; apply the inductive hypothesis to the
result, multiplied by `2γ_m - 1 ≥ 0`; recognise `Γ_m·(2γ_m - 1)` as `Γ_{m+1}`;
and reassemble with `levelVar_succ`.  Both nonnegativity side conditions come
from `0 ≤ 2γ_j - 1`. -/
theorem improvedFactor_mul_levelVar_le (w : Finset E → ℝ) (n : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ n → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (γ : ℕ → ℝ) (hγ : ∀ j, 0 ≤ 2 * γ j - 1)
    (hgap : ∀ (j : ℕ) (hj : j + 1 < n) (τ : Finset E) (hcard : τ.card = j)
      (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w n 2 τ hw hsupp (by omega) hpos (by omega))
        (downUp (linkShiftNorm w τ) (n - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ j / 2))
    (f : Finset E → ℝ) :
    ∀ m : ℕ, m < n →
      improvedFactor γ m * levelVar w n hw hsupp hsum f (m + 1)
        ≤ (∑ i ∈ Finset.range (m + 1), improvedFactor γ i)
            * levelEnergy w n hw hsupp hsum f m := by
  intro m
  induction m with
  | zero =>
    intro h0
    have hV0 : levelVar w n hw hsupp hsum f 0 = 0 := by
      rw [levelVar_apply w n 0 hw hsupp hsum f (Nat.zero_le n), Var_pi_zero]
    have hstep := levelVar_succ w n 0 hw hsupp hsum f h0
    rw [Finset.sum_range_one, improvedFactor_zero, hstep, hV0]
    linarith
  | succ m ih =>
    intro hm
    have hm' : m < n := by omega
    have hIH := ih hm'
    -- `lem:improved-technical` at level `m`
    have hIT : (2 * γ m - 1) * levelEnergy w n hw hsupp hsum f m
        ≤ levelEnergy w n hw hsupp hsum f (m + 1) :=
      levelEnergy_ge_of_downUp_gap w n m hw hsupp hsum (by linarith [hγ m]) hm
        (fun τ hcard hpos => hgap m hm τ hcard hpos) f
    -- `lem:diff-var` one level up
    have hVar := levelVar_succ w n (m + 1) hw hsupp hsum f hm
    have hSnn : 0 ≤ ∑ i ∈ Finset.range (m + 1), improvedFactor γ i :=
      Finset.sum_nonneg fun i _ => improvedFactor_nonneg hγ i
    have hΓnn : 0 ≤ improvedFactor γ m := improvedFactor_nonneg hγ m
    -- multiply `lem:improved-technical` by the partial sum
    have h1 : (∑ i ∈ Finset.range (m + 1), improvedFactor γ i)
          * ((2 * γ m - 1) * levelEnergy w n hw hsupp hsum f m)
        ≤ (∑ i ∈ Finset.range (m + 1), improvedFactor γ i)
            * levelEnergy w n hw hsupp hsum f (m + 1) :=
      mul_le_mul_of_nonneg_left hIT hSnn
    -- multiply the inductive hypothesis by `2γ_m - 1`
    have h2 : (2 * γ m - 1) * (improvedFactor γ m * levelVar w n hw hsupp hsum f (m + 1))
        ≤ (2 * γ m - 1) * ((∑ i ∈ Finset.range (m + 1), improvedFactor γ i)
            * levelEnergy w n hw hsupp hsum f m) :=
      mul_le_mul_of_nonneg_left hIH (hγ m)
    rw [Finset.sum_range_succ (improvedFactor γ) (m + 1), improvedFactor_succ γ m, hVar]
    nlinarith [h1, h2, hΓnn]

/-- **The Improved Random Walk Theorem, `eqn:RW-one-improved`.**  For a weighted
complex of dimension `m + 1` whose links all have the stated local gap,

  **`γ(P^∨∧_{m+1}) ≥ Γ_m / ∑_{i≤m} Γ_i`,  `Γ_i = ∏_{j<i}(2γ_j - 1)`.**

This is `improvedFactor_mul_levelVar_le` at the top level, where `f^{(m+1)} = f`
by `levelFun_top`, so the two guarded scalars become the variance and the
Dirichlet form of an *arbitrary* function — which is what the Poincaré
inequality quantifies over.  The division is legitimate because
`∑_{i≤m} Γ_i ≥ Γ_0 = 1`.

The dimension is written `m + 1` rather than `n` purely to keep `ℕ`-subtraction
out of the statement.

Compare `thm:RW`: there the bound is `(1/(m+1))·∏_{j<m} γ_j`.  Here the product
is replaced by `Γ_m = ∏_{j<m}(2γ_j - 1)` and the factor `1/(m+1)` by
`1/∑_{i≤m} Γ_i`, which is at least `1/(m+1)` whenever `γ_j ≤ 1` for every `j`,
since then every `Γ_i ≤ 1`.  Nothing below assumes `γ_j ≤ 1`; it is recorded
only because it is what makes the comparison with `thm:RW` a genuine
improvement. -/
theorem downUp_top_spectralGapAtLeast (w : Finset E → ℝ) (m : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ m + 1 → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (γ : ℕ → ℝ) (hγ : ∀ j, 0 ≤ 2 * γ j - 1)
    (hgap : ∀ (j : ℕ) (hj : j + 1 < m + 1) (τ : Finset E) (hcard : τ.card = j)
      (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w (m + 1) 2 τ hw hsupp (by omega) hpos (by omega))
        (downUp (linkShiftNorm w τ) (m + 1 - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ j / 2)) :
    SpectralGapAtLeast (pi w (m + 1) (m + 1) hw hsupp hsum le_rfl)
      (downUp w (m + 1) m hw hsupp (Nat.lt_succ_self m))
      (improvedFactor γ m / ∑ i ∈ Finset.range (m + 1), improvedFactor γ i) := by
  have hSpos : (0 : ℝ) < ∑ i ∈ Finset.range (m + 1), improvedFactor γ i :=
    lt_of_lt_of_le zero_lt_one (one_le_sum_improvedFactor hγ m)
  intro f
  have hkey := improvedFactor_mul_levelVar_le w (m + 1) hw hsupp hsum γ hγ hgap f m
    (Nat.lt_succ_self m)
  rw [levelVar_apply w (m + 1) (m + 1) hw hsupp hsum f le_rfl,
    levelEnergy_apply w (m + 1) m hw hsupp hsum f (Nat.lt_succ_self m),
    levelFun_top w (m + 1) hw hsupp f] at hkey
  rw [dirichlet_apply, div_mul_eq_mul_div, div_le_iff₀ hSpos]
  rw [← dirichlet_apply]
  linarith [hkey]

/-- The Improved Random Walk Theorem with the local hypothesis in the up-down
form the monograph writes, `γ(P^∧∨_{τ,1}) ≥ γ_j/2`.  The conversion is
`lem:updown-downup` inside each link, and it carries the side condition
`γ_j ≤ 2` — see `levelEnergy_ge_of_upDown_gap`. -/
theorem downUp_top_spectralGapAtLeast_of_upDown_gap (w : Finset E → ℝ) (m : ℕ)
    (hw : ∀ σ : Finset E, 0 ≤ w σ)
    (hsupp : ∀ σ : Finset E, σ.card ≠ m + 1 → w σ = 0)
    (hsum : ∑ σ : Finset E, w σ = 1) (γ : ℕ → ℝ) (hγ : ∀ j, 0 ≤ 2 * γ j - 1)
    (hγ2 : ∀ j, γ j ≤ 2)
    (hgap : ∀ (j : ℕ) (hj : j + 1 < m + 1) (τ : Finset E) (hcard : τ.card = j)
      (hpos : 0 < mu w τ),
      SpectralGapAtLeast (linkShiftPi w (m + 1) 1 τ hw hsupp (by omega) hpos (by omega))
        (upDown (linkShiftNorm w τ) (m + 1 - τ.card) 1 (linkShiftNorm_nonneg hw τ)
          (linkShiftNorm_supp hsupp (by omega)) (by omega)) (γ j / 2)) :
    SpectralGapAtLeast (pi w (m + 1) (m + 1) hw hsupp hsum le_rfl)
      (downUp w (m + 1) m hw hsupp (Nat.lt_succ_self m))
      (improvedFactor γ m / ∑ i ∈ Finset.range (m + 1), improvedFactor γ i) := by
  refine downUp_top_spectralGapAtLeast w m hw hsupp hsum γ hγ ?_
  intro j hj τ hcard hpos
  exact downUp_spectralGapAtLeast_of_upDown (linkShiftNorm w τ) (m + 1 - τ.card) 1
    (linkShiftNorm_nonneg hw τ) (linkShiftNorm_supp hsupp (by omega))
    (sum_linkShiftNorm w hpos) (by omega) (by linarith [hγ2 j]) (hgap j hj τ hcard hpos)

end Arlib.MarkovChains
