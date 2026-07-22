/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# `thm: union` — d-SDNNF is not closed under disjunction

The paper's Theorem `thm: union` (`source/kc/arXiv.tex:471`, proof in the
appendix at `:672`): *there are two functions `f`, `g` which both admit small
d-DNNFs respecting a common v-tree, but whose disjunction `f ∨ g` has no small
d-SDNNF.*

## Why this file is short

The appendix proof is four sentences, and its first is "the proof follows a
similar structure to Theorem `thm: main`".  That is literally true here: every
component was already built for `thm: main`, and each is used at its
*partition* half rather than its *cover* half.  The correspondence is exact:

| `thm: main` | `thm: union` |
| --- | --- |
| `Cov₀` / `NCC₀` — non-deterministic | `Par₁` / `UCC₁` — unambiguous |
| `FixedPartitionHard` | `UnionHard` |
| `hasCoverOfSize_cutPartition` | `hasPartitionOfSize_cutPartition` |
| `hasCoverOfSize_of_hasCoverOfSize_permDNF` | `..._permDNF_union` |

Both halves of the rectangle lemma and both halves of the lifting were proved
when they were first written, precisely so that this file would be the
composition and nothing more.

## The two places it is genuinely different

*Determinism becomes a hypothesis of the lower bound.*  `thm: main` bounds the
size of any **structured DNNF** for `¬f`, because a cover needs no disjointness.
Here the imported hardness is about **unambiguous** communication, i.e. about
rectangular *partitions*, and the only thing that makes a circuit's rectangles
disjoint is determinism at its `∨`-nodes.  So the lower bound below is about
d-SDNNF and not about SDNNF.  This is not an artefact of the formalization — it
is the paper's own footnote at `source/kc/arXiv.tex:481`, which observes that
`thm: union` "almost implies" `thm: main` but yields only a d-SDNNF bound.

*No negation appears.*  `thm: main` had to translate "covering `(¬f)⁻¹(1)`" into
"covering `f⁻¹(0)`" (`Separation.hasCoverOfSize_of_not`).  Here the circuit
computes the union itself and the hardness is about the `1`-fibre, so the
rectangle lemma's `true` and the import's `true` already agree and there is
nothing to translate.

## A common v-tree, and then some

The paper's clause (1) asks for *some* v-tree `T` respected by small circuits
for both `f` and `g`.  The statement below gives more: **every** well-formed
v-tree over the variables works, for both formulas simultaneously, with the same
size bound.  That is what `exists_isdSDNNF_of_unambiguous_kDNF` delivers — it
compiles an unambiguous `k`-DNF against a *prescribed* v-tree — and it is worth
stating in the stronger form, since a reader checking clause (1) can then pick
any `T` at all rather than having to unfold an existential to find out which one
the proof happened to produce.
-/
import Arlib.KnowledgeCompilation.LowerBounds.Separation

namespace Arlib.KnowledgeCompilation
namespace Separation

open AffinePerms Lifting

section Union

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} [NeZero m]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {Zι : Type} [Fintype Zι] [DecidableEq Zι]
variable {k termBound partBound : ℕ}

/-- **The lower-bound half of `thm: union`**: every *deterministic* structured
DNNF computing `ψ' ∨ φ'` has size at least `partBound`.

Read backwards, as in `thm: main`: the imported `UnionHard` forbids a
`Π`-*partition* of `(ψ ∪ φ)⁻¹(1)` below `partBound`; the lifting manufactures one
from any `Γ`-partition of `(ψ' ∪ φ')⁻¹(1)` with `Γ` balanced; and the rectangle
lemma manufactures such a `Γ` and such a partition, of size `|C|`, from the
circuit — this last step being where `hdet` is spent.

As in `thm: main`, the v-tree is not assumed to mention every variable: the
first step grafts the missing ones on (`NNF.Respects.exists_graft`), which `C`
still respects. -/
theorem partBound_le_size_of_computes_union
    (H : Imported.UnionHard (Finset.univ : Finset ι) k termBound partBound)
    {e : ι × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F)
    {T : VTree (F ⊕ Zι)} {C : NNF (F ⊕ Zι)} (hT : T.WellFormed)
    (hR : C.Respects T) (hdet : C.Deterministic) (hCT : C.vars ⊆ T.vars)
    (hC : C.Computes (fun α => DNF.eval (permDNF e rep H.ψ) α ||
      DNF.eval (permDNF e rep H.φ) α)) :
    partBound ≤ C.size := by
  by_contra hlt
  push_neg at hlt
  -- graft the omitted variables onto `T`: `C` respects the larger v-tree too
  obtain ⟨T', hT', hR', hsub, hT'vars⟩ :=
    NNF.Respects.exists_graft hT hR (Finset.univ : Finset (F ⊕ Zι))
  replace hT'vars : T'.vars = (Finset.univ : Finset (F ⊕ Zι)) := by
    rw [hT'vars]
    exact Finset.eq_univ_of_forall fun x => Finset.mem_union_right _ (Finset.mem_univ x)
  have hCT' : C.vars ⊆ T'.vars := hCT.trans hsub.vars_subset
  -- a field has at least two elements, so the v-tree has at least two variables
  have hcard2 : 2 ≤ T'.vars.card := by
    rw [hT'vars, Finset.card_univ, Fintype.card_sum]
    have := Fintype.one_lt_card (α := F)
    omega
  -- the rectangle lemma, partition half: determinism is spent here
  obtain ⟨s, hs, hbal⟩ := VTree.exists_balanced_cut hT' hcard2
  have hpart : HasPartitionOfSize (VTree.cutPartition hs)
      (fun α => DNF.eval (permDNF e rep H.ψ) α || DNF.eval (permDNF e rep H.φ) α)
      true C.size :=
    hasPartitionOfSize_cutPartition hT' hR' hdet hs hCT' hC
  -- the lifting, applied to both formulas through a single substitution
  exact H.not_hasPartition hlt
    (hasPartitionOfSize_of_hasPartitionOfSize_permDNF_union (P := H.P) (ψ := H.ψ) (φ := H.φ)
      he (fun _ _ _ _ h => hrep h) hT'vars hbal hm hz hpart)

/-- **`thm: union`** (`source/kc/arXiv.tex:471`): *there are two functions, each
with a small d-SDNNF respecting any prescribed common v-tree, whose disjunction
has no small d-SDNNF.*

The two functions are `ψ'` and `φ'`, the copy-and-permute liftings of the two
hard `k`-DNFs supplied by `Imported.UnionHard`.  As in `thm_main` the bounds are
explicit rather than asymptotic, and the whole statement is conditional on that
one import and on nothing else.

* **upper** `|C| ≤ |𝒫|·(termBound·m^k)·(2(|Zι| + km) + 2) + 1`, for each of the
  two, respecting any prescribed v-tree over `var(ψ')`;
* **lower** `partBound ≤ |C|`, for every *deterministic* structured DNNF
  computing `ψ' ∨ φ'`.

The paper's `n^{Ω̃(log n)}` is the comparison of these two numbers; see the
docstring of `thm_main` and `ROADMAP.md` §5. -/
theorem thm_union
    (H : Imported.UnionHard (Finset.univ : Finset ι) k termBound partBound)
    {e : ι × Fin m → F} (he : Function.Injective e)
    {rep : F × F → Zι → Bool} (hrep : Function.Injective rep)
    (hm : 6 * Fintype.card ι < m) (hz : 8 * Fintype.card Zι ≤ Fintype.card F) :
    ∃ ψ' φ' : DNF (F ⊕ Zι),
      -- (1) both admit d-SDNNFs of the stated size respecting *any* common v-tree
      (∀ T : VTree (F ⊕ Zι), T.WellFormed → T.vars = Finset.univ →
        (∃ C : NNF (F ⊕ Zι), C.Computes (DNF.eval ψ') ∧ C.Respects T ∧ C.IsdSDNNF ∧
          C.size ≤ (maps F).card * (termBound * m ^ k)
            * (2 * (Fintype.card Zι + k * m) + 2) + 1) ∧
        (∃ C : NNF (F ⊕ Zι), C.Computes (DNF.eval φ') ∧ C.Respects T ∧ C.IsdSDNNF ∧
          C.size ≤ (maps F).card * (termBound * m ^ k)
            * (2 * (Fintype.card Zι + k * m) + 2) + 1)) ∧
      -- (2) their disjunction has no small d-SDNNF
      (∀ (T : VTree (F ⊕ Zι)) (C : NNF (F ⊕ Zι)), T.WellFormed →
        C.Respects T → C.Deterministic → C.vars ⊆ T.vars →
        C.Computes (fun α => DNF.eval ψ' α || DNF.eval φ' α) →
          partBound ≤ C.size) := by
  refine ⟨permDNF e rep H.ψ, permDNF e rep H.φ, fun T hT hTvars => ⟨?_, ?_⟩, ?_⟩
  · exact exists_isdSDNNF_permDNF hrep H.isKDNF.1 H.unambiguous.1 H.numTerms_le.1 T hT hTvars
  · exact exists_isdSDNNF_permDNF hrep H.isKDNF.2 H.unambiguous.2 H.numTerms_le.2 T hT hTvars
  · exact fun T C hT hR hdet hCT hC =>
      partBound_le_size_of_computes_union H he hrep hm hz hT hR hdet hCT hC

end Union

end Separation
end Arlib.KnowledgeCompilation
