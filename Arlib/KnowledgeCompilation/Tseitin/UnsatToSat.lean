/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Step 1: from an unsatisfiable refutation to a satisfiable DNNF

The reduction of §3 of Florent de Colnet and Stefan Mengel, *Characterizing
Tseitin-formulas with short regular resolution refutations*
(`source/kc/decolnet/main.tex:449`).  A regular refutation of an unsatisfiable
`T(G,c)` is turned, via a well-structured 1-BP, into a **DNNF for a satisfiable**
`T(G,c*)` of only polynomial overhead.

* **Lemma 11** (`lemma:from_well_struct_1BP_to_DNNF`, `:453`) —
  `WellStructuredToDNNF`: a well-structured 1-BP of size `s` for
  `SearchVertex(G,c)` (with `G` connected, `T(G,c)` unsatisfiable, `T(G,c*)`
  satisfiable) yields a DNNF of size `≤ c₀·s·|V(G)|` computing `T(G,c*)`.
* **Theorem 5** (`theorem:from_refutation_to_sat_DNNF`, `:406`) — `theorem5`:
  **proved by composition** of Corollary 8, Lemma 10 and Lemma 11: a regular
  refutation of length `S` yields a DNNF of size `≤ c₀·S·|V(G)|` for the
  satisfiable `T(G,c*)`.

## Lemma 11 is boxed, not proved

Lemma 11's proof (`:456`–`:489`) is a reverse-topological induction over the 1-BP:
each node `u_i` computing `SearchVertex(G_i,c_i)` is assigned a gate computing the
*satisfiable* `T(G_i, c_i+1_v)`, decision nodes add `≤ 3|V_k|` `∨`/`∧`-gates, and
decomposability holds because the two sides of a split share no edge.  This is a
heavy induction on a BP model the repository does not build (the opaque
`HasWS1BPForSearchVertexLe` carrier of `Search.lean`), so following `ROADMAP.md`
§1.3 it is a boxed import with the **explicit** `c₀·s·|V|` size field — the honest
quantitative content — and is un-inhabited (inhabiting = the induction itself).
The `|D_k| ≤ 3(|V_1|+…+|V_S|)` bound of `:489` is why the constant is a single `c₀`
with a factor `|V|`.

Theorem 5 itself is **proved**: it is exactly the composition
`refutation → 1-BP (Cor 8) → well-structured (Lem 10) → DNNF (Lem 11)`, and the
charge transfer to an arbitrary satisfiable `c*` is `ThreeConnected.ReduceToZeroCharge`
(Lemma 6).
-/
import Arlib.KnowledgeCompilation.Tseitin.ThreeConnected
import Arlib.KnowledgeCompilation.Tseitin.Search

namespace Arlib.KnowledgeCompilation.Tseitin

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **`lemma:from_well_struct_1BP_to_DNNF`**
(`source/kc/decolnet/main.tex:453`), imported with an explicit size bound: a
well-structured 1-BP of size `s` for `SearchVertex(G,c)` gives a DNNF of size at
most `c₀·s·|V(G)|` computing the satisfiable `T(G,c*)`.  Not inhabited — inhabiting
is the reverse-topological BP induction itself; see the module docstring. -/
structure WellStructuredToDNNF (c cstar : V → ZMod 2) (c₀ : ℕ) : Prop where
  /-- A well-structured 1-BP of size `≤ s` yields a DNNF of size `≤ c₀·s·|V|` for
  `T(G,c*)`. -/
  toDNNF : ∀ s, HasWS1BPForSearchVertexLe G c s →
    DNNFSizeLe G cstar (c₀ * s * Fintype.card V)

/-- **`theorem:from_refutation_to_sat_DNNF`**
(`source/kc/decolnet/main.tex:406`), **proved by composition**: for an
unsatisfiable `T(G,c)` with `G` connected, a regular resolution refutation of
length `S` yields a DNNF of size at most `c₀·S·|V(G)|` computing the satisfiable
`T(G,c*)`.

The proof is the chain `Corollary 8` (refutation → 1-BP of size `≤ S`), `Lemma 10`
(→ a well-structured one), `Lemma 11` (→ a DNNF of size `≤ c₀·S·|V|`). -/
theorem theorem5 {c cstar : V → ZMod 2} {c₀ : ℕ}
    {F : List (Clause {e // e ∈ G.edgeSet})}
    (cor8 : Corollary8 G c F) (lem10 : Lemma10 G c)
    (lem11 : WellStructuredToDNNF G c cstar c₀)
    {S : ℕ} (href : RegRefutationLen F S) :
    DNNFSizeLe G cstar (c₀ * S * Fintype.card V) :=
  lem11.toDNNF S (lem10.minimal_wellStructured S (cor8.bp_le_refutation S href))

end Arlib.KnowledgeCompilation.Tseitin
