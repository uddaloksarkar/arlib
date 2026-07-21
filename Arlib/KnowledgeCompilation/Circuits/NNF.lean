/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Circuits in Negation Normal Form

The base object of the whole area: a Boolean circuit in Negation Normal Form
(NNF), in the sense of Darwiche–Marquis.  Every representation language studied
here — DNNF, d-DNNF, structured d-DNNF, SDD — is an NNF with extra conditions,
so this file fixes the encoding that all of them inherit.

## The encoding, and why it is a DAG and not a tree

An NNF is a *directed acyclic graph* with a unique source, fan-in-two `∧`/`∨`
internal nodes, and leaves labelled `0`, `1`, `x` or `¬x`; its size `|C|` is the
number of vertices (paper §2, `def: NNF`, `source/kc/arXiv.tex:141`).

The tempting Lean encoding — an inductive tree — is **wrong for this area**, and
the reason is worth stating once, loudly, because everything downstream depends
on it.  A DAG represents a shared subcircuit once; unfolding it to a tree can
blow the vertex count up exponentially.  This area exists to prove *lower*
bounds on `|C|`, and a lower bound on tree size does not imply a lower bound on
DAG size.  Formalizing trees would therefore silently prove a strictly weaker
theorem than the paper's.  So we pay for the DAG up front.

The encoding is the standard straight-line-program one: nodes are the indices
`Fin size`, `gate i` is the label of node `i`, and every child of `i` has a
strictly smaller index (`child_lt`).  That single field does three jobs at once:
it makes the graph acyclic, it fixes a topological order, and it is the
termination measure for every recursion over the circuit.

## Nodes, not subcircuits

The paper writes `C(g)` for the subcircuit rooted at `g` and uses it constantly.
We deliberately do **not** introduce a subcircuit operation.  Every use of `C(g)`
in the paper is really a statement about the *function computed at the node* `g`
— determinism compares `sat(C(gₗ))` with `sat(C(gᵣ))`, structuredness compares
`var(C(gₗ))` with `var(t_ℓ)` — and that is exactly `valAt`/`varsAt` at a node.
Carrying node-indexed families instead of reconstructed circuits removes a layer
of bookkeeping from every proof downstream, at no loss of expressiveness.

## `dom` versus `var`

The paper carries a variable set `dom(C) ⊇ var(C)` so that a circuit can be read
as a function on a larger cube than it mentions.  Here assignments are total
functions `V → Bool` on the ambient variable type, which is `dom(C)` taken as
large as possible; `varsAt` computes `var(·)` syntactically.  Since determinism
in the paper is stated with `dom(C(gₗ)) = dom(C(gᵣ)) = dom(C)`, this choice is
exactly the paper's convention, with none of the bookkeeping.

## A recorded gap

`Decomposable` and `Deterministic` below quantify over **all** node indices,
whereas the paper imposes them only on the nodes of the circuit, i.e. those
reachable from the source.  Our classes are therefore contained in the paper's,
which weakens a lower bound stated over them.  The two agree up to pruning:
unreachable nodes can be deleted, which only decreases `size`.  That pruning
lemma is a deferred obligation — see `ROADMAP.md`, §"Recorded gaps".  Nothing
proved here depends on it.
-/
import Arlib.Prelude
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

namespace Arlib.KnowledgeCompilation

/-- The label of a single node of an `n`-node NNF circuit: a constant, a
positive or negative literal, or a fan-in-two conjunction or disjunction whose
children are node indices.

`lit x true` is the literal `x`, and `lit x false` is `¬x`. -/
inductive Gate (V : Type*) (n : ℕ) where
  | const : Bool → Gate V n
  | lit : V → Bool → Gate V n
  | conj : Fin n → Fin n → Gate V n
  | disj : Fin n → Fin n → Gate V n
  deriving Inhabited

variable {V : Type*} {n : ℕ}

/-- The children of a gate, as a list of node indices.  Leaves have none. -/
def Gate.children : Gate V n → List (Fin n)
  | .const _ => []
  | .lit _ _ => []
  | .conj j k => [j, k]
  | .disj j k => [j, k]

@[simp] lemma Gate.children_const (b : Bool) :
    (Gate.const b : Gate V n).children = [] := rfl

@[simp] lemma Gate.children_lit (x : V) (p : Bool) :
    (Gate.lit x p : Gate V n).children = [] := rfl

@[simp] lemma Gate.children_conj (j k : Fin n) :
    (Gate.conj j k : Gate V n).children = [j, k] := rfl

@[simp] lemma Gate.children_disj (j k : Fin n) :
    (Gate.disj j k : Gate V n).children = [j, k] := rfl

/-- **A Boolean circuit in Negation Normal Form** over variables `V`
(paper `def: NNF`, `source/kc/arXiv.tex:141`).

Nodes are the indices `Fin size`; `gate i` labels node `i`; `child_lt` says
every child of `i` is a strictly smaller index, which makes the graph acyclic
and fixes a topological order; `root` is the unique source.

`size` is the paper's `|C|`. -/
structure NNF (V : Type*) where
  /-- The number of nodes.  This is the paper's `|C|`. -/
  size : ℕ
  /-- The label of each node. -/
  gate : Fin size → Gate V size
  /-- Acyclicity: children come strictly earlier in the indexing. -/
  child_lt : ∀ i : Fin size, ∀ j ∈ (gate i).children, j < i
  /-- The unique source, i.e. the output node. -/
  root : Fin size

namespace NNF

variable (C : NNF V)

/-- The children of a conjunction node come strictly earlier. -/
lemma conj_lt {i j k : Fin C.size} (h : C.gate i = .conj j k) : j < i ∧ k < i :=
  ⟨C.child_lt i j (by rw [h]; simp), C.child_lt i k (by rw [h]; simp)⟩

/-- The children of a disjunction node come strictly earlier. -/
lemma disj_lt {i j k : Fin C.size} (h : C.gate i = .disj j k) : j < i ∧ k < i :=
  ⟨C.child_lt i j (by rw [h]; simp), C.child_lt i k (by rw [h]; simp)⟩

/-! ## Semantics -/

/-- The value of node `i` under the assignment `α`.

Recursion is on the node index, which is legitimate by `child_lt`.  A negative
literal `¬x` evaluates to the negation of `α x`; this is the only place negation
enters an NNF, which is the whole point of the normal form. -/
def valAt (α : V → Bool) (i : Fin C.size) : Bool :=
  match h : C.gate i with
  | .const b => b
  | .lit x p => if p then α x else !α x
  | .conj j k => valAt α j && valAt α k
  | .disj j k => valAt α j || valAt α k
termination_by i.val
decreasing_by
  · exact (C.conj_lt h).1
  · exact (C.conj_lt h).2
  · exact (C.disj_lt h).1
  · exact (C.disj_lt h).2

@[simp] lemma valAt_const {α : V → Bool} {i : Fin C.size} {b : Bool}
    (h : C.gate i = .const b) : C.valAt α i = b := by
  rw [valAt]; split <;> simp_all

@[simp] lemma valAt_lit {α : V → Bool} {i : Fin C.size} {x : V} {p : Bool}
    (h : C.gate i = .lit x p) : C.valAt α i = if p then α x else !α x := by
  rw [valAt]; split <;> simp_all

@[simp] lemma valAt_conj {α : V → Bool} {i j k : Fin C.size}
    (h : C.gate i = .conj j k) : C.valAt α i = (C.valAt α j && C.valAt α k) := by
  rw [valAt]; split <;> simp_all

@[simp] lemma valAt_disj {α : V → Bool} {i j k : Fin C.size}
    (h : C.gate i = .disj j k) : C.valAt α i = (C.valAt α j || C.valAt α k) := by
  rw [valAt]; split <;> simp_all

/-- The Boolean function computed by `C`: the value at its source.  This is the
paper's `f_C`. -/
def eval (α : V → Bool) : Bool := C.valAt α C.root

/-- `C` is satisfied by `α`.  The paper's `sat(C)` is `{α | C.Sat α}`. -/
def Sat (α : V → Bool) : Prop := C.eval α = true

/-- Two circuits are *equivalent* when they compute the same function. -/
def Equiv (C D : NNF V) : Prop := ∀ α, C.eval α = D.eval α

/-- `C` is *equivalent to* the Boolean function `f`. -/
def Computes (f : (V → Bool) → Bool) : Prop := ∀ α, C.eval α = f α

/-! ## Variables -/

section Vars

variable [DecidableEq V]

/-- The variables occurring at or below node `i`; the paper's `var(C(g))`.
Constants contribute nothing, and a literal contributes its variable
irrespective of sign. -/
def varsAt (i : Fin C.size) : Finset V :=
  match h : C.gate i with
  | .const _ => ∅
  | .lit x _ => {x}
  | .conj j k => varsAt j ∪ varsAt k
  | .disj j k => varsAt j ∪ varsAt k
termination_by i.val
decreasing_by
  · exact (C.conj_lt h).1
  · exact (C.conj_lt h).2
  · exact (C.disj_lt h).1
  · exact (C.disj_lt h).2

@[simp] lemma varsAt_const {i : Fin C.size} {b : Bool} (h : C.gate i = .const b) :
    C.varsAt i = ∅ := by rw [varsAt]; split <;> simp_all

@[simp] lemma varsAt_lit {i : Fin C.size} {x : V} {p : Bool} (h : C.gate i = .lit x p) :
    C.varsAt i = {x} := by rw [varsAt]; split <;> simp_all

@[simp] lemma varsAt_conj {i j k : Fin C.size} (h : C.gate i = .conj j k) :
    C.varsAt i = C.varsAt j ∪ C.varsAt k := by rw [varsAt]; split <;> simp_all

@[simp] lemma varsAt_disj {i j k : Fin C.size} (h : C.gate i = .disj j k) :
    C.varsAt i = C.varsAt j ∪ C.varsAt k := by rw [varsAt]; split <;> simp_all

/-- The variables of `C`; the paper's `var(C)`. -/
def vars : Finset V := C.varsAt C.root

/-- **The value at a node depends only on the variables below that node.**

This is the workhorse behind decomposability: it is what lets a decomposable
`∧`-node be evaluated by handing each child its own block of the assignment.
Proved by induction along the topological order. -/
theorem valAt_congr {α β : V → Bool} (i : Fin C.size)
    (h : ∀ x ∈ C.varsAt i, α x = β x) : C.valAt α i = C.valAt β i := by
  match hg : C.gate i with
  | .const b => rw [C.valAt_const hg, C.valAt_const hg]
  | .lit x p =>
    have hx : α x = β x := h x (by rw [C.varsAt_lit hg]; simp)
    rw [C.valAt_lit hg, C.valAt_lit hg, hx]
  | .conj j k =>
    rw [C.varsAt_conj hg] at h
    rw [C.valAt_conj hg, C.valAt_conj hg,
      valAt_congr j (fun x hx => h x (Finset.mem_union_left _ hx)),
      valAt_congr k (fun x hx => h x (Finset.mem_union_right _ hx))]
  | .disj j k =>
    rw [C.varsAt_disj hg] at h
    rw [C.valAt_disj hg, C.valAt_disj hg,
      valAt_congr j (fun x hx => h x (Finset.mem_union_left _ hx)),
      valAt_congr k (fun x hx => h x (Finset.mem_union_right _ hx))]
termination_by i.val
decreasing_by
  · exact (C.conj_lt hg).1
  · exact (C.conj_lt hg).2
  · exact (C.disj_lt hg).1
  · exact (C.disj_lt hg).2

/-- The function computed by `C` depends only on `var(C)`. -/
theorem eval_congr {α β : V → Bool} (h : ∀ x ∈ C.vars, α x = β x) :
    C.eval α = C.eval β :=
  C.valAt_congr C.root h

end Vars

/-! ## Decomposability and determinism

The two syntactic restrictions that carve d-DNNF out of NNF (paper §2,
`source/kc/arXiv.tex:146`).  Both are stated over all node indices; see the
recorded gap in the module docstring. -/

/-- **Decomposability**: the two children of every `∧`-node have disjoint
variable sets. -/
def Decomposable [DecidableEq V] : Prop :=
  ∀ ⦃i j k : Fin C.size⦄, C.gate i = .conj j k → Disjoint (C.varsAt j) (C.varsAt k)

/-- **Determinism**: the two children of every `∨`-node have disjoint sets of
satisfying assignments.

The paper phrases this as `sat(C(gₗ)) ∩ sat(C(gᵣ)) = ∅` with both subcircuits
read over the full domain `dom(C)`; since our assignments are already total on
`V`, that is literally the statement below. -/
def Deterministic : Prop :=
  ∀ ⦃i j k : Fin C.size⦄, C.gate i = .disj j k →
    ∀ α, ¬(C.valAt α j = true ∧ C.valAt α k = true)

/-- A **DNNF** is a decomposable NNF. -/
def IsDNNF [DecidableEq V] : Prop := C.Decomposable

/-- A **d-DNNF** is a deterministic, decomposable NNF. -/
def IsdDNNF [DecidableEq V] : Prop := C.Decomposable ∧ C.Deterministic

lemma IsdDNNF.decomposable [DecidableEq V] {C : NNF V} (h : C.IsdDNNF) :
    C.Decomposable := h.1

lemma IsdDNNF.deterministic [DecidableEq V] {C : NNF V} (h : C.IsdDNNF) :
    C.Deterministic := h.2

/-- **A decomposable `∧`-node splits.**  At a decomposable conjunction the two
children may be evaluated on assignments that agree with `α` only on their own
variables.  This is the form in which decomposability is actually consumed, both
in the rectangle lemma and in every upper-bound construction; note that the
disjointness hypothesis is what makes such a pair `β`, `γ` assemble back into a
single assignment. -/
theorem valAt_conj_split [DecidableEq V] {i j k : Fin C.size}
    (h : C.gate i = .conj j k) {α β γ : V → Bool}
    (hβ : ∀ x ∈ C.varsAt j, β x = α x) (hγ : ∀ x ∈ C.varsAt k, γ x = α x) :
    C.valAt α i = (C.valAt β j && C.valAt γ k) := by
  rw [C.valAt_conj h, C.valAt_congr j (fun x hx => (hβ x hx).symm),
    C.valAt_congr k (fun x hx => (hγ x hx).symm)]

/-- **Determinism at an `∨`-node, in disjunctive form.**  If the node fires,
exactly one child fires. -/
theorem valAt_disj_unique (hC : C.Deterministic) {i j k : Fin C.size}
    (h : C.gate i = .disj j k) {α : V → Bool} (hi : C.valAt α i = true) :
    (C.valAt α j = true ∧ C.valAt α k = false) ∨
      (C.valAt α j = false ∧ C.valAt α k = true) := by
  have hd := hC h α
  rw [C.valAt_disj h] at hi
  cases hj : C.valAt α j <;> cases hk : C.valAt α k <;> simp_all

end NNF

end Arlib.KnowledgeCompilation
