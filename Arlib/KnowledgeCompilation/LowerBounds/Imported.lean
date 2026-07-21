/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The imported hardness results, as explicit hypotheses

The paper's headline theorems rest on results proved elsewhere.  This file makes
each of them a **named bundle of data and properties**, so that a downstream
theorem takes it as a parameter and a reader of the statement can see exactly
what it is conditional on.

This is the area's §1.3 commitment (`ROADMAP.md`), and it is not pedantry.  The
fixed-partition hardness below is the *sole* source of quantitative content in
the entire paper: every other step is a reduction that moves a bound around.
Were it an `axiom`, `thm: main` would typecheck while proving nothing at all, and
the formalization would be worthless in a way that no amount of `#print axioms`
checking would reveal.  As a hypothesis it is honest — and, just as importantly,
anyone who later proves it can discharge the hypothesis and the whole chain
becomes unconditional with no other change.

## Why there are no asymptotics here

The paper states these results with `Õ` and `Ω̃`.  The bundles below instead carry
**explicit numeric bounds as parameters** — `termBound`, `coverBound` — and the
downstream theorems will relate the bounds they are given to the bounds they
produce.  The result is a chain of fully explicit implications with no
asymptotic notation anywhere: *given* hardness with these constants, the
separation has those constants.

This is `ROADMAP.md` §5 applied at the boundary.  It is strictly more useful than
encoding `Ω̃`: it says something for every choice of constants, it is far easier
to prove, and the asymptotic packaging is recovered by instantiating the
parameters at the end.  Encoding "polylogarithmic factors suppressed" as a Lean
predicate would be a substantial development in its own right, consumed exactly
once, at the very last step.

## What is *not* here

De Colnet–Mengel (used only by the arithmetic-circuit section) is deliberately
absent: it needs vocabulary — the relabelling `φ` — that does not exist yet.  It
belongs here once it does.

`SDD` closed under polynomial-time complementation (used only by `thm: sep`,
`source/kc/arXiv.tex:465`) was in the same position and is now here, as
`SDDComplementation`: `Circuits/SDD.lean` supplies `IsSDDAt`, the vocabulary it
was waiting for.
-/
import Arlib.KnowledgeCompilation.Circuits.DNF
import Arlib.KnowledgeCompilation.Circuits.SDD
import Arlib.KnowledgeCompilation.Communication.Measures

namespace Arlib.KnowledgeCompilation
namespace Imported

variable {ι : Type} [DecidableEq ι]

/-- **I1 — fixed-partition hardness** (`thm: fixed_part`,
`source/kc/arXiv.tex:311`), from Göös et al., building on GLMWZ and Balodis et
al.

The data: a function on variables `Z`, presented as an unambiguous `k`-DNF `ψ`
with at most `termBound` terms, together with a *balanced* partition `P` under
which certifying the value `0` needs at least `coverBound` rectangles.

The paper's clause (2) reads `NCC₀^Π(g) = Ω̃(k²)`.  Since `NCC` is by definition
`log₂ Cov` (inventory D20) and we never take logarithms, that clause appears
here directly as a lower bound on `Cov₀^Π` — which is what every consumer
actually uses.

**This is not to be proved here.**  It is a substantial paper in its own right,
and it carries all of the quantitative content of the main theorem. -/
structure FixedPartitionHard (Z : Finset ι) (k termBound coverBound : ℕ) where
  /-- The hard function, presented as a DNF. -/
  ψ : DNF ι
  /-- The balanced partition witnessing hardness. -/
  P : VarPartition Z
  /-- `P` is balanced — the paper's `|Z|/3 ≤ min(|X|,|Y|)`. -/
  balanced : P.Balanced
  /-- Every term has at most `k` literals. -/
  isKDNF : DNF.IsKDNF k ψ
  /-- Every assignment satisfies at most one term. -/
  unambiguous : DNF.Unambiguous ψ
  /-- The paper's `2^{Õ(k)}` bound on the number of terms. -/
  numTerms_le : ψ.numTerms ≤ termBound
  /-- The paper's `NCC₀^Π(g) = Ω̃(k²)`, stated on `Cov₀^Π` directly. -/
  hard : coverBound ≤ fixedCov P (DNF.eval ψ) false

namespace FixedPartitionHard

variable {Z : Finset ι} {k termBound coverBound : ℕ}

/-- The hardness clause, in the form a lower-bound proof consumes it: **no**
cover of `ψ⁻¹(0)` by fewer than `coverBound` rectangles exists, for the
distinguished partition. -/
theorem not_hasCover (H : FixedPartitionHard Z k termBound coverBound) {j : ℕ}
    (hj : j < coverBound) : ¬HasCoverOfSize H.P (DNF.eval H.ψ) false j :=
  not_hasCover_of_lt_fixedCov (lt_of_lt_of_le hj H.hard)

end FixedPartitionHard

/-- **I1′ — fixed-partition hardness for unions** (`thm: fixed_or`,
`source/kc/arXiv.tex:671`), from Göös et al., Theorem 2.  Same provenance and
same status as `FixedPartitionHard`; used only for `thm: union` and hence for
the disjunction and existential-quantification results.

Two differences from I1.  The hardness is about the *union* `f ∪ g` rather than
about a single function, and it is measured by `UCC₁` — unambiguous protocols —
rather than `NCC₀`.  Since `UCC = log₂ Par` (inventory D20), that appears here as
a lower bound on `Par₁`, the rectangular *partition* number.  Both `f` and `g`
must be presented as unambiguous `k`-DNFs. -/
structure UnionHard (Z : Finset ι) (k termBound partBound : ℕ) where
  /-- The first function, as a DNF. -/
  ψ : DNF ι
  /-- The second function, as a DNF. -/
  φ : DNF ι
  /-- The balanced partition witnessing hardness. -/
  P : VarPartition Z
  /-- `P` is balanced. -/
  balanced : P.Balanced
  /-- Both are `k`-DNFs. -/
  isKDNF : DNF.IsKDNF k ψ ∧ DNF.IsKDNF k φ
  /-- Both are unambiguous. -/
  unambiguous : DNF.Unambiguous ψ ∧ DNF.Unambiguous φ
  /-- Both have few terms. -/
  numTerms_le : ψ.numTerms ≤ termBound ∧ φ.numTerms ≤ termBound
  /-- The paper's `UCC₁^Π(f ∪ g) = Ω̃(k²)`, stated on `Par₁^Π` directly. -/
  hard : partBound ≤ fixedPar P (fun α => DNF.eval ψ α || DNF.eval φ α) true

namespace UnionHard

variable {Z : Finset ι} {k termBound partBound : ℕ}

/-- The hardness clause of I1′, in consumable form. -/
theorem not_hasPartition (H : UnionHard Z k termBound partBound) {j : ℕ}
    (hj : j < partBound) :
    ¬HasPartitionOfSize H.P (fun α => DNF.eval H.ψ α || DNF.eval H.φ α) true j :=
  not_hasPartition_of_lt_fixedPar (lt_of_lt_of_le hj H.hard)

end UnionHard

/-- **I5 — SDD is closed under complementation, in polynomial time** (Darwiche,
via `source/kc/arXiv.tex:465`), used only by `thm: sep`.

The paper's sentence is "we may complement this SDD to get an SDD for `¬f` of
size polynomial in `|C|`".  Three things are made explicit here.

*The polynomial.*  Following `ROADMAP.md` §5, "polynomial" is the pair of
parameters `c, d` and the bound `|C'| ≤ c·|C|^d`.  A downstream theorem then
relates the constants it is given to the constants it produces, with no
asymptotic notation anywhere.

*The v-tree is preserved.*  Complementation of an SDD negates its terminals and
leaves its structure alone, so the output respects the *same* v-tree.  Stated
this way the bundle is both closer to the truth and much easier to consume: the
lower bound needs a v-tree for `C'`, and asking the import to produce one out of
nowhere would be asking for more than it gives.

*Nothing about reachability.*  The bundle used to carry a third clause, that the
output circuit has no unreachable nodes, purely so that a consumer could get from
`IsSDDAt` — which constrains only what lies below the source — to `Respects` and
`Deterministic`, which then quantified over every node index.  That was
`ROADMAP.md` gap G1; with the two conditions now imposed on the reachable nodes,
`NNF.IsSDDAt.respectsFrom` bridges the two outright and the clause is gone. -/
structure SDDComplementation (V : Type*) [DecidableEq V] (c d : ℕ) where
  /-- From an SDD for `f` respecting `T`, an SDD for `¬f` respecting `T`, of
  size at most `c·|C|^d`. -/
  compl : ∀ (T : VTree V) (C : NNF V) (f : (V → Bool) → Bool), T.WellFormed →
    C.IsSDDAt C.root T → C.Computes f →
    ∃ C' : NNF V, C'.IsSDDAt C'.root T ∧
      C'.Computes (fun α => !(f α)) ∧ C'.size ≤ c * C.size ^ d

end Imported
end Arlib.KnowledgeCompilation
