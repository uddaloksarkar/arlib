/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib.KnowledgeCompilation

Knowledge compilation: representation languages for Boolean functions, and
lower bounds on their size.

The development follows Harry Vinall-Smeeth, *Structured d-DNNF Is Not Closed
Under Negation* (IJCAI 2024), in `source/kc/arXiv.tex`.  See `ROADMAP.md` for
the design principles and `PAPER-INVENTORY.md` for the statement-by-statement
catalogue of the source paper.

The area is split three ways, mirroring the shape of the argument:

* **`Circuits/`** — the *objects*.  NNF and the syntactic restrictions that cut
  representation languages out of it: decomposability, determinism, v-trees and
  structuredness, SDD, and the arithmetic-circuit analogues.
* **`Communication/`** — the *tool*.  Rectangles, covers and partitions of
  `f⁻¹(b)`, the measures `Cov`, `Par`, `NCC`, `UCC`, and the distinction
  between the fixed-partition and best-partition models.
* **`LowerBounds/`** — the *bridge and the argument*.  The rectangle lemma
  connecting circuit size to rectangle covers, the copy-and-permute lifting
  from fixed to best partition, and the separation theorems.

Two conventions are worth stating up front, because they shape everything.

**Circuits are DAGs, never trees.** Size is the vertex count of a shared graph.
A lower bound on tree size would not imply one on DAG size, so a tree encoding
would silently prove a weaker theorem than the paper's.  See the docstring of
`Circuits.NNF`.

**Imported results are hypotheses, never axioms.** The paper's headline theorems
rest on results proved elsewhere (Göös–Jain–Watson, Knop, de Colnet–Mengel).
Those enter as explicit hypotheses on the theorems that consume them, so that
what is and is not proved here is visible in the statement.  See `ROADMAP.md`,
§"Imported results".

## Modules

### Circuits

* `Circuits.NNF` — the DAG encoding, node values `valAt`, the computed function
  `eval`, syntactic variables `varsAt`, the locality lemma `valAt_congr`, and
  the predicates `Decomposable`, `Deterministic`, `IsDNNF`, `IsdDNNF`.
* `Circuits.VTree` — v-trees, well-formedness (equivalently, no repeated leaf),
  the subtree relation, `NNF.Respects`, and the structured classes `IsSDNNF`
  and `IsdSDNNF`.  Includes `Respects.decomposable`: respecting a well-formed
  v-tree already forces decomposability.
* `Circuits.SDD` — `XDecomposition`, the fan-in-2 chain relation `IsChain`, the
  SDD predicate `IsSDDAt` by recursion on the v-tree, reachability, and the
  containment SDD ⊆ d-SDNNF.
* `Circuits.DNF` — terms as finite sets of literals, width, DNF formulas as
  lists of terms, `IsKDNF`, and `Unambiguous` in its counting form.  This is the
  shape in which every imported hardness result arrives, and the object the
  copy-and-permute construction transforms.

### Communication

* `Communication.Rectangle` — `VarPartition` and balancedness, Π-rectangles as
  pairs of predicates each local to its side of the partition, and the closure
  property `mem_cross` that every rectangle argument runs on.
* `Communication.Measures` — `fixedCov`/`fixedPar` and their best-partition
  counterparts, together with the per-partition unfolded form in which a lower
  bound is actually consumed.

### LowerBounds

* `LowerBounds.Copies` — Step 1 of the lifting: the derived terms `copyTerm`,
  the collapse of an assignment on copies, and the fact that the construction is
  faithful exactly on the *one-hot* region — soundness unconditionally, its
  converse only there.
* `LowerBounds.BalancedCut` — the first half of the rectangle lemma: every
  v-tree on at least two variables has a node carrying between a third and two
  thirds of them, so cutting there induces a *balanced* partition.  This is what
  supplies the partition that a best-partition measure is minimised over.
* `LowerBounds.AffinePerms` — the Wegman–Carter family `x ↦ ax+b` over a finite
  field, and its pairwise independence.  This **discharges** import I3: the paper
  cites it, we prove it.
* `LowerBounds.Imported` — the results the paper genuinely imports, as named
  bundles of data and hypotheses rather than axioms.  Every downstream theorem
  takes one as a parameter, so what a statement is conditional on is visible in
  the statement.
-/

import Arlib.KnowledgeCompilation.Basic
import Arlib.KnowledgeCompilation.Circuits.NNF
import Arlib.KnowledgeCompilation.Circuits.VTree
import Arlib.KnowledgeCompilation.Circuits.SDD
import Arlib.KnowledgeCompilation.Circuits.DNF
import Arlib.KnowledgeCompilation.Communication.Rectangle
import Arlib.KnowledgeCompilation.Communication.Measures
import Arlib.KnowledgeCompilation.LowerBounds.Copies
import Arlib.KnowledgeCompilation.LowerBounds.BalancedCut
import Arlib.KnowledgeCompilation.LowerBounds.AffinePerms
import Arlib.KnowledgeCompilation.LowerBounds.Imported
