/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Structured probabilistic circuits

The knowledge-compilation area's **probabilistic-circuit** substructure: v-trees
with finite leaf domains, structured arithmetic circuits over them, and pairs of
such circuits over a *shared* v-tree.  These are distinct from the Boolean
d-DNNF / SDD circuits of `Circuits/` — they are inductive scope-decomposition
trees over ℝ, and their semantics is routed through the coreset region-tree engine
of `Arlib.Approximation.Coresets` so that a domain-reduction scheme can sparsify
them region by region.

| Module | Content |
| --- | --- |
| `StructuredCircuit` | `Vtree` (leaf domains `Fin m`), its joint assignment space `Vtree.Assign`, and the single structured circuit `Circuit V g` whose scope decomposition *is* `V`. |
| `CircuitPair` | Two circuits over the *same* `V`, compared region by region: the joint feature index `Coord`, the block-diagonal structure tensor `blockTensor`, the joint region tree `pairRegion`, the pair `CircuitPair V gP gQ` with its `valP`/`valQ` semantics, and its `Reduction` execution object. |
-/
import Arlib.KnowledgeCompilation.Probabilistic.StructuredCircuit
import Arlib.KnowledgeCompilation.Probabilistic.CircuitPair
