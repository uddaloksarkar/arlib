/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib.Approximation

**Relative-error approximation, and the data structures that achieve it.**

An approximation algorithm's guarantee is a *window*: the value it reports lies
in `[lo · v, hi · v]` around the truth.  Windows compose, sum, telescope, and
must finally be calibrated so that the composed window is the one the theorem
promises.  That algebra is problem-independent, and it is the area's foundation
(`MulError`).

Built on it, `Coresets/` develops **domain reduction for `ℓ¹` linear tests**: a
weighted set of points, each carrying a feature vector, is summarised by a much
smaller weighted set that reproduces `∑ᵢ μᵢ |⟨y, vᵢ⟩|` — the weighted sum of
*absolute* linear tests — for **every** query `y` simultaneously.  That
functional is `‖A y‖₁` for the matrix `A` with rows `μᵢ vᵢᵀ`, so the sets that do
this are exactly the outputs of an `ℓ¹` subspace embedding, and Lewis-weight row
sampling is how one is produced.  Lewis weights themselves are *not* here: this
area formalizes what one may do with such a reduction once one has it, and a
development that needs one takes the sampling guarantee as an explicit
hypothesis, in the `KnowledgeCompilation` style.

The uniformity over queries is the point of the whole subject.  A reduction built
now will be tested later, against a query that is not yet determined — by the
coordinates a dynamic program has not reached, or by the sibling region of a
circuit that has not been processed.  Everything under `Coresets/` is organised
around propagating a guarantee that does not know what it will be asked.

| Module | Content |
| --- | --- |
| `MulError` | Two-sided multiplicative windows `Between lo hi a b`, their composition, summation and telescoping, and the `δ = ε/(3n)` calibration — with `(1+a)^n ≤ 1 + 2na` proved by elementary induction rather than through the exponential. Mentions no data structure at all. |
| `Coresets.Basic` | The linear test `dot`, weighted point sets `WPS ι d`, the evaluation functional `WPS.E`, and the unreduced set `WPS.exact` on a whole finite domain. |
| `Coresets.Embedding` | `Embeds lo hi U C` — `C` reproduces every linear test on `U` inside the window. Reflexivity, composition (the source of the `(1 ± δ)^L` exponent), widening, and the family-of-queries form in which one factor's reduction is consumed. |
| `Coresets.Tensor` | The Cartesian product of two weighted point sets with features combined **bilinearly**, the two Fubini identities that view a linear test on the product as a linear test on either factor, and hence the composition theorem: reducing each factor reduces the product. The Hadamard product is the diagonal special case. |
| `Coresets.Linear` | Reparametrising features by a fixed matrix is free — `⟨y, Lv⟩ = ⟨Lᵀy, v⟩`, so a reduction survives with the same window and the same number of points. This is why a layer of sum gates costs nothing and only product steps are ever sparsified. |
| `Coresets.RegionTree` | The assembled engine: a tree of regions whose feature map is bilinear in its children's, a bottom-up choice of reduced set at each internal node, and the **propagation invariant** — if every internal node was sparsified to within `(1 ± δ)`, the root reproduces every linear test on the entire exact domain to within `(1 ± δ)^{steps}`. |

This is the area root; it re-exports the modules below.
-/

import Arlib.Approximation.MulError
import Arlib.Approximation.Coresets.Basic
import Arlib.Approximation.Coresets.Embedding
import Arlib.Approximation.Coresets.Tensor
import Arlib.Approximation.Coresets.Linear
import Arlib.Approximation.Coresets.RegionTree

import Arlib.Approximation.LewisWeights
