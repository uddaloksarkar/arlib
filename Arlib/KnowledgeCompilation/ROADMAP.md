# `Arlib.KnowledgeCompilation` — roadmap

Entry point for anyone picking this area up. Read this file, then
[`PAPER-INVENTORY.md`](PAPER-INVENTORY.md) for the statement-by-statement catalogue
of the source paper.

**Source.** Harry Vinall-Smeeth, *Structured d-DNNF Is Not Closed Under Negation*,
IJCAI 2024 (arXiv:2403.03362), in `source/kc/arXiv.tex`. Line numbers throughout the
inventory refer to that file.

**What the paper proves.** Structured d-DNNF (d-SDNNF) does not support polynomial-time
negation, disjunction, or existential quantification; consequently d-SDNNF is strictly
more succinct than SDD, and the analogous gap holds between the monotone-arithmetic
analogues dSD-AC and PSDD. The engine is a reduction to *best-partition* non-deterministic
communication complexity, reached from the *fixed-partition* model by a
copy-and-permute construction.

---

## 1. Design principles

Three commitments shape every file here. Please do not break them without saying so
loudly.

### 1.1 Circuits are DAGs. Never trees.

An NNF is a directed acyclic graph and `|C|` is its **vertex count**. The inductive-tree
encoding, which is what one reaches for first in Lean, is wrong for this area: a DAG
stores a shared subcircuit once, and unfolding it to a tree can blow the vertex count up
exponentially.

This matters because of the *direction* of the results. A lower bound on tree size does
**not** imply a lower bound on DAG size. Formalizing trees would therefore silently prove
a strictly weaker theorem than the paper's, while looking identical on the page. So we pay
for the DAG up front, in `Circuits/NNF.lean`: nodes are indices `Fin size`, `gate i` is
the label of node `i`, and `child_lt` says every child of `i` has a strictly smaller
index.

That one field does three jobs: acyclicity, a topological order, and the termination
measure for every recursion over a circuit. Every recursion in this area is on the node
index, and `Circuits/NNF.lean` shows the pattern (`valAt`, `varsAt`, `valAt_congr`).

Concrete rule for contributors: **if you find yourself writing `inductive Circuit`, stop.**
Whatever you were about to prove is either a size-blind semantic fact — in which case it
belongs on the function, not the circuit — or it is a size bound, in which case the tree
encoding will quietly make it false.

### 1.2 Nodes, not subcircuits.

The paper writes `C(g)` for the subcircuit rooted at `g` and leans on it constantly. We do
not define a subcircuit operation. Every use of `C(g)` in the paper is a claim about the
*function computed at the node*: determinism compares `sat(C(gₗ))` with `sat(C(gᵣ))`,
structuredness compares `var(C(gₗ))` with `var(t_ℓ)`. Those are `valAt` and `varsAt` at a
node, and node-indexed families are cheaper to carry than reconstructed circuits.

The same discipline applies to the recursive definitions still to come: SDD is a predicate
`IsSDDAt C i t` on a node and a v-tree node, not a recursively rebuilt circuit.

### 1.3 Imported results are hypotheses. Never axioms.

The paper's headline theorems rest on four results proved elsewhere. None of them is
`axiom`-ed here. Each is a named `structure` or hypothesis, threaded explicitly into the
theorems that consume it, so that a reader of a statement can see exactly what it is
conditional on.

This is not pedantry: two of the four are the *entire* quantitative content of the main
theorem. If they were axioms, `thm: main` would typecheck while proving nothing.

See §3 for the list and the status of each.

---

## 2. Module plan

Three directories, mirroring the shape of the argument.

### `Circuits/` — the objects

| Module | Contents | Status |
| --- | --- | --- |
| `NNF` | DAG encoding, `valAt`, `eval`, `varsAt`, `valAt_congr`, `Decomposable`, `Deterministic`, `IsDNNF`, `IsdDNNF` | **done** |
| `VTree` | v-trees, `WellFormed` (⟺ no repeated leaf), `IsSubtree`, `Respects`, `IsSDNNF`, `IsdSDNNF`, `Respects.decomposable` | **done** |
| `SDD` | `X`-decomposition, `IsSDDAt`, SDD ⊆ d-SDNNF | next |
| `DNF` | terms, width, `IsKDNF`, `Unambiguous` — **done**; the DNF-to-d-SDNNF upper bound still to do, now unblocked by `VTree` | partial |
| `Arithmetic` | AC, monotone/positive AC, `supp`, the relabelling `φ`, p-decomposition, PSDD | last |

### `Communication/` — the tool

| Module | Contents | Status |
| --- | --- | --- |
| `Rectangle` | `VarPartition`, `Balanced`, Π-rectangles as locality-constrained predicate pairs, `mem_cross`, covers, rectangular partitions | **done** |
| `Measures` | `fixedCov`/`fixedPar`, `bestCov`/`bestPar`, the unfolded per-partition lower-bound form, the trivial `2^{|Z|}` upper bound | **done** |

### `LowerBounds/` — the bridge and the argument

| Module | Contents | Status |
| --- | --- | --- |
| `RectangleLemma` | d-SDNNF of size `s` ⟹ `Par₁(f) ≤ s`; SDNNF of size `s` ⟹ `Cov₁(f) ≤ s` | the crown jewel — see §4 |
| `Copies` | Step 1: `copyTerm`, `collapse`, `OneHot`, soundness + one-hot completeness — **done**; unambiguity of `ψ^∨` and the term count still to do | partial |
| `AffinePerms` | the Wegman–Carter family `x ↦ ax+b` over `𝔽_{2ᵗ}`, and its pairwise independence | reuse `Probability.PolyHash` |
| `ClaimPerm` | the probabilistic argument producing a good permutation (Chebyshev) | see §3, gap G2 |
| `Lifting` | Step 2 and `thm: fixed_to_best`: the protocol simulation | |
| `Separation` | `thm: main`, `thm: sep`, `thm: union`, `thm: ex` | conditional on I1, I4 |

---

## 3. Imported results

Four results are used but not proved by the paper. Each becomes an explicit hypothesis.

**I1 — Göös–Jain–Watson-style fixed-partition hardness** (`thm: fixed_part`, line 311; and
`thm: fixed_or`, line 671). *For every `k` there is `m = k^O(1)`, a function
`g : {0,1}^m → {0,1}` with an unambiguous `k`-DNF of `2^Õ(k)` terms, and a balanced `Π`
with `NCC₀^Π(g) = Ω̃(k²)`.* This is the sole source of quantitative hardness in the whole
paper. It will be a `structure FixedPartitionHard` bundling the data and the two
properties, and every downstream theorem takes it as a parameter. **Not to be proved
here** — it is a substantial paper in its own right.

**I2 — the rectangle lemma** (`lem: rectangle`, line 299). Attributed to
Pipatsrisawat–Darwiche and Bova et al. Unlike I1 this is *within reach* and is the single
highest-value target in the area; see §4.

**I3 — Wegman–Carter pairwise independence** (`lem: indperm`, line 423). Provable, and
mostly already present: `Arlib.Probability.PolyHash` builds the degree-`<k` polynomial
family over a finite field and `Arlib.Probability.KWiseIndependent` states the interface.
The paper's family is the `k = 2` case restricted to `a ≠ 0` (so that the maps are
permutations), which is a genuine but small difference from `polyHash` — the restriction
changes the normalisation to `1/(n'(n'-1))` and requires `c ≠ d`.

**I4 — de Colnet–Mengel, Proposition 2** (`lem: AC`, line 527). Needed only for the
arithmetic-circuit section. Note the paper's own footnote (line 119): the cited source
states it as an iff, but only one direction actually holds. Formalize the direction that
is used, and record the other as false rather than silently omitting it.

---

## 4. The crown jewel: the rectangle lemma

`lem: rectangle` (line 299) is where circuit size meets communication complexity, and it
is the reason a lower bound on rectangle covers is a lower bound on circuits at all:

> If `f` admits a d-SDNNF of size `s` then `Par₁(f) ≤ s`; if `f` admits an SDNNF of size
> `s` then `Cov₁(f) ≤ s`.

The paper imports it. We should prove it, for three reasons. It is the only step that
touches both halves of the area, so it is what keeps `Circuits/` and `Communication/`
honest against each other. It is the step whose hypotheses are easiest to get subtly
wrong — in particular *which* balanced partition the v-tree yields, and that is exactly
where the `Fin size` DAG encoding earns its cost. And unlike I1 it is a self-contained
combinatorial argument: pick a v-tree node whose variable set is a constant fraction of
the whole, cut the circuit there, and read off one rectangle per `∧`-node above the cut,
with determinism upgrading the cover to a partition.

Everything else in `LowerBounds/` can be developed against its statement before it is
proved, so it need not block progress — but it should not stay a hypothesis
indefinitely. Treat it as the area's main open obligation.

---

## 5. Asymptotics

The paper is written in `Õ` / `Ω̃` throughout, but its proofs produce explicit bounds:
`ψ'` has `O(ℓ · n^{k+4})` terms because there are at most `m^k = (cn)^k` terms derived from
each term and `|𝒫| = n'(n'-1) = O(n⁴)` permutations.

**State the explicit bound; derive the asymptotic packaging separately, if at all.** A Lean
statement quantified over an unspecified `O(·)` is both harder to prove and weaker than the
inequality the proof actually gives. Concretely, `thm: fixed_to_best` should conclude with
a term count of `ℓ · (cn)^k · n'(n'-1)`, not with an asymptotic class.

The one place asymptotics are unavoidable is the final separation, `n^Ω̃(log n)`, where the
statement genuinely is about a family indexed by `k`. Keep that packaging in
`LowerBounds/Separation.lean` and nowhere else.

---

## 6. Recorded gaps

Deferred obligations. Each is a real hole; none is currently load-bearing.

**G1 — pruning to reachable nodes.** `Decomposable` and `Deterministic` in `Circuits/NNF`
quantify over all node indices, whereas the paper imposes them only on nodes reachable
from the source. Our classes are therefore *contained* in the paper's, which weakens any
lower bound stated over them. The fix is a lemma: from a circuit satisfying the conditions
on reachable nodes, build one satisfying them everywhere with `size` no larger. This
requires a reachability predicate and a renumbering, and is pure bookkeeping. Nothing
proved so far depends on it, but the final separation theorems will.

**G2 — Claim `perm` has no proof in the paper.** Claim `perm` (line 448) is the technical
heart of the lifting, and the paper proves it by citing Knop, Theorem 4.2, noting only
that "an inspection of the proof shows that everything goes through" under the relaxed
notion of balancedness (line 460). Formalizing it therefore means *reconstructing* the
argument, not transcribing one: a second-moment argument over the family `𝒫`, using
pairwise independence (I3) and Chebyshev (`ProbSpace.chebyshev`) to show that some
`σ ∈ 𝒫` sends, for every `i` and every side `k` of the partition, at least one copy
`y_{i,j}` to that side. Budget for this accordingly; it is the hardest genuinely-provable
step in the paper.

*Amended.* The claim that the paper's balancedness is a relaxation needs care. For a
genuine partition, `|Z| ≤ 3·min(|X|,|Y|)` is **equivalent** to `|Z|/3 ≤ |X| ≤ 2|Z|/3`
(proved as `VarPartition.balanced_iff_left`), so the paper's notion is not weaker than the
familiar two-sided one. Whatever Knop's proof assumes must therefore be *stricter* — most
likely an exact split `|X| = |Y|`. Establish which before starting, because the difficulty
being worked around is not the one the inventory originally described.

**G4 — no concrete circuit instantiates the definitions.** `Decomposable`, `Deterministic`,
`Respects` and `IsdSDNNF` are so far only ever *pushed around* by general lemmas; nothing
checks them against an object whose answer is known independently. That is exactly how an
encoding error survives — a `∀ g, ∃ t` misread as `∃ t, ∀ g` would support every general
lemma we currently have. `Arlib.MarkovChains` guards against this with `Chains/`, and this
area needs the analogue.

An attempt was made and abandoned; what it cost is worth recording, because it is a real
consequence of the `Fin size` DAG encoding chosen in §1.1:

- `child_lt` *is* dischargeable by `decide` — it is purely syntactic in `gate`.
- Nothing routed through `valAt` or `varsAt` is. Both are well-founded recursions, and
  `WellFounded.fix` does not reduce in the kernel, so `decide` gets stuck no matter how
  small the circuit. Every value must come from the unfolding lemmas.
- Worse, `fin_cases`/`interval_cases` will not fire on a node index `i : Fin C.size`,
  because `C.size` is not syntactically a numeral. The index has to be destructured and the
  size unfolded by hand before any case analysis begins.

So a concrete circuit costs roughly a lemma per node, not a `decide`. It is still worth
building one — the validation is real — but budget for it, and do not expect automation to
carry it. A worked instance of the paper's own Figure 1 (`source/kc/arXiv.tex:238`) is the
natural target, since the caption states the computed formula independently.

**G3 — the `n' = 2^t` simplification.** The construction assumes the variable count is a
power of two (line 421), with the general case handled by padding with dummy variables.
Follow the paper and assume it; the padding is uninteresting but should eventually be
discharged if the separation is to be stated for all `n`.

---

## 7. Where to start

In order, and each is a commit:

1. `Circuits/VTree` — v-trees and `Respects`. Small, and unblocks both `SDD` and the
   rectangle lemma.
2. `Communication/Rectangle` — rectangles, covers, partitions. Independent of everything
   above; can be done in parallel.
3. `Communication/Measures` — `Cov`, `Par`, and the fixed/best distinction.
4. `LowerBounds/RectangleLemma` — see §4.
5. `LowerBounds/Copies` — Step 1. Fully proved in the paper (lines 395–416) and entirely
   self-contained, so it is the best place to go if the rectangle lemma stalls.

When you add a language to `Circuits/`, add the containment lemma that places it in the
hierarchy (SDD ⊆ d-SDNNF ⊆ d-DNNF ⊆ NNF). The containments are what make a lower bound for
one class say anything about another, and they are cheap to prove at the time and painful
to retrofit.
