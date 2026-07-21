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
| `SDD` | `XDecomposition`, `IsChain`, `IsSDDAt`, `Reaches`, SDD ⊆ d-SDNNF | **done** (see G1) |
| `DNF` | terms, width, `IsKDNF`, `Unambiguous` | **done** |
| `DNFtoCircuit` | the DNF-to-d-SDNNF construction, `size ≤ ℓ·(2k+2) + 1` | **done** |
| `Arithmetic` | AC, monotone/positive AC, `supp`, the relabelling `φ`, p-decomposition, PSDD | last |

### `Communication/` — the tool

| Module | Contents | Status |
| --- | --- | --- |
| `Rectangle` | `VarPartition`, `Balanced`, Π-rectangles as locality-constrained predicate pairs, `mem_cross`, covers, rectangular partitions | **done** |
| `Measures` | `fixedCov`/`fixedPar`, `bestCov`/`bestPar`, the unfolded per-partition lower-bound form, the trivial `2^{|Z|}` upper bound | **done** |

### `LowerBounds/` — the bridge and the argument

| Module | Contents | Status |
| --- | --- | --- |
| `BalancedCut` | the v-tree separator, and the balanced partition it induces | **done** — first half of §4 |
| `RectangleLemma` | d-SDNNF of size `s` ⟹ `Par₁(f) ≤ s`; SDNNF of size `s` ⟹ `Cov₁(f) ≤ s` | **done** — discharges I2 |
| `Copies` | Step 1: `copyTerm`, `collapse`, `OneHot`, soundness + one-hot completeness, and `copyTerm_eq_of_sat` (the crux of unambiguity) — **done**; assembling `ψ^∨` as a `DNF` and counting its terms still to do | partial |
| `AffinePerms` | the Wegman–Carter family `x ↦ ax+b`, bijectivity, `|𝒫| = (q−1)q`, and exact pairwise independence | **done** — discharges I3 |
| `Imported` | I1 and I1′ as `structure`s carrying explicit bounds | **done** |
| `ClaimPerm` | the second-moment argument producing a good permutation | **done** — closes G2 |
| `Pullback` | protocol simulation as a rectangle pullback along a substitution | **done** |
| `Lifting` | Step 2 (adding permutations) and the assembly of `thm: fixed_to_best` | needs `ClaimPerm` |
| `Separation` | `thm: main`, `thm: sep`, `thm: union`, `thm: ex` | conditional on I1, I4 |

---

## 3. Imported results

Four results are used but not proved by the paper. Each becomes an explicit hypothesis — except
I3, which turned out to be within reach and is now **proved** (see below), leaving three.

**I1 — Göös–Jain–Watson-style fixed-partition hardness** (`thm: fixed_part`, line 311; and
`thm: fixed_or`, line 671). *For every `k` there is `m = k^O(1)`, a function
`g : {0,1}^m → {0,1}` with an unambiguous `k`-DNF of `2^Õ(k)` terms, and a balanced `Π`
with `NCC₀^Π(g) = Ω̃(k²)`.* This is the sole source of quantitative hardness in the whole
paper. It will be a `structure FixedPartitionHard` bundling the data and the two
properties, and every downstream theorem takes it as a parameter. **Not to be proved
here** — it is a substantial paper in its own right.

**I2 — the rectangle lemma** (`lem: rectangle`, line 299). **No longer an import: proved**,
in `LowerBounds/RectangleLemma.lean`. See §4.

**I3 — Wegman–Carter pairwise independence** (`lem: indperm`, line 423). **No longer an
import: proved**, in `LowerBounds/AffinePerms.lean`. In the end it did not need
`Probability.PolyHash` at all — the whole content is that `α·(a−b) = c−d` determines `α`,
so the result is one short algebraic argument (`existsUnique_affine`), proved directly over
an arbitrary finite field rather than only over `𝔽_{2ᵗ}`.

It is stated as an exact **count** (`card_filter_maps_eq_one`: exactly one member of `𝒫`
realises a given pair) rather than as a probability. That is sharper, it avoids introducing
a probability space the file does not otherwise need, and it is the form a second-moment
argument consumes. The two hypotheses do different jobs and both are needed: `a ≠ b` makes
the division legal, `c ≠ d` is what keeps the answer inside `𝒫` rather than a constant map.

**I4 — de Colnet–Mengel, Proposition 2** (`lem: AC`, line 527). Needed only for the
arithmetic-circuit section. Note the paper's own footnote (line 119): the cited source
states it as an iff, but only one direction actually holds. Formalize the direction that
is used, and record the other as false rather than silently omitting it.

---

## 4. The rectangle lemma — proved

`lem: rectangle` (line 299) is where circuit size meets communication complexity, and it is
the reason a lower bound on rectangle covers is a lower bound on circuits at all. The paper
imports it. **We prove it**, in `LowerBounds/RectangleLemma.lean`:

```
T.WellFormed → C.Respects T → C.Deterministic → C.vars ⊆ T.vars →
  2 ≤ T.vars.card → C.Computes f → bestPar T.vars f true ≤ C.size
```

together with the cover half, `bestCov_le_size_of_respects`, which does not need
`Deterministic`.

The route: cut the v-tree at a balanced node (`BalancedCut`, §above) to fix `X`; observe
that at every `∧`-node **at most one child carries `X`-variables** unless both lie inside
`X` (`Respects.conjSplit`, from laminarity of v-tree variable sets, `VTree.vars_laminar`);
conclude the `X`-dependence of the circuit is a *path*, not a branching structure; descend
it to an `X`-witness node (`descend`); and read off one rectangle per node. Determinism
enters exactly once, to make the descent stable across assignments agreeing on a side —
which is what upgrades the cover to a partition, `Cov₁` to `Par₁`.

### Corrections to what this section used to claim

Recorded because they were wrong for months of planning and someone will otherwise
re-derive them:

- **Proof trees / certificates were predicted to be "the next substantial piece of
  infrastructure". They were not needed at all.** Path stability of the descent delivers the
  same uniqueness directly, and nothing in the file builds a certificate. The prediction
  cost nothing here only because it was tested.
- **Indexing the rectangles by the nodes `v` with `var(v) ⊆ X` undercounts.** If `C` mentions
  no `X`-variable — entirely possible, since `X` comes from the v-tree and not from the
  circuit — no such node need exist, yet `f⁻¹(1)` still needs covering. The fix is to index
  by *all* of `Fin C.size`, with a left predicate that is vacuously true at nodes the
  descent cannot stop at. This also gives the bound `|C|` on the nose.
- **The descent must test its stopping rule before the `∧`-rule.** Otherwise it walks past a
  node lying entirely inside `X` into a child, and the sibling — also inside `X` — is no
  longer `Y`-only, which makes the lifting lemma false. This is the one genuinely delicate
  point in the proof.
- **`X ≠ ∅` is not needed** for the structural lemma, contrary to the original sketch: when
  `X = ∅` the disjunct `Disjoint _ X` holds outright. Had it been carried, every
  fixed-partition corollary would have inherited a balancedness hypothesis it does not need.

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

**G1 — pruning to reachable nodes. NOW LOAD-BEARING.** `Decomposable`, `Deterministic` and
`Respects` quantify over all node indices, whereas the paper imposes them only on nodes
reachable from the source.

This has stopped being hypothetical. `NNF.IsSDD.isdSDNNF` (SDD ⊆ d-SDNNF) currently carries
an extra hypothesis `∀ i, C.Reaches C.root i`, and **the unconditional statement is false as
formalized**: a circuit that is an SDD at its root but carries an unreachable
nondeterministic `∨`-node satisfies `IsSDD` and not `Deterministic`. This is not a proof
failure — `IsSDDAt.deterministicFrom` and `IsSDDAt.respectsFrom` are unconditional and give
both conditions at every reachable node, which is the paper's actual claim.

There are two ways out, and **the second is now clearly better**:

1. *Prune.* From a circuit satisfying the conditions on reachable nodes, build one
   satisfying them everywhere with `size` no larger. Needs a renumbering of `Fin size`;
   self-contained but genuinely fiddly.
2. *Restate.* Redefine `Decomposable`/`Deterministic`/`Respects` to quantify over reachable
   nodes only, matching the paper exactly. `Circuits/SDD` has already built the vocabulary
   this needs — `NNF.Reaches`, `DeterministicFrom`, `RespectsFrom` — so most of the work is
   done. It makes the containment unconditional and removes the gap outright rather than
   working around it.

Option 2 is a refactor of `Circuits/NNF` and `Circuits/VTree` and should be done in one
pass, not piecemeal.

**G2 — Claim `perm`. CLOSED.** The paper proves Claim `perm` (line 448) by citing Knop,
Theorem 4.2, remarking only that "an inspection of the proof shows that everything goes
through" under its own notion of balancedness (line 460). It is now **proved**, in
`LowerBounds/ClaimPerm.lean`, by a second-moment argument done entirely by *counting* —
no probability space is constructed and `Arlib.Probability` is not imported. The only
non-`ℕ` ring is `ℤ`, inside the centred square where signed subtraction is genuinely needed.

The reconstruction turned up four things worth recording.

- **The indicators are not pairwise independent.** The natural argument — "the copies land
  independently, so `Var[N] ≤ E[N]`" — is wrong, and so is the appeal to I3 as stated: `σ`
  is a *permutation*, so two distinct copies can never land on the same point, and the
  family is pairwise **negatively correlated**. `E[XⱼXⱼ']` is `|S|(|S|−1)/(q(q−1))`, not
  `|S|²/q²`. The conclusion `Var[N] ≤ E[N]` survives — it is `(m−1)(|S|−1)/(q−1) ≤ m|S|/q`,
  true because `|S| ≤ q` — but the covariance has to be handled explicitly.
- **The copies must be assumed distinct.** Writing `S_i = {y_{i,1}, …, y_{i,m}}` quietly
  assumes the `m` copies are distinct field elements; the second-moment step is false
  without it. It appears as an injectivity hypothesis.
- **Balancedness is far more than the argument needs, and the slack is load-bearing.** Only
  `|F| ≤ 4·|S|` is used — a full factor weaker than balancedness's `|F| ≤ 3·|S|` — and the
  two-sided bound is not needed at all. The `4` is sharp for this route.
- **The claim as stated in the paper indexes the wrong partition.** It is written with `Π`,
  but `Π` partitions `var(ψ)` while `σ` permutes `V = var(ψ^∨)`. The partition actually in
  play is `Γ`, of `var(ψ') = V ∪ Z` with `Z` the `2t` variables encoding `σ`. `Γ` balanced
  on `V ∪ Z` gives only `3|Γ_k ∩ V| ≥ |V| − 2|Z|`, **not** `≥ |V|` — so the `3`-form does
  not apply to it, and one must use the general form with `A := Γ₀ ∩ V`, `B := Γ₁ ∩ V`.
  This is exactly why the extra slack above matters: the call typechecks under `4` and not
  under `3`, with room to spare since `|Z| = O(log |V|)`.

**G3 is also not needed** for this: the file works over an arbitrary finite field, so the
`n' = 2^t` assumption never enters.

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
