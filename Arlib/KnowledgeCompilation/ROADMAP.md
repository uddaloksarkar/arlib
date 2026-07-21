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
| `Copies` | Step 1: `copyTerm`, `collapse`, `OneHot`, soundness + one-hot completeness, `copyTerm_eq_of_sat` (the crux of unambiguity), `copyDNF` and its term count | **done** — the *counting* form of unambiguity needs the enumeration of choice functions, which is in `Lifting` |
| `AffinePerms` | the Wegman–Carter family `x ↦ ax+b`, bijectivity, `|𝒫| = (q−1)q`, and exact pairwise independence | **done** — discharges I3 |
| `Imported` | I1 and I1′ as `structure`s carrying explicit bounds | **done** |
| `ClaimPerm` | the second-moment argument producing a good permutation | **done** — closes G2 |
| `Pullback` | protocol simulation as a rectangle pullback along a substitution | **done** |
| `Lifting` | the canonical choice-function enumeration and the counting unambiguity of `ψ^∨`; Step 2 (`zBlock`, `permTerm`, `permDNF`) with its term count, width and unambiguity; and `thm: fixed_to_best` as a `PartitionMap` | **done** |
| `Separation` | `thm: main` and `thm: sep`, with both bounds explicit | **done** — `thm: main` conditional on I1, `thm: sep` on I1 and I5; `thm: union`, `thm: ex` still to do |

---

## 3. Imported results

Five results are used but not proved by the paper. Two of them, I2 and I3, turned out to be
within reach and are now **proved** here (see below and §4), so they are no longer imports. The
remaining three — I1, I4, I5 — each become an explicit hypothesis. I5 was not on the original
list of four: it surfaced only when `thm: sep` was actually assembled, and it is used nowhere
else.

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

**I5 — SDD is closed under complementation in polynomial time** (Darwiche; used at line 465,
inside the two-sentence proof of `thm: sep`). *From an SDD for `f` respecting `T` one can build
an SDD for `¬f` respecting `T` of size polynomial in the original.* **In Lean** as
`Imported.SDDComplementation`, with the polynomial made explicit as `c·|C|^d` per §5. Two
things are pinned down that the paper leaves implicit and that a consumer needs: the v-tree is
*preserved* (complementation negates terminals and leaves the structure alone), and the output
circuit has no unreachable nodes — the latter only because `Respects`/`Deterministic` quantify
over all node indices while `IsSDDAt` constrains only what is below the source, i.e. gap G1.

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

**What came out.** `Separation.thm_main` states both halves explicitly and neither mentions
`O(·)`: with `H : FixedPartitionHard univ k termBound coverBound`, `m` copies, the field `F`
and the `z`-index type `Zι`,

* `ψ'` has at most `|𝒫|·(termBound·m^k)` terms of width at most `|Zι| + k·m`, hence a d-SDNNF
  of size `|𝒫|·(termBound·m^k)·(2(|Zι| + k·m) + 2) + 1` respecting any prescribed v-tree, where
  `|𝒫| = (|F| − 1)·|F|`;
* every structured DNNF computing `¬ψ'` has size at least `coverBound`.

The paper's `n^Ω̃(log n)` is the comparison of those two numbers under its choice of parameters,
and that comparison is the *only* asymptotic step left in the area. It has not been carried
out: doing it needs a family of fields `F` of order `2^t`, and nothing here builds one.

---

## 6. Recorded gaps

Deferred obligations, and the record of what closing them taught. G1, G2, G3 and G6 are
**closed**; G4 is partly closed; G5 remains. Entries are kept after closure because several
of them were wrong in instructive ways, and the corrections are worth more than the
original statements.

**G1 — the conditions must be relativized to reachable nodes. CLOSED.**
`Decomposable`, `Deterministic` and `Respects` used to quantify over *all* node indices,
whereas the paper imposes them only on nodes reachable from the source. They are now
relativized: `NNF.DecomposableFrom`, `DeterministicFrom` and `RespectsFrom` take a root, and
the absolute forms are *definitionally* the relativized ones at `C.root`.

`NNF.Reaches` moved from `Circuits/SDD.lean` down to `Circuits/NNF.lean`, where it belongs.
`NNF.IsSDD.isdSDNNF` is now **unconditional**, and `Imported.SDDComplementation` no longer
carries a reachability field to work around the mismatch.

Two corrections to this entry's own earlier account:

- The fix worked cheaply *only* because the absolute predicates were defined as the
  relativized ones at the root, definitionally. `IsSDDAt.deterministicFrom` already concluded
  in the `…From` form, so it *is* a proof of `Deterministic` with no glue, and no use site
  needed an unfolding lemma. Restating the predicates independently would have forced an
  unfolding step at every consumer.
- "Our classes are strictly contained in the paper's, so every lower bound over them is
  weaker" named the wrong harm. The lower bounds take these predicates as *hypotheses*, so the
  old reading made them apply to fewer circuits — a silent weakening, but not the visible
  break. What was actually broken was the SDD ⊆ d-SDNNF containment, whose unconditional form
  was **false** as formalized.

Worth naming for symmetry: the *upper*-bound half of `thm_main` now asserts a formally weaker
property of the circuit it builds. No content is lost — `dnfCircuit` satisfies the all-indices
version and the paper's claim is the reachable one — but that is the price of making both
halves speak about the paper's classes rather than about two different ones.

The anticipated "lemma that the descent stays within the reachable set" was not needed:
threading reachability alongside the node index through the recursion is strictly less work,
because the recursive structure hands you the child-step exactly where it is required.

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

**G3 — the `n' = 2^t` simplification. MOOT.** The construction assumes the variable count is a
power of two (line 421), with the general case handled by padding with dummy variables. It
never arose: `ClaimPerm` works over an arbitrary finite field, and `Lifting` takes the
representation `rep : 𝒫 → (Zι → Bool)` as a parameter whose only requirement is injectivity on
`𝒫`, so no relation between `|F|` and `2^{|Zι|}` is ever assumed. `Lifting.exists_rep_injective`
shows such a `rep` exists as soon as `|F|² ≤ 2^{|Zι|}`, which for `|F| = 2^t` is the paper's own
`|Zι| = 2t`. The variables of `ψ'` outside the image of the copies are exactly the paper's
padding, and they cost nothing.

**G5 — the v-tree of a lower-bound circuit must span every variable of `ψ'`.** The lower bounds
in `Separation` carry the hypothesis `T.vars = univ`. The paper's `def: vtree` (line 150)
builds this in — its v-trees are v-trees *for the variable set of the function* — so the
hypothesis is faithful, but it is not vacuous here, where `Respects` relates a circuit to an
arbitrary tree. It is load-bearing rather than cosmetic: the rectangle lemma hands back a
balanced partition of `var(T)`, while Claim `perm`'s cardinality bounds are about all of `|F|`,
so a v-tree omitting variables would need those bounds re-derived (and, for the dummy
variables, an argument that they may be added back to the tree without changing the circuit).

**G6 — the parameters are instantiated; the asymptotic packaging is not.** *(Non-vacuity half
closed, in `LowerBounds/Instance.lean`.)* `thm: main` takes `|F| ≥ 8|Zι|`, `|F|² ≤ 2^{|Zι|}`
(through `rep`), an injection `ι × Fin m ↪ F` and `6|ι| < m`. All four now hold simultaneously
in Lean, for every `n`, at `|ι| = n`, `m = 6n + 1`, `F = GaloisField 2 t` and `|Zι| = 2t` with
`t = 7 + ⌈log₂(n(6n+1))⌉` (`Instance.params_satisfiable`); `Instance.thm_main_instance` and
`Instance.thm_sep_instance` apply the headline theorems to them, leaving
`Imported.FixedPartitionHard` — and, for `thm: sep`, `SDDComplementation` — as the only
hypotheses. The `t ≥ 7` is sharp (`16t ≤ 2^t` fails at `t = 6`), but "any `t` with
`2^t ≥ n(6n+1)`" is *not* good enough: `t` must be **logarithmic**, since the upper bound
carries the factor `|𝒫| ≈ |F|²` and the paper's `n^{k+4}` term count is `n⁴` precisely because
`|F| = O(n²)`. `Instance.card_maps_Fld_le` records `|𝒫| ≤ (256·n(6n+1))²`.

What remains is the asymptotic packaging, and the obstacle is not the witness. The paper's
`n = k^{O(1)}`, `termBound = 2^{Õ(k)}` and `coverBound = 2^{Ω̃(k²)}` are properties of
`Imported.FixedPartitionHard` *as a family indexed by `k`*, while the bundle is stated for one
`k` at a time with both constants free. Turning the two explicit numbers into `n^{Ω̃(log n)}`
therefore needs a family version of that bundle plus a definition of `Õ`/`Ω̃` — the
"substantial development consumed exactly once" that `Imported.lean` declines.

---

## 7. What is left

The spine — `thm: main` and `thm: sep`, both halves, both bounds explicit — is closed. What
remains, in the order it is worth doing:

1. ~~**Instantiate the parameters**~~ (G6) — *done*, `LowerBounds/Instance.lean`. What is left
   of it is the asymptotic packaging: turning the two explicit bounds of `thm_main` into the
   paper's `n^{Ω̃(log n)}`. This is the only remaining asymptotic step in the area, and it now
   depends on a *family* version of `Imported.FixedPartitionHard` carrying `n = k^{O(1)}`,
   `termBound = 2^{Õ(k)}` and `coverBound = 2^{Ω̃(k²)}`, not on anything about the witness.
2. **`thm: union` and `thm: ex`** (T11, T12). `Imported.UnionHard` and the `Par`-side pullback
   (`Lifting.hasPartitionOfSize_of_hasPartitionOfSize_permDNF`) are both already in place, so
   T11 is the same assembly as `thm: main` with `Par₁` in place of `Cov₀`; T12 is a short
   circuit construction on top of it.
3. **Gap G1** — restate `Decomposable`/`Deterministic`/`Respects` over reachable nodes. This
   deletes a field of `Imported.SDDComplementation` and a hypothesis of `IsSDD.isdSDNNF`.
4. **Gap G5** — remove the `var(T) = var(ψ')` hypothesis of the lower bounds, if it is worth it.
5. `Circuits/Arithmetic` and Part D.

When you add a language to `Circuits/`, add the containment lemma that places it in the
hierarchy (SDD ⊆ d-SDNNF ⊆ d-DNNF ⊆ NNF). The containments are what make a lower bound for
one class say anything about another, and they are cheap to prove at the time and painful
to retrofit.
