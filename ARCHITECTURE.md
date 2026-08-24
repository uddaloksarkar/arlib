# Arlib architecture

Arlib is the foundation layer in a two-package system:

```text
Mathlib -> Arlib -> ArlibCommunity
```

Arlib contains reusable representations and mathematical infrastructure.
ArlibCommunity contains named procedures, concrete constructions, and their
algorithmic analyses. See `BOUNDARY.md` for the statement-level ownership test
and `BOUNDARY_MANIFEST.tsv` for the module migration ledger.

## Import structure

`Arlib.lean` re-exports the core area roots:

```text
Prelude
Combinatorics
Communication
Probability
InformationTheory
MarkovChains
MarkovChains.Continuous
Approximation
MDP
GameTheory
KnowledgeCompilation
Automata
```

There are three supported import granularities:

| Scope | Example |
| --- | --- |
| complete core | `import Arlib` |
| one area | `import Arlib.Probability` |
| one module | `import Arlib.Probability.FinDist` |

Continuous Markov infrastructure has a separate sub-root because it uses the
explicit `Arlib.MarkovChains.Continuous` namespace. Finite Markov infrastructure
keeps `Arlib.MarkovChains`. The two roots are compatible and are both included
by `import Arlib`.

## Source areas

The hard-split core has 144 Lean files under `Arlib/`. Counts below include an
area root where one exists.

| Area or support family | Files | Core responsibility |
| --- | ---: | --- |
| Prelude | 1 | shared error notation |
| Combinatorics | 8 | generic finite-family lemmas |
| Communication | 3 | reusable functions and rectangles |
| Probability | 61 | laws, spaces, kernels, moments, coupling, and total variation |
| InformationTheory | 16 | reusable entropy and information infrastructure |
| MarkovChains | 24 | generic finite and continuous chain theory |
| Approximation | 7 | reusable approximation predicates and representations |
| MDP | 2 | finite MDP representation |
| GameTheory | 2 | reusable game-theoretic foundations |
| KnowledgeCompilation | 8 | circuit and representation syntax |
| Automata | 3 | automaton representations |
| Convexity | 8 | polytopes, log-concavity, and geometric inequalities |
| Lattice | 1 | lattice representation support |

Counts are descriptive, not an ownership rule. A generic lemma needed by an
algorithm may belong in core even when its motivating application is in
community; a theorem about a concrete chain belongs in community even if its
proof is largely analytic.

## Namespace rules

- Core declarations use `Arlib.*`.
- The namespace follows the public module family.
- Finite and continuous Markov declarations are separated as described above.
- Arlib must not declare in or import `ArlibCommunity.*`.
- Compatibility exports are acceptable only for core-to-core API moves; they
  must not recreate ownership of a community algorithm in core.

## Dependency layering

Core imports should point toward more general infrastructure. Probability and
combinatorics sit low in the graph; information theory, Markov chains,
approximation, MDPs, circuits, and automata build on them. No edge may point to
ArlibCommunity. The boundary audit checks this forbidden edge directly, while a
successful `lake build Arlib` checks that retained core modules are closed under
their imports.

## Maintained invariants

- `scripts/BoundaryAudit.sh` rejects community imports and ownership-manifest
  regressions.
- `scripts/DeclarationInventory.sh` records source declarations independently of
  namespace renames; `DECLARATION_INVENTORY.baseline.txt` is the pre-split
  baseline used by the paired community audit.
- `scripts/AxiomAudit.lean` traverses every reachable core declaration and
  rejects `sorryAx` or any project axiom beyond the permitted Mathlib
  foundations.
- `lake build Arlib` builds the complete public core, including both Markov
  families.

Contributor conventions and release commands are documented in
`CONVENTIONS.md` and `CONTRIBUTING.md`; API changes are recorded in
`MIGRATION.md`.
