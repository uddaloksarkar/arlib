/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Arlib.Automata

Finite automata, and lower bounds on the number of states they need.

The development follows Mika Göös, Stefan Kiefer and Weiqiang Yuan, *Lower
Bounds for Unambiguous Automata via Communication Complexity* (ICALP 2022), in
`source/kc/goos/`.  The paper proves three blowup theorems about *unambiguous*
finite automata — automata with at most one accepting run per word — and it
proves all three by translating them into communication complexity.

## Why this area depends on `Arlib.KnowledgeCompilation`

The translation is the point of the paper, so the communication-complexity
machinery is not incidental here: it is where the content lives.  That machinery
already existed in this library, in `Arlib.KnowledgeCompilation.Communication`,
because the knowledge-compilation area was built on the same tools — indeed on
this very paper, which it cites as an imported result.  Two of its files,
`Communication.ConicalJunta` and `Communication.NonnegRank`, contain
Göös–Kiefer–Yuan's own Lemma 14 and the inequality `Par₁ ≥ rk⁺`, both proved.

So `Arlib.Automata` imports from `Arlib.KnowledgeCompilation` rather than
duplicating it.  If the dependency ever becomes awkward, the fix is to promote
`Communication/` to an area of its own that both depend on; nothing in either
area would have to change apart from module names.

## The two models of a two-party function

The area uses `Communication.TwoParty`, which is rectangles and covers for a
bare `F : X → Y → Bool` on arbitrary types, rather than `Communication.Rectangle`,
which fixes a partition of a *variable set*.  An automaton reads a word and the
split is at a *position*: Alice holds a prefix, Bob a suffix.  A variable
partition of a Boolean cube is the wrong shape for that, and it is the wrong
shape again for sparse set disjointness, where the two sides are the `k`-subsets
of `[n]` and there is no ambient cube at all.

`Automata.WordCoding` is the bridge between the two, and it is a step the paper
never takes: the lifting theorems are stated for a variable partition, in which
Alice's variables are *not* a contiguous block of word positions.

## Modules

* `Automata.Basic` — NFA, DFA and UFA; runs as objects rather than endpoints,
  which is what makes unambiguity statable at all; `IsRun`, `isRun_append`,
  `Reach`, `Accepts`, `Unambiguous`, and DFA ⊆ UFA.
* `Automata.Simulation` — the folklore lemmas `lem: NFA-CC` and `lem: UFA-CC`:
  an NFA with `s` states gives `Cov₁(F) ≤ s`, and a UFA gives `Par₁(F) ≤ s`.
  The second is *not* proved "the same way" as the first, contrary to the
  paper; see the module docstring.
* `Automata.DNFtoUFA` — an unambiguous `k`-DNF with `ℓ` terms over `n` variables
  compiled to a UFA with exactly `ℓ·(n+1)` states.  Unambiguity of the automaton
  needs uniqueness of the term *index*, not of the term, which is where the
  counting form of `DNF.Unambiguous` earns its keep.
* `Automata.WordCoding` — the coding between gadget variables and split words,
  and the transport of a lower bound between the two models.
* `Automata.Imported` — Balodis et al.'s unambiguous-DNF-versus-CNF-width
  separation and Göös's non-deterministic lifting theorem, as inhabited
  hypothesis bundles rather than axioms.
* `Automata.Complement` — `thm: complement`: a language with a small UFA whose
  complement needs a large NFA.  The paper's product with a length counter turns
  out to be unnecessary here.
* `Automata.Union` — `thm: union` and `thm: or`: two languages with small UFAs
  whose union needs a large UFA.  Conditional on the same two bundles as the
  knowledge-compilation area's union theorem, and on nothing else.
* `Automata.Disjointness` — `thm: separation`, via sparse set disjointness.
  Razborov's covering-set lemma is proved by counting, with an explicit family
  size; the full-rank fact about the `k`-uniform disjointness matrix is imported,
  since it is Gottlieb-type inclusion-matrix nonsingularity.
* `Automata.ErrorReduction` — the upper-bound half of `thm: error`: approximate
  non-negative rank admits no efficient error reduction, because `∨` is easy to
  approximate at error `1/4` and hard at error `10⁻⁵`.
-/

import Arlib.Automata.Basic
import Arlib.Automata.Simulation
import Arlib.Automata.DNFtoUFA
import Arlib.Automata.WordCoding
import Arlib.Automata.Imported
import Arlib.Automata.Complement
import Arlib.Automata.Union
import Arlib.Automata.Disjointness
import Arlib.Automata.ErrorReduction
