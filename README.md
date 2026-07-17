# Arlib

A curated, **mathlib-style** library of reusable Lean 4 + Mathlib results,
distilled from the meelgroup formalization projects. The goal is a single,
clean, `sorry`-free library that others can `import` and build on — rather than
re-proving the same infrastructure in every new project.

> **Status.** Early. The first area — finite/discrete **probability** — is
> migrated, building green, and axiom-clean. More areas follow (see
> [Roadmap](#roadmap)).

## Design philosophy

Emulating Mathlib: general, reusable content lives here under a single root
namespace (`Arlib`), organized by mathematical area, with docstrings and a root
module that re-exports everything. Project-specific *capstone* theorems (the
correctness proof of a particular algorithm) stay in their own repositories;
Arlib holds the **general lemmas underneath them** that are worth sharing.

Each area is a directory `Arlib/<Area>/` with an area root `Arlib/<Area>.lean`
that re-exports the area's modules. The library root `Arlib.lean` re-exports all
area roots, so `import Arlib` gives you everything and `import Arlib.Probability`
gives you one area.

## What's here

### `Arlib.Probability` — finite/discrete probability

25 modules, ~5.3k LOC, ~220 lemmas/theorems, 40 definitions/structures. Finite
probability spaces and the machinery built on them:

| Module | Content |
| --- | --- |
| `FinProb`, `ProbSpace` | Finite probability space; mass/probability; `Pr` (incl. disjoint-union additivity, complement), expectation `Ex`. |
| `Markov` | Linearity of expectation, **Markov's inequality**, variance (`Var`, `Var_eq`), **Chebyshev**. |
| `Conditioning` | Conditioning a `FinProb` on an event: `cond`, conditional `Pr`/`Ex`. |
| `Median`, `FirstBad` | Median-of-means amplification; first-failure decomposition. |
| `IntersectionTailBound` | Tail bound for an intersection of events. |
| `Independence`, `CoordIndep` | Independence of events and of coordinates. |
| `CondExp`, `CondExpConstruction`, `CondExpLinear` | Conditional expectation interface (fixed-variable + tower rules) and its concrete construction; linearity. |
| `ProductSpace`, `RunProduct`, `UniformCoin` | Product probability spaces; independent-runs product; uniform coin/grid model. |
| `CondExpProd`, `CondExpProdData`, `ReduceModel` | Conditional expectation over product spaces; model reduction. |
| `ContCoinProto`, `MixedCoinSpace`, `MixedRunProduct`, `MixedCoordIndep`, `MixedCondCELinear`, `MixedCondProd` | Continuous/mixed coin protocol and the mixed (continuous × discrete) product space and its independence / conditional-expectation algebra. |
| `ProbSpaceValidation` | Sanity/validation lemmas for the space axioms. |

### `Arlib.Combinatorics` — generic `Finset` / `List` helpers

Fully generic (`[DecidableEq α]` / `[LinearOrder α]`) helper lemmas that recurred
across several projects but are not in Mathlib under an obvious name.

| Module | Content |
| --- | --- |
| `Combinatorics.Finset` | Membership in a list-fold union (`mem_foldr_union`, `mem_foldr_union_map`); powerset of a union as an image of a product (`image_union_powerset`); recovering a summand of a disjoint union (`union_inter_left`/`right`); tiling an interval by consecutive blocks (`Ico_biUnion_blocks`); a concatenation counting bound `|A|·|B| ≤ |C|` (`concat_injOn`, `card_mul_le_of_concat_subset`). |
| `Combinatorics.BigOperators` | Diagonal/off-diagonal split of a double sum (`sum_matrix_diag_offdiag`); products of an idempotent function over subsets/unions/`biUnion`s (`prod_mul_prod_subset`, `prod_union_idem`, `prod_biUnion_idem`); a surjection–product inequality (`prod_le_prod_comp_of_surj`); products of `{0,1}`-valued functions (`prod_zero_or_one`, `zo_prod_eq_one_iff`). |
| `Combinatorics.ListFold` | Upper/lower bounds for `List.foldr min` (`foldr_min_le_init`, `foldr_min_le_mem`, `le_foldr_min`, `lt_foldr_min`). |

### `Arlib.Prelude`

Small shared notation, currently the multiplicative **relative-error interval**
`relErr ε b = [(1-ε)·b, (1+ε)·b]` and `mem_relErr`.

## Build

Pinned to **Lean `v4.15.0`** and **Mathlib `v4.15.0`** (same as the source
projects, so material migrates with zero porting).

```bash
lake exe cache get   # fetch prebuilt Mathlib oleans (don't compile Mathlib from source)
lake build           # builds everything; the root re-exports every area
```

`import Arlib` in your own file to use the library.

## Verifying "done" (axiom hygiene)

Arlib holds itself to the project standard: `sorry`-free and axiom-clean. Every
result depends only on Mathlib's three foundational axioms.

```bash
lake build   # must emit zero `declaration uses 'sorry'` warnings
```

```lean
import Arlib
#print axioms Arlib.FinProb.markov
-- 'Arlib.FinProb.markov' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Anything other than `[propext, Classical.choice, Quot.sound]` (a `sorryAx` or a
stray custom axiom) means a result is not actually proved.




## Layout

```
arlib/                    # repo folder (Lake package name stays lowercase)
  lean-toolchain          # leanprover/lean4:v4.15.0
  lakefile.toml           # requires mathlib @ v4.15.0
  Arlib.lean              # library root — re-exports every area
  Arlib/
    Prelude.lean
    Probability.lean      # area root — re-exports the modules below
    Probability/*.lean
    Combinatorics.lean    # area root
    Combinatorics/*.lean  # Finset, BigOperators, ListFold
```

## License

Released under the [Apache License 2.0](LICENSE), following Mathlib. Copyright ©
2026 Kuldeep S. Meel.

## Acknowledgements

Built with the assistance of **Claude** (Anthropic's Claude Code).
