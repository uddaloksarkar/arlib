# arlib

Arlib is a Lean 4 + Mathlib library of reusable mathematical foundations for
formalized algorithms. It provides general-purpose probability, finite and
continuous Markov-chain infrastructure, combinatorics, communication and
information theory, approximation primitives, representation types, and
supporting algebra and analysis.

Named algorithms, concrete reductions and chains, and their correctness or
resource analyses live in the companion
[`arlib-community`](https://github.com/meelgroup/arlib-community) repository.
The permanent dependency direction is:

```text
Mathlib -> Arlib -> ArlibCommunity
```

See [`BOUNDARY.md`](BOUNDARY.md) for the ownership rule and
[`BOUNDARY_MANIFEST.tsv`](BOUNDARY_MANIFEST.tsv) for the initial disposition of
every module considered during the hard split.

## Public imports

`import Arlib` gives the complete core. Narrower roots include:

```lean
import Arlib.Probability
import Arlib.MarkovChains
import Arlib.MarkovChains.Continuous
import Arlib.Convexity.Polytope
```

Finite Markov-chain declarations use `Arlib.MarkovChains`; continuous-state
declarations use `Arlib.MarkovChains.Continuous`. This explicit namespace split
allows both APIs to be imported together without short-name collisions.

The source tree contains 144 Lean files under `Arlib/`. It is `sorry`-free and
declares no project axiom; the semantic axiom audit permits only Mathlib's
standard `propext`, `Classical.choice`, and `Quot.sound` foundations.

## Getting started

Arlib currently follows Lean and Mathlib `v4.33.0`, pinned by
`lean-toolchain` and `lake-manifest.json`.

```toml
[[require]]
name = "arlib"
git = "https://github.com/meelgroup/arlib.git"
rev = "main"
```

Then run:

```bash
lake update arlib
lake build Arlib
```

For the paired hard-split branches, consumers should pin the exact reviewed
core commit rather than `main` until the core PR has merged.

## Contributing

Before adding a declaration, apply the statement test from `BOUNDARY.md`: if the
statement refers to a named procedure, concrete construction, or explicit cost
model, it normally belongs in ArlibCommunity. Mixed developments should place
generic representations and lemmas here and the consuming algorithmic analysis
there.

Run these release checks before submitting a core change:

```bash
scripts/BoundaryAudit.sh
lake build Arlib
lake env lean scripts/AxiomAudit.lean
```

See [`CONTRIBUTING.md`](CONTRIBUTING.md),
[`CONVENTIONS.md`](CONVENTIONS.md), and [`ARCHITECTURE.md`](ARCHITECTURE.md) for
the remaining contributor guidance. Namespace changes introduced by the split
are summarized at the top of [`MIGRATION.md`](MIGRATION.md).

## Citing

```bibtex
@software{meel2026arlib,
  author = {Meel, Kuldeep S.},
  title  = {arlib: reusable Lean foundations for formalized algorithms},
  year   = {2026},
  url    = {https://github.com/meelgroup/arlib}
}
```

## License and origins

Released under the [Apache License 2.0](LICENSE). Per-file headers are
authoritative for copyright and authorship; see [`CONTRIBUTORS.md`](CONTRIBUTORS.md).
