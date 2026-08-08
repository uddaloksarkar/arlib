# Arlib

A curated, **mathlib-style** library of reusable Lean 4 + Mathlib results,
distilled from the meelgroup formalization projects. The goal is a single,
clean, `sorry`-free library that others can `import` and build on — rather than
re-proving the same infrastructure in every new project.


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

Finite probability spaces and the machinery built on them, **plus** a smaller
group of modules built directly on Mathlib's measure theory (see below):

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
| `TVDistance` | Total variation distance over an unbounded index type, via `tsum` (companion to `Poisson`'s function-on-`ℕ` idiom, not the `Finset`-based `MarkovChains.Techniques.TotalVariation`): the metric facts, the event characterisation `abs_tsum_ite_sub_le_tvDist` (`\|Pr[X∈S]-Pr[Y∈S]\| ≤ d_TV`), and the conditional-TV chain rule `tvDist_condOn_le` for conditioning on an accept/reject draw whose acceptance probability depends on `X`. |

**Measure-theoretic modules.** Built on Mathlib's `MeasureTheory.Measure`,
`Filtration`, `condexp` and `Martingale` rather than on `FinProb`, because the
statements are about limits, conditional expectation and almost-sure convergence
and have no finite surrogate.

| Module | Content |
| --- | --- |
| `RobbinsMonro` | The deterministic half of stochastic approximation: **the product lemma** `∏(1 − aₙ) → 0` under `∑ aₙ = ∞`, the recursion `Y_{n+1} = (1−aₙ)Yₙ + aₙc` with its closed form and convexity bounds, and criteria for establishing `∑ α = ∞` when the sequence is bounded below only along a sparse set of active times (`tendsto_sum_atTop_of_count_harmonic_le`). No measure theory. |
| `StochasticApproximation` | **Robbins–Siegmund**, and `tendsto_zero_of_sa`: the scalar recursion `W_{t+1} = (1−α_t)W_t + α_t ε_t` drives `W_t → 0` a.s. under `E[ε_t ∣ F_t] = 0`, `E[ε_t² ∣ F_t] ≤ B`, `∑ α_t = ∞`, `∑ α_t² < ∞`. Stated over an arbitrary space and filtration. Includes `ae_exists_tendsto_of_nonneg_supermartingale` — a.e. convergence of a nonnegative supermartingale, which Mathlib states only in the `L¹`-bounded *sub*martingale form. |
| `CondExpFreshDraw` | A centred fresh draw independent of the history has conditional mean zero — *unbiasedness of a sampled target* — over an arbitrary probability space, sub-σ-algebra, finite draw space and bounded factors. Plus the second-moment bound and `∑_{k<n} 1/(k+1)² ≤ 2`. |
| `TorusProduct` | A **countably-indexed mutually independent uniform family**, built as normalised Haar measure on `ι → AddCircle 1` — no product construction needed, since independence and uniformity are *derived* from uniqueness of Haar measure on the finite-dimensional marginals. With `cylinderEvents` blocks and the time filtration `ℱ t = σ(draws before t)`. Mathlib v4.15 has no infinite product measure (`Measure.pi` stops at `Fintype`) and no Kolmogorov extension, so there is no other route to this object. |
| `InverseCDF` | An arbitrary finite law from one uniform coin, by cutting `(0,1]` at the cumulative sums; `measure_drawOf_eq` proves the law is `p` exactly, and `drawOf_pos` that a zero-probability element is never returned (pointwise, not merely a.s.). Complements the finite-grid `UniformCoin` and the single coin of `ContCoinProto`. |
| `LevyBorelCantelli` | Lévy's conditional Borel–Cantelli re-indexed for events adapted one step *late* — the shape a randomized process actually supplies, where the event at step `t` is decided by randomness drawn at step `t`. |
| `MeasurableIndex` | Measurability of `f (X ω) ω`, a quantity read at a random, countably-valued index. `measurable_comp_index` needs **no** hypothesis on `f` at all. |

### `Arlib.Combinatorics` — generic `Finset` / `List` helpers

Fully generic (`[DecidableEq α]` / `[LinearOrder α]`) helper lemmas that recurred
across several projects but are not in Mathlib under an obvious name.

| Module | Content |
| --- | --- |
| `Combinatorics.Finset` | Membership in a list-fold union (`mem_foldr_union`, `mem_foldr_union_map`); powerset of a union as an image of a product (`image_union_powerset`); recovering a summand of a disjoint union (`union_inter_left`/`right`); tiling an interval by consecutive blocks (`Ico_biUnion_blocks`); a concatenation counting bound `|A|·|B| ≤ |C|` (`concat_injOn`, `card_mul_le_of_concat_subset`). |
| `Combinatorics.BigOperators` | Diagonal/off-diagonal split of a double sum (`sum_matrix_diag_offdiag`); products of an idempotent function over subsets/unions/`biUnion`s (`prod_mul_prod_subset`, `prod_union_idem`, `prod_biUnion_idem`); a surjection–product inequality (`prod_le_prod_comp_of_surj`); products of `{0,1}`-valued functions (`prod_zero_or_one`, `zo_prod_eq_one_iff`). |
| `Combinatorics.ListFold` | Upper/lower bounds for `List.foldr min` (`foldr_min_le_init`, `foldr_min_le_mem`, `le_foldr_min`, `lt_foldr_min`). |
| `Combinatorics.FoldMax` | `maxOver s b f = s.fold max b f`, a `Finset` maximum **floored at `b`** — total, so no nonemptiness side condition ever appears at a call site, unlike `Finset.sup'`. The characterisation `maxOver_le_iff`, the two lower bounds, and the strict upper bound `maxOver_lt`. Companion to `ListFold`. |

### `Arlib.MarkovChains` — finite Markov chains

59 modules, ~28.8k LOC, split by a load-bearing design principle: `Techniques/` holds
machinery valid for *any* finite chain, `Chains/` holds the analysis of *specific* chains,
and every general definition is instantiated against a concrete chain that keeps it honest.
Following the Chen–Štefankovič–Vigoda monograph on spectral independence (`source/main.tex`).

The area's defining commitment: **the spectral gap is defined variationally**, by the
Poincaré inequality `γ·Var_μ(f) ≤ ℰ_P(f)`, and eigenvalues never appear — not in a
statement, not in a proof. Every step a textbook takes via the spectral theorem is taken
here by an elementary variational, discriminant, or adjointness argument.

| Module | Content |
| --- | --- |
| `Techniques.Chain` | `FinDist`, `FinKernel` (rectangular, so the up/down operators of the local-to-global machinery fit), `FinChain`, `act`/`push`, composition, iteration, `Stationary`, `Reversible`. |
| `Techniques.Bilinear` | Cauchy–Schwarz for a PSD symmetric bilinear form, by the discriminant trick rather than by eigenvalues. |
| `Techniques.Functional` | The `L²(μ)` calculus: `Ex`, `ip`, `Var`, the pair form of the variance, `relDensity`, `chiSq`. |
| `Techniques.Dirichlet` | The Dirichlet form and its pair form; the two-sided bound `\|⟪f,Pf⟫_μ\| ≤ ⟪f,f⟫_μ`; reversibility as self-adjointness; `SpectralGapAtLeast` (Poincaré) and `NonnegDefinite` (PSD). |
| `Techniques.SpectralGap` | From the numerical-range bound to the operator bound `⟪Pf,Pf⟫ ≤ c²⟪f,f⟫`; geometric decay of variance and of χ²-divergence. |
| `Techniques.TotalVariation` | TV distance, its event characterisation, the data-processing inequality, mixing time, and `(2·d_TV)² ≤ χ²`. |
| `Techniques.MixingTime` | Point masses, χ² decay along the chain, and the assembled bound `T_mix(ε) ≤ (2/γ)·ln(1/(2ε√μ_min))`. |
| `Techniques.Lazy` | The lazy chain `½(I+P)`: one source of PSD chains, and the capstone `Var_μ(P_lazy^t f) ≤ (1−γ/2)^{2t} Var_μ(f)`. |
| `Techniques.Mixture` | Convex combinations of kernels — two-way, uniform average, general weights — and the inheritance of stationarity, reversibility, PSD and the gap. |
| `Techniques.Adjoint` | Mutually adjoint kernel pairs `μ(x)K(x,y) = ν(y)L(y,x)`; composites are reversible **and** PSD for free. `Reversible` is the self-adjoint case. |
| `Techniques.Levels` | The up and down walks on the levels of a weighted complex, their adjointness, and hence reversibility, stationarity and PSD of the up-down and down-up walks. |
| `Techniques.LocalWalk` | Links of a face — again weighted complexes, so `Levels` applies verbatim — the one-level-up distribution, and the local walk with its reversibility. |
| `Techniques.Entropy` | The entropy functional `Ent_μ(f)`, the modified log-Sobolev inequality, entropy decay along a chain, and KL divergence with its contraction. |
| `Techniques.Comparison` | Comparison of Dirichlet forms and transfer of the spectral gap; off-diagonal domination suffices; the absolute bound for iterates. |
| `Techniques.Conductance` | Ergodic flow, cut, conductance; `ℰ_P(1_A) = cut`; the easy direction of Cheeger's inequality. |
| `Techniques.Coupling` | Couplings, the coupling inequality, and the maximal coupling — so TV distance *is* the minimum disagreement probability. |
| `Techniques.LevelVariance` | The law of total variance for a bare kernel — no hypotheses — and hence the local-to-global step `Var_{π_{k+1}}(g) = Var_{π_k}(Ug) + ℰ_{downUp}(g)` as an *identity*. |
| `Techniques.LocalToGlobal` | Telescoping that identity down the levels: `Var_{π_n}(f) = Σ_{k<n} ℰ_{downUp_k}(f^{(k+1)})`, exactly — `π_0` is a point mass, so there is no leading term. Includes the guarded link distribution the sum needs. |
| `Techniques.LinkRestriction` | A closed form for the level projections — `f^{(k)}(τ)` is the conditional expectation given `σ ⊇ τ` — and their compatibility with restriction to a link. Separates the *star* of a face (now `LocalWalk.starWeight`, renamed once this module proved it is not the link) from the link proper; they agree at level one, audited against `linkDist`. |
| `Techniques.FirstStep` | `claim:first-step` — the two-level variance drop equals the average over faces of the variance inside the two-levels-up link. Needs no WLOG centering (the squared means cancel by a pushforward identity), and the crux is the factor `2·(n−k).choose 2 = (n−k)(n−k−1)` relating the link to two applications of the up operator. |
| `Techniques.ImprovedRandomWalk` | `lem:improved-technical` and the Improved Random Walk Theorem — per-link Poincaré inequalities give the top-level down-up walk a gap of `Γ_m / ∑_{i≤m} Γ_i`, with `Γ_i = ∏_{j<i}(2γ_j − 1)`. The monograph's induction tacitly needs `2γ_j ≥ 1`, which is why the theorem is stated in those factors at all; here it is an explicit hypothesis. |
| `Techniques.LocalWalkBridge` | `P^∧∨_{τ,1} = (Q_τ + I)/2` — an entrywise identity on *every* row, degenerate ones included, because the two constructions' guards are literally the same predicate. Hence `γ(P^∧∨_{τ,1}) ≥ γ/2 ↔ γ(Q_τ) ≥ γ`, exact in both directions, and the Random Walk Theorem restated on `Q_τ`. |
| `Techniques.ImprovedRandomWalkSharp` | The monograph's suggested sharpening (line 1987): `γ/(2−γ)` for `2γ−1`. The gain is an identity — `γ/(2−γ) − (2γ−1) = 2(γ−1)²/(2−γ)`, exactly the term the other proof throws away — and the constants themselves compare, not just the factors. Not a strict improvement: at `γ = 2` the old factor is `3` and the sharp one `0`, and `BernoulliLaplace` attains `γ = 2`. |
| `Techniques.MultiStep` | `Adjoint.comp` — adjointness composes, with the order reversed on one side — hence multi-step operators between any two levels, `lem:diff-var` for general `i > j`, and the multi-level `eqn:RW-improved-general`. `multiDownUp_succ` audits the orientation against `Levels.downUp`. |
| `Techniques.UpDownDownUp` | Equal Poincaré constants for the two composites of an adjoint pair (`lem:updown-downup`), where the monograph uses equality of the nonzero spectra of `AB` and `BA`. The `γ ≤ 1` side condition is *necessary* — a point-mass source satisfies every Poincaré inequality vacuously — and the counterexample is formalized. |
| `Techniques.Transport` | μ-almost-everywhere agreement of chains, and transport of the whole `L²` theory along an injective embedding of state spaces. Rows of weight zero are invisible; the range carries all the mass. |
| `Techniques.Pinsker` | `2·d_TV² ≤ D_KL`, sharp constant, by a pointwise Padé bound plus tangent-line linearisation — no marginalisation and no square roots. Absolute continuity is required, not cosmetic: without it disjoint point masses give `klDiv = 0` and `tvDist = 1`. Chaining it after `klDiv_le_chiSq` is *worse* than the direct χ² bound by `√2`, so it pays only on KL bounds of entropy origin. |
| `Techniques.EntropyDecay` | `EntropyContraction` — the right hypothesis for geometric entropy decay — giving `D_KL ≤ ε` after `Θ(ρ⁻¹ log log(1/μ_min))` steps, against the χ² route's `Θ(γ⁻¹ log(1/μ_min))`. And the refutation: an MLSI does *not* imply decay (`exists_modLogSobolev_not_entropyContraction`; the deterministic swap on `Bool` has `ρ = 1` and constant entropy), because `Ent(f) − Ent(Pf) ≥ ℰ(f, log f)` forces `Pf = f`. |
| `Techniques.EntropyVariational` | Young's inequality for entropy, the Gibbs variational principle, `Ent ≤ Var/E`, and hence `KL ≤ χ²`. |
| `Techniques.PsdOrder` | Quadratic forms of a plain `ι → ι → ℝ` and the PSD ordering `PsdLe`. No `Matrix`, no spectrum, no eigenvalues. |
| `Techniques.SpectralIndependence` | The covariance form with `quadForm (Cov μ) a = Var μ (fun σ => ∑ v, a (v, σ v))`, so PSD-ness of `Cov` is a corollary of `Var_nonneg`; spectral independence **defined** as the ordering `Cov ⪯ η·diag(marg)` — the eigenvalue-free equivalent of `λ_max(Ψ) ≤ η`. |
| `Techniques.SpectralIndependenceConverse` | `SpectralIndependence μ η ↔ SpectralGapAtLeast (pinDist) (Q_η) ((m−η)/(m−1))` — an exact equivalence, since both directions are one identity read in opposite senses. One pinning's gap gives that pinning's independence: a site with a sure spin contributes a zero row to the covariance form, so the pinned coordinates are already invisible. |
| `Techniques.LocalSpectralIndependence` | Spectral independence ⟹ a Poincaré inequality for the local walk at any pinning, via the exact identity `ℰ_Q(f) = m/(m−1)·Var_π(f) − quadForm(Cov μ) f̃/(m(m−1))`. The monograph's `lem:QandPsi`, proved there with `λ_max(Ψ)` and a block-matrix argument; here with neither. |
| `Chains.Metropolis` | Metropolis–Hastings: manufacturing a chain reversible with respect to a prescribed target. |
| `Chains.TwoState` | The two-state chain computed exactly — gap, contraction factor and Dirichlet form as identities — then plugged back into the general predicates, and used to audit the Cheeger bound. |
| `Chains.IndependentSampler` | The `P(x,y) = μ(y)` chain: Dirichlet form = variance, gap exactly `1`, mixes in one step. The library's best case. |
| `Chains.SpinSystem` | Configurations, single-site updates, the Gibbs distribution and its local partition functions; the hard-core model. |
| `Chains.Glauber` | The Glauber dynamics: single-site heat-bath updates, reversibility w.r.t. Gibbs, and positive semidefiniteness via self-adjoint idempotence. |
| `Chains.Pinning` | Pinnings and conditional Gibbs measures; the single-site update recovered as "resample from the conditional distribution". |
| `Chains.BlockDynamics` | Heat-bath block dynamics; reversibility and PSD for a single block, inherited by the mixture; Glauber is the singleton-block case. |
| `Chains.GlauberTensorization` | The Dirichlet form of the Glauber dynamics as a mean conditional variance, and approximate tensorization of variance as an equivalent of the spectral gap. |
| `Chains.LevelEncoding` | Spin systems as weighted complexes; the down-up walk at the top level *is* the Glauber dynamics. |
| `Chains.GlauberViaLevels` | Transporting that encoding back: PSD-ness of the Glauber dynamics derived a third time, now from adjointness, and the Poincaré inequality transferred in both directions. |
| `Chains.PinnedGlauber` | Conditioning does not leave the category: pinned marginals, `π_{η,1}`, and the local walk `Q_η` — shown to be the complex-side `localWalk` entry for entry. |
| `Chains.UniformComplex` | The concrete instantiation the `Levels`/`LocalWalk` development lacked: `mu`, `π_k` (uniform, and *independent of the dimension*), `U_k = 1/(N−k)`, and `downUp` as the Bernoulli–Laplace walk in closed form. Audits the general theory against exact answers — detailed balance proved twice, the Rayleigh quotient exactly `N/((k+1)(N−k))`, and `ℰ ≤ Var` shown tight at `k = 0` with its slack computed above. |
| `Chains.BernoulliLaplace` | The first non-trivial Poincaré inequality here, and the first end-to-end use of local-to-global: `γ ≥ (N+1)/((N+1−d)(d+1))`, with the local input `γ(Q_τ) = M/(M−1)` discharged as an identity. Audited against the exact `N/((d+1)(N−d))`: the relative loss is `1 − d/(N(N+1−d))`, all of it in the assembly, and quadratic in the local gap's excess over 1. |
| `Chains.ProductMeasure` | The first weight for which approximate tensorization is *proved*, discharging the hypothesis the `GlauberTensorization` equivalences were built to consume: a product measure gives `C = 1`, hence Glauber gap exactly `1/n`. The induction needs no site ordering — proving it for every `Λ` at once makes it monotone, so plain `Finset.induction_on` closes it. |
| `Chains.ProductOptimalMixing` | `O(n log(n/ε))` mixing in relative entropy for product-measure Glauber — the monograph's headline claim. The comparison is made honestly: the variance route is `Θ(n²)` here, since `log(1/√m) = Θ(n)`, and the baseline is restated without laziness first, because Glauber is already PSD. KL only; no TV bound at this rate is claimed. |
| `Chains.SpectralIndependenceMixing` | **The monograph's central theorem.** Spectral independence at every pinning ⟹ a spectral gap for Glauber, chaining `LocalSpectralIndependence` → `PinnedGlauber` → `LocalWalkBridge` → `ImprovedRandomWalk` → `GlauberViaLevels`. Exactly `1/n` at `η = 1`, matching the product-measure answer with no slack. The `η ≤ 3/2` hypothesis is an artefact of our `ImprovedRandomWalk`, not of the mathematics. |
| `Chains.SpectralIndependenceMixingSharp` | The central theorem under `η ≤ 2` (one-sided — `0 ≤ η` is derived), deriving the old conclusion on the overlap. On `3/2 < η < 2` the old side condition is *refuted*, not merely unproved. The `η = 0` degeneracy is unreachable: any site with a marginal strictly inside `(0,1)` forces `0 < η`. |
| `Chains.GlauberToSpectralIndependence` | `lem:opt-relax-SI`: `T_relax(Glauber for μ_τ) ≤ C(n−|Λ|)` at every pinning ⟹ spectral independence with constant `C`. Testing the Poincaré inequality at a linear statistic is an *identity*, not a bound — a Dirichlet form only sees increments the kernel charges. Introduces `freeGlauber`, resampling only free sites. Round trip is lossless exactly at `C = 1`. |
| `Chains.TwoSiteSpectralIndependence` | The exact spectral independence constant for the smallest correlated system: `η = 1 + |ρ|`, with `Cov` the determinant `μ₀₀μ₁₁ − μ₀₁μ₁₀`. Attains `1` iff product and `2` at perfect correlation, so both the `ProductSpectralIndependence` calibration and the universal `|V|` bound are exact. Audits the local-walk gap `1 − |ρ|` by two independent routes. |
| `Chains.ProductSpectralIndependence` | Discharges the central theorem's hypothesis for the first time. Pairwise independence of a product weight is the *unnormalised* identity `Z(pin{v,u})·Z = Z(pin{v})·Z(pin{u})` — no division, no positivity needed, which matters because pinned families carry point masses. Yields `γ ≥ 1/n` via spectral independence: literally the same proposition `ProductMeasure` proves via tensorization. |
| `Chains.OptimalMixingTV` | `O(n log(n/δ))` for product Glauber in **total variation**. Pinsker's real cost is not a constant in a log but the squaring `δ ↦ δ²`, which halves the effective decay rate `ρ ↦ ρ/2`; the χ² route has no analogue. Proves the exact crossover: entropy beats variance iff `ln(nL/δ) < nL/2`, so neither dominates. |
| `Chains.ProductEntropy` | Tensorization of *entropy* for a product measure at `C = 1`, and the library's first modified log-Sobolev instance, `ModLogSobolev μ (glauber …) (1/n)` — stated against `entropyProduction`, never the vacuous naive form. Includes `localEnt_le_entropyProduction`, valid for any reversible chain. |
| `Chains.HardCore` | The monograph's two running examples. Hard-core, whose weight can vanish, with the exact `Zloc` trichotomy and the `λ/(1+λ)` update; and Ising, whose weight cannot, so `0 < Z` needs no hypothesis at all. |

### `Arlib.KnowledgeCompilation` — representation languages and their limits

29 modules, ~12.9k LOC, split three ways to mirror the shape of the argument:
`Circuits/` holds the *objects*, `Communication/` the *tool*, `LowerBounds/` the
*bridge and the argument*. Following Vinall-Smeeth, *Structured d-DNNF Is Not
Closed Under Negation* (IJCAI 2024), in `source/kc/arXiv.tex`.

Two conventions shape everything. **Circuits are DAGs, never trees** — size is
the vertex count of a shared graph, so a tree encoding would silently prove a
weaker theorem. And **imported results are hypotheses, never axioms**: the
paper's headline theorems rest on results proved elsewhere, and those enter as
explicit parameters of the theorems that consume them, so what a statement is
conditional on is visible in the statement.

| Module | Content |
| --- | --- |
| `Circuits.NNF` | The DAG encoding: node values `valAt`, computed function `eval`, syntactic variables `varsAt`, the locality lemma `valAt_congr`, reachability, and `Decomposable` / `Deterministic` / `IsDNNF` / `IsdDNNF` — each relativized to the nodes reachable from the source, as the paper defines them. |
| `Circuits.VTree` | V-trees, well-formedness, the subtree relation, `NNF.Respects`, and the structured classes `IsSDNNF`/`IsdSDNNF`. Includes `Respects.decomposable`: respecting a well-formed v-tree already forces decomposability. |
| `Circuits.SDD` | `XDecomposition`, the fan-in-2 chain relation, `IsSDDAt` by recursion on the v-tree, and the containment SDD ⊆ d-SDNNF — unconditional, because the conditions are relativized to reachable nodes. |
| `Circuits.Figure1` | The paper's Figure 1, built by hand and checked against the formula its caption states independently. The one place the *encoding* is checked rather than the reasoning about it. |
| `Circuits.DNF`, `DNFMap`, `DNFSubst`, `DNFMux` | Terms as finite sets of literals, width, `IsKDNF`, `Unambiguous` in counting form — the shape every imported hardness result arrives in. Then renaming, minterm expansion and substitution (with width, term count and, the hard part, unambiguity of the result), and the mux `(x ∧ ψ) ∨ (¬x ∧ φ)` over a fresh variable with the identity `∃x f_C ≡ f ∨ g`. |
| `Circuits.DNFtoCircuit` | The upper-bound half of `thm: main`: an unambiguous `k`-DNF with `ℓ` terms admits a d-SDNNF respecting *any* given v-tree, of size `≤ ℓ·(2k+2) + 1`. Determinism comes exactly from unambiguity. |
| `Circuits.Arithmetic` | Arithmetic circuits and the relabelling `φ` sending an AC to an NNF on the same graph. `supp(C) = sat(φ(C))` proved twice — once from monotonicity (the paper's hypothesis), once from *determinism*, which is the version Part D uses and the reason Part D imports nothing. |
| `Communication.Rectangle` | `VarPartition` and balancedness, Π-rectangles as pairs of predicates each local to its side, and the closure property `mem_cross` that every rectangle argument runs on. |
| `Communication.Measures` | `fixedCov`/`fixedPar` and their best-partition counterparts, with the per-partition unfolded form in which a lower bound is actually consumed. |
| `Communication.NonnegRank` | Nonnegative rank and `Par₁(F) ≥ rk⁺(F)`: a rectangular *partition* of `F⁻¹(1)` is a decomposition into that many rank-one non-negative pieces. Both halves of `Partitions` are needed — which is why this is about `Par₁`, not `Cov₁`. |
| `Communication.ConicalJunta` | The one *new* theorem in the chain behind `UnionHard`, proved rather than cited: Göös–Kiefer–Yuan's Lemma 14, that `∨` is at least as hard as `¬` for approximate conical juntas. Conical juntas, dual certificates, **weak duality**, the negated tensor product, and the powering trick — the last with the source's logarithmic parameters replaced by the three inequalities its proof actually uses. |
| `Communication.Gadget` | Composing a Boolean function with a two-party gadget, and the exactly-balanced partition it induces. Stated for a general variable type, so `ι ⊕ ι` gives the composition of the doubled function `f^∨` for free — which is how the union argument's four-block bookkeeping disappears. |
| `LowerBounds.RectangleLemma` | The bridge, and the reason a communication lower bound is a circuit lower bound: a structured d-DNNF of size `s` yields a rectangular *partition* of `f⁻¹(1)` into `s` pieces, so `Par₁(f) ≤ \|C\|`. **Discharges** import I2. |
| `LowerBounds.BalancedCut` | Every v-tree on ≥ 2 variables has a node carrying between a third and two thirds of them, so cutting there induces a *balanced* partition — the partition a best-partition measure is minimised over. |
| `LowerBounds.Copies`, `Pullback`, `Lifting` | The copy-and-permute lifting from fixed to best partition: the derived terms and the one-hot region where the construction is faithful; protocol simulation expressed on rectangles, with no protocol ever appearing; and `thm: fixed_to_best`. |
| `LowerBounds.ClaimPerm`, `AffinePerms` | The probabilistic heart of the lifting, which the paper proves only by citation: some affine permutation places, for every variable and every side of the partition, at least one copy on that side — done by counting, not by building a probability space. `AffinePerms` **discharges** import I3: the Wegman–Carter family `x ↦ ax+b` and its pairwise independence. |
| `LowerBounds.Instance` | A concrete witness for every parameter `thm: main` takes, so the headline theorems are not conditionals with unexhibited hypotheses. The field is `GaloisField 2 t` with `t` *logarithmic* in `n`, which matters: a linear `t` satisfies every hypothesis and still destroys the size comparison the theorem exists to make. |
| `LowerBounds.Separation` | `thm: main` and `thm: sep`, assembled, with fully explicit bounds and conditional only on the imported hardness. The lower-bound halves hold for *any* v-tree the circuit respects, not only one spanning every variable — omitted variables are grafted on. |
| `LowerBounds.Union` | `thm: union` and `thm: ex`: d-SDNNF is closed under neither disjunction nor existential quantification. The same composition as `thm: main`, run at the *partition* half of each component rather than the *cover* half. Determinism turns from a non-hypothesis into a hypothesis — the paper's own footnote: unambiguous communication needs disjoint rectangles, and only determinism supplies them. |
| `LowerBounds.Arithmetic` | `cor: add`: dSD-`AC` is not closed under addition. `thm: union` read through `φ`, with the paper's sixth imported result shown to be *unnecessary* — its only job is to make `supp = sat` available, and determinism already does that. So Part D is conditional on `UnionHard` alone. |
| `LowerBounds.Imported`, `UnionDerived` | The results the paper genuinely imports, as named bundles of data and hypotheses rather than axioms — every downstream theorem takes one as a parameter. `UnionDerived` then *derives* `UnionHard` from the two results Göös–Kiefer–Yuan themselves import, rather than assuming it. |
| `Communication.TwoParty` | Rectangles, covers, partitions and non-negative rank for a bare `F : X → Y → Bool` on two arbitrary types. The `VarPartition` model above is the wrong shape twice over: automata cut a word at a *position*, and sparse set disjointness lives on the `k`-subsets of `[n]` with no ambient Boolean cube at all. |

A **second paper** shares the area, Igor Razgon, *On the read-once property of
branching programs and CNFs of bounded treewidth* (`source/kc/razgon/`). It
shares the subject — how large a representation must be — but none of the
machinery: the engine is matching width and a probabilistic covering bound, not
communication complexity. CNFs of treewidth `k` need NROBPs of size `n^{Ω(k)}`,
so the `O(n^k)` upper bound cannot be made fixed-parameter; the consequence for
this area is a quasi-polynomial separation between FBDD and decision-DNNF.

| Module | Content |
| --- | --- |
| `BranchingPrograms.Basic` | `φ(G)`, the monotone 2-CNF of a graph, given **semantically** — the paper replaces it by Observation 1 immediately and never looks at the formula again, so `phi_iff_isVertexCover` (its satisfying assignments are the vertex covers) is the whole bridge. Cross matchings, and matching width defined *only* as the lower-bound predicate `MatchingWidthGe`, since every use in the paper is a lower bound and a numeric `sSup` would need a boundedness side condition at each use. |
| `BranchingPrograms.Covering` | Theorem `lbengine`: a `t`-cover of the vertex covers of a graph of max-degree `x` has at least `2^{t/f(x)}` members. The paper's probabilistic argument is replaced by an **exact count** — independence becomes a grafting bijection on `Ω × Ω`, and the `Pr(·) > 0` side condition its conditioning step carries disappears. Razgon's unproved "every `S` contains an independent subset of size `\|S\|/(x+1)`" is proved here; Mathlib v4.15 has no usable `Finset`-level independent-set API. |
| `BranchingPrograms.NROBP` | The model — a DAG with literal-labelled edges, size in nodes — plus `t`-nodes and Lemma `tnodecut`: if `mw(G) ≥ t` the `t`-nodes form a root–leaf cut. **Uniformity is an explicit hypothesis**; the reduction of an arbitrary NROBP to a uniform one is the paper's Appendix B and is not formalized, so the theorem is exactly what its §3–§6 prove. |
| `BranchingPrograms.TreeProduct` | The graphs `T_r(H)`, as Mathlib's box product, and the matching-width induction `dmwtwstruct`, with the degree, treewidth and vertex-count bounds for `T_r(P_{2p})`. Two steps needed **repair rather than transcription**: the paper's "w.l.o.g." in `mincase` is false as written (a non-partitioned copy may lie entirely on the far side), and its "assume w.l.o.g. `u₁…u₄` occur in this order" is not a symmetry — what the proof actually uses is a *median*, so one of the four subtrees is discarded. Treewidth is defined locally; Mathlib has none at this version. |
| `BranchingPrograms.Separation` | Theorem `nrobplbdmw` with its covering hypothesis discharged, and Theorem `maintheor` (explicit `r`, `p`). |
| `BranchingPrograms.Uniformize` | Razgon's Appendix A: an arbitrary read-once NROBP is turned into a **uniform** one of explicit size, which **discharges the `Uniform` hypothesis** — `uniformize_two_rpow_le_size` is the lower bound with no uniformity assumption. The paper's per-edge induction re-indexes the node set each step, unworkable against a `Fin size` node type; done in one fixed arithmetic layout instead. |
| `BranchingPrograms.Equivalence` | Appendix B: the AROSRN of `NROBP` and the textbook two-leaf guessing-node NROBP compute the same functions — forwards at **no cost** (stronger than the paper's ≤ 3×), backwards at an explicit blow-up. The "not constantly false" proviso is **unnecessary**, and a sink fact the paper never states is what actually excludes the rejecting branch. |
| `BranchingPrograms.Asymptotics` | `dmwtw`, `maintheor` as `n^{k/c}`, and Lemma `separ`, with every "sufficiently large" step made an explicit threshold. Razgon's `k ≥ 50` is **not needed**; two of his thresholds are **vacuous**; his `separ` chain **loses a factor of eight**; and `maintheor`'s constant is `64·f(5)`, not `32·f(5)` — a `Nat.log` rounding artefact (with real logs the paper is right). |
| `BranchingPrograms.DecisionDNNF` | decision-DNNF as a predicate on the NNF DAG; the containment decision-DNNF ⊆ d-DNNF (which needs **no** decomposability); FBDD as the deterministic fragment of NROBP; and Theorem `separ2`, the quasi-polynomial FBDD/decision-DNNF separation, its upper half now supplied by the proved Oztok–Darwiche bound below. |
| `BranchingPrograms.DecisionDNNFCompile` | **Oztok–Darwiche, CP 2014 Theorem 1** (`source/kc/darwiche/CP-45.pdf`), proved constructively: from a finite rooted tree decomposition `RootedTD G` of width `≤ w`, the separator-shared Shannon-cascade compilation `compileNNFSharp` emits a decision-DNNF for `φ(G)` — verified correct (`eval ⟺ phi`), decomposable and read-once (`IsDecisionDNNF`) — of size `≤ 15·2^{w+1}·n + 1` (`exists_decisionDNNF_of_rootedTD_sharp`), single-exponential in the width and **linear** in the number of tree nodes. The decomposability engine is `sibling_absent` + the running-intersection field `conn_meet` (which strengthens the original tree-decomposition definition to the standard vertex condition, found necessary here). A loose `O(2^{2w}·n²)` variant is kept as the simpler artefact. |
| `BranchingPrograms.OztokDarwicheBundle` | Makes the separation **unconditional**. A binary-heap indexing bijection `BinTreeNode r ≃ Fin(2^{r+1}−1)` (parent = shorter list ⟹ smaller index, so the topological order is free) wraps the explicit `T_r □ P_{2p}` decomposition as a `RootedTD`; feeding it to the sharp compiler gives an unconditional decision-DNNF for the separating class. Combined with `maintheor`, `separ2_quintic_unconditional` (hypothesis `1 ≤ r` only) exhibits a decision-DNNF of size `≤ 15·16·n⁵ + 1` against every uniform read-once NROBP of real size `≥ 2^{((r+1−⌈log₂r⌉)·r/2)/f(5)}` — both sides discharged inside Lean. |

#### Forgetting — Oztok & Darwiche, *On Compiling DNNFs without Determinism*

`source/kc/darwiche/draft.tex`. The constructive counterpart to the lower-bound work: compile a DNNF for `f(X)` by finding `g(X,Y)` *equivalent modulo forgetting* (`f ≡ ∃Y. g`), compiling `g` to a **deterministic** DNNF, then forgetting `Y`.

| Module | Content |
| --- | --- |
| `Forgetting.Basic` | `forgetNNF`, the substitution of `⊤` for every `Y`-literal, and that on a **decomposable** NNF it computes `∃Y` at **no size increase**. This is the paper's linear-time forgetting; the module works out and records *where decomposability is used* — the paper asserts it without argument. `emf`, the algorithm's correctness, and a witness that forgetting genuinely destroys determinism. |
| `Forgetting.Treewidth` | Jointrees and the primal treewidth of a CNF; `thm:width`, that `k` applications of bounded variable addition raise treewidth by at most `k`; and the bounded-treewidth half of `thm:bva`, via a from-scratch proof that the star graph is a tree (Mathlib v4.15 has neither treewidth nor that lemma). |
| `Forgetting.MinDegree` | The unbounded half of `thm:bva`, `treewidth(Δⁿₐ) ≥ n` (in fact `2n ≤ w`): the general `min-degree ≤ treewidth` bound for jointrees, proved by a leaf-pruning induction over an active `Finset` of tree nodes, on top of a from-scratch finite-tree-leaf lemma via the farthest-vertex route (Mathlib v4.15 has neither). Closes the last dropped statement in the area. |
| `Forgetting.Separation` | The Sauerhoff function `f_n = row_n ∨ col_n` and `g_n = (Z ∧ row_n) ∨ (¬Z ∧ col_n)`, defined explicitly; the proof that `f_n` is emf to `g_n` through the single variable `Z`; and `thm:sep` — exponential separation of DNNF from deterministic DNNF — conditional on two inhabited hardness bundles. |

#### Tseitin — de Colnet & Mengel, *Characterizing Tseitin-formulas with short regular resolution refutations*

`source/kc/decolnet/main.tex`. A proof-complexity/knowledge-compilation crossover: regular
resolution refutations of Tseitin formulas are short **iff** the graph has `O(log n)` treewidth.
This area formalizes the self-contained **Step 2** — that every DNNF for a *satisfiable* Tseitin
formula is `2^{Ω(tw/Δ)}` large (the paper's genuinely new adversarial multi-partition rectangle
game); Step 1 (regular resolution ↔ 1-BP) and the full main theorem are deferred.

| Module | Content |
| --- | --- |
| `Tseitin.Basic` | `T(G,c)` as a semantic parity predicate over edge variables (GF(2)); conditioning; **Proposition 3**, the easy direction (satisfiable ⟹ even charge per component) proved by GF(2) double-counting, the converse and the model count (Prop 4) as inhabited imports. |
| `Tseitin.Splitting` | Sub-constraints and vertex splitting; **Lemma 15** (a rectangle respects a sub-constraint) proved in full; the model-count lemmas (16–18) and the 3-connected `k/3` selection (Lemma 19) as inhabited imports. |
| `Tseitin.Branchwidth` | Branch decomposition as a v-tree over the edge set, cut `order`, `BranchwidthLe`; the Harvey–Wood `bw`↔`tw` bridge as an import. |
| `Tseitin.RectangleGame` | The adversarial multi-partition game value `aR(f,S)` (a structural recursion on the round budget); **Theorem 12** (`aR ≤ |D|` for a DNNF) as an import, evidenced by the proved `RectangleLemma` analogue. |
| `Tseitin.ThreeConnected` | Reduction to charge 0, safe separators, and treewidth-preserving topological minors (Lemmas 6, 20, 21, 23) as imports — topological minors are absent from Mathlib v4.15. |
| `Tseitin.DNNFLowerBound` | **Lemma 22** (`dnnf_lower`): any DNNF for a satisfiable Tseitin formula of max degree `Δ` has size `≥ 2^{2·tw/(9Δ)}`. The exponent chain and the model-count pigeonhole are proved; the game realizing the cut is threaded through as the imported hypotheses. |

### `Arlib.Automata` — finite automata and unambiguity

9 modules, ~2.9k LOC. Mika Göös, Stefan Kiefer and Weiqiang Yuan, *Lower Bounds
for Unambiguous Automata via Communication Complexity* (ICALP 2022), in
`source/kc/goos/`. A **UFA** is an NFA with at most one accepting run per word;
the paper shows that complementing one, or taking a union of two, or separating
a language from its complement, can each cost a quasi-polynomial blowup in
states. All three go through communication complexity.

The area depends on `Arlib.KnowledgeCompilation.Communication`, which is where
that machinery already lived — the knowledge-compilation area was built on this
same paper and cites it as an imported result, so two of its files already
contain Göös–Kiefer–Yuan's Lemma 14 and `Par₁ ≥ rk⁺`, proved. If the dependency
becomes awkward the fix is to promote `Communication/` to an area of its own.

| Module | Content |
| --- | --- |
| `Coresets.Basic` | NFA, DFA, UFA. Runs are **objects, not endpoints**: Mathlib's `evalFrom` answers "where can `w` land", but a UFA may well reach an accepting state along two paths and it is exactly that which is forbidden — so the reachable-set semantics would define the wrong class. `IsRun`, `isRun_append`, `Reach`, `Accepts`, `Unambiguous`, and DFA ⊆ UFA. |
| `Simulation` | `lem: NFA-CC` and `lem: UFA-CC`: an NFA with `s` states gives `Cov₁(F) ≤ s`, a UFA gives `Par₁(F) ≤ s`. The paper says the second is "proved the same way" as the first; it is not. Unambiguity equates the two accepting runs as lists of states but does not say the two rectangle memberships split that run at the same place. Closing it needs a fact about the *inputs* — and it is the only place the fixed word lengths are used, which is precisely what separates the cover from the partition. |
| `DNFtoUFA` | An unambiguous `k`-DNF with `ℓ` terms over `n` variables compiled to a UFA with exactly `ℓ·(n+1)` states — an equality, and no sink state, since with `step` a relation a forbidden letter simply has no successor. Unambiguity of the automaton needs uniqueness of the term **index**, not of the term; a repeated term would give two accepting runs. No extra hypothesis is needed, because `DNF.Unambiguous` is a *count* on `satTerms` — so the `List`-not-`Finset` choice in `Circuits.DNF` is load-bearing here. |
| `WordCoding` | The coding between gadget variables and split words. **The step the paper never takes**: the lifting theorems are stated for a partition of a *variable set*, in which Alice's variables are not a contiguous block of word positions, while an automaton cuts a word at a position. |
| `Imported` | Balodis et al.'s unambiguous-DNF-versus-CNF-width separation, and Göös's non-deterministic lifting theorem, as inhabited hypothesis bundles rather than axioms. `C₀` needs no CNF datatype: the paper's own `C₀(f) = C₁(¬f)` lets the hypothesis read "no `w`-DNF computes `¬f`". |
| `Complement` | `thm: complement`: a language with a small UFA whose complement needs a large NFA. The paper's product with a `2bn+2`-state length counter turns out to be **unnecessary** — it exists only because its `lem: NFA-CC` demands a language exactly `F⁻¹(1)`, and ours constrains the automaton only on split words. Also: the imported separation bounds no *term count*, yet the state count is proportional to it; the paper patches this by re-counting crudely in terms of `n`, and we carry an explicit parameter instead. |
| `Union` | `thm: union` and `thm: or`: two languages with small UFAs whose union needs a large UFA. Conditional on the same two bundles as `KnowledgeCompilation`'s union theorem and nothing else — the partition-equality side condition connecting the two is `rfl`. |
| `Disjointness` | `thm: separation`, via sparse set disjointness. Razborov's covering-set lemma is **proved, by counting**, with an explicit family size: the separators of a pair are exactly the lattice interval `[S, Tᶜ]`, so the union bound becomes arithmetic with no logarithm and no rounding. The full-rank fact for the `k`-uniform disjointness matrix is imported (Gottlieb-type inclusion-matrix nonsingularity) and inhabited. |
| `ErrorReduction` | The upper-bound half of `thm: error`: approximate non-negative rank admits no efficient error reduction, because `∨` is easy to approximate at error `1/4` and hard at `10⁻⁵`. |

### `Arlib.Algorithms` — analyses of specific algorithms

Randomised algorithms and estimators. Each entry carries only the *generic* half
of its analysis — the law of a counter, the arithmetic of a run-count schedule,
a termination argument. The *problem-specific* half — exhibiting the structure
the algorithm needs for one particular counting or sampling problem — stays in
the project that uses it. An entry that cannot be stated without naming a
problem is a sign the split has not been found yet.

Unlike `MarkovChains`, whose subdirectories are organisational and share one
namespace, each algorithm gets its own directory *and* namespace
`Arlib.Algorithms.<Name>`: the entries are independent, and their names would
otherwise collide.

| Module | Content |
| --- | --- |
| `TPA.Count` | The Tootsie Pop Algorithm (Huber, 2010). The closed form `tpaTail` for `P(U₁ ⋯ U_m > c)`, its one-dimensional integral recursion, the resulting Poisson law for the number of contractions, and almost-sure termination. |
| `TPA.UniformProduct` | The identification of `tpaTail` with the probability it is named for: on the product of `m` copies of `Uniform(0,1)` the event `{U₁ ⋯ U_m > c}` really does have measure `tpaTail m c` (for `0 < c < 1`), and consecutive differences are the Poisson masses `poissonPMF (ln(1/c))`. |
| `TPA.TwoPhase` | The arithmetic of the two-phase run-count schedule: the exact phase-one threshold, the phase-two budget inequalities (which force `1 ≤ A`), and the passage from additive log accuracy to relative accuracy. |

TPA estimates a ratio `μ(B)/μ(B')` for a centre `B'` inside a shell `B`, given a
nested family interpolating between them. It replaces the classical
self-reducibility product estimator, whose output is a product of scaled
binomials, by a single Poisson random variable — which is why its analysis is
sharp, and why it is worth having as reusable infrastructure.

### `Arlib.Approximation` — relative-error approximation

6 modules. An approximation algorithm's guarantee is a *window*: the value it
reports lies in `[lo·v, hi·v]` around the truth. Windows compose, sum, telescope
and must be calibrated, and that algebra is problem-independent — it is
`MulError`, the area's foundation. Built on it, `Coresets/` develops **domain
reduction for `ℓ¹` linear tests** — a weighted set of points, each carrying a
feature vector, summarised by a much smaller weighted set that reproduces `∑ᵢ μᵢ |⟨y, vᵢ⟩|` — the weighted
sum of *absolute* linear tests — for **every** query `y` simultaneously. That
functional is `‖Ay‖₁` for the matrix `A` with rows `μᵢ vᵢᵀ`, so the sets that do
this are exactly the outputs of an `ℓ¹` subspace embedding, and Lewis-weight row
sampling is how one is produced.

Lewis weights themselves are **not** here. This area formalizes what one may do
with a reduction once one has it; a development that needs one takes the sampling
guarantee as an explicit hypothesis, in the `KnowledgeCompilation` style.

The area's organising commitment: **the guarantee is uniform over queries**, and
every construction preserves that uniformity. A reduction built now will be
tested later against a query not yet determined — by the coordinates a dynamic
program has not reached, or by the sibling region of a circuit not yet processed.
A per-query guarantee would need a union bound over exponentially many queries
and nothing would survive.

| Module | Content |
| --- | --- |
| `MulError` (area level) | Two-sided multiplicative windows `Between lo hi a b`, their composition, summation and telescoping, and the `δ = ε/(3n)` calibration. `Between.sum` needs **no sign hypothesis** — the two inequalities are summed term by term — and the calibration's upper half is `(1+a)^n ≤ 1 + 2na` for `na ≤ ½`, by elementary induction: no exponential, no logarithm. Nothing here mentions coresets. |
| `Coresets.Basic` | The linear test `dot`, weighted point sets `WPS ι d`, the evaluation functional `WPS.E`, and `WPS.exact` on a whole finite domain. Points are an **indexed family**, not a `Finset` of features: two points may carry the same vector, and a construction that merged them would be wrong (their weights must add). |
| `Coresets.Embedding` | `Embeds lo hi U C` — `C` reproduces every linear test on `U` inside the window. Reflexivity, composition (the source of the `(1 ± δ)^L` exponent), widening, and `sum_queries`, the form in which one factor's reduction is consumed by the other. The window is kept **asymmetric** throughout, because composition does not preserve symmetry. |
| `Coresets.Tensor` | The Cartesian product with features combined **bilinearly** through a structure tensor, the two **Fubini identities** viewing a linear test on the product as a linear test on either factor, and hence `Embeds.tensor`: reducing each factor reduces the product, the windows multiplying. Proved by replacing one factor at a time — the right against the exact left, then the left against the already-reduced right. `WPS.hadamard` is the diagonal case, which is what a mixture of product distributions needs. |
| `Coresets.Linear` | Reparametrising features by a fixed matrix is free: `⟨y, Lv⟩ = ⟨Lᵀy, v⟩`, so a reduction survives with the same window and the same number of points. This is why a layer of sum gates in a circuit costs nothing and only *product* steps are ever sparsified. |
| `Coresets.RegionTree` | The assembled engine: `Region`, a tree whose feature map at an internal node is bilinear in its children's; `Reduction`, a bottom-up choice of reduced set at each internal node; and `embeds_exact`, the **propagation invariant** — if every internal node was sparsified to within `(1 ± δ)`, the root reproduces every linear test on the entire exact domain to within `(1 ± δ)^{steps}`. `exactReduction` witnesses that the hypothesis is satisfiable, so the theorem is not vacuous. The coordinate index is an arbitrary finite type, not a `Fin`, so a P-block/Q-block instantiation `Fin g ⊕ Fin g` needs no index arithmetic. |
| `StructuredCircuit` | **V-trees** and **structured arithmetic circuits**: `Vtree` (a binary tree over variables with a joint assignment space `Vtree.Assign`) and `Circuit V g`, a circuit whose scope decomposition *is* `V`. Two circuits **share a v-tree** exactly when indexed by the same `V` — the honest hypothesis under which a single coreset per region compares them (a function consuming two circuits over a shared `V` recurses on both at once and only typechecks because the shared index forces matching constructors); they may otherwise differ in gate counts and wiring. `toRegion` gives a circuit's feature map as a `Region`. |

`steps` counts internal nodes **with multiplicity down the tree**. That this
equals the number of distinct sparsification calls — which is what a union bound
over the calls needs — holds precisely because the region graph is a *tree*; on a
region DAG with shared regions the two counts come apart, and nothing here covers
that case. `Coresets.RegionTree`'s docstring says so.

The first client is the formalization of *Total Variation Distance Estimation
through Domain Reduction*, which uses `Coresets.Tensor` for its dynamic program
over coordinates and `Coresets.RegionTree` for its structured probabilistic
circuits.

### `Arlib.MDP` — finite Markov decision processes, reachability objectives

11 modules, ~2.6k LOC. The control layer over `Arlib.MarkovChains`: an `MDP S A`
carries its transition kernel as a `MarkovChains.FinKernel (S × A) S`, so every
one-step expectation in the area *is* `FinKernel.act` and the kernel algebra is
inherited rather than re-proved.

**Scope.** The objective throughout is **reachability** — maximise the
probability of ever hitting the target set `S_T`. There are no rewards and no
discount factor, and the terminal/target partition is part of the `MDP`
structure. What replaces the missing discount factor is the hitting-time weight
`T_s`, and the central result is that it supplies a genuine contraction.

`MarkovChains.Techniques.{HittingTime, RankingSupermartingale, ProgressPath,
ReachDistance}` are the **fixed-chain** version of the same story; this area is
those questions with a `sup` over policies in front of them.

| Module | Content |
| --- | --- |
| `MDP.Basic` | The `MDP` structure over a `FinKernel`; the state partition `Sₙₜ` / `S_T` / `S_N` and the enabled non-terminal pairs `SAnt`; the greedy value `vmax`. |
| `MDP.Bellman` | The Bellman optimality operator `H` and the boundary extension `extVal` — `1` on a target, `0` on a non-target terminal, `max_{a'} Q(s',a')` on a non-terminal. |
| `MDP.EndComponent` | `IsEC` (closed + strongly connected), the no-EC condition `NoEC`, reachability from `s₀`, and `AllReachable`. |
| `MDP.HittingWeight` | The `HittingWeight` interface — the worst-case expected time to termination `T_s` — and the contraction factor `β = 1 − 1/maxₛ T_s < 1`. |
| `MDP.WeightedNorm` | `‖Q‖_w = max_{(s,a) ∈ Sₙₜ×A} \|Q(s,a)\|/w(s,a)`, its pointwise form `WLe`, and the bridge between them. |
| `MDP.Contraction` | **The crux**: `H` is a `β`-contraction in the `T_s`-weighted maximum norm. Proved for *two arbitrary arguments*, which is what lets `Q*` be constructed rather than assumed. |
| `MDP.FixedPoint` | `Q*` **constructed** by value iteration from `0` plus Banach, with `H_Qstar`, uniqueness (`eq_Qstar_of_fixed`) and `Qstar_mem_Icc`. |
| `MDP.Termination` | `exists_hittingWeight_of_noEC`: no end component ⟹ a uniform escape probability ⟹ a bounded expected hitting time. The `HittingWeight` interface is *discharged*, not postulated. Runs on the survival values `surviveVal`, the `Good` sets and `EscapeBound`. |
| `MDP.Reachability` | `V*` and `Q*` by dynamic programming (`reachVal`, `Vstar`, `Qsem`), the Bellman optimality equations, and `Qsem_eq_Qstar` coupling the semantic value to the fixed point. |
| `MDP.Trajectory` | Trajectory probabilities, with `pathProb_eq_prod` giving the honest product `∏ₖ P(s_{k+1} ∣ s_k, π(s_k))`, and **`isGreatest_reachProbSem`: the dynamic program is the attained maximum over policies**, not merely a supremum. `Vstar_isLUB_reachProbSem` at the infinite horizon. |
| `MDP.PolicyValue` | `V^π` by the same route one policy at a time; the policy operator `Hpi` and its contraction; `Vpi_eq_Vstar` for a greedy-optimal policy; `greedy_eventually_optimal` and `tendsto_Vpi_greedy`. |

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
    Approximation.lean            # area root
    Approximation/MulError.lean   # multiplicative error windows
    Approximation/Coresets/*.lean # Basic, Embedding, Tensor, Linear, RegionTree
    Approximation/StructuredCircuit.lean # v-trees and structured circuits
    MarkovChains.lean     # area root
    MarkovChains/
      Techniques/*.lean   # machinery valid for any finite chain
      Chains/*.lean       # analysis of specific chains
    KnowledgeCompilation.lean   # area root
    KnowledgeCompilation/
      Circuits/*.lean       # the representation languages themselves
      Communication/*.lean  # rectangles and the complexity measures
      LowerBounds/*.lean    # the bridge, the lifting, the separations
      BranchingPrograms/*.lean  # NROBP size lower bounds via matching width
      Forgetting/*.lean     # compiling DNNF by forgetting auxiliary variables
    Automata.lean         # area root
    Automata/*.lean       # NFA/DFA/UFA, and state lower bounds via communication
    MDP.lean              # area root
    MDP/*.lean            # finite MDPs with reachability objectives
```

## License

Released under the [Apache License 2.0](LICENSE), following Mathlib. Copyright ©
2026 Kuldeep S. Meel.

## Acknowledgements

Built with the assistance of **Claude** (Anthropic's Claude Code).
