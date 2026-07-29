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
sampling is how one is produced.  Lewis weights themselves **are** here, under
`LewisWeights/`: their existence is proved (`exists_isLewis`), and so is the fact
that importance sampling by them yields a genuine `(1 ± δ)` embedding for every
query simultaneously (`lewis_importance_embeds`), whose conclusion is literally
the `Coresets.Embedding.Embeds` predicate the rest of the area consumes.

The two halves are nonetheless kept apart on purpose.  Everything under
`Coresets/` takes `Embeds` as an *explicit hypothesis* and never mentions a
sampler, in the `KnowledgeCompilation` style, so a consumer may discharge it from
`LewisWeights/` or from any other construction, and nothing under `Coresets/`
has to be re-proved when the sampler's size bound improves.

The uniformity over queries is the point of the whole subject.  A reduction built
now will be tested later, against a query that is not yet determined — by the
coordinates a dynamic program has not reached, or by the sibling region of a
circuit that has not been processed.  Everything under `Coresets/` is organised
around propagating a guarantee that does not know what it will be asked.

## What the cost model constrains, and what it does not

The second half of the area — `Counting` and everything downstream of it —
models an algorithm as `RandAlg α β := α → PMF (β × ℕ)`, the joint law of an
output and a *recorded step count*.  **`Arlib.Approximation` has no model of
computation.**  There is no machine, no instruction set, and no relation between
the `ℕ` a `RandAlg` records and any work anything does; the `ℕ` is data the `PMF`
carries.  Both `IsFPRAS.polytime` and `IsFPAUS.polytime` constrain it only
through an **upper** bound `c · (size w + … + 1) ^ d` whose constants `c` and `d`
are *existentially quantified*.

The consequence deserves stating plainly, because no statement in the area
displays it: the algorithm that records `0` steps satisfies the `polytime` clause
of `IsFPRAS`, of `IsFPAUS`, and of any other predicate built on `RandAlg`
— including `CQCount`'s `IsBPPDecider` — for free.  A zero-cost non-algorithm
meets every running-time requirement stated here.  Whether a `RandAlg` is
computable at all is never asked, and could not be asked of a `PMF` on an
arbitrary type.  So a `polytime` clause discharged in this library is a
bookkeeping fact about a number the caller supplied, not evidence that anything
runs; running time is an *assumption* discharged elsewhere, exactly as circuit
size is in `Arlib.KnowledgeCompilation`.

There are three moves here and it is worth keeping them apart, because the first
two are not enough.  `RandAlg`'s `ℕ` is constrained **only from above, and with
existentially quantified constants**.  `Pinned` makes the second move: it
re-states the clauses with `c` and `d` as parameters, so a development that has
computed an exponent can say which one.  But naming the constants does not by
itself exclude the degenerate model — `Pinned.IsFPAUS.pinnedTime_of_cost_zero`
and `Pinned.IsFPRAS.pinnedTime_of_cost_zero` *prove* that the zero-cost sampler
and the zero-cost estimator satisfy `PinnedTime size A c e` at **every** pair of
constants, `(0,0)` included, precisely because a pinned bound is still an upper
bound.  The third move is what closes it: `Charges` (`∀ p ∈ support, 0 < p.2`),
in an `IsFPAUS` and an `IsFPRAS` form, is the weakest companion the zero-cost
non-algorithm fails, and `Charges.map_add` is the fact that it survives every hop
that only *adds* cost, so it transports along a reduction rather than having to
be re-established.  **`Charges`, not pinning, is what rules out the degenerate
model**; `Sampling`'s `retrySampler_cost_ge` is how a real sampler supplies it.
A cost claim in this area is therefore only as strong as the *sandwich* — an
upper bound with named constants together with a lower bound — and an upper
bound quoted on its own, however small its constants, remains a bookkeeping fact
about a number the caller supplied.

None of that weakens the theorems below, because they are not about cost.  What
the definitions genuinely constrain is **accuracy**, and there the constraint
bites on a real object: `outProbR`, the pushforward of the law onto the output,
is pinned inside a multiplicative window at a fixed success probability, which is
a falsifiable property of an actual `PMF`.  `IsFPRAS.comp_parsimonious` and
`IsFPAUS.comp_bijection` transport such a guarantee along a reduction with no
loss in `ε`, `δ` or the `3/4`; `IsFPRAS.amplify` raises the confidence to
`1 - δ`; `card_unionAll_eq_sum_mul_hitProb` is an exact counting identity with no
probability in it at all; `isFPRAS_unionFprasAlg` assembles an estimator out of
per-disjunct ones.  Those are theorems about laws, and the laws are the part that
was modelled.

| Module | Content |
| --- | --- |
| `MulError` | Two-sided multiplicative windows `Between lo hi a b`, their composition, summation and telescoping, and the `δ = ε/(3n)` calibration — with `(1+a)^n ≤ 1 + 2na` proved by elementary induction rather than through the exponential. Also the full `(1 ± ε)` calculus for *independent* windows — `Between.mul`, `.pow`, `.prod`, `.div` with their symmetric `relErr` faces — and two machine-checked **refutations** of the folklore forms the source papers use: `one_add_pow_lt_one_add_mul_example` (`(1+ε)^n ≰ 1+nε`) and `relErr_div_counterexample` (a ratio of two `(1±ε)` quantities need not be `(1±ε)`), with the honest replacements `one_sub_two_mul_le_one_sub_pow` and `Between.relErr_of_pow_calibrated`, which need `n·ε ≤ 1/2` and a factor `2`. `compose_tol_le` and `tol_absorb` are the tolerance bookkeeping. Mentions no data structure at all. |
| `Coresets.Basic` | The linear test `dot`, weighted point sets `WPS ι d`, the evaluation functional `WPS.E`, and the unreduced set `WPS.exact` on a whole finite domain. |
| `Coresets.Embedding` | `Embeds lo hi U C` — `C` reproduces every linear test on `U` inside the window. Reflexivity, composition (the source of the `(1 ± δ)^L` exponent), widening, and the family-of-queries form in which one factor's reduction is consumed. |
| `Coresets.Tensor` | The Cartesian product of two weighted point sets with features combined **bilinearly**, the two Fubini identities that view a linear test on the product as a linear test on either factor, and hence the composition theorem: reducing each factor reduces the product. The Hadamard product is the diagonal special case. |
| `Coresets.Linear` | Reparametrising features by a fixed matrix is free — `⟨y, Lv⟩ = ⟨Lᵀy, v⟩`, so a reduction survives with the same window and the same number of points. This is why a layer of sum gates costs nothing and only product steps are ever sparsified. |
| `Coresets.RegionTree` | The assembled engine: a tree of regions whose feature map is bilinear in its children's, a bottom-up choice of reduced set at each internal node, and the **propagation invariant** — if every internal node was sparsified to within `(1 ± δ)`, the root reproduces every linear test on the entire exact domain to within `(1 ± δ)^{steps}`. |
| `LewisWeights` | **Cohen–Peng ℓ₁ row sampling by Lewis weights, proved rather than assumed** — the sub-area that *supplies* the reduction `Coresets/` consumes. Twenty-four modules with their own root and roadmap; see `Approximation/LewisWeights.lean` for the module-by-module table. `Existence.exists_isLewis` constructs ℓ₁ Lewis weights by a Banach fixed point, `Trace.sum_lewis_eq_card` is the trace identity `∑ᵢ w̄ᵢ = d`, and `Sensitivity.abs_dot_le_lewis_L1` the ℓ₁ sensitivity bound `\|aᵢ·y\| ≤ w̄ᵢ‖Ay‖₁`. The headline is `Embed.lewis_importance_embeds`: for spanning nonzero rows, `m`-fold importance sampling by Lewis weights returns — off an explicit small failure event, with no `Classical.choice` in the decoding — a reweighted subset satisfying **exactly the `Coresets.Embedding.Embeds` predicate** at `(1 ± δ)` for every query simultaneously, assembled from a bounded-independent-sum Chernoff bound (`Bernstein`, `SampleConc`), an ε-net of the Lewis-metric unit ball (`Net`, `MNet`) and Lipschitz control of both functionals (`EmbedAux`). That route certifies `O(d² log d · δ⁻²)` points — polynomial but not optimal, the net's `log\|net\| = Θ(d log d)` costing one extra factor of `d`. The net-free route reaches the optimal-in-`d` uniform tail `RouteA.process_uniform_tail` through the sup-bridge `SupBridge.lewlinf`, and the symmetrization/contraction chain (`SymmSwap`, `Symmetrize`, `Contraction`, `MomentReduct`) is proved for the *sampling* moment; what is still open is the supremum-level contraction, which needs suprema-of-stochastic-processes infrastructure Mathlib does not have. |
| `Counting` | `IsFPRAS` and `IsFPAUS`: what it *means* for a randomized algorithm to approximately count, or almost uniformly sample, the solutions of an instance. An algorithm is modelled as the joint law of its output and its step count (`RandAlg α β := α → PMF (β × ℕ)`), so accuracy and worst-case running time are both statements about one `PMF`. The success probability is the fixed constant `3/4`; an FPRAS may be polynomial in `ε⁻¹` where an FPAUS must be polynomial in `log(1/δ)`. |
| `Parsimonious` | A **parsimonious reduction** `f w = g (h w)` transports both guarantees: `IsFPRAS.comp_parsimonious`, and — given a family of bijections between solution sets, which is what lets a sample be decoded — `IsFPAUS.comp_bijection`. Neither `ε`, `δ` nor the `3/4` confidence is degraded; the only cost is running time, and that is elementary `Nat` arithmetic (`poly_comp_add`). |
| `Pinned` | The companions of `PolyBounded`, `IsFPRAS.polytime` and `IsFPAUS.polytime` **with the constants written down**. `PolyBounded s B` is `∃ c e, PinnedBounded s B c e` on the nose (`polyBounded_iff`), and that existential is the reason a zero-cost non-algorithm satisfies every complexity claim in the area: an algorithm whose exponent has actually been computed has, through `PolyBounded`, no way to say so. `PinnedBounded`, `IsFPRAS.PinnedTime` and `IsFPAUS.PinnedTime` are the unquantified forms — predicates *about* an algorithm rather than fields of a structure, so that they attach to an existing conclusion without changing its type. `pinnedCompConst c c' c'' d = c(c'+2)^d + c''` and `pinnedCompExp d d' d'' = max (max d' 1 · d) d''` promote the witnesses of `Parsimonious.poly_comp_add` out of its proof term and into a statement, and `IsFPRAS.comp_parsimonious_pinned` / `IsFPAUS.comp_bijection_pinned` are the transfer theorems with the exponent surviving the hop — each returning a **conjunction** of the original conclusion (proved by the original theorem, so the two cannot disagree) with the named bound on the same composed algorithm. The `_on` variants assume the source algorithm's bound only *along the reduction*, which is what a target whose running-time analysis carries standing normalisation hypotheses can actually supply. `PinnedReduction` is `ParsimoniousReduction` with the two constants named, and forgets to it. **Naming the constants is not by itself enough**, and the module says so with a theorem: `IsFPAUS.pinnedTime_of_cost_zero` shows the algorithm recording `0` satisfies `IsFPAUS.PinnedTime size A c e` at *every* pair of constants, `(0,0)` included, because a pinned bound is still only an **upper** bound. `IsFPAUS.Charges` — `∀ p ∈ support, 0 < p.2`, deliberately weak, "records something" rather than "records at least the bound", which would be false for any algorithm with a fast path — is the minimal companion that excludes it, `Charges.not_cost_zero` is the incompatibility (non-vacuous, since a `PMF`'s support is never empty), and `IsFPAUS.Charges.map_add` carries it across the "run `B` at `h w`, relabel, add `cost w`" shape common to every reduction here, so a caller transports the whole sandwich and not just its upper half. The counting side has all four — `IsFPRAS.pinnedTime_of_cost_zero`, `IsFPRAS.Charges`, `IsFPRAS.Charges.not_cost_zero`, `IsFPRAS.Charges.map_add` — spelled out rather than derived from a common generalisation, because the two `PinnedTime`s differ in their second size parameter (`⌈ε⁻¹⌉₊` against `⌈log(1/δ)⌉₊`) and a shared abstraction would have to be indexed by that choice. **And the counting degeneracy is strictly worse than the sampling one.** `IsFPAUS` has three clauses, so a zero-cost sampler must still meet `uniform` and `empty`; `IsFPRAS` has only `accuracy` and `polytime`, and a zero-cost estimator may also be *exact* — return the count with probability `1`, so `outProbR = 1 ≥ 3/4` — which makes it a **complete `IsFPRAS` at every pinned pair of constants**, not merely a satisfier of the cost clause. `IsFPRAS.Charges` is therefore doing more work than its sampling twin, not less; `CQCount.Cost.FinWitness.isFPRAS_exactCount` is precisely that object, kept in the sibling repo as a satisfiability certificate and explicitly *not* an algorithm. That repo is also where the machinery is used rather than merely defined: the counting half of the project's headline theorem no longer carries `∃ c d` at its head, but a `#TA`-level `IsFPRAS.PinnedTime` and a `#k-HW` statement at an explicit constant and exponent. |
| `Amplification` | **Median amplification** — the missing bridge between the `3/4` in the *definition* of an FPRAS and the `1 - δ` that concrete schemes are proved to achieve. `repeatPMF`/`medianAlg` run a scheme `m` times independently (a `PMF.bind` tower, costs summed) and return the median; `median_mem_Icc_of_majority`, on top of `Arlib.Probability.Median`, says a majority landing in an interval drags the median in with it; `IsFPRAS.amplify` takes `m = ⌈8 log(1/δ)⌉₊` and gets confidence `1 - δ` with the running-time bound's constant multiplied by `m` and its degree untouched. The Hoeffding step is the named hypothesis bundle `MajorityConcentration`, in the `KnowledgeCompilation.Imported` style, because `Probability.Chernoff` is stated for finite `FinProb` products while an algorithm here lives on an uncountable `PMF`. |
| `Concentration` | **`MajorityConcentration`, proved** (`majorityConcentration`) — so `IsFPRAS.amplify` and `IsFPRAS.amplify_isFPRAS` are now unconditional, and the `Amplification` row's "imported hypothesis" is history. Not a transport of `Probability.Chernoff`: the multiplicative bound gives only `exp(-m/24)` where the sharp Hoeffding constant `exp(-m/8)` is what the statement fixes. Instead the Chernoff argument is run on the `PMF.bind` tower directly. `pexp_repeatPMF_pow` — the expectation of `c ^ #{i \| v i ∈ S}` over `repeatPMF μ m` equals `(P[X ∉ S] + c · P[X ∈ S])^m`, by induction along `repeatPMF`'s own recursion — is the only use of independence and the only place a product is ever unfolded; the count's law is never named, so no binomial distribution appears. Markov at `s = 1`, plus `exp_half_mul_quarter_le`, reduces the whole bound to `(e + 3)^8 ≤ 65536 e^3`. |
| `KarpLuby` | The **union-of-sets estimator**. `card_unionAll_eq_sum_mul_hitProb` is the exact identity `\|⋃ⱼ Aⱼ\| = Σⱼ \|Aⱼ\|·pⱼ` with `pⱼ` the first-occurrence probability, proved by exhibiting the bijection onto `{(j,x) : x ∈ Aⱼ, ∀ j' < j, x ∉ A_{j'}}`; `totalCard_le_mul_card_unionAll` is the `1/ℓ` bound on the acceptance rate. The estimator is built in the *coverage* formulation — one draw from `Σⱼ Aⱼ`, accept on first occurrence — which needs a single application of Hoeffding and **no union bound over `j` at all**, unlike the per-`pⱼ` route the source papers take. `isFPRAS_unionAlg` at `h = O(ℓ² log(1/δ)/ε²)`. |
| `Hoeffding` | **`HoeffdingBound`, proved** (`hoeffdingBound`) at the sharp two-sided constant `2·exp(-2ht²)`, making `KarpLuby` unconditional. Mathlib at this tag has no Hoeffding lemma — `Probability/Moments/SubGaussian.lean` does not exist — so `one_sub_add_mul_exp_le` (`1 - q + q e^s ≤ e^{sq + s²/8}` for `q ∈ [0,1]`) is proved from the Bernoulli CGF's second derivative, `L'' = q(1-q)e^s/D² ≤ 1/4`. The two tails then come from `Concentration.pexp_repeatPMF_pow` at `c = e^{±4t}`, `s = ±4t` being where `-st + s²/8` bottoms out at `-2t²`. `cosh_le_exp_half_sq` would have given only the weak constant `2exp(-ht²/2)`. |
| `SelfReducible` | The **telescoping rejection sampler**: given a partition-chain structure on a finite solution set and a *deterministic* estimator accurate to `(1±η)` at every node, the walk-and-reject algorithm is **exactly** uniform conditioned on acceptance. `prod_card_ratio_chainFrom` is the telescoping identity `∏ⱼ pⱼ = 1/\|U root\|` on its own, with no probability in sight; `chainFrom_unique` and `walk_support_eq` are what make the acceptance step well defined. The acceptance rate must be shown `≤ 1`, not merely `≥ 1/4`: `accProb` is clamped to keep the sampler total, and a clamp that fires does so by *different amounts at different solutions*, destroying the very uniformity being claimed. `accProb_eq` shows the hypothesis `hacc` stops it firing, and one hypothesis covers both endpoints. |
| `Sampling` | Turning a *defective* sampler into an `IsFPAUS`. Two independent defects are repaired: a preprocessing step that fails with probability `δ₀` and cannot be detected as having failed, and a per-call `FAIL` rate of `3/4`. `between_of_abs_sub_le` is the additive-to-multiplicative conversion — an additive-`δ₀` approximation to the uniform law is a multiplicative `(1±δ)` one once `δ₀ ≤ δ/\|U\|` — and it needs no nonemptiness hypothesis. `retryPMF` is bounded repeat-until-success, with `outProbR_retryPMF` showing the loop scales *every* solution's probability by the same `1 - f^k`; the perturbation is therefore already multiplicative, so `k = Θ(log δ⁻¹)` suffices and the `log\|U\|` factor the source papers carry is unnecessary. `PreprocessedSampler.isFPAUS` assembles both, and needs `log \|g w\|` to be polynomially bounded — the one hypothesis without which the `polytime` clause cannot hold. The cost bound is also proved in the *other* direction, which is what makes `Pinned`'s `IsFPAUS.Charges` reachable through the retry loop: `one_le_retryCount` says `retryCount δ` is never zero on `(0,1)`, so at least one attempt always runs; `retryPMF_cost_ge` says a loop that runs charges at least what its attempt charges; and `retrySampler_cost_ge` combines them over both branches of the mixture — with its hypotheses at `preTol g w δ`, the tolerance at which the assembly actually invokes `good` and `bad`, which is the weakest form a caller can discharge. Paired with `retryPMF_cost_le` this *sandwiches* the assembled sampler's cost, and an upper bound alone is no evidence that any work was done. |
| `KarpLubyApprox` | `KarpLuby` again, but with the two exact ingredients replaced by approximate ones — the disjunct sizes `\|Aⱼ\|` known only to `(1±ε₀)`, and the draw from `Aⱼ` only almost uniform. The perturbed acceptance probability is computed exactly (`outProbR_perturbedTrialAlg_one`), and the resulting tolerance is the explicit `klEta ε₀ δ₀ = 2ε₀/(1-ε₀) + δ₀ + (2ε₀/(1-ε₀))·δ₀`: the index-weight window is the *ratio* tolerance `2ε₀/(1-ε₀)`, not `ε₀`, and the third summand is the cross term. **`ℓ` does not appear in `η`** — summing over the `ℓ` indices is free — so it enters only the sample count. `klBudget` witnesses satisfiability (`ε₀ = ε/28`, `δ₀ = ε/16`, `ε₁ = ε/8`). The index window is required only when the family is nonempty: on the empty family every true weight is `0` and no PMF lies in a multiplicative window around them, yet the estimator is exact there anyway. `isFPRAS_unionFpausAlg` is the assembled result, from per-disjunct `IsFPAUS` samplers plus *deterministic* size estimates; upgrading those to `IsFPRAS` estimates needs a heterogeneous product `PMF`, which `KarpLubyFpras` supplies. |
| `UnionBound` | Failure-budget bookkeeping for staged randomized algorithms. `one_sub_sum_le_prod_one_sub` (`∏(1-aᵢ) ≥ 1-∑aᵢ`, which Mathlib lacks — it has only the *identity* `Finset.prod_one_sub_ordered`), the union bounds over `outProbR`, and `one_sub_le_outProbR_biInter_of_le_div`: to advertise `1-δ` overall, each of `k` sources must run at `δ/k`. `one_sub_rpow_le_of_geom_step` is the geometric invariant `1 - 2^{-γ+2i}` — true as stated, but needing the unstated `γ ≥ 1`, since the step multiplies by `1 - 2^{-γ+1}`. |
| `RejectionCollect` | Collecting `h` samples from an oracle that *fails*. `collectLaw_toOuterMeasure` is the exact factorisation `Pr[the loop returns a full list ∧ that list ∈ A] = binTail (d none) s c (h-\|acc\|) · Pr_{l ∼ iidList ν (h-\|acc\|)}[acc ++ l ∈ A]`, by induction on the call budget, with no hypothesis beyond `d (some x) = s·ν x` and no independence side condition — a fresh oracle call *is* a `PMF.bind`. Its two halves are what a caller wants: `collectLaw_full` identifies the loop's success probability as a binomial upper tail, and dividing gives that the conditional law of the retained samples is exactly `iidList ν h`, so **discarding failures neither biases nor correlates the survivors** — and neither does the early-stopping guard, which makes the number of oracle calls a random variable depending on the samples already drawn. `binTail_eq_outProb_repeatPMF` identifies `binTail` with a `repeatPMF` event so `Hoeffding.outProbR_lower_tail` applies verbatim, giving `one_sub_exp_le_binTail`; `le_outProbR_collectSamples` packages both as `Pr_{iidList ν h}[A] - exp(-2ct²) ≤ Pr[collect full ∧ ∈ A]` — *analyse the algorithm as if it drew `h` exact i.i.d. samples, and pay `exp(-2ct²)` once*. The budget hypothesis `h/c ≤ s - t` is not removable: at `c ≤ h/s` the probability of `h` successes is exponentially small, not large. |
| `CountLaw` | The identification of an algorithm's `List.countP` statistic with the sum a concentration theorem talks about: the pushforward of `RejectionCollect.iidList ν n` along `l ↦ (l.countP p : ℝ)` is the pushforward of `Amplification.repeatPMF (countTrial ν p c) n` along `q ↦ ∑ᵢ q.1 i`, for every `ν`, every predicate, every `n` and every cost. One induction along the two recursions, which are the same recursion — `List.countP_cons` on one side, `Fin.sum_cons` on the other — and no independence hypothesis, because in both terms independence *is* the `PMF.bind`. `map_countP_iidList_congr` lets the predicate be replaced by any predicate agreeing with it on `ν.support`, which is what reconciles the predicate an algorithm tests with the one its analysis uses; its engine `bind_congr_support` is the "almost surely" form of `PMF.bind` congruence that Mathlib lacks. |
| `KarpLubyFpras` | `KarpLubyApprox`'s last deterministic hypothesis removed: the disjunct sizes are estimated by genuine per-disjunct **`IsFPRAS`** counters, not oracles. The asymmetry that makes this work is that an `IsFPAUS` guarantee is about the law of one run and composes unconditionally, while an `IsFPRAS` guarantee holds only with probability `3/4`, so each `Ñ(Aⱼ)` is a *random* real. Three new pieces: `outProbR_bind_ge`, the chain rule `Pr[A ∧ B] ≥ Pr[B\|A]·Pr[A]` on a `PMF.bind` with **no independence assumed** (paper-independent; `CQCount.TA.outProbR_bind_ge` duplicates it); `prodPMF`, the product of `ℓ` **heterogeneous** runs — `Amplification.repeatPMF` repeats one law and does not apply — with the same recursion, hence the same cost induction, and **exact coordinate marginals** (`outProb_prodPMF_coord`), which is what makes the union bound over the `ℓ` coordinates an application of `UnionBound` rather than a new induction; and `exists_uniform_polytime`, one polynomial bound for a whole finite family of schemes. The `3/4` is split `1/8` for the size estimates (`1/(8ℓ)` each, so `sizeReps ℓ = ⌈8 log(8ℓ)⌉₊` median repetitions) and `1/8` for the estimator's own Hoeffding deviation — which is why the scheme calls `estimateApproxAlg` directly rather than `unionApproxAlg`, whose confidence is hard-wired at `1/4`. `isFPRAS_unionFprasAlg` is the headline and `isFPRAS_unionFpras_of_isUnion` its consumer form; `isFPRAS_unionFprasAlg_satisfiable` exhibits a nondegenerate instance satisfying all three hypothesis bundles. |

The **structured (probabilistic) circuits** that ride on this engine — v-trees,
single circuits, and pairs of circuits over a shared v-tree — live under
`Arlib.KnowledgeCompilation.Probabilistic`, not here.

This is the area root; it re-exports the modules below.
-/

import Arlib.Approximation.MulError
import Arlib.Approximation.Coresets.Basic
import Arlib.Approximation.Coresets.Embedding
import Arlib.Approximation.Coresets.Tensor
import Arlib.Approximation.Coresets.Linear
import Arlib.Approximation.Coresets.RegionTree

import Arlib.Approximation.LewisWeights

import Arlib.Approximation.Counting
import Arlib.Approximation.Parsimonious
import Arlib.Approximation.Pinned
import Arlib.Approximation.Amplification
import Arlib.Approximation.Concentration
import Arlib.Approximation.KarpLuby
import Arlib.Approximation.Hoeffding
import Arlib.Approximation.SelfReducible
import Arlib.Approximation.UnionBound
import Arlib.Approximation.Sampling
import Arlib.Approximation.RejectionCollect
import Arlib.Approximation.CountLaw
import Arlib.Approximation.KarpLubyApprox
import Arlib.Approximation.KarpLubyFpras
