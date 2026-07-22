/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Optimal mixing in total variation: entropy contraction composed with Pinsker

`Chains/ProductOptimalMixing.lean` proves `O(n log(n/ε))` mixing for the Gibbs
sampler of a product measure **in relative entropy**, and says in bold that no
total-variation bound at that rate is claimed, for one reason only: the library
had no Pinsker inequality.  `Techniques/Pinsker.lean` now supplies one, with the
sharp constant.  This module closes the loop, and then states the resulting
comparison with the variance route *in the same distance*, which is the only way
the two step counts can honestly be put beside each other.

## Where this file sits

The generic composition — entropy contraction plus Pinsker gives a mixing time in
total variation — mentions no state space, no spin system and no product measure,
and lives in `Techniques/EntropyMixing.lean` by the rule of §1.1 of the roadmap.
What is here is the *instance*: that composition applied to the Gibbs sampler of
a product measure, and the arithmetic of comparing it against the variance route.

## The composition does not pass through χ²

`Techniques/Pinsker.lean` records that chaining Pinsker after
`EntropyVariational.klDiv_le_chiSq` gives `‖·‖_TV ≤ √(D_{χ²}/2)`, which is worse
than the direct `TotalVariation.tvDist_sq_le_chiSq` by a factor `√2`; Pinsker
earns its place only on divergence bounds of *entropy* origin.  The chain of
lemmas used below is

  `EntropyContraction` → `Ent_act_le` (by `localEnt_eq_Ent_sub_Ent`) →
  `klDiv_push_le` → `klDiv_iter_push_le` → `klDiv_iter_row_le` →
  `klDiv_iter_row_le_of_log_le` → `two_mul_tvDist_sq_le_klDiv`,

and `chiSq` occurs nowhere in it.  The variance route appears in this file only
as the *baseline being compared against*, never as an input to the entropy route.

## The two step counts, side by side

Fix a strictly positive product weight on `n = |V|` sites with `a ≤ φ_v(s)` and
`∑_s φ_v(s) ≤ b`, write `L = ln(b/a) > 0`, and ask for total-variation accuracy
`δ` from every starting configuration.  Both of the following conclude
`MixesWithin (glauber …) (gibbs …) δ t`, so they are directly comparable:

| route | requirement on `t` | expanded |
| --- | --- | --- |
| entropy + Pinsker | `n·ln(n·L/(2δ²))` | `n ln n + n ln L + 2n ln(1/δ) − n ln 2` |
| variance, PSD, no lazy | `n·ln(1/(2δ)) + (n²/2)·L` | `n ln(1/δ) − n ln 2 + (n²/2) L` |

**What the entropy route buys.**  The `μ_min` term collapses from `(n²/2)·L` to
`n·(ln n + ln L)`: `Θ(n²)` becomes `Θ(n log n)`.  Its entire source is
`EntropyDecay.klDiv_dirac` against `MixingTime.chiSq_dirac` — the initial
divergence of a point mass is `ln(1/μ(σ)) ≤ nL` where the χ² route pays
`1/μ(σ) − 1 ≤ (b/a)^n − 1`, and it is the number of steps needed to consume that
initial value, `ln` of it, that differs by the exponential.

**What it costs.**  The coefficient of `ln(1/δ)` doubles, from `n` to `2n`.  The
reason is structural and worth naming: `klDiv` decays like `(1 − ρ)^t`, and
Pinsker gives `‖·‖_TV ≤ √(D_KL/2)`, so the total variation decays like
`(1 − ρ)^{t/2}` — **Pinsker halves the effective decay rate of the distance one
actually wanted**, `ρ ↦ ρ/2`.  The variance route has no such loss: `chiSq`
decays like `c^{2t}` and `tvDist_sq_le_chiSq` takes a square root of *that*, so
its TV rate is `1 − c = γ` undiminished.  At `ρ = γ = 1/n` the entropy route's TV
decay rate is `1/(2n)` and the variance route's is `1/n`, which is exactly the
`n ↦ 2n` above.

Quantitatively, `pinsker_step_cost` states the loss as an identity: demanding
`D_KL ≤ δ` needs `n·ln(nL/δ)` steps and demanding `‖·‖_TV ≤ δ` needs
`n·ln(nL/(2δ²))`, and the difference is exactly `n·ln(1/(2δ))` steps.  Note which
part of that is the cost.  The *squaring* `δ ↦ δ²` is the cost, and it is the
`n ln(1/δ)` in the difference; the constant `2` from Pinsker's sharp constant
enters as `−n ln 2`, i.e. it *saves* `n ln 2` steps.  A proof of Pinsker with a
worse constant `κ < 2` would replace that by `−n ln κ` and change nothing
asymptotically — the sharp constant is worth `n ln(2/κ)` steps, never a
logarithm.

**Where the crossover is.**  `entropySteps_lt_varianceSteps_iff` computes it
exactly: the entropy count is the smaller of the two precisely when

  `ln(n·L/δ) < n·L/2`.

So the entropy route wins for every fixed `δ` once `n` is large, and the variance
route wins in the opposite regime of very small `δ` at fixed `n` — the doubled
`ln(1/δ)` coefficient is a real loss and not an artefact of the bookkeeping.

**What is still not claimed.**  Both routes run at `1/n`, and that remains a
coincidence of the product case rather than an instance of any comparison between
the entropy contraction rate `ρ` and the Poincaré constant `γ`.  Nothing here
proves `ρ ≥ γ` or `γ ≥ ρ`, and `Techniques/EntropyDecay.lean`'s caveat to that
effect stands unchanged.

## Main declarations

The generic composition it is built on,
`Techniques.EntropyMixing.EntropyContraction.mixesWithin_of_log_le`, is not
restated here.

* **`glauber_mixesWithin_prodWeight_of_entropy`** — the headline instance with an
  abstract lower bound `m` on the Gibbs measure.
* **`glauber_mixesWithin_prodWeight_of_bounds`** — the headline instance with `m`
  discharged from `a ≤ φ_v(s)` and `∑_s φ_v(s) ≤ b`, hence with no opaque
  constant: `MixesWithin (glauber …) (gibbs …) δ t` once
  `t ≥ n·ln(n·ln(b/a)/(2δ²))`, i.e. `O(n log(n/δ))` **in total variation**.
* **`glauber_mixesWithin_prodWeight_variance_of_bounds`** — the fair baseline:
  `ProductOptimalMixing.glauber_mixesWithin_prodWeight_of_psd` (laziness-free,
  since `glauber_nonnegDefinite` supplies what laziness would manufacture) with
  the same `m` discharged the same way, so that the two requirements on `t` are
  literally comparable expressions in `n`, `L` and `δ`.
* **`pinsker_step_cost`** and **`entropySteps_lt_varianceSteps_iff`** — the two
  arithmetic facts that make the comparison above a statement rather than a
  remark.

Everything here is proved from first principles with no `sorry`; no eigenvalue,
and no spectral notion beyond the Dirichlet form, appears anywhere.
-/
import Arlib.MarkovChains.Chains.ProductOptimalMixing
import Arlib.MarkovChains.Techniques.EntropyMixing

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

/-! ## The headline instance: the Gibbs sampler of a product measure

`ProductOptimalMixing.glauber_klDiv_le_prodWeight` and its explicit form
`glauber_klDiv_le_prodWeight_of_bounds` are bounds on `D_KL`; composing each with
Pinsker turns them into `MixesWithin` statements at the *same* rate, with `ε`
replaced by `2δ²` inside the logarithm. -/

section ProdWeight

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ}
variable [Nonempty V]

/-- **Optimal mixing of the Gibbs sampler of a product measure, in total
variation.**

Let `μ` be the Gibbs measure of a strictly positive product weight on `n = |V|`
sites and let `m > 0` be a lower bound on `μ`.  Then from *every* starting
configuration

  `‖P_GD^t(σ, ·) − μ‖_TV ≤ δ`  as soon as  `ln(ln(1/m)/(2δ²)) ≤ t/n`,

i.e. after `t ≥ n·ln(ln(1/m)/(2δ²))` steps.

This is `ProductOptimalMixing.glauber_klDiv_le_prodWeight` at `ε = 2δ²` composed
with Pinsker, and it is the statement that module could not make: the sentence
"no total-variation bound at rate `O(n log n)` is claimed or proved here" in its
docstring is now discharged.  See `glauber_mixesWithin_prodWeight_of_bounds` for
the form with `m` eliminated, and the module docstring for the comparison against
the variance route — which is now a comparison of two bounds on the same
quantity. -/
theorem glauber_mixesWithin_prodWeight_of_entropy (hφ : ∀ v s, 0 < φ v s)
    (hc : ∀ v, 0 < ∑ s, φ v s) {m δ : ℝ} (hm : 0 < m)
    (hmin : ∀ σ, m ≤ gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
      (Z_prodWeight_pos hc) σ)
    (hL : 0 < Real.log (1 / m)) (hδ : 0 < δ) {t : ℕ}
    (ht : Real.log (Real.log (1 / m) / (2 * δ ^ 2)) ≤ (1 / (Fintype.card V : ℝ)) * t) :
    MixesWithin (glauber (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le))
      (gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
        (Z_prodWeight_pos hc)) δ t := by
  refine mixesWithin_of_klDiv_le_two_mul_sq (gibbs_prodWeight_pos hφ hc) hδ.le fun σ => ?_
  exact glauber_klDiv_le_prodWeight hφ hc hm hmin hL (by positivity) ht σ

/-- **`O(n log(n/δ))` mixing of the Gibbs sampler of a product measure in total
variation, with every constant explicit.**

Suppose every site weight satisfies `a ≤ φ_v(s)` and every site normaliser
`∑_s φ_v(s) ≤ b`, with `0 < a < b`, and write `n = |V|`, `L = ln(b/a) > 0`.  Then
from every starting configuration

  `‖P_GD^t(σ, ·) − μ‖_TV ≤ δ`  as soon as  `t ≥ n·ln(n·L/(2δ²))`,

which expands to `n ln n + n ln L + 2n ln(1/δ) − n ln 2` and is `O(n log(n/δ))`.

**This is the monograph's headline claim in the distance the monograph states it
in.**  `ProductOptimalMixing.glauber_klDiv_le_prodWeight_of_bounds` reached the
same rate in relative entropy and stopped there for want of Pinsker's inequality;
this is that theorem at `ε = 2δ²` composed with
`Pinsker.mixesWithin_of_klDiv_le_two_mul_sq`.

Compare `glauber_mixesWithin_prodWeight_variance_of_bounds`, which is the same
conclusion for the same chain from the variance route with the same `m`, and asks
for `t ≥ n·ln(1/(2δ)) + (n²/2)·L` — quadratic in `n`.  The exact crossover is
`entropySteps_lt_varianceSteps_iff`. -/
theorem glauber_mixesWithin_prodWeight_of_bounds (hφ : ∀ v s, 0 < φ v s)
    (hc : ∀ v, 0 < ∑ s, φ v s) {a b δ : ℝ} (ha : 0 < a) (hab : a < b)
    (hlo : ∀ v s, a ≤ φ v s) (hhi : ∀ v, ∑ s, φ v s ≤ b) (hδ : 0 < δ) {t : ℕ}
    (ht : Real.log ((Fintype.card V : ℝ) * Real.log (b / a) / (2 * δ ^ 2))
      ≤ (1 / (Fintype.card V : ℝ)) * t) :
    MixesWithin (glauber (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le))
      (gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
        (Z_prodWeight_pos hc)) δ t := by
  refine mixesWithin_of_klDiv_le_two_mul_sq (gibbs_prodWeight_pos hφ hc) hδ.le fun σ => ?_
  exact glauber_klDiv_le_prodWeight_of_bounds hφ hc ha hab hlo hhi (by positivity) ht σ

end ProdWeight

/-! ## The variance baseline, with the same constants discharged

`ProductOptimalMixing.glauber_mixesWithin_prodWeight_of_psd` is already the fair
baseline — it uses `glauber_nonnegDefinite` rather than laziness, so the factor
two in `ProductMeasure.glauber_mixesWithin_prodWeight` is gone — but it is stated
with an abstract `m`.  For the two step counts to be *comparable expressions*
they must be written in the same variables, so `m = (a/b)^n` is discharged here
by the same `gibbs_prodWeight_ge` that the entropy route uses. -/

section VarianceBaseline

variable {V : Type*} [Fintype V] [DecidableEq V] {S : Type*} [Fintype S] [DecidableEq S]
variable {φ : V → S → ℝ}
variable [Nonempty V]

/-- **The variance route for the Gibbs sampler of a product measure, laziness-free
and with every constant explicit.**

Under the same hypotheses as `glauber_mixesWithin_prodWeight_of_bounds` — every
site weight at least `a`, every site normaliser at most `b`, `0 < a < b`, and
`L = ln(b/a)` — the variance route gives the same conclusion
`MixesWithin (glauber …) (gibbs …) δ t` as soon as

  `t ≥ n·ln(1/(2δ)) + (n²/2)·L`.

The `(n²/2)·L` term is `(n/2)·ln(1/m)` with `m = (a/b)^n`, and it is what makes
this bound `Θ(n²)`.  There is no laziness factor: the underlying statement is
`ProductOptimalMixing.glauber_mixesWithin_prodWeight_of_psd`, which uses
`glauber_nonnegDefinite` in place of `lazy_nonnegDefinite` and therefore runs at
the absolute spectral bound `1 − 1/n` rather than `1 − 1/(2n)`.

Beside `glauber_mixesWithin_prodWeight_of_bounds`, which needs
`t ≥ n·ln(n·L/(2δ²)) = n ln n + n ln L + 2n ln(1/δ) − n ln 2`, this is the whole
comparison in one place: the entropy route trades a quadratic `μ_min` term for a
`n ln n`, and pays for it with a doubled `ln(1/δ)` coefficient. -/
theorem glauber_mixesWithin_prodWeight_variance_of_bounds (hφ : ∀ v s, 0 < φ v s)
    (hc : ∀ v, 0 < ∑ s, φ v s) {a b δ : ℝ} (ha : 0 < a) (hab : a < b)
    (hlo : ∀ v s, a ≤ φ v s) (hhi : ∀ v, ∑ s, φ v s ≤ b) (hδ : 0 < δ) {t : ℕ}
    (ht : Real.log (1 / (2 * δ)) + (Fintype.card V : ℝ) / 2 * Real.log (b / a)
      ≤ (1 / (Fintype.card V : ℝ)) * t) :
    MixesWithin (glauber (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le))
      (gibbs (prodWeight φ) (prodWeight_nonneg fun v s => (hφ v s).le)
        (Z_prodWeight_pos hc)) δ t := by
  have hb : 0 < b := ha.trans hab
  have hab0 : (0 : ℝ) < a / b := div_pos ha hb
  have hmpos : (0 : ℝ) < (a / b) ^ Fintype.card V := pow_pos hab0 _
  refine glauber_mixesWithin_prodWeight_of_psd hφ hc (m := (a / b) ^ Fintype.card V)
    hmpos (gibbs_prodWeight_ge (fun v s => (hφ v s).le) hc ha hb hlo hhi) hδ ?_
  -- Rewrite `ln(1/(2δ√m))` as `ln(1/(2δ)) + (n/2)·ln(b/a)`.
  have hsqrt : Real.log (Real.sqrt ((a / b) ^ Fintype.card V))
      = -((Fintype.card V : ℝ) / 2 * Real.log (b / a)) := by
    rw [Real.log_sqrt hmpos.le, Real.log_pow, Real.log_div ha.ne' hb.ne',
      Real.log_div hb.ne' ha.ne']
    ring
  have hprod : Real.log (2 * δ * Real.sqrt ((a / b) ^ Fintype.card V))
      = Real.log (2 * δ) - (Fintype.card V : ℝ) / 2 * Real.log (b / a) := by
    rw [Real.log_mul (by positivity) (Real.sqrt_ne_zero'.mpr hmpos), hsqrt]
    ring
  have hgoal : Real.log (1 / (2 * δ * Real.sqrt ((a / b) ^ Fintype.card V)))
      = Real.log (1 / (2 * δ)) + (Fintype.card V : ℝ) / 2 * Real.log (b / a) := by
    rw [one_div, Real.log_inv, hprod, one_div, Real.log_inv]
    ring
  rw [hgoal]
  exact ht

end VarianceBaseline

/-! ## The comparison, as arithmetic

Both step counts above are explicit real expressions in `n = |V|`,
`L = ln(b/a) > 0` and the accuracy `δ`, so the comparison between them is a fact
about real numbers and is proved as one.  Nothing in this section knows what a
Markov chain is; the two lemmas exist so that the claims in the module docstring
are statements of the library rather than remarks in prose. -/

section Arithmetic

/-- **The exact price of Pinsker, in steps.**

`ProductOptimalMixing.glauber_klDiv_le_prodWeight_of_bounds` reaches `D_KL ≤ δ`
in `n·ln(n·L/δ)` steps; `glauber_mixesWithin_prodWeight_of_bounds` reaches
`‖·‖_TV ≤ δ` in `n·ln(n·L/(2δ²))` steps.  The difference is exactly

  `n·ln(1/(2δ))`   steps.

Read the two halves of that separately, because they point in opposite
directions.  The `n·ln(1/δ)` is the cost: Pinsker relates `‖·‖_TV` to the *square
root* of `D_KL`, so an accuracy `δ` in total variation is an accuracy `δ²` in
divergence, and the coefficient of `ln(1/δ)` in the step count doubles from `n`
to `2n` — equivalently, the effective decay rate of the distance one wanted is
`ρ/2` rather than `ρ`.  The `−n·ln 2` is a *saving*, contributed by the sharp
constant `2` of `two_mul_tvDist_sq_le_klDiv`: a proof with a worse constant
`κ < 2` would give `−n ln κ` instead, costing `n·ln(2/κ)` steps and changing
nothing asymptotically.  The sharp constant is worth a constant times `n`; the
squaring is worth `n·ln(1/δ)`. -/
theorem pinsker_step_cost {n L δ : ℝ} (hn : 0 < n) (hL : 0 < L) (hδ : 0 < δ) :
    n * Real.log (n * L / (2 * δ ^ 2)) - n * Real.log (n * L / δ)
      = n * Real.log (1 / (2 * δ)) := by
  have hnL : (0 : ℝ) < n * L := mul_pos hn hL
  have h1 : Real.log (2 * δ ^ 2) = Real.log 2 + 2 * Real.log δ := by
    rw [Real.log_mul two_ne_zero (pow_ne_zero 2 hδ.ne'), Real.log_pow]
    push_cast
    ring
  have h2 : Real.log (2 * δ) = Real.log 2 + Real.log δ := Real.log_mul two_ne_zero hδ.ne'
  rw [Real.log_div hnL.ne' (by positivity), Real.log_div hnL.ne' hδ.ne', one_div,
    Real.log_inv, h1, h2]
  ring

/-- **Where the two routes cross.**  With `n` sites, `L = ln(b/a) > 0` and
accuracy `δ > 0`, the entropy-plus-Pinsker step count
`n·ln(n·L/(2δ²))` is smaller than the variance step count
`n·ln(1/(2δ)) + (n²/2)·L` **exactly when**

  `ln(n·L/δ) < n·L/2`.

Everything about the comparison is in that line.  For fixed `δ` the right-hand
side grows linearly in `n` and the left-hand side logarithmically, so the entropy
route wins for all large `n` — this is the `Θ(n log n)` against `Θ(n²)` of the
module docstring.  For fixed `n` and `δ → 0` the left-hand side grows like
`ln(1/δ)` and the right-hand side is constant, so the *variance* route wins: the
doubled `ln(1/δ)` coefficient that Pinsker costs is a real loss and eventually
dominates.  Neither route dominates the other; which one to use depends on
whether `n` or `ln(1/δ)` is the large parameter.

The proof is the expansion of the three logarithms and a division by `n`. -/
theorem entropySteps_lt_varianceSteps_iff {n L δ : ℝ} (hn : 0 < n) (hL : 0 < L)
    (hδ : 0 < δ) :
    n * Real.log (n * L / (2 * δ ^ 2)) < n * Real.log (1 / (2 * δ)) + n ^ 2 / 2 * L
      ↔ Real.log (n * L / δ) < n * L / 2 := by
  have hnL : (0 : ℝ) < n * L := mul_pos hn hL
  have h1 : Real.log (2 * δ ^ 2) = Real.log 2 + 2 * Real.log δ := by
    rw [Real.log_mul two_ne_zero (pow_ne_zero 2 hδ.ne'), Real.log_pow]
    push_cast
    ring
  have h2 : Real.log (2 * δ) = Real.log 2 + Real.log δ := Real.log_mul two_ne_zero hδ.ne'
  rw [Real.log_div hnL.ne' (by positivity), Real.log_div hnL.ne' hδ.ne', one_div,
    Real.log_inv, h1, h2]
  constructor
  · intro h
    nlinarith [h, hn]
  · intro h
    nlinarith [h, hn]

end Arithmetic

end Arlib.MarkovChains

