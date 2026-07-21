/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The independent sampler

The chain that ignores its current state and redraws from `μ`:
`P(x, y) = μ(y)`.  It is the chain you would use if you could sample from `μ`
directly — which is exactly what MCMC exists to avoid — so it is useless as an
algorithm and maximally useful as a calibration point.

Where `Chains.TwoState` pins down the *generic* behaviour of the general theory,
this module pins down its *extreme*: the independent sampler saturates every
inequality in the library at the best possible value.  Its Dirichlet form **is**
the variance, so its Poincaré constant is exactly `1` — the largest a spectral
gap can be — and it reaches stationarity in a single step.  Any general theorem
whose conclusion is not tight here has slack that should be looked at.

* `independentSampler` — the chain, and `act_independentSampler`, which says it
  collapses every function to the constant `Ex μ f`.
* `independentSampler_reversible`, `independentSampler_stationary`.
* `dirichlet_independentSampler` — **`ℰ_P(f) = Var_μ(f)`**, an identity.
* `independentSampler_spectralGapAtLeast` — spectral gap `1`, and
  `independentSampler_nonnegDefinite`, so the chain sits inside the hypotheses of
  `Techniques.SpectralGap` with `c = 0`.
* `Var_act_independentSampler` — the variance is annihilated in one step, and
  `independentSampler_mixesWithin_one` — total variation distance `0` after one
  step, which is the strongest possible form of the mixing statement.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.Dirichlet
import Arlib.MarkovChains.Techniques.TotalVariation

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The chain -/

/-- The **independent sampler**: from any state, redraw from `μ`. -/
def independentSampler (μ : FinDist Ω) : FinChain Ω where
  P _ y := μ y
  P_nonneg _ y := μ.coe_nonneg y
  P_sum _ := μ.sum_coe

@[simp] theorem independentSampler_apply (μ : FinDist Ω) (x y : Ω) :
    independentSampler μ x y = μ y := rfl

/-- The chain collapses every function to its mean: `P f ≡ μ(f)`.  Everything
else in this module is a consequence. -/
@[simp] theorem act_independentSampler (μ : FinDist Ω) (f : Ω → ℝ) :
    (independentSampler μ).act f = fun _ => Ex μ f := rfl

/-- Every row is `μ`. -/
@[simp] theorem row_independentSampler (μ : FinDist Ω) (x : Ω) :
    (independentSampler μ).row x = μ := FinDist.ext fun _ => rfl

/-! ## Detailed balance -/

/-- **Detailed balance** for the independent sampler: `μ(x) μ(y) = μ(y) μ(x)`. -/
theorem independentSampler_reversible (μ : FinDist Ω) :
    Reversible μ (independentSampler μ) := fun x y => by
  simp only [independentSampler_apply]; ring

theorem independentSampler_stationary (μ : FinDist Ω) :
    Stationary μ (independentSampler μ) :=
  (independentSampler_reversible μ).stationary

/-! ## The Dirichlet form is the variance -/

/-- The quadratic form of the independent sampler is the squared mean. -/
theorem ip_act_independentSampler (μ : FinDist Ω) (f : Ω → ℝ) :
    ip μ f ((independentSampler μ).act f) = (Ex μ f) ^ 2 := by
  rw [act_independentSampler, show ip μ f (fun _ => Ex μ f) = Ex μ f * ip μ f (fun _ => 1) from ?_]
  · rw [ip_one_right]; ring
  · simp only [ip]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring

/-- **The Dirichlet form of the independent sampler is exactly the variance.**

`ℰ_P(f) = ⟪f,f⟫_μ - (μ f)² = Var_μ(f)`.  Local variation and global variation
coincide, which is the precise sense in which this chain has no geometry at all. -/
theorem dirichlet_independentSampler (μ : FinDist Ω) (f : Ω → ℝ) :
    dirichlet μ (independentSampler μ) f f = Var μ f := by
  rw [dirichlet_apply, ip_act_independentSampler, Var_eq_ip_sub_sq]

/-- **The spectral gap of the independent sampler is `1`** — the largest value a
Poincaré constant can take, attained with equality for every `f`. -/
theorem independentSampler_spectralGapAtLeast (μ : FinDist Ω) :
    SpectralGapAtLeast μ (independentSampler μ) 1 := fun f => by
  rw [dirichlet_independentSampler, one_mul]

/-- The independent sampler is positive semidefinite: its quadratic form is a
square. -/
theorem independentSampler_nonnegDefinite (μ : FinDist Ω) :
    NonnegDefinite μ (independentSampler μ) := fun f => by
  rw [ip_act_independentSampler]; exact sq_nonneg _

/-! ## One-step convergence

With gap `1`, `Techniques.SpectralGap` predicts contraction by `(1 - 1)² = 0`.
The chain does exactly that: it is stationary after a single step, in variance
and in total variation alike. -/

/-- The variance is annihilated in one step. -/
@[simp] theorem Var_act_independentSampler (μ : FinDist Ω) (f : Ω → ℝ) :
    Var μ ((independentSampler μ).act f) = 0 := by
  rw [act_independentSampler, Var_const]

/-- **One step suffices**: the distribution after one step is exactly `μ`, so the
total variation distance to stationarity is `0`. -/
theorem independentSampler_mixesWithin_one [DecidableEq Ω] (μ : FinDist Ω) :
    MixesWithin (independentSampler μ) μ 0 1 := by
  intro x
  have h : (independentSampler μ).iter 1 = independentSampler μ := by
    rw [FinKernel.iter_succ, FinKernel.iter_zero, FinKernel.comp_id]
  rw [h, row_independentSampler, tvDist_self]

end Arlib.MarkovChains
