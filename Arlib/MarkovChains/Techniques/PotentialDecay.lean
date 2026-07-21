/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Geometric decay of a potential under a drift condition

The `L²` machinery of this area measures convergence of a chain to *stationarity*.
A perfect-sampling argument needs something different and much cruder: a
guarantee that the chain has *reached a target set*, with a tail bound on how
long it takes.  The standard elementary device for that is a Lyapunov (or
supermartingale) potential, and this module contains it in the smallest form
that is actually useful.

The input is a nonnegative function `Φ : Ω → ℝ` and a *drift condition*

  `(K Φ)(x) ≤ lam · Φ(x)` for every `x`,

i.e. one step of the chain multiplies the potential by at most `lam`.  Since
`act` is monotone and positive, this self-improves: `t` steps multiply `Φ` by at
most `lam ^ t` (`act_iter_le_of_drift`).  Combining that with a one-line finite
Markov inequality turns the potential into a hitting-time tail bound
(`not_reached_le_of_drift`): if `Φ ≥ 1` off a target set `T`, then the chain
started at `x₀` is still outside `T` at time `t` with probability at most
`lam ^ t · Φ(x₀)`.

* `act_mono`, `act_nonneg` — positivity and monotonicity of the one-step
  operator, the only structural facts the argument uses.
* `act_iter_le_of_drift` — the headline: `K^t Φ ≤ lam^t Φ` pointwise.
* `sum_push_mul` — the adjoint bookkeeping `⟨νK, f⟩ = ⟨ν, Kf⟩`.
* `expectation_iter_le_of_drift` — the same statement read as an expectation
  against a starting distribution.
* `not_reached_le_of_drift` — the Markov-inequality corollary.

Nothing here is specific to any chain, and nothing here uses reversibility, a
stationary distribution, or a spectral gap; in particular no eigenvalue appears,
in keeping with the standing commitment of this area.  Everything is proved from
first principles with no `sorry`.

The intended consumer is `Arlib.MarkovChains.Techniques.SinusoidalPotential`,
where `Φ` is Wilson's sinusoidal potential and the drift condition is a
trigonometric identity.
-/
import Arlib.MarkovChains.Techniques.MixingTime

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset FinKernel

variable {Ω : Type*} [Fintype Ω]

/-! ## Positivity and monotonicity of the one-step operator -/

/-- The one-step operator preserves nonnegativity. -/
theorem act_nonneg (K : FinChain Ω) (f : Ω → ℝ) (hf : ∀ y, 0 ≤ f y) (x : Ω) :
    0 ≤ act K f x :=
  Finset.sum_nonneg fun y _ => mul_nonneg (K.coe_nonneg x y) (hf y)

/-- The one-step operator is monotone: a kernel has nonnegative entries, so it
cannot reverse an inequality between functions. -/
theorem act_mono (K : FinChain Ω) {f g : Ω → ℝ} (h : ∀ y, f y ≤ g y) (x : Ω) :
    act K f x ≤ act K g x :=
  Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (h y) (K.coe_nonneg x y)

/-! ## Geometric decay -/

variable [DecidableEq Ω]

set_option linter.unusedVariables false in
/-- **Geometric decay of a potential under a drift condition.**  If a nonnegative
potential `Φ` contracts by a factor `lam` in one step of the kernel, then it
contracts by `lam ^ t` in `t` steps.

The induction is the whole proof: `K^{t+1} Φ = K (K^t Φ) ≤ K (lam^t Φ) =
lam^t · K Φ ≤ lam^{t+1} Φ`, where the first inequality is monotonicity of `act`
and the second is the hypothesis.  Nonnegativity of `Φ` is not needed for *this*
statement — the drift hypothesis already carries all the information — but it is
kept in the signature because it is what makes the conclusion meaningful, and
every downstream consumer has it. -/
theorem act_iter_le_of_drift
    (K : FinChain Ω) (Φ : Ω → ℝ) (lam : ℝ)
    (hΦ : ∀ x, 0 ≤ Φ x) (hlam : 0 ≤ lam)
    (hdrift : ∀ x, act K Φ x ≤ lam * Φ x) (t : ℕ) (x : Ω) :
    act (K.iter t) Φ x ≤ lam ^ t * Φ x := by
  induction t generalizing x with
  | zero => simp
  | succ t ih =>
      rw [FinKernel.act_iter_succ]
      calc act K (act (K.iter t) Φ) x
          ≤ act K (fun y => lam ^ t * Φ y) x := act_mono K (fun y => ih y) x
        _ = lam ^ t * act K Φ x := by rw [FinKernel.act_smul]
        _ ≤ lam ^ t * (lam * Φ x) :=
            mul_le_mul_of_nonneg_left (hdrift x) (pow_nonneg hlam t)
        _ = lam ^ (t + 1) * Φ x := by ring

/-! ## The distributional form -/

omit [DecidableEq Ω] in
/-- **Adjointness of `push` and `act`.**  Averaging `f` against the pushforward
of `ν` is averaging `K f` against `ν`. -/
theorem sum_push_mul (K : FinChain Ω) (ν : FinDist Ω) (f : Ω → ℝ) :
    ∑ y, (K.push ν) y * f y = ∑ x, ν x * act K f x := by
  simp only [FinKernel.push_apply, FinKernel.act_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- **Geometric decay of the expected potential.**  The distributional reading of
`act_iter_le_of_drift`: the expectation of `Φ` under the law of the chain at time
`t` is at most `lam ^ t` times its initial expectation. -/
theorem expectation_iter_le_of_drift
    (K : FinChain Ω) (Φ : Ω → ℝ) (lam : ℝ)
    (hΦ : ∀ x, 0 ≤ Φ x) (hlam : 0 ≤ lam)
    (hdrift : ∀ x, act K Φ x ≤ lam * Φ x) (t : ℕ) (μ : FinDist Ω) :
    ∑ x, ((K.iter t).push μ) x * Φ x ≤ lam ^ t * ∑ x, μ x * Φ x := by
  rw [sum_push_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  calc μ x * act (K.iter t) Φ x
      ≤ μ x * (lam ^ t * Φ x) :=
        mul_le_mul_of_nonneg_left (act_iter_le_of_drift K Φ lam hΦ hlam hdrift t x)
          (μ.coe_nonneg x)
    _ = lam ^ t * (μ x * Φ x) := by ring

/-- The expectation of `f` under a point mass is the value of `f` there. -/
theorem sum_dirac_mul (x₀ : Ω) (f : Ω → ℝ) :
    ∑ x, (FinDist.dirac x₀) x * f x = f x₀ := by
  rw [Finset.sum_eq_single x₀ (fun z _ hz => by simp [hz])
    (fun h => absurd (mem_univ x₀) h)]
  simp

/-! ## The Markov-inequality corollary -/

/-- **A finite Markov inequality against a potential.**  If `Φ ≥ 0` everywhere
and `Φ ≥ 1` off `T`, the mass a distribution puts outside `T` is at most its
expectation of `Φ`. -/
theorem sum_sdiff_le_expectation (ν : FinDist Ω) (Φ : Ω → ℝ) (T : Finset Ω)
    (hΦ : ∀ x, 0 ≤ Φ x) (hΦT : ∀ x, x ∉ T → 1 ≤ Φ x) :
    ∑ x ∈ Finset.univ \ T, ν x ≤ ∑ x, ν x * Φ x := by
  calc ∑ x ∈ Finset.univ \ T, ν x
      ≤ ∑ x ∈ Finset.univ \ T, ν x * Φ x := by
        refine Finset.sum_le_sum fun x hx => ?_
        have hxT : x ∉ T := (Finset.mem_sdiff.mp hx).2
        simpa using mul_le_mul_of_nonneg_left (hΦT x hxT) (ν.coe_nonneg x)
    _ ≤ ∑ x, ν x * Φ x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun x _ _ => mul_nonneg (ν.coe_nonneg x) (hΦ x)

/-- **Hitting-time tail bound from a drift condition.**  If `Φ ≥ 1` off a target
set `T` and `Φ ≥ 0` everywhere, the probability of not having reached `T` after
`t` steps, starting from `x₀`, is at most `lam ^ t * Φ x₀`.

This is the form in which a Lyapunov potential is actually consumed by a
perfect-sampling analysis: `T` is the set of "collapsed" states and `Φ` is a
potential that is large far from `T` and drifts down. -/
theorem not_reached_le_of_drift
    (K : FinChain Ω) (Φ : Ω → ℝ) (lam : ℝ) (T : Finset Ω)
    (hΦ : ∀ x, 0 ≤ Φ x) (hΦT : ∀ x, x ∉ T → 1 ≤ Φ x) (hlam : 0 ≤ lam)
    (hdrift : ∀ x, act K Φ x ≤ lam * Φ x) (t : ℕ) (x₀ : Ω) :
    ∑ x ∈ Finset.univ \ T, ((K.iter t).push (FinDist.dirac x₀)) x
      ≤ lam ^ t * Φ x₀ := by
  calc ∑ x ∈ Finset.univ \ T, ((K.iter t).push (FinDist.dirac x₀)) x
      ≤ ∑ x, ((K.iter t).push (FinDist.dirac x₀)) x * Φ x :=
        sum_sdiff_le_expectation _ Φ T hΦ hΦT
    _ ≤ lam ^ t * ∑ x, (FinDist.dirac x₀) x * Φ x :=
        expectation_iter_le_of_drift K Φ lam hΦ hlam hdrift t _
    _ = lam ^ t * Φ x₀ := by rw [sum_dirac_mul]

end Arlib.MarkovChains
