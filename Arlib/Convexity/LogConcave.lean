/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.Basic

/-
# Log-concave functions on `ℝ`

Mathlib (`v4.15`) has no notion of log-concavity, so this file introduces one in the
multiplicative form the convex-geometry literature uses:

  `f((1−t)x + ty) ≥ f(x)^(1−t) · f(y)^t`.

This is the hypothesis under which the isoperimetric inequality of
`Arlib.Convexity.Isoperimetry` is stated, and it is the form in which the
Lovász–Simonovits / Kannan–Lovász–Simonovits results are quoted.

Stated with `Real.rpow` rather than `Monotone`/`ConvexOn (-log f)` so that it applies to
functions with zeros — which is essential, since the densities of interest are supported
on a bounded body and vanish outside it.

## Main definitions

* `Arlib.LogConcave` — the multiplicative inequality above.

## Main results

* `Arlib.LogConcave.mul` — a product of log-concave functions is log-concave. This is the
  closure property the Gaussian-restricted densities `f · γ` need.
* `Arlib.logConcave_const` — constants are log-concave.
-/

namespace Arlib

open Real

/-- **Log-concavity** on `ℝ`, in multiplicative form:
`f(x)^(1−t) · f(y)^t ≤ f((1−t)x + ty)` for every `t ∈ [0,1]`.

Nonnegativity is carried separately (`hf : ∀ x, 0 ≤ f x`) rather than bundled, so the
definition composes with Mathlib's `Real.rpow` lemmas without side conditions. -/
def LogConcave (f : ℝ → ℝ) : Prop :=
  ∀ x y t : ℝ, 0 ≤ t → t ≤ 1 →
    f x ^ (1 - t) * f y ^ t ≤ f ((1 - t) * x + t * y)

/-- A nonnegative constant function is log-concave. -/
theorem logConcave_const {c : ℝ} (hc : 0 ≤ c) : LogConcave (fun _ => c) := by
  intro x y t ht0 ht1
  simp only
  rcases eq_or_lt_of_le hc with h | h
  · simp [← h, Real.zero_rpow, sub_eq_zero]
    rcases eq_or_lt_of_le ht0 with h' | h'
    · simp [← h']
    · simp [Real.zero_rpow (ne_of_gt h'), zero_mul]
  · rw [← Real.rpow_add h]
    simp

/-- **A product of log-concave functions is log-concave.**

This is the closure property the analysis of Gaussian-restricted densities needs: if `f`
is log-concave and `γ` is the Gaussian weight (log-concave, being `exp` of a concave
quadratic), then `f · γ` is log-concave. -/
theorem LogConcave.mul {f g : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : LogConcave f) (hg : LogConcave g) : LogConcave (fun x => f x * g x) := by
  intro x y t ht0 ht1
  have h1t : (0 : ℝ) ≤ 1 - t := by linarith
  calc (f x * g x) ^ (1 - t) * (f y * g y) ^ t
      = (f x ^ (1 - t) * f y ^ t) * (g x ^ (1 - t) * g y ^ t) := by
        rw [Real.mul_rpow (hf0 x) (hg0 x), Real.mul_rpow (hf0 y) (hg0 y)]; ring
    _ ≤ f ((1 - t) * x + t * y) * g ((1 - t) * x + t * y) := by
        refine mul_le_mul (hf x y t ht0 ht1) (hg x y t ht0 ht1) ?_ ?_
        · exact mul_nonneg (Real.rpow_nonneg (hg0 x) _) (Real.rpow_nonneg (hg0 y) _)
        · exact le_trans (mul_nonneg (Real.rpow_nonneg (hf0 x) _)
            (Real.rpow_nonneg (hf0 y) _)) (hf x y t ht0 ht1)

end Arlib
