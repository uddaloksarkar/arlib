/-
Copyright (c) 2026 Uddalok Sarkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uddalok Sarkar
-/
/-
# Correctness of rejection sampling

The classical fact behind every acceptance/rejection sampler, in full generality:
no particular target distribution, no particular proposal, no floating point.

## The setup

A **proposal** is a mass function `h : ι → ℝ`, the **target** is a mass function
`target : ι → ℝ`, and `α : ℝ` is the **rejection constant**.  The sampler draws a
candidate `k` from `h` and accepts it with probability

  `a k = target k / (α * h k)`,

restarting on rejection.  The law of the accepted candidate is the normalized
product of proposal and acceptance probability — exactly
`Arlib.condOn h a = fun k => h k * a k / ∑' j, h j * a j`, the conditioning
operator of `Arlib.Probability.TVDistance`.

## Main results

* `hat_nonneg_of_dominates`, `covers_of_dominates`, `acc_mem_Icc` — the basic
  consequences of the **domination** hypothesis `∀ k, target k ≤ α * h k`: the
  proposal is automatically nonnegative, it covers the target, and `a k ∈ [0,1]`
  so the acceptance rule really is a probability.
* `mul_acc_eq_div` — the pointwise cancellation `h k * a k = target k / α`.  The
  hat cancels out; this is the heart of the argument.
* `hasSum_accept`, `tsum_accept_eq_inv` — `∑' k, h k * a k = 1 / α`: **one trial
  accepts with probability `1/α`**, so the number of trials is geometric with
  mean `α`, i.e. `α` is the expected number of trials.  (The geometric-mean step
  itself is arithmetic and is not formalized here.)
* `condOn_eq_of_covers`, `condOn_eq_of_dominates` — the main deliverable:
  **`Arlib.condOn h a = target`**, the sampler's output law is *exactly* the
  target, with no error term.
* `mul_acc_eq_tsum_mul_target` — the same statement multiplied out into the shape
  `∀ k, h k * a k = (∑' j, h j * a j) * target k`, which is the form a caller
  carrying the normalizing constant abstractly wants.
* `tsum_accept_pos` — the acceptance probability is positive, so the rejection
  loop terminates a.s.; this discharges the `0 < ∑' i, p i * a i` side condition
  of `Arlib.hasSum_condOn` and `Arlib.tvDist_condOn_le`.

## Two non-obvious facts the proofs establish

* **`Summable h` is never needed**, and neither is `∀ k, 0 ≤ h k` nor
  `HasSum h 1`.  Domination together with `0 ≤ target` already forces
  `0 ≤ h k` pointwise (`hat_nonneg_of_dominates`), and the normalizing constant
  `∑' k, h k * a k` is computed from the *target's* mass alone, via the
  cancellation.  So every theorem here holds verbatim when `h` is only a
  **sub-probability** proposal — an unnormalized, or even non-summable, envelope.
  This is what makes the results applicable to a truncated/discretized hat.
* **The covering hypothesis `h k = 0 → target k = 0` is genuinely necessary**,
  and it is consumed at exactly one point: the `h k = 0` branch of
  `mul_acc_eq_div`.  There the left-hand side `h k * a k` is `0` for the trivial
  reason (and `a k = target k / 0 = 0` by Lean's junk-value convention), while
  the right-hand side `target k / α` is `0` *only* because the target vanishes
  there too.  Every other lemma either takes covering as a hypothesis or derives
  it from domination (`covers_of_dominates`).  A proposal with zeros is therefore
  admissible precisely when the target vanishes on those zeros.

No `sorry`.
-/
import Arlib.Probability.TVDistance

namespace Arlib

/-! ## The generic rejection-sampling identity

Throughout, `α` is the rejection constant, `h` the proposal ("hat") mass
function, `target` the distribution we want to produce, and `a` the acceptance
probability, tied to the others by `hacc : ∀ k, a k = target k / (α * h k)`.
Stating `a` as a variable with a defining equation, rather than as a
`def`, lets callers apply these lemmas to whatever expression their sampler
literally computes. -/

variable {ι : Type*} {target h a : ι → ℝ} {α : ℝ}

/-- Under domination the proposal is automatically nonnegative wherever the
target is: `0 ≤ target k ≤ α * h k` with `0 < α` forces `0 ≤ h k`.  So
nonnegativity of `h` never has to be assumed separately. -/
theorem hat_nonneg_of_dominates (hα : 0 < α) (htnn : ∀ k, 0 ≤ target k)
    (hdom : ∀ k, target k ≤ α * h k) (k : ι) : 0 ≤ h k :=
  nonneg_of_mul_nonneg_right (le_trans (htnn k) (hdom k)) hα

/-- **The proposal covers the target.**  If the hat puts no mass on `k` then,
by domination, neither does the target.  This is the hypothesis that makes the
pointwise cancellation `mul_acc_eq_div` true at the zeros of `h`, and it is why
a proposal is allowed to have bounded support only if the target vanishes on the
complement. -/
theorem covers_of_dominates (htnn : ∀ k, 0 ≤ target k)
    (hdom : ∀ k, target k ≤ α * h k) {k : ι} (hk : h k = 0) : target k = 0 :=
  le_antisymm (by simpa [hk] using hdom k) (htnn k)

/-- **The acceptance probability is a genuine probability**, `a k ∈ [0,1]`.
At a zero of `h` this uses Lean's `x / 0 = 0` convention: `a k = target k / 0 = 0`. -/
theorem acc_mem_Icc (hα : 0 < α) (htnn : ∀ k, 0 ≤ target k)
    (hdom : ∀ k, target k ≤ α * h k) (hacc : ∀ k, a k = target k / (α * h k)) (k : ι) :
    a k ∈ Set.Icc (0 : ℝ) 1 := by
  have hh : 0 ≤ h k := hat_nonneg_of_dominates hα htnn hdom k
  rcases eq_or_lt_of_le hh with hk | hk
  · -- `h k = 0`: the ratio is junk `0`.
    rw [hacc k, ← hk, mul_zero, div_zero]
    exact ⟨le_refl 0, zero_le_one⟩
  · have hpos : 0 < α * h k := mul_pos hα hk
    refine ⟨?_, ?_⟩
    · exact (hacc k) ▸ div_nonneg (htnn k) hpos.le
    · rw [hacc k, div_le_one hpos]
      exact hdom k

/-- **Pointwise cancellation**: the joint mass of proposing `k` and accepting it
is `target k / α`, the hat having cancelled out.

Both cases are needed.  Where `h k ≠ 0` this is `field_simp`.  Where `h k = 0`
the left side is `0 * a k = 0`, and the right side is `0` *only* because the
covering hypothesis says the target vanishes there — this is precisely the case
one must not wave away, since a discretized hat genuinely has zeros. -/
theorem mul_acc_eq_div (hα : α ≠ 0) (hcov : ∀ k, h k = 0 → target k = 0)
    (hacc : ∀ k, a k = target k / (α * h k)) (k : ι) :
    h k * a k = target k / α := by
  rcases eq_or_ne (h k) 0 with hk | hk
  · rw [hacc k, hk, zero_mul, hcov k hk, zero_div]
  · rw [hacc k]
    field_simp
    ring

/-- The joint "propose `k` and accept" masses sum to `1 / α`, as a `HasSum`
(the summability of the family comes for free from that of `target`). -/
theorem hasSum_accept (hα : α ≠ 0) (htsum : HasSum target 1)
    (hcov : ∀ k, h k = 0 → target k = 0) (hacc : ∀ k, a k = target k / (α * h k)) :
    HasSum (fun k => h k * a k) (1 / α) := by
  have h1 : HasSum (fun k => target k / α) (1 / α) := htsum.div_const α
  exact h1.congr_fun fun k => mul_acc_eq_div hα hcov hacc k

/-- **The acceptance probability of one trial is `1 / α`.**  Hence the number of
trials before acceptance is geometric with mean `α`: the rejection constant *is*
the expected number of trials. -/
theorem tsum_accept_eq_inv (hα : α ≠ 0) (htsum : HasSum target 1)
    (hcov : ∀ k, h k = 0 → target k = 0) (hacc : ∀ k, a k = target k / (α * h k)) :
    ∑' k, h k * a k = 1 / α :=
  (hasSum_accept hα htsum hcov hacc).tsum_eq

/-- **Rejection sampling is exact**, stated from the covering hypothesis
directly: the law of the accepted candidate, `Arlib.condOn h a`, is the target.

`condOn h a k = (h k * a k) / (∑' j, h j * a j) = (target k / α) / (1 / α)`,
which is `target k`. -/
theorem condOn_eq_of_covers (hα : α ≠ 0) (htsum : HasSum target 1)
    (hcov : ∀ k, h k = 0 → target k = 0) (hacc : ∀ k, a k = target k / (α * h k)) :
    condOn h a = target := by
  funext k
  rw [condOn, tsum_accept_eq_inv hα htsum hcov hacc, mul_acc_eq_div hα hcov hacc k]
  field_simp

/-- **Rejection sampling is exact** — the main deliverable, in the form most
applications use: from `0 < α`, nonnegativity and total mass `1` of the target,
and the domination `target k ≤ α * h k` (the defining property of the rejection
constant), the output law of the sampler is *exactly* the target. -/
theorem condOn_eq_of_dominates (hα : 0 < α) (htnn : ∀ k, 0 ≤ target k)
    (htsum : HasSum target 1) (hdom : ∀ k, target k ≤ α * h k)
    (hacc : ∀ k, a k = target k / (α * h k)) :
    condOn h a = target :=
  condOn_eq_of_covers hα.ne' htsum (fun _ hk => covers_of_dominates htnn hdom hk) hacc

/-- The multiplied-out form of `condOn_eq_of_dominates`: joint mass = acceptance
probability × target mass,

  `h k * a k = (∑' j, h j * a j) * target k`.

This is the shape wanted by callers that carry the normalizing constant
`∑' j, h j * a j` abstractly rather than dividing by it. -/
theorem mul_acc_eq_tsum_mul_target (hα : 0 < α) (htnn : ∀ k, 0 ≤ target k)
    (htsum : HasSum target 1) (hdom : ∀ k, target k ≤ α * h k)
    (hacc : ∀ k, a k = target k / (α * h k)) (k : ι) :
    h k * a k = (∑' j, h j * a j) * target k := by
  have hcov : ∀ k, h k = 0 → target k = 0 := fun _ hk => covers_of_dominates htnn hdom hk
  rw [tsum_accept_eq_inv hα.ne' htsum hcov hacc, mul_acc_eq_div hα.ne' hcov hacc k]
  field_simp

/-- The acceptance probability is positive as soon as the target is a genuine
distribution, so the rejection loop terminates: this discharges the
`0 < ∑' i, p i * a i` hypothesis of `Arlib.hasSum_condOn` and
`Arlib.tvDist_condOn_le`. -/
theorem tsum_accept_pos (hα : 0 < α) (htsum : HasSum target 1)
    (hcov : ∀ k, h k = 0 → target k = 0) (hacc : ∀ k, a k = target k / (α * h k)) :
    0 < ∑' k, h k * a k := by
  rw [tsum_accept_eq_inv hα.ne' htsum hcov hacc]
  positivity

end Arlib
