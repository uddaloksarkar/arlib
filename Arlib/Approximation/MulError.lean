/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# Two-sided multiplicative error windows

Approximation algorithms whose guarantee is *relative* accumulate their error
multiplicatively: each stage replaces a quantity `b` by something in
`[lo · b, hi · b]`, and the analysis must compose such windows, sum them over a
family, iterate them along a chain, and finally calibrate the per-stage
tolerance so that the composed window is the one the theorem promises.

`Arlib.relErr` (in `Arlib.Prelude`) already names the symmetric window
`(1 ± ε)·b`.  What is missing — and what every relative-accuracy argument needs —
is the *asymmetric* window `[lo·b, hi·b]`, because that is the shape a window
takes after composition: `(1-δ)^n` and `(1+δ)^n` are not of the form `1 ∓ ε` for
a common `ε`.

* `Between lo hi a b` — `a` lies in the window `[lo·b, hi·b]`.
* `Between.trans` — windows compose by multiplying their endpoints.
* `Between.sum` — a window shared by every member of a family is inherited by
  the sums.  This lemma itself needs no sign hypothesis, because the two
  inequalities are summed term by term; but note that *obtaining* the per-term
  windows for scaled quantities does need nonnegative coefficients
  (`Between.const_mul`), and a negative coefficient genuinely breaks the
  conclusion.
* `Between.pow_of_chain` — a per-step window `[lo, hi]` along `F 0, …, F n`
  telescopes to `[lo^n, hi^n]`.
* `one_add_div_pow_le` / `one_sub_div_pow_ge` — the calibration
  `δ = ε/(3n)`: `(1 + ε/(3n))^n ≤ 1 + ε` and `1 - ε ≤ (1 - ε/(3n))^n` for
  `ε ∈ [0,1]`, hence `Between.relErr_of_calibrated`, which turns a telescoped
  window straight into `a ∈ relErr ε b`.

The `(1+·)^n` bound is proved by the elementary induction
`(1+a)^n ≤ 1 + 2na` valid whenever `n·a ≤ 1/2` (`one_add_pow_le_one_add_two_mul`);
no exponential and no logarithm appears.

Nothing here mentions any particular data structure: this is the arithmetic every
relative-error guarantee in the area runs on, which is why it sits at area level
rather than under `Coresets/`.  No `sorry`.
-/
import Arlib.Prelude
import Mathlib.Algebra.Order.Ring.Pow

namespace Arlib.Approximation

open scoped BigOperators
open Finset

/-! ## The window -/

/-- `Between lo hi a b` says that `a` lies in the multiplicative window
`[lo · b, hi · b]` around `b`.  Unlike `Arlib.relErr` the window is allowed to
be asymmetric, which is what composition forces: composing `(1 ± δ)` with itself
`n` times gives `[(1-δ)^n, (1+δ)^n]`. -/
def Between (lo hi a b : ℝ) : Prop := lo * b ≤ a ∧ a ≤ hi * b

namespace Between

variable {lo hi lo' hi' a b c : ℝ}

theorem lower (h : Between lo hi a b) : lo * b ≤ a := h.1

theorem upper (h : Between lo hi a b) : a ≤ hi * b := h.2

theorem mk (h₁ : lo * b ≤ a) (h₂ : a ≤ hi * b) : Between lo hi a b := ⟨h₁, h₂⟩

/-- The trivial window: every value lies in `[1·b, 1·b]` around itself. -/
theorem refl (a : ℝ) : Between 1 1 a a := ⟨by ring_nf; exact le_refl a, by ring_nf; exact le_refl a⟩

/-- Rewriting a window along an equality of the *outer* value. -/
theorem of_eq (h : a = b) : Between 1 1 a b := by
  subst h; exact refl a

/-- **Windows compose.**  If `a` is within `[lo', hi']` of `b` and `b` is within
`[lo, hi]` of `c`, then `a` is within `[lo'·lo, hi'·hi]` of `c`.

The nonnegativity of the *outer* endpoints is needed and is exactly what makes
the two inequalities chain: a negative multiplier would reverse them. -/
theorem trans (hlo' : 0 ≤ lo') (hhi' : 0 ≤ hi')
    (hab : Between lo' hi' a b) (hbc : Between lo hi b c) :
    Between (lo' * lo) (hi' * hi) a c := by
  refine ⟨?_, ?_⟩
  · calc lo' * lo * c = lo' * (lo * c) := by ring
      _ ≤ lo' * b := by exact mul_le_mul_of_nonneg_left hbc.1 hlo'
      _ ≤ a := hab.1
  · calc a ≤ hi' * b := hab.2
      _ ≤ hi' * (hi * c) := by exact mul_le_mul_of_nonneg_left hbc.2 hhi'
      _ = hi' * hi * c := by ring

/-- A window is preserved by multiplying both sides by a nonnegative scalar. -/
theorem const_mul (hc : 0 ≤ c) (h : Between lo hi a b) :
    Between lo hi (c * a) (c * b) := by
  refine ⟨?_, ?_⟩
  · calc lo * (c * b) = c * (lo * b) := by ring
      _ ≤ c * a := mul_le_mul_of_nonneg_left h.1 hc
  · calc c * a ≤ c * (hi * b) := mul_le_mul_of_nonneg_left h.2 hc
      _ = hi * (c * b) := by ring

/-- Widening the window. -/
theorem mono (hb : 0 ≤ b) (hl : lo' ≤ lo) (hh : hi ≤ hi') (h : Between lo hi a b) :
    Between lo' hi' a b :=
  ⟨le_trans (mul_le_mul_of_nonneg_right hl hb) h.1,
   le_trans h.2 (mul_le_mul_of_nonneg_right hh hb)⟩

/-- **A shared window is inherited by sums.**  The two inequalities are summed
term by term, so this needs no sign hypothesis.

Do not read more into that than it says: a *weighted* sum `∑ cᵢ · aᵢ` inherits the
window only when the `cᵢ` are nonnegative, since that is what `Between.const_mul`
needs to produce the per-term windows in the first place.  With coefficients
`(1, -1)` the conclusion is false. -/
theorem sum {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (h : ∀ i ∈ s, Between lo hi (f i) (g i)) :
    Between lo hi (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  refine ⟨?_, ?_⟩
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' => (h i hi').1
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi' => (h i hi').2

/-- **Telescoping.**  A per-step window `[lo, hi]` along `F 0, F 1, …, F n`
composes to the window `[lo^n, hi^n]` between the endpoints. -/
theorem pow_of_chain (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) (F : ℕ → ℝ) (n : ℕ)
    (h : ∀ t < n, Between lo hi (F (t + 1)) (F t)) :
    Between (lo ^ n) (hi ^ n) (F n) (F 0) := by
  induction n with
  | zero => simpa using refl (F 0)
  | succ n ih =>
      have hstep : Between lo hi (F (n + 1)) (F n) := h n (Nat.lt_succ_self n)
      have hprev : Between (lo ^ n) (hi ^ n) (F n) (F 0) :=
        ih fun t ht => h t (lt_trans ht (Nat.lt_succ_self n))
      have := trans hlo hhi hstep hprev
      simpa [pow_succ, mul_comm] using this

/-- The symmetric window `Between (1-ε) (1+ε)` is exactly `Arlib.relErr`. -/
theorem relErr_iff {ε : ℝ} : Between (1 - ε) (1 + ε) a b ↔ a ∈ relErr ε b := Iff.rfl

end Between

/-! ## Calibrating the per-step tolerance

The algorithm sets its per-step tolerance to `δ = ε/(3n)` and pays it `n` times.
These are the two inequalities that turn `(1 ± δ)^n` back into `1 ± ε`. -/

/-- An elementary Bernoulli-type upper bound: if `n·a ≤ 1/2` then
`(1+a)^n ≤ 1 + 2na`.

Proved by induction; the step needs `2·k·a ≤ 1` for `k < n`, which is exactly
what `n·a ≤ 1/2` supplies.  No exponential is involved. -/
theorem one_add_pow_le_one_add_two_mul {a : ℝ} (ha : 0 ≤ a) (n : ℕ)
    (hn : (n : ℝ) * a ≤ 1 / 2) :
    (1 + a) ^ n ≤ 1 + 2 * n * a := by
  induction n with
  | zero => simp
  | succ k ih =>
      have hk : (k : ℝ) * a ≤ 1 / 2 := by
        have : (k : ℝ) * a ≤ ((k : ℝ) + 1) * a := by nlinarith
        push_cast at hn; linarith
      have ihk : (1 + a) ^ k ≤ 1 + 2 * k * a := ih hk
      have hka : 2 * (k : ℝ) * a ≤ 1 := by linarith
      have hpos : (0 : ℝ) ≤ 1 + a := by linarith
      calc (1 + a) ^ (k + 1) = (1 + a) ^ k * (1 + a) := by ring
        _ ≤ (1 + 2 * k * a) * (1 + a) := by
              exact mul_le_mul_of_nonneg_right ihk hpos
        _ ≤ 1 + 2 * ((k : ℝ) + 1) * a := by nlinarith
        _ = 1 + 2 * ((k + 1 : ℕ) : ℝ) * a := by push_cast; ring

/-- **Upper calibration.**  For `ε ∈ [0,1]` and `n ≥ 1`,
`(1 + ε/(3n))^n ≤ 1 + ε`.

The slack is real: the bound actually obtained is `1 + 2ε/3`. -/
theorem one_add_div_pow_le {ε : ℝ} {n : ℕ} (hn : 0 < n) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (1 + ε / (3 * n)) ^ n ≤ 1 + ε := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 0 ≤ ε / (3 * n) := div_nonneg hε (by linarith)
  have hprod : (n : ℝ) * (ε / (3 * n)) = ε / 3 := by
    field_simp
    ring
  have hn2 : (n : ℝ) * (ε / (3 * n)) ≤ 1 / 2 := by rw [hprod]; linarith
  calc (1 + ε / (3 * n)) ^ n ≤ 1 + 2 * n * (ε / (3 * n)) :=
        one_add_pow_le_one_add_two_mul ha n hn2
    _ = 1 + 2 * (ε / 3) := by rw [mul_assoc, hprod]
    _ ≤ 1 + ε := by linarith

/-- **Lower calibration.**  For `ε ∈ [0,1]` and any `n`,
`1 - ε ≤ (1 - ε/(3n))^n`.

This is Bernoulli's inequality (`one_add_mul_le_pow`) at `a = -ε/(3n)`; the
bound actually obtained is `1 - ε/3`. -/
theorem one_sub_div_pow_ge {ε : ℝ} {n : ℕ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    1 - ε ≤ (1 - ε / (3 * n)) ^ n := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0; simpa using hε
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : -2 ≤ -(ε / (3 * n)) := by
    have : ε / (3 * n) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  have hber := one_add_mul_le_pow ha n
  have hprod : (n : ℝ) * (ε / (3 * n)) = ε / 3 := by
    field_simp
    ring
  have : (1 : ℝ) - ε / 3 ≤ (1 - ε / (3 * n)) ^ n := by
    have h1 : (1 : ℝ) + (n : ℝ) * -(ε / (3 * n)) = 1 - ε / 3 := by
      rw [mul_neg, hprod]; ring
    have h2 : (1 : ℝ) + -(ε / (3 * n)) = 1 - ε / (3 * n) := by ring
    rw [h1, h2] at hber
    exact hber
  linarith

/-- **The calibration, packaged.**  A telescoped window `[(1-δ)^n, (1+δ)^n]`
with `δ = ε/(3n)` is contained in the relative-error window `(1 ± ε)`. -/
theorem Between.relErr_of_calibrated {ε a b : ℝ} {n : ℕ}
    (hn : 0 < n) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hb : 0 ≤ b)
    (h : Between ((1 - ε / (3 * n)) ^ n) ((1 + ε / (3 * n)) ^ n) a b) :
    a ∈ relErr ε b :=
  Between.mono hb (one_sub_div_pow_ge hε hε1) (one_add_div_pow_le hn hε hε1) h

/-! ## Reciprocal windows

The two facts a median-of-means / reciprocal-estimator argument runs on: passing a
relative-error window through `x ↦ 1/x`, and the observation that a "loose" `(1±ε/2)`
window sits inside the "failing" reciprocal interval `[b/(1+ε), b/(1-ε)]`.  Both are
pure algebra over `ℝ`, independent of any probability model. -/

/-- **Reciprocal of a relative-error interval.**  For `x, c > 0` and `0 ≤ ε < 1`,
`1/x ∈ (1±ε)·c` iff `x ∈ [1/((1+ε)c), 1/((1-ε)c)]` — the passage between an estimate
`1/median ∈ (1±ε)/N` and the median lying in the reciprocal window `(1±ε)⁻¹·N`. -/
theorem recip_mem_relErr {x c ε : ℝ} (hx : 0 < x) (hc : 0 < c) (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    1 / x ∈ relErr ε c ↔ x ∈ Set.Icc (1 / ((1 + ε) * c)) (1 / ((1 - ε) * c)) := by
  have hd1 : 0 < (1 - ε) * c := mul_pos (by linarith) hc
  have hd2 : 0 < (1 + ε) * c := mul_pos (by linarith) hc
  rw [mem_relErr, Set.mem_Icc, le_div_iff₀ hx, div_le_iff₀ hx, div_le_iff₀ hd2,
    le_div_iff₀ hd1]
  constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> nlinarith [ha, hb]

/-- **Failing intervals are loose.**  For `0 ≤ ε < 1` and `b ≥ 0`, the loose interval
`(1±ε/2)·b` is contained in the failing interval `[b/(1+ε), b/(1-ε)]`.  Hence a value
outside the failing interval is outside `(1±ε/2)b` — the step that lets an `(1±ε/2)`
concentration bound cap the `(1±ε)⁻¹` failure probability. -/
theorem relErr_half_subset_recip {b ε : ℝ} (hb : 0 ≤ b) (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    relErr (ε / 2) b ⊆ Set.Icc (b / (1 + ε)) (b / (1 - ε)) := by
  intro y hy
  rw [mem_relErr] at hy
  rw [Set.mem_Icc]
  refine ⟨?_, ?_⟩
  · have h1 : b / (1 + ε) ≤ (1 - ε / 2) * b := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (mul_nonneg hb hε0) (show (0 : ℝ) ≤ 1 - ε by linarith)]
    linarith [hy.1]
  · have h2 : (1 + ε / 2) * b ≤ b / (1 - ε) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [mul_nonneg (mul_nonneg hb hε0) (show (0 : ℝ) ≤ 1 + ε by linarith)]
    linarith [hy.2]

end Arlib.Approximation
