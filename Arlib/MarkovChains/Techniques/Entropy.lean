/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The entropy functional `Ent_μ(f)` and modified log-Sobolev inequalities

The spectral gap controls the decay of *variance*, and variance decay converts
into a mixing-time bound only at the cost of a factor `log(1/μ_min)`: the χ²
divergence of a point mass from `μ` is `1/μ(x) - 1`, so the number of steps
needed is `γ⁻¹ · log(1/μ_min)` (see `mixesWithin_of_log_le`).  For a spin system
on `n` sites `μ_min` is exponentially small in `n`, so `log(1/μ_min) = Θ(n)` and
the resulting bound is `O(n²)` — off by a factor of `n` from the truth.

The fix, and the route the monograph takes to *optimal* `O(n log n)` mixing, is
to replace variance by **entropy**.  The entropy functional
`Ent_μ(f) = μ(f log f) - μ(f) log μ(f)` plays exactly the role `Var_μ(f)` plays
in the `L²` theory — it is nonnegative, vanishes on constants, and is compared
to a Dirichlet form — but it is *linearly* homogeneous rather than quadratically
so, and the divergence it produces (the Kullback–Leibler divergence, rather than
χ²) is only `log(1/μ_min)` rather than `1/μ_min` for a point mass.  That single
change is what removes the spurious factor of `n`.

This module builds the functional as the exact analogue of `Var`:

* `mul_log_le_mul_log_add_sub`, `mul_log_lt_mul_log_add_sub` — the pointwise
  inequality `t log m ≤ t log t + (m - t)`, and its strict form.  Everything
  analytic in this file is a consequence of these; they are in turn immediate
  from `Real.log_le_sub_one_of_pos` applied to `m / t`.  No convexity API, no
  Jensen machinery, no measure theory.
* `mul_log_sum_le_sum_mul_log` — **Jensen's inequality for `t ↦ t log t`** in
  the only form we need: for weights `p` summing to `1` and `a ≥ 0`,
  `(∑ p a) log (∑ p a) ≤ ∑ p (a log a)`.  Applied with `p = μ` it is
  `Ent_nonneg`; applied with `p` a *row of the transition kernel* it is the
  one-step contraction `Ent_act_le`.
* `Ent`, `Ent_apply`, `Ent_const`, **`Ent_nonneg`**, `Ent_smul`,
  `eq_Ex_of_Ent_eq_zero` — the functional and its basic calculus.
* `ModLogSobolev μ P ρ` — the modified log-Sobolev inequality, deliberately the
  exact analogue of `SpectralGapAtLeast` with `Ent` in place of `Var`.
* `naiveModLogSobolev_le_zero` — **a warning**: with the Dirichlet form `ℰ(f, f)` on
  the right-hand side, that analogy is *false*, and the definition above is
  vacuous for `ρ > 0`.  Entropy is `1`-homogeneous and `ℰ(f, f)` is
  `2`-homogeneous, so testing the inequality at `c · f` and letting `c → 0`
  forces `ρ · Ent_μ(f) ≤ 0`.  The genuine modified log-Sobolev inequality has
  the *entropy production* `ℰ(f, log f)` on the right, which is `1`-homogeneous
  up to the additive `log c`; that functional is not developed here.
* **`Ent_act_le`** — entropy is non-increasing along any stationary chain,
  `Ent_μ(P f) ≤ Ent_μ(f)`, together with its iterate `Ent_act_iter_le`.  This is
  the honest discrete-time statement; the geometric decay
  `Ent_μ(P f) ≤ (1 - ρ) Ent_μ(f)` is *not* proved here, and does not follow from
  `ModLogSobolev` as defined above (see `naiveModLogSobolev_le_zero`).
* `klDiv ν μ = Ent_μ(ν/μ)` — the Kullback–Leibler divergence, with
  `klDiv_nonneg` and the data-processing bound `klDiv_push_le`, mirroring
  `chiSq_nonneg` and `chiSq_push_le` in `Arlib.MarkovChains.Techniques.SpectralGap`.

No eigenvalue, and no spectral notion beyond the Dirichlet form itself, appears
anywhere in this file.  Everything here is proved from first principles with no
`sorry`.
-/
import Arlib.MarkovChains.Techniques.SpectralGap
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## The pointwise inequality

Every analytic statement below is a consequence of `log x ≤ x - 1`, applied at
`x = m / t`, multiplied through by `t` and rearranged.  Recording it once in the
rearranged form `t log m ≤ t log t + (m - t)` keeps the rest of the file
algebraic.  Note the convention `Real.log 0 = 0`, which is what makes the
degenerate case `t = 0` work out to the harmless `0 ≤ m`. -/

/-- The **fundamental pointwise inequality** behind the entropy functional: for
`m > 0` and `t ≥ 0`,
`t · log m ≤ t · log t + (m - t)`.

Taking `μ`-expectations of this with `m = μ(f)` and `t = f y` makes the linear
term `(m - t)` integrate to zero and leaves exactly `Ent_nonneg`. -/
theorem mul_log_le_mul_log_add_sub {m t : ℝ} (hm : 0 < m) (ht : 0 ≤ t) :
    t * Real.log m ≤ t * Real.log t + (m - t) := by
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [zero_mul, Real.log_zero, zero_add, sub_zero]
    linarith
  · have ht0 : t ≠ 0 := hpos.ne'
    have hlog : Real.log (m / t) ≤ m / t - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hm.ne' ht0] at hlog
    have h2 := mul_le_mul_of_nonneg_left hlog hpos.le
    have hcancel : t * (m / t - 1) = m - t := by field_simp
    rw [hcancel] at h2
    linarith

/-- The **strict** form of `mul_log_le_mul_log_add_sub`: equality holds only at
`t = m`.  This is the equality case of `log x ≤ x - 1`, and it is what turns
`Ent_μ(f) = 0` into "`f` is constant on the support of `μ`". -/
theorem mul_log_lt_mul_log_add_sub {m t : ℝ} (hm : 0 < m) (ht : 0 ≤ t) (hne : t ≠ m) :
    t * Real.log m < t * Real.log t + (m - t) := by
  rcases ht.eq_or_lt with h0 | hpos
  · rw [← h0]
    simp only [zero_mul, Real.log_zero, zero_add, sub_zero]
    linarith
  · have ht0 : t ≠ 0 := hpos.ne'
    have hne' : m / t ≠ 1 := by
      intro hcon
      apply hne
      field_simp at hcon
      linarith
    have hlog : Real.log (m / t) < m / t - 1 :=
      Real.log_lt_sub_one_of_pos (by positivity) hne'
    rw [Real.log_div hm.ne' ht0] at hlog
    have h2 := mul_lt_mul_of_pos_left hlog hpos
    have hcancel : t * (m / t - 1) = m - t := by field_simp
    rw [hcancel] at h2
    linarith

/-! ## Jensen's inequality for `t ↦ t log t`

The single convexity fact this development needs, in the weighted finite-sum
form.  It is stated for an arbitrary probability weight vector `p` rather than
for a `FinDist`, because it is used twice with two different weight vectors: the
stationary distribution `μ` (giving `Ent_nonneg`) and a *row* `P x ·` of the
transition kernel (giving the one-step contraction of entropy). -/

/-- **Jensen's inequality for `t ↦ t log t`.**  For nonnegative weights `p`
summing to `1` and a nonnegative `a`,
`(∑ p a) · log (∑ p a) ≤ ∑ p · (a log a)`.

The proof is the pointwise bound `mul_log_le_mul_log_add_sub` at
`m = ∑ p a` and `t = a y`, summed against `p`; the linear correction term
telescopes to `(∑ p a) · (∑ p) - (∑ p a) = 0`. -/
theorem mul_log_sum_le_sum_mul_log {p a : Ω → ℝ} (hp : ∀ y, 0 ≤ p y)
    (hp1 : ∑ y, p y = 1) (ha : ∀ y, 0 ≤ a y) :
    (∑ y, p y * a y) * Real.log (∑ y, p y * a y) ≤ ∑ y, p y * (a y * Real.log (a y)) := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ y, p y * a y := ⟨_, rfl⟩
  rw [← hA]
  have hterm : ∀ y : Ω, 0 ≤ p y * a y := fun y => mul_nonneg (hp y) (ha y)
  have hA0 : 0 ≤ A := hA ▸ Finset.sum_nonneg fun y _ => hterm y
  rcases hA0.eq_or_lt with hzero | hpos
  · -- Degenerate case: `∑ p a = 0` forces every term of both sums to vanish.
    have hz : ∀ y : Ω, p y * a y = 0 := by
      intro y
      refine (Finset.sum_eq_zero_iff_of_nonneg fun z _ => hterm z).mp ?_ y (Finset.mem_univ y)
      exact hA.symm.trans hzero.symm
    have hR : ∑ y : Ω, p y * (a y * Real.log (a y)) = 0 := by
      refine Finset.sum_eq_zero fun y _ => ?_
      rcases mul_eq_zero.mp (hz y) with h1 | h1
      · rw [h1]; ring
      · rw [h1]; simp
    rw [hR, ← hzero]
    simp
  · have key : ∀ y : Ω, p y * (a y * Real.log A)
        ≤ p y * (a y * Real.log (a y)) + (A * p y - p y * a y) := by
      intro y
      have hstep := mul_log_le_mul_log_add_sub hpos (ha y)
      have := mul_le_mul_of_nonneg_left hstep (hp y)
      linarith
    have hL : A * Real.log A = ∑ y : Ω, p y * (a y * Real.log A) := by
      rw [hA, Finset.sum_mul]
      exact Finset.sum_congr rfl fun y _ => by ring
    have hR : ∑ y : Ω, (p y * (a y * Real.log (a y)) + (A * p y - p y * a y))
        = ∑ y : Ω, p y * (a y * Real.log (a y)) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hp1, mul_one, ← hA]
      ring
    calc A * Real.log A = ∑ y : Ω, p y * (a y * Real.log A) := hL
      _ ≤ ∑ y : Ω, (p y * (a y * Real.log (a y)) + (A * p y - p y * a y)) :=
          Finset.sum_le_sum fun y _ => key y
      _ = ∑ y : Ω, p y * (a y * Real.log (a y)) := hR

/-! ## The entropy functional -/

/-- The **entropy of a function** `f` with respect to `μ`:
`Ent_μ(f) = μ(f log f) - μ(f) log μ(f)`.

This is the entropy of a *function against a distribution*, not the Shannon
entropy of a distribution; it is the entropy analogue of `Var μ f`, and the two
occupy the same place in the theory.  The one structural difference is
homogeneity: `Var` is quadratic (`Var_μ(c f) = c² Var_μ(f)`) whereas `Ent` is
*linear* (`Ent_smul`).  That difference is the whole point — it is why the
entropy route loses only `log log (1/μ_min)` where the `L²` route loses
`log (1/μ_min)`. -/
noncomputable def Ent (μ : FinDist Ω) (f : Ω → ℝ) : ℝ :=
  Ex μ (fun x => f x * Real.log (f x)) - Ex μ f * Real.log (Ex μ f)

theorem Ent_apply (μ : FinDist Ω) (f : Ω → ℝ) :
    Ent μ f = Ex μ (fun x => f x * Real.log (f x)) - Ex μ f * Real.log (Ex μ f) := rfl

/-- Entropy vanishes on constants.  No sign hypothesis on `c` is needed: for
`c < 0` both terms are still `c log c`, and for `c = 0` the Mathlib convention
`Real.log 0 = 0` makes both terms `0`. -/
@[simp] theorem Ent_const (μ : FinDist Ω) (c : ℝ) : Ent μ (fun _ => c) = 0 := by
  simp [Ent]

/-- A function that is constant has zero entropy. -/
theorem Ent_eq_zero_of_const (μ : FinDist Ω) {f : Ω → ℝ} {c : ℝ} (h : ∀ x, f x = c) :
    Ent μ f = 0 := by
  rw [show f = fun _ => c from funext h, Ent_const]

/-- **Entropy is nonnegative.**  This is the entropy analogue of `Var_nonneg`
and the key inequality of the module.

It is `mul_log_sum_le_sum_mul_log` with weights `μ`: no hypothesis beyond
`f ≥ 0` is needed, the degenerate case `μ(f) = 0` being covered by the
degenerate case of that lemma. -/
theorem Ent_nonneg (μ : FinDist Ω) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ Ent μ f := by
  have key := mul_log_sum_le_sum_mul_log (a := f) μ.coe_nonneg μ.sum_coe hf
  simp only [Ent, Ex]
  linarith

/-- **Entropy is linearly homogeneous**: `Ent_μ(c f) = c · Ent_μ(f)` for `c ≥ 0`.

Contrast `Var`, which is *quadratically* homogeneous.  This is not a cosmetic
difference: it is exactly why an inequality of the shape
`ρ · Ent_μ(f) ≤ ℰ_P(f, f)` is degenerate (`naiveModLogSobolev_le_zero`), and why the
correct right-hand side for a modified log-Sobolev inequality is the entropy
production `ℰ_P(f, log f)` rather than the Dirichlet form. -/
theorem Ent_smul (μ : FinDist Ω) {c : ℝ} (hc : 0 ≤ c) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) :
    Ent μ (fun x => c * f x) = c * Ent μ f := by
  rcases hc.eq_or_lt with h0 | hpos
  · rw [← h0]; simp [Ent]
  · have hm : 0 ≤ Ex μ f := Ex_nonneg hf
    have hmean : Ex μ (fun x => c * f x) = c * Ex μ f := Ex_smul μ c f
    have hpt : ∀ x : Ω, c * f x * Real.log (c * f x)
        = c * (f x * Real.log (f x)) + c * Real.log c * f x := by
      intro x
      rcases (hf x).eq_or_lt with hx0 | hx
      · rw [← hx0]; simp
      · rw [Real.log_mul hpos.ne' hx.ne']; ring
    have hfun : (fun x => c * f x * Real.log (c * f x))
        = (fun x => c * (f x * Real.log (f x)) + c * Real.log c * f x) := funext hpt
    have hlog : c * Ex μ f * Real.log (c * Ex μ f)
        = c * Real.log c * Ex μ f + c * (Ex μ f * Real.log (Ex μ f)) := by
      rcases hm.eq_or_lt with hm0 | hmpos
      · rw [← hm0]; simp
      · rw [Real.log_mul hpos.ne' hmpos.ne']; ring
    simp only [Ent]
    rw [hmean, hfun,
      Ex_add μ (fun x => c * (f x * Real.log (f x))) (fun x => c * Real.log c * f x),
      Ex_smul, Ex_smul, hlog]
    ring

/-- **Entropy detects constancy.**  If `f ≥ 0` has positive mean and zero
entropy then `f` is constant on the support of `μ`, equal to its own mean.

This is the converse to `Ent_eq_zero_of_const`, and the exact analogue of
"variance zero implies almost surely constant".  The proof is the equality case
of the pointwise inequality: `Ent_μ(f)` is the `μ`-average of the nonnegative
defect `f log f + (μ f - f) - f log μ(f)`, so a zero average forces the defect to
vanish wherever `μ` is positive, and `mul_log_lt_mul_log_add_sub` says that
happens only at `f = μ(f)`. -/
theorem eq_Ex_of_Ent_eq_zero {μ : FinDist Ω} {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hm : 0 < Ex μ f) (h : Ent μ f = 0) {x : Ω} (hx : x ∈ μ.support) :
    f x = Ex μ f := by
  -- The pointwise defect is nonnegative.
  have hD : ∀ y : Ω,
      0 ≤ μ y * (f y * Real.log (f y) + (Ex μ f - f y) - f y * Real.log (Ex μ f)) := by
    intro y
    refine mul_nonneg (μ.coe_nonneg y) ?_
    linarith [mul_log_le_mul_log_add_sub hm (hf y)]
  -- ... and it has `μ`-average `Ent μ f = 0`.
  have hEx : ∑ y : Ω, μ y * f y = Ex μ f := rfl
  have hEnt : ∑ y : Ω, μ y * (f y * Real.log (f y)) = Ex μ f * Real.log (Ex μ f) := by
    have hunfold : Ex μ (fun y => f y * Real.log (f y))
        = ∑ y : Ω, μ y * (f y * Real.log (f y)) := rfl
    rw [Ent_apply, hunfold] at h
    linarith
  have hsum : ∑ y : Ω,
      μ y * (f y * Real.log (f y) + (Ex μ f - f y) - f y * Real.log (Ex μ f)) = 0 := by
    have e : ∀ y : Ω,
        μ y * (f y * Real.log (f y) + (Ex μ f - f y) - f y * Real.log (Ex μ f))
        = μ y * (f y * Real.log (f y)) + (Ex μ f * μ y - μ y * f y)
          - Real.log (Ex μ f) * (μ y * f y) := fun y => by ring
    rw [Finset.sum_congr rfl fun y _ => e y, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, μ.sum_coe, mul_one,
      hEx, hEnt]
    ring
  -- Zero average of a nonnegative quantity: the defect vanishes at `x`.
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hD y).mp hsum x (Finset.mem_univ x)
  have hμx : 0 < μ x := μ.pos_of_mem_support hx
  have hDx : f x * Real.log (f x) + (Ex μ f - f x) - f x * Real.log (Ex μ f) = 0 := by
    rcases mul_eq_zero.mp hzero with h1 | h1
    · exact absurd h1 hμx.ne'
    · exact h1
  by_contra hne
  linarith [mul_log_lt_mul_log_add_sub hm (hf x) hne]

/-! ## The modified log-Sobolev inequality

Formally the exact analogue of `SpectralGapAtLeast`: replace `Var` by `Ent` and
keep the Dirichlet form on the right.  We record the two structural lemmas that
mirror `spectralGapAtLeast_zero` and `SpectralGapAtLeast.mono`, and then the
lemma that shows why this particular analogy has to be handled with care. -/

/-- Scaling a function scales the Dirichlet form quadratically:
`ℰ_P(c f, c f) = c² ℰ_P(f, f)`.  Compare `Ent_smul`, which is linear. -/
theorem dirichlet_smul_self (μ : FinDist Ω) (P : FinChain Ω) (c : ℝ) (f : Ω → ℝ) :
    dirichlet μ P (fun x => c * f x) (fun x => c * f x) = c ^ 2 * dirichlet μ P f f := by
  simp only [dirichlet_apply, FinKernel.act_smul, ip_smul_left, ip_smul_right]
  ring

/-- The **naive** analogue of `SpectralGapAtLeast`, with `Ent` substituted for
`Var` and the Dirichlet form `ℰ_P(f, f)` left on the right.

**This is a trap, and is recorded here only so that the trap is documented.**
It is vacuous for `ρ > 0`: see
`naiveModLogSobolev_le_zero`, which shows that for `ρ > 0` the condition forces
`Ent_μ(f) = 0` for every nonnegative `f`.  The non-degenerate inequality of the
literature has the entropy production `ℰ_P(f, log f)` on the right-hand side. -/
def NaiveModLogSobolev (μ : FinDist Ω) (P : FinChain Ω) (ρ : ℝ) : Prop :=
  ∀ f : Ω → ℝ, (∀ x, 0 ≤ f x) → ρ * Ent μ f ≤ dirichlet μ P f f

/-- Every stationary chain satisfies the modified log-Sobolev inequality with
constant `0`, since the Dirichlet form is nonnegative.  Mirrors
`spectralGapAtLeast_zero`. -/
theorem naiveModLogSobolev_zero {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P) :
    NaiveModLogSobolev μ P 0 := fun f _ => by
  simpa using dirichlet_self_nonneg h f

/-- A modified log-Sobolev constant weakens.  Mirrors `SpectralGapAtLeast.mono`;
note that here the monotonicity uses `Ent_nonneg` where the variance version
uses `Var_nonneg`, which is why the nonnegativity hypothesis on `f` is carried
along. -/
theorem NaiveModLogSobolev.mono {μ : FinDist Ω} {P : FinChain Ω} {ρ ρ' : ℝ}
    (h : NaiveModLogSobolev μ P ρ) (hle : ρ' ≤ ρ) : NaiveModLogSobolev μ P ρ' := fun f hf =>
  le_trans (mul_le_mul_of_nonneg_right hle (Ent_nonneg μ hf)) (h f hf)

/-- **The homogeneity obstruction.**  If `μ` is stationary for `P` and
`ModLogSobolev μ P ρ` holds, then `ρ · Ent_μ(f) ≤ 0` for every nonnegative `f`.

In particular the inequality carries no information for `ρ > 0`: it then says
`Ent_μ(f) = 0` for all `f ≥ 0`, which happens only in the degenerate case.  The
reason is pure homogeneity — `Ent_μ(c f) = c · Ent_μ(f)` while
`ℰ_P(c f, c f) = c² ℰ_P(f, f)`, so testing at `c f` gives
`ρ · Ent_μ(f) ≤ c · ℰ_P(f, f)` for *every* `c > 0`, and the right-hand side can
be made arbitrarily small.  This is why the modified log-Sobolev inequality of
the literature pairs `Ent_μ(f)` with the entropy production `ℰ_P(f, log f)`,
which scales the same way. -/
theorem naiveModLogSobolev_le_zero {μ : FinDist Ω} {P : FinChain Ω} {ρ : ℝ}
    (hst : Stationary μ P) (h : NaiveModLogSobolev μ P ρ) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ρ * Ent μ f ≤ 0 := by
  have hE : 0 ≤ dirichlet μ P f f := dirichlet_self_nonneg hst f
  have key : ∀ c : ℝ, 0 < c → ρ * Ent μ f ≤ c * dirichlet μ P f f := by
    intro c hc
    have h1 := h (fun x => c * f x) fun x => mul_nonneg hc.le (hf x)
    rw [Ent_smul μ hc.le hf, dirichlet_smul_self] at h1
    refine le_of_mul_le_mul_left ?_ hc
    linarith
  by_contra hcon
  push_neg at hcon
  rcases hE.eq_or_lt with h0 | hpos
  · have h1 := key 1 one_pos
    rw [← h0] at h1
    linarith
  · have hK0 : dirichlet μ P f f ≠ 0 := hpos.ne'
    have h1 := key (ρ * Ent μ f / (2 * dirichlet μ P f f)) (by positivity)
    have heq : ρ * Ent μ f / (2 * dirichlet μ P f f) * dirichlet μ P f f
        = ρ * Ent μ f / 2 := by field_simp; ring
    rw [heq] at h1
    linarith

/-! ## Entropy decay along the chain

The one-step statement that is genuinely true in discrete time is that entropy
is *non-increasing*.  Its proof is Jensen's inequality for `t ↦ t log t` applied
to the row `P x ·` of the kernel — that is, `mul_log_sum_le_sum_mul_log` again,
with the kernel row in place of `μ` — combined with the fact that stationarity
preserves `μ`-expectations, which handles both the `μ(f) log μ(f)` term and the
`μ(P (f log f)) = μ(f log f)` step.

We do *not* prove a geometric decay `Ent_μ(P f) ≤ (1 - ρ) Ent_μ(f)`.  The clean
statement of that kind belongs to the continuous-time semigroup, where the
derivative of the entropy is exactly the entropy production; the discrete-time
version needs an extra hypothesis, and in any case it cannot be deduced from
`ModLogSobolev` as defined above, by `naiveModLogSobolev_le_zero`. -/

/-- **Jensen along a kernel row**: `(P f)(x) · log (P f)(x) ≤ (P (f log f))(x)`.

This is `mul_log_sum_le_sum_mul_log` with the weight vector taken to be the row
`P x ·`, which is a probability vector by `FinKernel.sum_coe`. -/
theorem mul_log_act_le (P : FinChain Ω) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Ω) :
    P.act f x * Real.log (P.act f x) ≤ P.act (fun y => f y * Real.log (f y)) x := by
  have key := mul_log_sum_le_sum_mul_log (a := f) (P.coe_nonneg x) (P.sum_coe x) hf
  simpa only [FinKernel.act_apply] using key

/-- **Entropy is non-increasing along a stationary chain**:
`Ent_μ(P f) ≤ Ent_μ(f)` for every `f ≥ 0`.

The two ingredients are Jensen's inequality applied row by row
(`mul_log_act_le`), which gives `μ(P f · log P f) ≤ μ(P (f log f))`, and
stationarity, which gives both `μ(P (f log f)) = μ(f log f)` and
`μ(P f) = μ(f)`, so that the subtracted terms of the two entropies agree
exactly. -/
theorem Ent_act_le {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P) {f : Ω → ℝ}
    (hf : ∀ x, 0 ≤ f x) : Ent μ (P.act f) ≤ Ent μ f := by
  have hmean : Ex μ (P.act f) = Ex μ f := Ex_act_of_stationary h f
  have h1 : Ex μ (fun x => P.act f x * Real.log (P.act f x))
      ≤ Ex μ (P.act (fun y => f y * Real.log (f y))) :=
    Ex_mono fun x => mul_log_act_le P hf x
  have h2 : Ex μ (P.act (fun y => f y * Real.log (f y)))
      = Ex μ (fun y => f y * Real.log (f y)) := Ex_act_of_stationary h _
  simp only [Ent, hmean]
  linarith

section Iterate

variable [DecidableEq Ω]

/-- Entropy is non-increasing along every number of steps of a stationary chain:
`Ent_μ(P^t f) ≤ Ent_μ(f)`. -/
theorem Ent_act_iter_le {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P) {f : Ω → ℝ}
    (hf : ∀ x, 0 ≤ f x) (t : ℕ) : Ent μ ((P.iter t).act f) ≤ Ent μ f := by
  have hnn : ∀ (K : FinChain Ω) (g : Ω → ℝ), (∀ x, 0 ≤ g x) → ∀ x, 0 ≤ K.act g x :=
    fun K g hg x => Finset.sum_nonneg fun y _ => mul_nonneg (K.coe_nonneg x y) (hg y)
  induction t with
  | zero => simp
  | succ t ih =>
      rw [FinKernel.act_iter_succ]
      exact le_trans (Ent_act_le h (hnn (P.iter t) f hf)) ih

end Iterate

/-! ## The Kullback–Leibler divergence

Applying `Ent` to the relative density `ν/μ` produces the KL divergence, exactly
as applying `Var` to it produces the χ²-divergence (`chiSq`).  The two lemmas
below are the entropy counterparts of `chiSq_nonneg` and `chiSq_push_le`, and
they use the same bridge `relDensity_push` from
`Arlib.MarkovChains.Techniques.SpectralGap`. -/

/-- The **Kullback–Leibler divergence** `D(ν ‖ μ) = Ent_μ(ν/μ)`.

This is the entropy analogue of `chiSq ν μ = Var_μ(ν/μ)`, and is the divergence
that gives *optimal* mixing bounds: for a point mass it is `log(1/μ(x))` rather
than `1/μ(x) - 1`. -/
noncomputable def klDiv (ν μ : FinDist Ω) : ℝ := Ent μ (relDensity ν μ)

theorem klDiv_apply (ν μ : FinDist Ω) : klDiv ν μ = Ent μ (relDensity ν μ) := rfl

/-- **The KL divergence is nonnegative** — Gibbs' inequality, here an immediate
consequence of `Ent_nonneg`. -/
theorem klDiv_nonneg (ν μ : FinDist Ω) : 0 ≤ klDiv ν μ := by
  refine Ent_nonneg μ fun x => ?_
  by_cases hx : μ x = 0
  · simp [relDensity, hx]
  · simp only [relDensity, if_neg hx]
    exact div_nonneg (ν.coe_nonneg x) (μ.coe_nonneg x)

/-- The KL divergence of a fully supported distribution from itself is `0`. -/
theorem klDiv_self (μ : FinDist Ω) (hpos : ∀ x, 0 < μ x) : klDiv μ μ = 0 := by
  refine Ent_eq_zero_of_const (c := 1) μ fun x => ?_
  simp only [relDensity, if_neg (hpos x).ne']
  exact div_self (hpos x).ne'

/-- **Data processing for the KL divergence.**  Along a reversible chain with
fully supported stationary distribution, `D(ν P ‖ μ) ≤ D(ν ‖ μ)`.

This is the entropy counterpart of `chiSq_push_le`, and the natural starting
point for an optimal-mixing module: it says the KL divergence is a Lyapunov
function for the chain, and a quantitative rate for its decay is exactly what a
genuine modified log-Sobolev inequality would supply. -/
theorem klDiv_push_le {μ ν : FinDist Ω} {P : FinChain Ω} (hrev : Reversible μ P)
    (hpos : ∀ x, 0 < μ x) : klDiv (P.push ν) μ ≤ klDiv ν μ := by
  rw [klDiv_apply, klDiv_apply, relDensity_push hrev hpos]
  refine Ent_act_le hrev.stationary fun x => ?_
  simp only [relDensity, if_neg (hpos x).ne']
  exact div_nonneg (ν.coe_nonneg x) (μ.coe_nonneg x)

/-! ## Entropy production and the correct modified log-Sobolev inequality

The homogeneity obstruction above says the Dirichlet form `ℰ_P(f, f)` is the
wrong right-hand side.  The right one is the **entropy production**
`ℰ_P(f, log f)`, which is linearly homogeneous in `f` exactly as `Ent` is —
scaling `f` by `c` adds the constant `log c` to the second argument, and
constants lie in the kernel of the Dirichlet form. -/

/-- Constants are annihilated in the second argument of the Dirichlet form. -/
theorem dirichlet_const_right (μ : FinDist Ω) (P : FinChain Ω) (f : Ω → ℝ) (c : ℝ) :
    dirichlet μ P f (fun _ => c) = 0 := by
  rw [dirichlet_apply, FinKernel.act_const]
  ring

/-- Adding a constant to the second argument does not change the Dirichlet form. -/
theorem dirichlet_const_add_right (μ : FinDist Ω) (P : FinChain Ω) (f g : Ω → ℝ) (c : ℝ) :
    dirichlet μ P f (fun x => c + g x) = dirichlet μ P f g := by
  have hact : P.act (fun x => c + g x) = fun x => c + P.act g x := by
    funext x
    show ∑ y, P x y * (c + g y) = _
    have step : ∀ y : Ω, P x y * (c + g y) = c * P x y + P x y * g y := fun y => by ring
    rw [Finset.sum_congr rfl fun y _ => step y, Finset.sum_add_distrib, ← Finset.mul_sum,
      P.sum_coe x, mul_one]
    rfl
  have hip : ∀ h : Ω → ℝ, ip μ f (fun x => c + h x) = c * Ex μ f + ip μ f h := by
    intro h
    simp only [ip, Ex]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [dirichlet_apply, dirichlet_apply, hact, hip, hip]
  ring

/-- Scaling the first argument scales the Dirichlet form linearly. -/
theorem dirichlet_smul_left (μ : FinDist Ω) (P : FinChain Ω) (c : ℝ) (f g : Ω → ℝ) :
    dirichlet μ P (fun x => c * f x) g = c * dirichlet μ P f g := by
  rw [dirichlet_apply, dirichlet_apply, ip_smul_left, ip_smul_left]
  ring

/-- The **entropy production** of `f` for the chain `P`: the Dirichlet form
pairing `f` with `log f`.

`ℰ_P(f, log f) = ½ ∑_{x,y} μ(x) P(x,y) (f x − f y)(log f x − log f y)` for a
reversible chain, a sum of products of equal sign — which is the reason it is
the natural nonnegative quantity to put opposite `Ent`. -/
noncomputable def entropyProduction (μ : FinDist Ω) (P : FinChain Ω) (f : Ω → ℝ) : ℝ :=
  dirichlet μ P f (fun x => Real.log (f x))

theorem entropyProduction_apply (μ : FinDist Ω) (P : FinChain Ω) (f : Ω → ℝ) :
    entropyProduction μ P f = dirichlet μ P f (fun x => Real.log (f x)) := rfl

/-- **Entropy production is linearly homogeneous**, matching `Ent_smul`.

This is precisely what `ℰ_P(f, f)` fails to do, and hence precisely what makes
`ModLogSobolev` below a non-vacuous condition where `NaiveModLogSobolev` is
not. -/
theorem entropyProduction_smul (μ : FinDist Ω) (P : FinChain Ω) {c : ℝ} (hc : 0 < c)
    {f : Ω → ℝ} (hf : ∀ x, 0 < f x) :
    entropyProduction μ P (fun x => c * f x) = c * entropyProduction μ P f := by
  have hlog : (fun x => Real.log (c * f x)) = fun x => Real.log c + Real.log (f x) := by
    funext x
    rw [Real.log_mul hc.ne' (hf x).ne']
  rw [entropyProduction_apply, hlog, dirichlet_smul_left,
    dirichlet_const_add_right, entropyProduction_apply]

/-- **The modified log-Sobolev inequality** with constant `ρ`: for every strictly
positive `f`,

  `ρ · Ent_μ(f) ≤ ℰ_P(f, log f)`.

Both sides are linearly homogeneous in `f` (`Ent_smul`, `entropyProduction_smul`),
so unlike `NaiveModLogSobolev` this carries real content for `ρ > 0`.  It is the
entropy analogue of the Poincaré inequality `SpectralGapAtLeast`, and the route
to the optimal `O(n log n)` mixing bounds of §6.7 of the monograph. -/
def ModLogSobolev (μ : FinDist Ω) (P : FinChain Ω) (ρ : ℝ) : Prop :=
  ∀ f : Ω → ℝ, (∀ x, 0 < f x) → ρ * Ent μ f ≤ entropyProduction μ P f

/-- A modified log-Sobolev constant weakens. -/
theorem ModLogSobolev.mono {μ : FinDist Ω} {P : FinChain Ω} {ρ ρ' : ℝ}
    (h : ModLogSobolev μ P ρ) (hle : ρ' ≤ ρ) : ModLogSobolev μ P ρ' := fun f hf =>
  le_trans (mul_le_mul_of_nonneg_right hle (Ent_nonneg μ fun x => (hf x).le)) (h f hf)

/-- Scaling invariance of the inequality: if it holds at `f` it holds at `c f`.
A sanity check that the two sides really do scale together. -/
theorem ModLogSobolev.smul {μ : FinDist Ω} {P : FinChain Ω} {ρ : ℝ}
    (h : ModLogSobolev μ P ρ) {c : ℝ} (hc : 0 < c) {f : Ω → ℝ} (hf : ∀ x, 0 < f x) :
    ρ * Ent μ (fun x => c * f x) ≤ entropyProduction μ P (fun x => c * f x) :=
  h _ fun x => mul_pos hc (hf x)

end Arlib.MarkovChains
