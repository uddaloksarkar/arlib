/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.PhaseVar

/-!
# The terminal phase of Gaussian cooling: the second-moment bound at `i + 1 = m`

`Arlib.GaussianCooling.coolLaw_sq_moment_le` proves the per-phase second-moment bound

  `E_π(W²) ≤ (1 + 2/n) · E_π(W)²`,   `π = coolLaw m σsq K i`, `W = phaseScore m σsq K i`,

only for **interior** phases, `i + 1 < m`. The guard is not cosmetic. Its proof routes
through `fixed_var_bound_indicator`, i.e. through the logconcavity input
(`vol3_journal.tex:1342`, `lem:z-logconcave`) applied to the *three* Gaussian weights
`σᵢ²/(1+α)`, `σᵢ²`, `σᵢ²/(1−α)`; that only makes sense while the next phase weight is
still a Gaussian. At the terminal step the next weight is the constant `1`
(`coolWeight_of_ge`), so

  `coolRatio m σsq i x = e^{+‖x‖²/(2σᵢ²)}`   (`coolRatio_of_last`)

— note the **positive** exponent — and the second moment is the "`b = ∞`" degeneration

  `E_π(W²) = (∫_K e^{+‖x‖²/(2σᵢ²)}) / ∫_K e^{−‖x‖²/(2σᵢ²)}`,

which is a ratio of a *growing* Gaussian weight to a decaying one. No amount of
logconcavity controls it: the Gaussian decay that the interior argument spends is exactly
what has vanished.

## What is true, and what is not

**The bound is genuinely conditional on a radius/variance relation.** This file proves:

* `coolLaw_sq_moment_le_terminal` — the conditional bound. For `K ⊆ R·Bₙ` and any terminal
  index (`m ≤ i + 1`, which covers both `i + 1 = m` and every `i ≥ m`),

    `E_π(W²) ≤ e^{R²/(2σᵢ²)} · E_π(W)²`.

  No convexity, no logconcavity, no `n ≥ 3` — the argument is `1 ≤ W ≤ e^{R²/(2σᵢ²)}` on
  `K` and nothing else. This is the formal content of the second half of
  `vol3_journal.tex:1326` (`lem:starting-gauss`), whose hypothesis is
  `K ⊆ C√n·Bₙ`, `σᵢ² ≥ C²n`, `σᵢ₊₁² = ∞`. **The paper's stated constant is `e²`
  (`vol3_journal.tex:1336`); the bound proved here is `e^{R²/(2σᵢ²)}`, which under the
  paper's own hypothesis `R² = C²n ≤ σᵢ²` is `e^{1/2}` — a factor `e^{3/2}` better.**
  `coolLaw_sq_moment_le_terminal_paper` records that specialization.
* `coolLaw_sq_moment_le_terminal_flat` — the same in the shape the interior bound has,
  `E_π(W²) ≤ (1 + 2/n) · E_π(W)²`, under the explicit *flatness condition*

    `R² ≤ 2 σᵢ² · log(1 + 2/n)`   (`hflat`),

  i.e. the terminal Gaussian is flat enough on `K` that its total variation over `K` is
  within the interior phases' own variance allowance. This is strictly stronger than the
  paper's `σᵢ² ≥ R²` and is what a *uniform* constant across all phases costs.
* `coolLaw_sq_moment_le_all` — interior, terminal and past-the-end phases combined:
  `∀ i, E_π(W²) ≤ (1 + 2/n) · E_π(W)²`, for a convex body, the fixed rate, and `hflat` at
  the single index `i + 1 = m`. This is the `∀ i` shape that
  `Ttc.VolumeAlgorithm.cousinsVempalaOfSampler`'s `hvar_exact` field asks for, and which
  `Ttc.CV.hvar_exact_of_fixedRate` could supply only for `i + 1 < m`.

**The unconditional bound is false.** `terminal_sq_moment_unbounded` exhibits, for every
proposed constant `C` and every dimension `n ≥ 1`, a variance `σ² > 0` at which the
terminal ratio on the unit ball exceeds `C`:

  `∀ C, ∃ s > 0, C · E_π(W)² < E_π(W²)`   for `K = B₁`, `m = 1`, `i = 0`, `σ₀² = s`.

The body there is convex, measurable, contains the unit ball and has finite volume — every
hypothesis the interior theorem has — so the failure is caused solely by dropping the
radius/variance relation. The mechanism is transparent from the identity

  `E(W²)/E(W)² = (∫_K e^{+‖x‖²/2s})(∫_K e^{−‖x‖²/2s}) / Vol(K)²`

(`integral_phaseScore_sq_coolLaw_last` together with `integral_phaseScore_coolLaw`): as
`s ↓ 0` the first factor blows up like `e^{r²/2s}` on the shell `‖x‖ ≥ r`
(`setIntegral_exp_normSq_ge`) while the second only decays polynomially, since the inner
ball `‖x‖ ≤ ρ` alone contributes `e^{−ρ²/2s}ρⁿ` (`setIntegral_exp_neg_normSq_ge`).

## Scope

Nothing here is a rate claim. The flatness condition `R² ≤ 2σᵢ² log(1 + 2/n)` is a
statement about *one* phase's variance, and no schedule, phase count or running time is
constructed or bounded anywhere in this file. As everywhere in this development, the
conductance constants it would have to be combined with are exponentially small
(`Unblock.lean:591`), so no polynomial-time consequence follows from anything below.

No new `axiom`, no `sorry`, and no `Prop`-valued definition packaging a conclusion as a
hypothesis: `hflat` is an inequality between real numbers already in the statement's
signature.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open scoped ENNReal

/-! ## A bounded observable: `E(W²) ≤ B · E(W)`

The whole terminal argument is this one inequality plus `E(W) ≥ 1`. -/

section Bounded

variable {Ω : Type*} [MeasurableSpace Ω] {π : Measure Ω}

/-- **The elementary second-moment bound for a bounded observable.** If `0 ≤ W ≤ B` then
`W² ≤ B·W` pointwise, hence `E(W²) ≤ B·E(W)`.

This is where the terminal phase's second moment comes from: unlike the interior phases,
which need Brascamp–Lieb and logconcavity, the terminal score is *bounded above and below*
on the body and nothing finer is required. -/
theorem integral_sq_le_bound_mul_integral [IsProbabilityMeasure π] {W : Ω → ℝ} {B : ℝ}
    (hWm : Measurable W) (hW0 : ∀ x, 0 ≤ W x) (hWB : ∀ x, W x ≤ B) :
    ∫ x, W x ^ 2 ∂π ≤ B * ∫ x, W x ∂π := by
  have hsq : ∀ x, W x ^ 2 ≤ B ^ 2 := fun x => by nlinarith [hW0 x, hWB x]
  have hint2 : Integrable (fun x => W x ^ 2) π :=
    integrable_of_bounded (μ := π) (hWm.pow_const 2) (fun x => by positivity) hsq
  have hint1 : Integrable W π := integrable_of_bounded (μ := π) hWm hW0 hWB
  have hmono : ∫ x, W x ^ 2 ∂π ≤ ∫ x, B * W x ∂π :=
    integral_mono hint2 (hint1.const_mul B) fun x => by nlinarith [hW0 x, hWB x]
  rwa [integral_const_mul] at hmono

end Bounded

/-! ## The terminal phase

`m ≤ i + 1` is the terminal regime: the *next* phase weight is the constant `1`, so
`coolRatio` has the positive exponent `+‖x‖²/(2σᵢ²)` (or is `1` outright, past the end).
Both sub-cases are handled at once — the only facts used are `coolRatio ≥ 1` on `K`
(equivalently `chain (i+1) = Vol(K) ≥ chain i`) and `coolRatio ≤ e^{R²/(2σᵢ²)}` on `K`. -/

section TerminalBound

variable {n : ℕ}

/-- **The terminal phase's mean is at least `1`.** For `m ≤ i + 1` the next chain entry is
`Vol(K)` exactly (`chain_of_ge`), and every chain entry is at most `Vol(K)`
(`chain_le_volume`), so

  `E_π(W) = chain (i+1) / chain i ≥ 1`.

Contrast the interior phases, where the mean is a genuine ratio of two Gaussian integrals
and no such normalization is available. -/
theorem one_le_integral_phaseScore_coolLaw_terminal {m : ℕ} {σsq : ℕ → ℝ}
    (hσ : ∀ j, 0 < σsq j) {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤) {i : ℕ}
    (hterm : m ≤ i + 1) :
    1 ≤ ∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i) := by
  have hchain := chain_pos (m := m) (σsq := σsq) hσ hball hfin i
  rw [integral_phaseScore_coolLaw hKm hchain, le_div_iff₀ hchain, one_mul,
    chain_of_ge hterm K]
  exact chain_le_volume (hσ i) hfin

/-- **The terminal-phase second-moment bound, conditional on a radius.**

For a body `K ⊆ R·Bₙ` containing the unit ball, and any terminal index (`m ≤ i + 1`),

  `E_π(W²) ≤ e^{R²/(2σᵢ²)} · E_π(W)²`.

The proof is two lines of real content: `E(W²) ≤ B·E(W)` because `0 ≤ W ≤ B` everywhere
(`integral_sq_le_bound_mul_integral`, `phaseScore_le`), and `E(W) ≤ E(W)²` because
`E(W) ≥ 1` (`one_le_integral_phaseScore_coolLaw_terminal`).

**Convexity of `K` is not used**, nor is `n ≥ 3`, nor any logconcavity input — in sharp
contrast to the interior bound `coolLaw_sq_moment_le`. What *is* used, and cannot be
dropped, is the radius `R`: see `terminal_sq_moment_unbounded`, which shows the bound is
false with no relation between `R` and `σᵢ`.

Paper: `vol3_journal.tex:1326` (`lem:starting-gauss`, second statement), whose hypotheses
are `K ⊆ C√n·Bₙ` and `σᵢ² ≥ C²n`, i.e. exactly `R² ≤ σᵢ²`. -/
theorem coolLaw_sq_moment_le_terminal {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R) {i : ℕ} (hterm : m ≤ i + 1) :
    ∫ x, phaseScore m σsq K i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ Real.exp (R ^ 2 / (2 * σsq i))
        * (∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i)) ^ 2 := by
  haveI := coolLaw_isProbabilityMeasure (m := m) (σsq := σsq) hσ hball hfin i
  have hB : (0 : ℝ) < Real.exp (R ^ 2 / (2 * σsq i)) := Real.exp_pos _
  have h1 : ∫ x, phaseScore m σsq K i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ Real.exp (R ^ 2 / (2 * σsq i))
        * ∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i) :=
    integral_sq_le_bound_mul_integral (measurable_phaseScore hKm i)
      (phaseScore_nonneg m σsq K i) (phaseScore_le hσ hKR i)
  have h2 : 1 ≤ ∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i) :=
    one_le_integral_phaseScore_coolLaw_terminal hσ hKm hball hfin hterm
  have h3 : (∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i))
      ≤ (∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i)) ^ 2 := by nlinarith
  calc ∫ x, phaseScore m σsq K i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ Real.exp (R ^ 2 / (2 * σsq i))
        * ∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i) := h1
    _ ≤ Real.exp (R ^ 2 / (2 * σsq i))
        * (∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i)) ^ 2 :=
      mul_le_mul_of_nonneg_left h3 hB.le

/-- **The paper's own terminal statement, sharpened.** Under `vol3_journal.tex:1326`'s
hypothesis `R² ≤ σᵢ²` (there `R = C√n`, `σᵢ² ≥ C²n`), the terminal ratio is at most
`e^{1/2}`. The paper asserts `e²` at `vol3_journal.tex:1336`, via `Y ≤ e` where in fact
`Y ≤ e^{1/2}`; the loss is not used anywhere downstream, so this is a sharpening, not a
correction. -/
theorem coolLaw_sq_moment_le_terminal_paper {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R) {i : ℕ} (hterm : m ≤ i + 1)
    (hRσ : R ^ 2 ≤ σsq i) :
    ∫ x, phaseScore m σsq K i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ Real.exp (1 / 2)
        * (∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i)) ^ 2 := by
  refine (coolLaw_sq_moment_le_terminal hσ hKm hball hfin hKR hterm).trans ?_
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (sq_nonneg _)
  rw [div_le_div_iff₀ (by linarith [hσ i] : (0:ℝ) < 2 * σsq i) (by norm_num : (0:ℝ) < 2)]
  nlinarith [hσ i]

/-- **The terminal bound in the interior phases' shape**, under the *flatness condition*

  `R² ≤ 2 σᵢ² · log(1 + 2/n)`.

That is exactly `e^{R²/(2σᵢ²)} ≤ 1 + 2/n`: the terminal Gaussian varies over `K` by no
more than the interior phases' own variance allowance. It is a strictly stronger demand
than the paper's `σᵢ² ≥ R²` (`vol3_journal.tex:1326`), which only yields the constant
`e^{1/2}`; the price of a *uniform* constant across all phases is `σᵢ² ≳ n R²/4`. -/
theorem coolLaw_sq_moment_le_terminal_flat {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R) {i : ℕ} (hterm : m ≤ i + 1)
    (hn : 0 < n) (hflat : R ^ 2 ≤ 2 * σsq i * Real.log (1 + 2 / (n : ℝ))) :
    ∫ x, phaseScore m σsq K i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ (1 + 2 / (n : ℝ))
        * (∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i)) ^ 2 := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hC : (0 : ℝ) < 1 + 2 / (n : ℝ) := by positivity
  refine (coolLaw_sq_moment_le_terminal hσ hKm hball hfin hKR hterm).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [← Real.exp_log hC]
  refine Real.exp_le_exp.2 ?_
  rw [div_le_iff₀ (by linarith [hσ i] : (0:ℝ) < 2 * σsq i)]
  linarith [hflat]

end TerminalBound

/-! ## All phases at once

The interior bound (`coolLaw_sq_moment_le`) and the terminal bound above have the same
shape and the same constant once the flatness condition holds, so they glue into a single
`∀ i` statement — the shape `Ttc.VolumeAlgorithm.cousinsVempalaOfSampler`'s `hvar_exact`
field asks for. -/

section AllPhases

variable {n : ℕ}

/-- Along the fixed-rate schedule the variance is nondecreasing. -/
theorem sigmaSq_mono_of_fixedRate {σsq : ℕ → ℝ} {n : ℕ} (hσ : ∀ j, 0 < σsq j)
    (hn : 0 < n) (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + 1 / (n : ℝ)))
    {j k : ℕ} (hjk : j ≤ k) : σsq j ≤ σsq k := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1n : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  have hstep : ∀ l, σsq l ≤ σsq (l + 1) := by
    intro l
    rw [hrate l]
    nlinarith [hσ l]
  exact monotone_nat_of_le_succ hstep hjk

/-- **The flatness condition only has to be checked once.** Along the fixed-rate schedule
`R² ≤ 2σ_j² log(1 + 2/n)` at one index propagates to every later index, so `hflat` in
`coolLaw_sq_moment_le_all` is really a condition at the single terminal index `j = m − 1`. -/
theorem flat_of_fixedRate_of_le {σsq : ℕ → ℝ} {n : ℕ} {R : ℝ} (hσ : ∀ j, 0 < σsq j)
    (hn : 0 < n) (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + 1 / (n : ℝ)))
    {j k : ℕ} (hjk : j ≤ k)
    (hflat : R ^ 2 ≤ 2 * σsq j * Real.log (1 + 2 / (n : ℝ))) :
    R ^ 2 ≤ 2 * σsq k * Real.log (1 + 2 / (n : ℝ)) := by
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (1 + 2 / (n : ℝ)) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
                        linarith)
  have := sigmaSq_mono_of_fixedRate hσ hn hrate hjk
  nlinarith

/-- **The per-phase second-moment bound at *every* phase.**

For a convex body `K` with `B₁ ⊆ K ⊆ R·Bₙ`, the fixed cooling rate `σⱼ₊₁² = σⱼ²(1 + 1/n)`,
`n ≥ 3`, and the flatness condition `R² ≤ 2σⱼ² log(1 + 2/n)` at the terminal indices,

  `∀ i, E_π(W²) ≤ (1 + 2/n) · E_π(W)²`.

Interior phases (`i + 1 < m`) are `coolLaw_sq_moment_le` — Brascamp–Lieb plus
logconcavity, radius-free. Terminal phases (`m ≤ i + 1`) are
`coolLaw_sq_moment_le_terminal_flat` — elementary, but radius-bound. The `∀ i` quantifier
is what `hvar_exact` needs and what `Ttc.CV.hvar_exact_of_fixedRate` could not supply.

By `flat_of_fixedRate_of_le`, `hflat` need only be verified at `j = m − 1`. -/
theorem coolLaw_sq_moment_le_all {m : ℕ} {σsq : ℕ → ℝ} (hσ : ∀ j, 0 < σsq j)
    {K : Set (EuclSpace n)} (hK : Convex ℝ K) (hKm : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R) (hn : 3 ≤ n)
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + 1 / (n : ℝ)))
    (hflat : ∀ j, m ≤ j + 1 → R ^ 2 ≤ 2 * σsq j * Real.log (1 + 2 / (n : ℝ)))
    (i : ℕ) :
    ∫ x, phaseScore m σsq K i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ (1 + 2 / (n : ℝ))
        * (∫ x, phaseScore m σsq K i x ∂(coolLaw m σsq K i)) ^ 2 := by
  rcases lt_or_ge (i + 1) m with h | h
  · exact coolLaw_sq_moment_le hσ hK hKm hball hfin h hn (hrate i)
  · exact coolLaw_sq_moment_le_terminal_flat hσ hKm hball hfin hKR h (by omega) (hflat i h)

end AllPhases

/-! ## Non-vacuity: a concrete instance of every hypothesis at once

The witness is `n = 3`, `m = 1`, `K = closedBall 0 1 ⊆ EuclSpace 3`, `R = 1`, and the
geometric schedule `σⱼ² = 2·(4/3)ʲ`. Every hypothesis of `coolLaw_sq_moment_le_all` holds,
and — the point — with `m = 1` the *only* phase is `i = 0`, which is terminal
(`i + 1 = m`). The interior theorem `coolLaw_sq_moment_le` covers **no** phase of this
instance; the theorem proved here covers all of them.

The conclusion is not degenerate: `1 ≤ E_π(W)` (`one_le_integral_phaseScore_coolLaw_terminal`),
so both sides of the inequality are `≥ 1` and the constant `5/3` is a real constraint,
not a bound on `0 ≤ 0`. -/

section Witness

/-- `log(5/3) ≥ 2/5`, from `log t ≤ t − 1` at `t = 3/5`. -/
theorem two_fifths_le_log_five_thirds : (2 : ℝ) / 5 ≤ Real.log (5 / 3) := by
  have h : Real.log ((5 / 3 : ℝ)⁻¹) ≤ (5 / 3 : ℝ)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  rw [Real.log_inv] at h
  norm_num at h ⊢
  linarith

/-- **The non-vacuity witness.** All hypotheses of `coolLaw_sq_moment_le_all` are
simultaneously satisfiable, with a conclusion that is not trivially true: at the concrete
instance `n = 3`, `m = 1`, `K = B̄₁ ⊆ ℝ³`, `σⱼ² = 2·(4/3)ʲ`, every phase is terminal and

  `1 ≤ E_π(W)`   and   `E_π(W²) ≤ (5/3)·E_π(W)²`. -/
theorem terminal_witness (i : ℕ) :
    1 ≤ (∫ x, phaseScore 1 (fun j => 2 * (4 / 3 : ℝ) ^ j)
            (closedBall (0 : EuclSpace 3) 1) i x
          ∂(coolLaw 1 (fun j => 2 * (4 / 3 : ℝ) ^ j)
            (closedBall (0 : EuclSpace 3) 1) i)) ∧
      (∫ x, phaseScore 1 (fun j => 2 * (4 / 3 : ℝ) ^ j)
            (closedBall (0 : EuclSpace 3) 1) i x ^ 2
          ∂(coolLaw 1 (fun j => 2 * (4 / 3 : ℝ) ^ j)
            (closedBall (0 : EuclSpace 3) 1) i))
        ≤ (5 / 3 : ℝ)
          * (∫ x, phaseScore 1 (fun j => 2 * (4 / 3 : ℝ) ^ j)
              (closedBall (0 : EuclSpace 3) 1) i x
            ∂(coolLaw 1 (fun j => 2 * (4 / 3 : ℝ) ^ j)
              (closedBall (0 : EuclSpace 3) 1) i)) ^ 2 := by
  have hσ : ∀ j, (0 : ℝ) < 2 * (4 / 3 : ℝ) ^ j := fun j => by positivity
  have hKm : MeasurableSet (closedBall (0 : EuclSpace 3) 1) := measurableSet_closedBall
  have hball : ball (0 : EuclSpace 3) 1 ⊆ closedBall (0 : EuclSpace 3) 1 :=
    ball_subset_closedBall
  have hfin : volume (closedBall (0 : EuclSpace 3) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hcast : ((3 : ℕ) : ℝ) = 3 := by norm_num
  have hrate : ∀ j, 2 * (4 / 3 : ℝ) ^ (j + 1)
      = 2 * (4 / 3 : ℝ) ^ j * (1 + 1 / ((3 : ℕ) : ℝ)) := by
    intro j; rw [hcast, pow_succ]; ring
  have hone : ∀ j : ℕ, (1 : ℝ) ≤ (4 / 3 : ℝ) ^ j :=
    fun j => one_le_pow₀ (by norm_num)
  have hflat : ∀ j : ℕ, 1 ≤ j + 1 →
      (1 : ℝ) ^ 2 ≤ 2 * (2 * (4 / 3 : ℝ) ^ j) * Real.log (1 + 2 / ((3 : ℕ) : ℝ)) := by
    intro j _
    have hL : (2 : ℝ) / 5 ≤ Real.log (1 + 2 / ((3 : ℕ) : ℝ)) := by
      rw [hcast, show (1 : ℝ) + 2 / 3 = 5 / 3 by norm_num]
      exact two_fifths_le_log_five_thirds
    nlinarith [hone j]
  refine ⟨one_le_integral_phaseScore_coolLaw_terminal hσ hKm hball hfin (by omega), ?_⟩
  have key := coolLaw_sq_moment_le_all (m := 1) (σsq := fun j => 2 * (4 / 3 : ℝ) ^ j)
    hσ (convex_closedBall (0 : EuclSpace 3) 1) hKm hball hfin
    (R := 1) subset_rfl (by norm_num) hrate hflat i
  rw [hcast] at key
  norm_num at key ⊢
  linarith [key]

end Witness

/-! ## The unconditional bound is false

The radius hypothesis in `coolLaw_sq_moment_le_terminal` is not an artefact of the proof.
This section exhibits, for every dimension `n ≥ 1` and every proposed constant `C`, a
variance at which the terminal second-moment bound fails on the **unit ball** — a body
satisfying every hypothesis of the interior theorem `coolLaw_sq_moment_le` (convex,
measurable, containing `B₁`, finite volume) and every hypothesis of
`coolLaw_sq_moment_le_terminal` except the relation between `R` and `σ`.

The mechanism is the closed form `integral_phaseScore_sq_coolLaw_last`:

  `E_π(W²) = (∫_K e^{+‖x‖²/(2σ²)}) / ∫_K e^{−‖x‖²/(2σ²)}`,   `E_π(W) = Vol(K) / ∫_K e^{−‖x‖²/(2σ²)}`,

so the ratio is `(∫_K e^{+})·(∫_K e^{−}) / Vol(K)²`. As `σ² ↓ 0` the outer shell
`3/4 ≤ ‖x‖ < 1` forces the first factor above `e^{9/(32σ²)}·(1 − (3/4)ⁿ)·Vol(K)`, while the
inner ball `‖x‖ < 1/2` alone keeps the second above `e^{−1/(8σ²)}·2^{−n}·Vol(K)`; the
product grows like `e^{5/(32σ²)}`. -/

section Counterexample

variable {n : ℕ}

/-- **The terminal second moment in closed form.** At a terminal phase (`i < m ≤ i + 1`)
the phase weight of the *next* step is the constant `1`, so the score is
`e^{+‖x‖²/(2σᵢ²)}` and its square against the phase density is again a Gaussian weight —
but with the sign of the exponent *reversed*:

  `E_π(W²) = (∫_K e^{+‖x‖²/(2σᵢ²)}) / chain i`.

Compare `integral_phaseScore_sq_coolLaw`, the interior identity, where the same computation
lands on the *decaying* weight at the harmonic parameter `ab/(2a−b)`. -/
theorem integral_phaseScore_sq_coolLaw_last {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)}
    {i : ℕ} (hKm : MeasurableSet K) (hchain : 0 < chain m σsq K i) (hi : i < m)
    (hterm : m ≤ i + 1) :
    ∫ x, phaseScore m σsq K i x ^ 2 ∂(coolLaw m σsq K i)
      = (∫ x in K, Real.exp (‖x‖ ^ 2 / (2 * σsq i))) / chain m σsq K i := by
  rw [integral_coolLaw hchain]
  rw [show (∫ x in K, (coolWeight m σsq i x / chain m σsq K i)
        * phaseScore m σsq K i x ^ 2)
      = ∫ x in K, Real.exp (‖x‖ ^ 2 / (2 * σsq i)) / chain m σsq K i from
    setIntegral_congr_fun hKm fun x hx => by
      have hexp : Real.exp (-(‖x‖ ^ 2) / (2 * σsq i))
          * Real.exp (‖x‖ ^ 2 / (2 * σsq i)) ^ 2
          = Real.exp (‖x‖ ^ 2 / (2 * σsq i)) := by
        rw [pow_two (Real.exp (‖x‖ ^ 2 / (2 * σsq i))), ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [phaseScore_of_mem hx, coolRatio_of_last hi hterm, coolWeight_of_lt hi,
        div_mul_eq_mul_div, hexp]]
  rw [integral_div]

/-- Ball volumes scale by `ρⁿ` in `EuclSpace n`. -/
theorem volume_ball_toReal_eq (n : ℕ) (hn : 0 < n) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (volume (ball (0 : EuclSpace n) ρ)).toReal
      = ρ ^ n * (volume (ball (0 : EuclSpace n) 1)).toReal := by
  haveI : Nontrivial (EuclSpace n) := by
    refine Module.nontrivial_of_finrank_pos (R := ℝ) ?_
    rw [finrank_euclideanSpace_fin]; exact hn
  rw [Measure.addHaar_ball (volume : Measure (EuclSpace n)) 0 hρ, finrank_euclideanSpace_fin,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

/-- The outer shell `r ≤ ‖x‖ < 1` carries at least a `1 − rⁿ` fraction of the unit ball. -/
theorem volume_shell_ge (n : ℕ) (hn : 0 < n) {r : ℝ} (hr0 : 0 ≤ r) :
    (1 - r ^ n) * (volume (ball (0 : EuclSpace n) 1)).toReal
      ≤ (volume (ball (0 : EuclSpace n) 1 \ ball (0 : EuclSpace n) r)).toReal := by
  have hsub : ball (0 : EuclSpace n) 1
      ⊆ (ball (0 : EuclSpace n) 1 \ ball (0 : EuclSpace n) r) ∪ ball (0 : EuclSpace n) r := by
    rw [Set.sdiff_union_self]; exact Set.subset_union_left
  have hle : volume (ball (0 : EuclSpace n) 1)
      ≤ volume (ball (0 : EuclSpace n) 1 \ ball (0 : EuclSpace n) r)
        + volume (ball (0 : EuclSpace n) r) :=
    (measure_mono hsub).trans (measure_union_le _ _)
  have hf1 : volume (ball (0 : EuclSpace n) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hfd : volume (ball (0 : EuclSpace n) 1 \ ball (0 : EuclSpace n) r) ≠ ⊤ :=
    ((measure_mono Set.sdiff_subset).trans_lt measure_ball_lt_top).ne
  have hfr : volume (ball (0 : EuclSpace n) r) ≠ ⊤ := measure_ball_lt_top.ne
  have hR := (ENNReal.toReal_le_toReal hf1 (ENNReal.add_ne_top.2 ⟨hfd, hfr⟩)).2 hle
  rw [ENNReal.toReal_add hfd hfr, volume_ball_toReal_eq n hn hr0] at hR
  linarith

/-- A continuous function bounded on a ball is integrable there. -/
theorem integrableOn_ball_of_bounded {f : EuclSpace n → ℝ} {M ρ : ℝ}
    (hf : Continuous f) (hb : ∀ x ∈ ball (0 : EuclSpace n) ρ, ‖f x‖ ≤ M) :
    IntegrableOn f (ball (0 : EuclSpace n) ρ) volume := by
  refine Measure.integrableOn_of_bounded (M := M) measure_ball_lt_top.ne
    hf.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx using hb x hx

/-- **Lower bound on the growing Gaussian integral, via the outer shell.** On
`r ≤ ‖x‖ < 1` the weight `e^{+‖x‖²/(2s)}` is at least `e^{r²/(2s)}`, and that shell carries
at least a `1 − rⁿ` fraction of the ball. -/
theorem setIntegral_exp_normSq_ge (n : ℕ) (hn : 0 < n) {s r : ℝ} (hs : 0 < s)
    (hr0 : 0 ≤ r) :
    Real.exp (r ^ 2 / (2 * s)) * ((1 - r ^ n) * (volume (ball (0 : EuclSpace n) 1)).toReal)
      ≤ ∫ x in ball (0 : EuclSpace n) 1, Real.exp (‖x‖ ^ 2 / (2 * s)) := by
  have h2s : (0 : ℝ) < 2 * s := by positivity
  have hcg : Continuous fun x : EuclSpace n => Real.exp (‖x‖ ^ 2 / (2 * s)) := by fun_prop
  have hIg : IntegrableOn (fun x : EuclSpace n => Real.exp (‖x‖ ^ 2 / (2 * s)))
      (ball (0 : EuclSpace n) 1) volume := by
    refine integrableOn_ball_of_bounded (M := Real.exp (1 / (2 * s))) hcg fun x hx => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ((div_le_div_iff₀ h2s h2s).2 ?_)
    have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg x, mem_ball_zero_iff.1 hx]
    exact mul_le_mul_of_nonneg_right hx2 h2s.le
  have hSm : MeasurableSet (ball (0 : EuclSpace n) 1 \ ball (0 : EuclSpace n) r) :=
    measurableSet_ball.diff measurableSet_ball
  have hSsub : ball (0 : EuclSpace n) 1 \ ball (0 : EuclSpace n) r
      ⊆ ball (0 : EuclSpace n) 1 := Set.sdiff_subset
  have hSfin : volume (ball (0 : EuclSpace n) 1 \ ball (0 : EuclSpace n) r) ≠ ⊤ :=
    ((measure_mono hSsub).trans_lt measure_ball_lt_top).ne
  have step1 : (∫ _x in ball (0 : EuclSpace n) 1 \ ball (0 : EuclSpace n) r,
        Real.exp (r ^ 2 / (2 * s)))
      ≤ ∫ x in ball (0 : EuclSpace n) 1 \ ball (0 : EuclSpace n) r,
          Real.exp (‖x‖ ^ 2 / (2 * s)) := by
    refine setIntegral_mono_on (integrableOn_const' hSfin _) (hIg.mono_set hSsub) hSm
      fun x hx => ?_
    refine Real.exp_le_exp.2 ((div_le_div_iff₀ h2s h2s).2 ?_)
    have hxr : r ≤ ‖x‖ := by
      by_contra hcon
      exact hx.2 (mem_ball_zero_iff.2 (lt_of_lt_of_le (not_le.1 hcon) le_rfl))
    exact mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg x]) h2s.le
  have step2 : (∫ x in ball (0 : EuclSpace n) 1 \ ball (0 : EuclSpace n) r,
        Real.exp (‖x‖ ^ 2 / (2 * s)))
      ≤ ∫ x in ball (0 : EuclSpace n) 1, Real.exp (‖x‖ ^ 2 / (2 * s)) :=
    setIntegral_mono_set hIg (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
      (Filter.Eventually.of_forall fun x hx => hSsub hx)
  have step3 : (∫ _x in ball (0 : EuclSpace n) 1 \ ball (0 : EuclSpace n) r,
        Real.exp (r ^ 2 / (2 * s)))
      = Real.exp (r ^ 2 / (2 * s))
        * (volume (ball (0 : EuclSpace n) 1 \ ball (0 : EuclSpace n) r)).toReal := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
  have step4 : Real.exp (r ^ 2 / (2 * s))
        * ((1 - r ^ n) * (volume (ball (0 : EuclSpace n) 1)).toReal)
      ≤ Real.exp (r ^ 2 / (2 * s))
        * (volume (ball (0 : EuclSpace n) 1 \ ball (0 : EuclSpace n) r)).toReal :=
    mul_le_mul_of_nonneg_left (volume_shell_ge n hn hr0) (Real.exp_pos _).le
  linarith [step1, step2, step3.le, step3.ge, step4]

/-- **Lower bound on the decaying Gaussian integral, via the inner ball.** On `‖x‖ < ρ` the
weight `e^{−‖x‖²/(2s)}` is at least `e^{−ρ²/(2s)}`, and that ball is a `ρⁿ` fraction of the
unit ball. This decays only polynomially in `ρ`, which is why the product with the previous
bound still blows up. -/
theorem setIntegral_exp_neg_normSq_ge (n : ℕ) (hn : 0 < n) {s ρ : ℝ} (hs : 0 < s)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Real.exp (-(ρ ^ 2) / (2 * s)) * (ρ ^ n * (volume (ball (0 : EuclSpace n) 1)).toReal)
      ≤ ∫ x in ball (0 : EuclSpace n) 1, Real.exp (-(‖x‖ ^ 2) / (2 * s)) := by
  have h2s : (0 : ℝ) < 2 * s := by positivity
  have hcf : Continuous fun x : EuclSpace n => Real.exp (-(‖x‖ ^ 2) / (2 * s)) := by fun_prop
  have hIf : IntegrableOn (fun x : EuclSpace n => Real.exp (-(‖x‖ ^ 2) / (2 * s)))
      (ball (0 : EuclSpace n) 1) volume := by
    refine integrableOn_ball_of_bounded (M := 1) hcf fun x _ => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(‖x‖ ^ 2) / (2 * s))
        ≤ Real.exp 0 := by
          refine Real.exp_le_exp.2 ?_
          rw [div_le_iff₀ h2s, zero_mul]
          exact neg_nonpos.2 (sq_nonneg _)
      _ = 1 := Real.exp_zero
  have hsub : ball (0 : EuclSpace n) ρ ⊆ ball (0 : EuclSpace n) 1 := ball_subset_ball hρ1
  have step1 : (∫ _x in ball (0 : EuclSpace n) ρ, Real.exp (-(ρ ^ 2) / (2 * s)))
      ≤ ∫ x in ball (0 : EuclSpace n) ρ, Real.exp (-(‖x‖ ^ 2) / (2 * s)) := by
    refine setIntegral_mono_on (integrableOn_const' measure_ball_lt_top.ne _)
      (hIf.mono_set hsub) measurableSet_ball fun x hx => ?_
    refine Real.exp_le_exp.2 ((div_le_div_iff₀ h2s h2s).2 ?_)
    exact mul_le_mul_of_nonneg_right
      (by nlinarith [norm_nonneg x, mem_ball_zero_iff.1 hx]) h2s.le
  have step2 : (∫ x in ball (0 : EuclSpace n) ρ, Real.exp (-(‖x‖ ^ 2) / (2 * s)))
      ≤ ∫ x in ball (0 : EuclSpace n) 1, Real.exp (-(‖x‖ ^ 2) / (2 * s)) :=
    setIntegral_mono_set hIf (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
      (Filter.Eventually.of_forall fun x hx => hsub hx)
  have step3 : (∫ _x in ball (0 : EuclSpace n) ρ, Real.exp (-(ρ ^ 2) / (2 * s)))
      = Real.exp (-(ρ ^ 2) / (2 * s))
        * (ρ ^ n * (volume (ball (0 : EuclSpace n) 1)).toReal) := by
    rw [setIntegral_const, smul_eq_mul, measureReal_def, volume_ball_toReal_eq n hn hρ0]
    ring
  linarith [step1, step2, step3.le, step3.ge]

/-- **The terminal second-moment bound is false without a radius/variance relation.**

For every dimension `n ≥ 1` and every proposed constant `C` there is a variance `s > 0`
with

  `C · E_π(W)² < E_π(W²)`

at `K = B₁ ⊆ ℝⁿ`, `m = 1`, `i = 0`, `σ₀² = s`. The body is convex, measurable, contains
the unit ball and has finite volume — every hypothesis `coolLaw_sq_moment_le` places on
`K` — and `i + 1 = m`, so this is exactly the phase the interior theorem excludes. Hence
`coolLaw_sq_moment_le` **cannot** be extended to `i + 1 = m` by any argument with a
constant depending on `n` alone: `coolLaw_sq_moment_le_terminal`'s dependence on `R` and
`σᵢ` is necessary.

Concretely `s = 5 / (32·log(4·2ⁿ·(|C| + 1)))`, which makes the shell/inner-ball product
below equal `4·2ⁿ·(|C| + 1)` exactly. -/
theorem terminal_sq_moment_unbounded (n : ℕ) (hn : 0 < n) (C : ℝ) :
    ∃ s : ℝ, 0 < s ∧
      C * (∫ x, phaseScore 1 (fun _ => s) (ball (0 : EuclSpace n) 1) 0 x
              ∂(coolLaw 1 (fun _ => s) (ball (0 : EuclSpace n) 1) 0)) ^ 2
        < ∫ x, phaseScore 1 (fun _ => s) (ball (0 : EuclSpace n) 1) 0 x ^ 2
              ∂(coolLaw 1 (fun _ => s) (ball (0 : EuclSpace n) 1) 0) := by
  -- the variance, chosen so that `e^{5/(32s)} = 4·2ⁿ·(|C|+1)`
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hA0 : (0 : ℝ) < 4 * 2 ^ n * (|C| + 1) := by nlinarith [abs_nonneg C]
  have hA1 : (1 : ℝ) < 4 * 2 ^ n * (|C| + 1) := by nlinarith [abs_nonneg C]
  have hL : 0 < Real.log (4 * 2 ^ n * (|C| + 1)) := Real.log_pos hA1
  refine ⟨5 / (32 * Real.log (4 * 2 ^ n * (|C| + 1))), by positivity, ?_⟩
  set s : ℝ := 5 / (32 * Real.log (4 * 2 ^ n * (|C| + 1))) with hsdef
  have hs0 : (0 : ℝ) < s := by rw [hsdef]; positivity
  have hsne : s ≠ 0 := hs0.ne'
  have hLs : (5 : ℝ) / (32 * s) = Real.log (4 * 2 ^ n * (|C| + 1)) := by
    rw [hsdef]; field_simp
  -- the body, the chain, and the two moments in closed form
  have hσ : ∀ j : ℕ, (0 : ℝ) < (fun _ : ℕ => s) j := fun _ => hs0
  have hfin : volume (ball (0 : EuclSpace n) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hchain : 0 < chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 :=
    chain_pos hσ subset_rfl hfin 0
  have hc_eq : chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0
      = ∫ x in ball (0 : EuclSpace n) 1, Real.exp (-(‖x‖ ^ 2) / (2 * s)) :=
    chain_of_lt (by norm_num) _
  have hV0 : 0 < (volume (ball (0 : EuclSpace n) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne' hfin
  have hmean : (∫ x, phaseScore 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 x
        ∂(coolLaw 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0))
      = (volume (ball (0 : EuclSpace n) 1)).toReal
        / chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 := by
    rw [integral_phaseScore_coolLaw measurableSet_ball hchain,
      chain_of_ge (show 1 ≤ 0 + 1 by norm_num) (ball (0 : EuclSpace n) 1)]
  have hsq : (∫ x, phaseScore 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 x ^ 2
        ∂(coolLaw 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0))
      = (∫ x in ball (0 : EuclSpace n) 1, Real.exp (‖x‖ ^ 2 / (2 * s)))
        / chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 :=
    integral_phaseScore_sq_coolLaw_last measurableSet_ball hchain (by norm_num) (by norm_num)
  -- the two shell estimates, at `r = 3/4` and `ρ = 1/2`
  have hP_lb : Real.exp ((3 / 4 : ℝ) ^ 2 / (2 * s))
        * ((1 - (3 / 4 : ℝ) ^ n) * (volume (ball (0 : EuclSpace n) 1)).toReal)
      ≤ ∫ x in ball (0 : EuclSpace n) 1, Real.exp (‖x‖ ^ 2 / (2 * s)) :=
    setIntegral_exp_normSq_ge n hn hs0 (by norm_num)
  have hc_lb : Real.exp (-((1 / 2 : ℝ) ^ 2) / (2 * s))
        * ((1 / 2 : ℝ) ^ n * (volume (ball (0 : EuclSpace n) 1)).toReal)
      ≤ chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 := by
    rw [hc_eq]
    exact setIntegral_exp_neg_normSq_ge n hn hs0 (by norm_num) (by norm_num)
  have hP0 : (0 : ℝ) ≤ ∫ x in ball (0 : EuclSpace n) 1, Real.exp (‖x‖ ^ 2 / (2 * s)) :=
    setIntegral_nonneg measurableSet_ball fun x _ => (Real.exp_pos _).le
  have hprod : Real.exp ((3 / 4 : ℝ) ^ 2 / (2 * s)) * Real.exp (-((1 / 2 : ℝ) ^ 2) / (2 * s))
      = 4 * 2 ^ n * (|C| + 1) := by
    rw [← Real.exp_add,
      show ((3 / 4 : ℝ) ^ 2 / (2 * s) + -((1 / 2 : ℝ) ^ 2) / (2 * s)) = 5 / (32 * s) by
        field_simp; ring,
      hLs, Real.exp_log hA0]
  -- combine the two lower bounds
  have hmul := mul_le_mul hP_lb hc_lb
    (mul_nonneg (Real.exp_pos _).le (mul_nonneg (by positivity) hV0.le)) hP0
  have hLHS : Real.exp ((3 / 4 : ℝ) ^ 2 / (2 * s))
        * ((1 - (3 / 4 : ℝ) ^ n) * (volume (ball (0 : EuclSpace n) 1)).toReal)
      * (Real.exp (-((1 / 2 : ℝ) ^ 2) / (2 * s))
        * ((1 / 2 : ℝ) ^ n * (volume (ball (0 : EuclSpace n) 1)).toReal))
      = (4 * 2 ^ n * (|C| + 1)) * ((1 - (3 / 4 : ℝ) ^ n) * (1 / 2 : ℝ) ^ n)
        * (volume (ball (0 : EuclSpace n) 1)).toReal ^ 2 := by
    rw [← hprod]; ring
  rw [hLHS] at hmul
  -- the constant that comes out is `|C| + 1`
  have hpow_le_one : ∀ k : ℕ, (3 / 4 : ℝ) ^ k ≤ 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) k]
  have h34 : (3 / 4 : ℝ) ^ n ≤ 3 / 4 := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [pow_succ]
    nlinarith [hpow_le_one k, pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) k]
  have hAbig : |C| + 1
      ≤ (4 * 2 ^ n * (|C| + 1)) * ((1 - (3 / 4 : ℝ) ^ n) * (1 / 2 : ℝ) ^ n) := by
    have hpn : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
    have hstep : (4 * 2 ^ n * (|C| + 1)) * ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n)
        ≤ (4 * 2 ^ n * (|C| + 1)) * ((1 - (3 / 4 : ℝ) ^ n) * (1 / 2 : ℝ) ^ n) := by
      refine mul_le_mul_of_nonneg_left ?_ hA0.le
      nlinarith
    have heq : (4 * 2 ^ n * (|C| + 1)) * ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n) = |C| + 1 := by
      rw [show (4 * 2 ^ n * (|C| + 1)) * ((1 / 4 : ℝ) * (1 / 2 : ℝ) ^ n)
          = (|C| + 1) * ((2 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) by ring, ← mul_pow]
      norm_num
    linarith
  have hVsq : (0 : ℝ) < (volume (ball (0 : EuclSpace n) 1)).toReal ^ 2 := pow_pos hV0 2
  have h6 : (|C| + 1) * (volume (ball (0 : EuclSpace n) 1)).toReal ^ 2
      ≤ (4 * 2 ^ n * (|C| + 1)) * ((1 - (3 / 4 : ℝ) ^ n) * (1 / 2 : ℝ) ^ n)
        * (volume (ball (0 : EuclSpace n) 1)).toReal ^ 2 :=
    mul_le_mul_of_nonneg_right hAbig hVsq.le
  have hkey : C * (volume (ball (0 : EuclSpace n) 1)).toReal ^ 2
      < (∫ x in ball (0 : EuclSpace n) 1, Real.exp (‖x‖ ^ 2 / (2 * s)))
        * chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 := by
    nlinarith [le_abs_self C, hVsq, h6, hmul]
  -- divide back
  rw [hmean, hsq]
  have hc3 : (0 : ℝ) < chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 ^ 3 :=
    pow_pos hchain 3
  have e1 : C * ((volume (ball (0 : EuclSpace n) 1)).toReal
        / chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0) ^ 2
      = (C * (volume (ball (0 : EuclSpace n) 1)).toReal ^ 2
          * chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0)
        / chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 ^ 3 := by
    field_simp
  have e2 : (∫ x in ball (0 : EuclSpace n) 1, Real.exp (‖x‖ ^ 2 / (2 * s)))
        / chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0
      = ((∫ x in ball (0 : EuclSpace n) 1, Real.exp (‖x‖ ^ 2 / (2 * s)))
          * chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 ^ 2)
        / chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 ^ 3 := by
    field_simp
  have hpos : 0 < ((∫ x in ball (0 : EuclSpace n) 1, Real.exp (‖x‖ ^ 2 / (2 * s)))
        * chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 ^ 2
      - C * (volume (ball (0 : EuclSpace n) 1)).toReal ^ 2
        * chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0)
      / chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 ^ 3 :=
    div_pos (by nlinarith [hkey, hchain]) hc3
  have hsplit : ((∫ x in ball (0 : EuclSpace n) 1, Real.exp (‖x‖ ^ 2 / (2 * s)))
        * chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 ^ 2
      - C * (volume (ball (0 : EuclSpace n) 1)).toReal ^ 2
        * chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0)
      / chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 ^ 3
      = ((∫ x in ball (0 : EuclSpace n) 1, Real.exp (‖x‖ ^ 2 / (2 * s)))
          * chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 ^ 2)
        / chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 ^ 3
        - (C * (volume (ball (0 : EuclSpace n) 1)).toReal ^ 2
          * chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0)
          / chain 1 (fun _ : ℕ => s) (ball (0 : EuclSpace n) 1) 0 ^ 3 := by
    ring
  linarith [e1, e2, hpos, hsplit]

end Counterexample

/-! ### Axiom audit

Every result above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms integral_sq_le_bound_mul_integral
#print axioms one_le_integral_phaseScore_coolLaw_terminal
#print axioms coolLaw_sq_moment_le_terminal
#print axioms coolLaw_sq_moment_le_terminal_paper
#print axioms coolLaw_sq_moment_le_terminal_flat
#print axioms sigmaSq_mono_of_fixedRate
#print axioms flat_of_fixedRate_of_le
#print axioms coolLaw_sq_moment_le_all
#print axioms two_fifths_le_log_five_thirds
#print axioms terminal_witness
#print axioms integral_phaseScore_sq_coolLaw_last
#print axioms volume_ball_toReal_eq
#print axioms volume_shell_ge
#print axioms integrableOn_ball_of_bounded
#print axioms setIntegral_exp_normSq_ge
#print axioms setIntegral_exp_neg_normSq_ge
#print axioms terminal_sq_moment_unbounded

end Arlib.GaussianCooling
