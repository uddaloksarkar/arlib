/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.PhaseFromTV
import Arlib.Convexity.GaussianCooling.TerminalPhase

/-!
# `hterm`: the terminal-phase exact-law second moment, discharged

`Arlib/Convexity/GaussianCooling/PhaseFromTV.lean:317`'s `hphase_var_of_tvLe` proves
`Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`'s `hphase_var` binder from one
per-phase total-variation hypothesis, carrying exactly one unproved *exact-law* input,
`hterm` (`PhaseFromTV.lean:345`): the second-moment bound

    `∫ W² ∂π ≤ (1 + 2/n) · (∫ W ∂π)²`,   `π = coolLaw m σsq K i`,
    `W = phaseScore m σsq (interior K) i`

at the **terminal** index `i + 1 = m`, where the cooling switches from Gaussian to uniform.
Every non-terminal index is discharged outright by `coolLaw_interior_sq_moment_le`
(`PhaseFromTV.lean:221`, itself `PhaseVar.lean:513`), which needs `i + 1 < m`.

This file discharges `hterm` and produces `hphase_var_of_tvLe_of_flat` (§3), which is
`hphase_var_of_tvLe` with `hterm` gone.

## The finding, first: `hterm` is not an oversight, it is a genuine side condition

**`hterm` is not derivable from the other binders of `hphase_var_of_tvLe`, and no rewriting
of the terminal ratio makes it so.**  At `i + 1 = m` the next weight is the constant `1`
(`Chain.lean:144`, `coolWeight_of_ge`), so the terminal chain entry *is* `Vol(K)`
(`chain_end`) and the score is the Gaussian-to-uniform switch with a **positive** exponent,

    `coolRatio m σsq i x = e^{+‖x‖²/(2σᵢ²)}`   (`coolRatio_of_last`),

whence, in closed form (`TerminalPhase.lean:406`),

    `E_π(W²) = (∫_K e^{+‖x‖²/(2σᵢ²)}) / (∫_K e^{−‖x‖²/(2σᵢ²)})`,
    `E_π(W)  = Vol(K) / (∫_K e^{−‖x‖²/(2σᵢ²)})`,

so `E_π(W²)/E_π(W)²  =  (∫_K e^{+}) · (∫_K e^{−}) / Vol(K)²`.  Cauchy–Schwarz makes that
`≥ 1` always, and as `σᵢ² ↓ 0` it grows like `e^{Ω(R²/σᵢ²)}` — the ratio is *computable*
directly, exactly as the terminal weight being constant suggests, but the number that comes
out is `e^{R²/(2σᵢ²)}`, not `1 + 2/n`.

`§4` states this in `hterm`'s own shape.  `hterm_not_dischargeable` gives, for every
`n ≥ 1`, a variance `s > 0` at which the *`hterm` conclusion itself* — same score, same law,
same constant `1 + 2/n` — is **false**, at `K = B₁` (convex, containing the unit ball, of
finite volume: every hypothesis `hphase_var_of_tvLe` places on the body), with `phases = 1`,
terminal index `i = 0`, and the **fixed-rate** schedule `σⱼ² = s(1 + 1/n)ʲ`, so that the
`hrate` binder holds at the counterexample too.  §1's schedule-congruence lemmas are there
only to put `TerminalPhase.lean:568`'s refutation on that fixed-rate schedule.

`hterm` is therefore *satisfiable* but *conditional*: it is not false as a binder (it holds
vacuously at `phases = 0`, and genuinely at flat schedules — see the §5 witness), so
`PhaseFromTV.lean`'s results stand; but it cannot be deleted, only paid for.

## What it costs, and what the paper actually says

The price is the **flatness condition** at the terminal index,

    `hflat :  R² ≤ 2 σᵢ² · log(1 + 2/n)`,   i.e. exactly `e^{R²/(2σᵢ²)} ≤ 1 + 2/n`,

which by `log(1 + 2/n) ≍ 2/n` is `σᵢ² ≳ n R²/4`.  `coolLaw_interior_sq_moment_le_terminal`
(§2) is the unconditional-in-`n` half — `E(W²) ≤ B·E(W) ≤ B·E(W)²` from `1 ≤ W ≤ B` on the
body, `B = e^{R²/(2σᵢ²)}`, no convexity of the scored set, no logconcavity, no `n ≥ 3` —
and `hflat` is what turns `B` into `1 + 2/n`.

**The paper never claims `1 + 2/n` at the terminal phase.**  `1409.6011/vol3_journal.tex`:
`lem:fixed-var-bound` (`:1353`) proves `1 + 2/n` only for a Gaussian-to-Gaussian step at the
fixed rate; the terminal step is `lem:starting-gauss` (`:1326`, second statement), which
assumes `K ⊆ C√n·Bₙ` and `σᵢ² ≥ C²n` (i.e. `R² ≤ σᵢ²`) and concludes the *different*
constant `e²` (`:1336`); and `lem:accuracy` (`:1419`) then pays for it with a separate
factor `(1 + e²/k)` in its Chebyshev product, alongside `(1 + 2/(kn))^{m₁}` for the interior
phases.  `Ttc.VolumeAlgorithm.cousinsVempalaOfRunsApproxMean`'s `hphase_var` collapses that
two-constant accounting into **one** constant `1 + κ/m` valid at every phase, and `hflat`
(`σᵢ² ≳ nR²/4`, versus the paper's `σᵢ² ≥ R²`) is precisely what that collapse costs.  The
weaker `R² ≤ σᵢ²` buys only `e^{1/2}` (`TerminalPhase.lean:199`), which is `> 1 + 2/n` for
every `n ≥ 3`, so it does **not** discharge `hterm`.

`hflat` is the same flatness *inequality* the `Ttc` side already uses for the sampler
constructors that expose a radius (`Ttc/Volume/CousinsVempala.lean:2419-2424`, up to the
`radius K` / `R K ε p` naming), but at a different quantifier: there it is imposed at every
index `j` with `phases K ε p ≤ j + 1`, here only at the single in-range terminal index
`i : Fin (phases K ε p)` with `(i : ℕ) + 1 = phases K ε p`, which is all this route consumes.
Nothing under `Ttc/` is edited.

## What is reused verbatim (nothing below re-proves it)

* `Arlib.GaussianCooling.coolLaw_sq_moment_le_terminal` — `TerminalPhase.lean:169`, the
  conditional terminal bound at a measurable body.
* `Arlib.GaussianCooling.coolLaw_sq_moment_le_terminal_flat` — `TerminalPhase.lean:220`, the
  same at the constant `1 + 2/n` under `hflat`.
* `Arlib.GaussianCooling.one_le_integral_phaseScore_coolLaw_terminal` — `TerminalPhase.lean:142`.
* `Arlib.GaussianCooling.terminal_sq_moment_unbounded` — `TerminalPhase.lean:568`, the
  refutation of the unconditional bound.
* `Arlib.GaussianCooling.coolLaw_interior`, `chain_interior`, `ball_subset_interior`,
  `volume_interior_ne_top` — `PhaseFromTV.lean:133-155`, the interior bridge (the score is
  `interior K` because `MeasurableSet K` is **not** available from the binders; see that
  file's own finding).
* `Arlib.GaussianCooling.hphase_var_of_tvLe` — `PhaseFromTV.lean:317`; §3 is that theorem
  with `hterm` supplied, not a re-proof of it.

## Hypotheses still carried unproved by `hphase_var_of_tvLe_of_flat`

Unchanged from `hphase_var_of_tvLe` except that `hterm` is gone and `hflat` is new:

* `hTV` — the sampler's guarantee.  Conductance/mixing; not touched here.
* `hKR` — a radius `K ⊆ closedBall 0 (R K ε p)`.  `cousinsVempala` exposes none.
* `hslack`, `htop` — the smallness of the TV error.
* `hrate`, `hn : 3 ≤ n` — the fixed cooling rate, the regime of the interior bound.
* `hbudget` — `2m ≤ n·varBudget (ε/2)`.  Inherited **unchanged**: nothing here repairs or
  worsens the obstruction `geomSchedule_total_cooling_lt` (`PhaseVar.lean:620`) records,
  that a fixed-rate schedule meeting this budget cools by a total factor `< 1.1`.
* `hflat` — **new here**, and the only binder added: the terminal flatness condition above.
  It is a hypothesis about caller-chosen schedule data (`σsq`, `R`), and §5 exhibits a
  concrete body and fixed-rate schedule satisfying it for every `n ≥ 3`.

## Scope

Nothing here produces a TV bound, a conductance bound, a phase count or a running time.
-/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open scoped ENNReal

variable {n : ℕ}

/-! ## 1.  Schedule congruence

`coolWeight m σsq i` reads `σsq` at the single index `i`, and only when `i < m` — the
`if i < m` guard does not mention the schedule at all.  So every object built from it
depends on the schedule only through the values it actually reads.  This is used in §4 to
put the counterexample on a *fixed-rate* schedule, so that the `hrate` binder cannot be
said to rescue `hterm`. -/

theorem coolWeight_congr {m : ℕ} {σsq τ : ℕ → ℝ} {i : ℕ} (h : i < m → σsq i = τ i)
    (x : EuclSpace n) : coolWeight m σsq i x = coolWeight m τ i x := by
  unfold coolWeight
  by_cases hi : i < m
  · rw [if_pos hi, if_pos hi, h hi]
  · rw [if_neg hi, if_neg hi]

theorem chain_congr {m : ℕ} {σsq τ : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (h : i < m → σsq i = τ i) : chain m σsq K i = chain m τ K i := by
  simp only [chain, coolWeight_congr h]

theorem coolLaw_congr {m : ℕ} {σsq τ : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (h : i < m → σsq i = τ i) : coolLaw m σsq K i = coolLaw m τ K i := by
  simp only [coolLaw, coolWeight_congr h, chain_congr h]

theorem coolRatio_congr {m : ℕ} {σsq τ : ℕ → ℝ} {i : ℕ} (h : i < m → σsq i = τ i)
    (h' : i + 1 < m → σsq (i + 1) = τ (i + 1)) (x : EuclSpace n) :
    coolRatio m σsq i x = coolRatio m τ i x := by
  simp only [coolRatio, coolWeight_congr h, coolWeight_congr h']

theorem phaseScore_congr {m : ℕ} {σsq τ : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}
    (h : i < m → σsq i = τ i) (h' : i + 1 < m → σsq (i + 1) = τ (i + 1)) :
    phaseScore m σsq K i = phaseScore m τ K i := by
  simp only [phaseScore, funext (coolRatio_congr h h')]

/-! ## 2.  The terminal bound across the interior bridge

`TerminalPhase.lean` proves the terminal-phase bounds at a *measurable* body.  `hterm`
scores `interior K` under `coolLaw … K i`, so each is moved across
`PhaseFromTV.lean`'s bridge exactly as `coolLaw_interior_sq_moment_le` moves the interior
bound: `interior K` is open, hence Borel, and `coolLaw_interior` says the law does not see
the frontier. -/

section Interior

variable {m : ℕ} {σsq : ℕ → ℝ} {K : Set (EuclSpace n)} {i : ℕ}

/-- **The terminal-phase mean is at least `1`**, for the interior score under the law at
`K`.  `one_le_integral_phaseScore_coolLaw_terminal` across the bridge. -/
theorem one_le_integral_phaseScore_interior_coolLaw_terminal (hσ : ∀ j, 0 < σsq j)
    (hK : Convex ℝ K) (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    (hterm : m ≤ i + 1) :
    1 ≤ ∫ x, phaseScore m σsq (interior K) i x ∂(coolLaw m σsq K i) := by
  rw [← coolLaw_interior hK i]
  exact one_le_integral_phaseScore_coolLaw_terminal hσ isOpen_interior.measurableSet
    (ball_subset_interior hball) (volume_interior_ne_top hfin) hterm

/-- **The terminal-phase second moment, conditional on a radius.**  For `K ⊆ R·Bₙ` and any
terminal index (`m ≤ i + 1`),

    `E_π(W²) ≤ e^{R²/(2σᵢ²)} · E_π(W)²`,

with `π = coolLaw m σsq K i` and `W = phaseScore m σsq (interior K) i`.  No convexity of the
scored set, no logconcavity, no `n ≥ 3`: the content is `1 ≤ W ≤ e^{R²/(2σᵢ²)}` on the body.
(`hK` is used only by the bridge, to know the frontier is null.) -/
theorem coolLaw_interior_sq_moment_le_terminal (hσ : ∀ j, 0 < σsq j) (hK : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R) (hterm : m ≤ i + 1) :
    ∫ x, phaseScore m σsq (interior K) i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ Real.exp (R ^ 2 / (2 * σsq i))
        * (∫ x, phaseScore m σsq (interior K) i x ∂(coolLaw m σsq K i)) ^ 2 := by
  rw [← coolLaw_interior hK i]
  exact coolLaw_sq_moment_le_terminal hσ isOpen_interior.measurableSet
    (ball_subset_interior hball) (volume_interior_ne_top hfin)
    (interior_subset.trans hKR) hterm

/-- **`hterm`, discharged under the flatness condition `R² ≤ 2σᵢ² log(1 + 2/n)`.**

That condition is exactly `e^{R²/(2σᵢ²)} ≤ 1 + 2/n`: the terminal Gaussian varies over the
body by no more than the interior phases' own variance allowance.  This is the statement
`PhaseFromTV.lean`'s `hterm` binder asks for, at every terminal index at once. -/
theorem coolLaw_interior_sq_moment_le_terminal_flat (hσ : ∀ j, 0 < σsq j) (hK : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R) (hterm : m ≤ i + 1) (hn : 0 < n)
    (hflat : R ^ 2 ≤ 2 * σsq i * Real.log (1 + 2 / (n : ℝ))) :
    ∫ x, phaseScore m σsq (interior K) i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ (1 + 2 / (n : ℝ))
        * (∫ x, phaseScore m σsq (interior K) i x ∂(coolLaw m σsq K i)) ^ 2 := by
  rw [← coolLaw_interior hK i]
  exact coolLaw_sq_moment_le_terminal_flat hσ isOpen_interior.measurableSet
    (ball_subset_interior hball) (volume_interior_ne_top hfin)
    (interior_subset.trans hKR) hterm hn hflat

/-- **Every phase at once, for the interior score.**  Interior phases (`i + 1 < m`) are
`coolLaw_interior_sq_moment_le` — logconcavity, radius-free; terminal phases (`m ≤ i + 1`)
are the flat bound above.  Both land on the same constant `1 + 2/n`. -/
theorem coolLaw_interior_sq_moment_le_all (hσ : ∀ j, 0 < σsq j) (hK : Convex ℝ K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {R : ℝ} (hKR : K ⊆ closedBall (0 : EuclSpace n) R) (hn : 3 ≤ n)
    (hrate : ∀ j, σsq (j + 1) = σsq j * (1 + 1 / (n : ℝ)))
    (hflat : ∀ j, m ≤ j + 1 → R ^ 2 ≤ 2 * σsq j * Real.log (1 + 2 / (n : ℝ))) (i : ℕ) :
    ∫ x, phaseScore m σsq (interior K) i x ^ 2 ∂(coolLaw m σsq K i)
      ≤ (1 + 2 / (n : ℝ))
        * (∫ x, phaseScore m σsq (interior K) i x ∂(coolLaw m σsq K i)) ^ 2 := by
  rcases lt_or_ge (i + 1) m with h | h
  · exact coolLaw_interior_sq_moment_le hσ hK hball hfin h hn (hrate i)
  · exact coolLaw_interior_sq_moment_le_terminal_flat hσ hK hball hfin hKR h (by omega)
      (hflat i h)

end Interior

/-! ## 3.  `hphase_var_of_tvLe` without `hterm` -/

section Family

/-- **`cousinsVempalaOfRunsApproxMean`'s `hphase_var`, with `hterm` discharged.**

Every binder of `PhaseFromTV.lean`'s `hphase_var_of_tvLe` is copied here character for
character except the last exact-law input: `hterm` — an *integral inequality* the caller had
to supply — is replaced by `hflat`, an inequality between three real numbers already in the
signature,

    `R K ε p ² ≤ 2 · σsq K ε p i · log(1 + 2/n)`   at the terminal index `i + 1 = phases K ε p`.

The conclusion is unchanged, so this theorem is a drop-in replacement wherever
`hphase_var_of_tvLe` was going to be applied.

`hflat` cannot be dropped: §4 exhibits, for `K = B₁` (convex, containing the unit ball, of
finite volume) on a *fixed-rate* schedule with `phases = 1`, a variance at which `hterm`'s
own conclusion fails for the constant `1 + 2/n`, and indeed for every constant. -/
theorem hphase_var_of_tvLe_of_flat (E : Type) [MeasurableSpace E] (hn : 3 ≤ n)
    (phases : Set (EuclSpace n) → ℝ → ℝ → ℕ)
    (σsq : Set (EuclSpace n) → ℝ → ℝ → ℕ → ℝ)
    (ν : ℕ → ℕ → Measure E) [∀ j i, IsProbabilityMeasure (ν j i)]
    (X : Set (EuclSpace n) → ℝ → ℝ → ℕ → ℕ → E → EuclSpace n)
    (R : Set (EuclSpace n) → ℝ → ℝ → ℝ)
    (tvErr : Set (EuclSpace n) → ℝ → ℝ → ℕ → ℕ → ℝ≥0∞)
    (hσ : ∀ K ε p j, 0 < σsq K ε p j)
    (hX : ∀ K ε p j i, Measurable (X K ε p j i))
    (hKR : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)),
      K ⊆ Metric.closedBall (0 : EuclSpace n) (R K ε p))
    (htop : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      tvErr K ε p j (i : ℕ) ≠ ⊤)
    (hTV : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      TVLe ((ν j (i : ℕ)).map (X K ε p j (i : ℕ)))
        (coolLaw (phases K ε p) (σsq K ε p) K (i : ℕ)) (tvErr K ε p j (i : ℕ)))
    (hrate : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (i : Fin (phases K ε p)),
      σsq K ε p ((i : ℕ) + 1) = σsq K ε p (i : ℕ) * (1 + 1 / (n : ℝ)))
    (hbudget : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (_i : Fin (phases K ε p)),
      2 * (phases K ε p : ℝ) ≤ (n : ℝ) * varBudget (ε / 2))
    (hflat : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ →
      ∀ (_j : ℕ) (i : Fin (phases K ε p)),
      (i : ℕ) + 1 = phases K ε p →
      R K ε p ^ 2 ≤ 2 * σsq K ε p (i : ℕ) * Real.log (1 + 2 / (n : ℝ)))
    (hslack : ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      (tvErr K ε p j (i : ℕ)).toReal
          * (Real.exp (R K ε p ^ 2 / (2 * σsq K ε p (i : ℕ))) ^ 2
              * (1 + 2 * (1 + varBudget (ε / 2) / (phases K ε p : ℝ))))
        ≤ (varBudget (ε / 2) / (phases K ε p : ℝ) - 2 / (n : ℝ))
            * (chain (phases K ε p) (σsq K ε p) K ((i : ℕ) + 1)
                / chain (phases K ε p) (σsq K ε p) K (i : ℕ)) ^ 2) :
    ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (j : ℕ) (i : Fin (phases K ε p)),
      ∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
            (X K ε p j (i : ℕ) x) ^ 2 ∂(ν j (i : ℕ))
        ≤ (1 + varBudget (ε / 2) / (phases K ε p : ℝ))
            * (∫ x, phaseScore (phases K ε p) (σsq K ε p) (interior K) (i : ℕ)
                (X K ε p j (i : ℕ) x) ∂(ν j (i : ℕ))) ^ 2 :=
  hphase_var_of_tvLe E hn phases σsq ν X R tvErr hσ hX hKR htop hTV hrate hbudget
    (fun K ε p hε hp hp1 hconv hball hfin j i heq =>
      coolLaw_interior_sq_moment_le_terminal_flat (hσ K ε p) hconv hball hfin
        (hKR K ε p hε hp hp1 hconv hball hfin j i) (le_of_eq heq.symm) (by omega)
        (hflat K ε p hε hp hp1 hconv hball hfin j i heq))
    hslack

end Family

/-! ## 4.  `hterm` cannot simply be deleted

The bound `hflat` buys is not an artefact of the route taken above.  `TerminalPhase.lean`'s
`terminal_sq_moment_unbounded` refutes the unconditional terminal bound at the *unit ball*
with a constant schedule; the two restatements below put that refutation in `hterm`'s exact
shape — the score is `interior K`, the law is at `K`, and the schedule is the fixed-rate one
that `hphase_var_of_tvLe`'s own `hrate` binder demands.  So neither the interior bridge nor
`hrate` rescues `hterm`. -/

section Refutation

/-- **`hterm`'s conclusion is false, in `hterm`'s own shape, on a fixed-rate schedule.**

For every dimension `n ≥ 1` and every proposed constant `C` there is a variance `s > 0`
such that at `K = B₁`, `phases = 1`, terminal index `i = 0`, and the fixed-rate schedule
`σⱼ² = s(1 + 1/n)ʲ` (so `hrate` holds),

  `C · E_π(W)² < E_π(W²)`,   `W = phaseScore 1 σsq (interior K) 0`, `π = coolLaw 1 σsq K 0`.

`K = B₁` is convex, contains the unit ball and has finite volume — every hypothesis
`hphase_var_of_tvLe` places on the body. -/
theorem terminal_interior_sq_moment_unbounded (n : ℕ) (hn : 0 < n) (C : ℝ) :
    ∃ s : ℝ, 0 < s ∧
      C * (∫ x, phaseScore 1 (fun j => s * (1 + 1 / (n : ℝ)) ^ j)
                (interior (ball (0 : EuclSpace n) 1)) 0 x
              ∂(coolLaw 1 (fun j => s * (1 + 1 / (n : ℝ)) ^ j)
                  (ball (0 : EuclSpace n) 1) 0)) ^ 2
        < ∫ x, phaseScore 1 (fun j => s * (1 + 1 / (n : ℝ)) ^ j)
                (interior (ball (0 : EuclSpace n) 1)) 0 x ^ 2
              ∂(coolLaw 1 (fun j => s * (1 + 1 / (n : ℝ)) ^ j)
                  (ball (0 : EuclSpace n) 1) 0) := by
  obtain ⟨s, hs0, hlt⟩ := terminal_sq_moment_unbounded n hn C
  refine ⟨s, hs0, ?_⟩
  have h0 : (0 : ℕ) < 1 → (fun _ : ℕ => s) 0 = (fun j => s * (1 + 1 / (n : ℝ)) ^ j) 0 := by
    intro _; simp
  have h1 : (0 : ℕ) + 1 < 1 →
      (fun _ : ℕ => s) 1 = (fun j => s * (1 + 1 / (n : ℝ)) ^ j) 1 := by
    intro h; exact absurd h (by omega)
  rw [isOpen_ball.interior_eq,
    ← phaseScore_congr (m := 1) (i := 0) (K := ball (0 : EuclSpace n) 1)
      (σsq := fun _ => s) (τ := fun j => s * (1 + 1 / (n : ℝ)) ^ j) h0 h1,
    ← coolLaw_congr (m := 1) (i := 0) (K := ball (0 : EuclSpace n) 1)
      (σsq := fun _ => s) (τ := fun j => s * (1 + 1 / (n : ℝ)) ^ j) h0]
  exact hlt

/-- **The finding, at the constant `hterm` actually asks for.**  `hterm`'s conclusion with
`C = 1 + 2/n` is false at the instance above, so `hterm` is **not** derivable from the other
binders of `hphase_var_of_tvLe`: it is a genuine radius/variance condition, and
`hphase_var_of_tvLe_of_flat`'s `hflat` is what pays for it. -/
theorem hterm_not_dischargeable (n : ℕ) (hn : 0 < n) :
    ∃ s : ℝ, 0 < s ∧
      ¬ (∫ x, phaseScore 1 (fun j => s * (1 + 1 / (n : ℝ)) ^ j)
                (interior (ball (0 : EuclSpace n) 1)) 0 x ^ 2
              ∂(coolLaw 1 (fun j => s * (1 + 1 / (n : ℝ)) ^ j)
                  (ball (0 : EuclSpace n) 1) 0)
          ≤ (1 + 2 / (n : ℝ))
              * (∫ x, phaseScore 1 (fun j => s * (1 + 1 / (n : ℝ)) ^ j)
                    (interior (ball (0 : EuclSpace n) 1)) 0 x
                  ∂(coolLaw 1 (fun j => s * (1 + 1 / (n : ℝ)) ^ j)
                      (ball (0 : EuclSpace n) 1) 0)) ^ 2) := by
  obtain ⟨s, hs0, hlt⟩ := terminal_interior_sq_moment_unbounded n hn (1 + 2 / (n : ℝ))
  exact ⟨s, hs0, not_le.2 hlt⟩

end Refutation

/-! ## 5.  Non-vacuity (`CLAUDE.md` §11)

Two witnesses, of the two kinds `PhaseFromTV.lean` §5 distinguishes.

The **per-phase** one is genuine and is the one that matters here: it shows the new
hypothesis `hflat` is satisfiable *together with* the fixed rate, at a concrete body
(`closedBall 0 1`, of radius `R = 1`) and the concrete schedule `σⱼ² = (n+2)(1 + 1/n)ʲ`,
for every `n ≥ 3` at once — and that the conclusion it buys is not vacuous, since the mean
is at least `1`, so both sides of the inequality are `≥ 1`.

The **family** one is degenerate on purpose (zero phases), exactly as
`hphase_var_of_tvLe_witness` is, and for the same reason recorded there: `ν` is a fixed
family of laws chosen before `K` is seen, while `hTV` asks each `ν j i` to be TV-close to
`coolLaw … K i` for every admissible `K`.  That is the `Ttc` interface's own obstruction,
untouched here. -/

section Witness

/-- `log(1 + 2/n) ≥ 2/(n+2)`, from `log t ≤ t − 1` at `t = (1 + 2/n)⁻¹`. -/
theorem two_div_add_two_le_log {n : ℕ} (hn : 0 < n) :
    2 / ((n : ℝ) + 2) ≤ Real.log (1 + 2 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hinv : (0 : ℝ) < (1 + 2 / (n : ℝ))⁻¹ := by positivity
  have h := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv] at h
  have heq : (1 + 2 / (n : ℝ))⁻¹ = (n : ℝ) / ((n : ℝ) + 2) := by
    rw [show (1 : ℝ) + 2 / (n : ℝ) = ((n : ℝ) + 2) / (n : ℝ) by field_simp, inv_div]
  rw [heq] at h
  have hstep : (n : ℝ) / ((n : ℝ) + 2) - 1 = -(2 / ((n : ℝ) + 2)) := by
    field_simp
    ring
  linarith

/-- **Non-vacuity of `coolLaw_interior_sq_moment_le_terminal_flat`.**  At `m = 1` the only
phase `i = 0` is terminal, so the interior bound `coolLaw_interior_sq_moment_le` covers no
phase of this instance and the flat terminal bound covers it.  Every hypothesis holds
simultaneously — `K = B̄₁` is convex, contains the unit ball, has finite volume and radius
`R = 1`; the schedule `σⱼ² = (n+2)(1 + 1/n)ʲ` is positive and fixed-rate; and
`R² = 1 ≤ 4 ≤ 2σ₀² log(1 + 2/n)` — and the conclusion is not a bound on `0 ≤ 0`: the mean
is at least `1`. -/
theorem coolLaw_interior_sq_moment_le_terminal_flat_witness (hn : 3 ≤ n) :
    1 ≤ (∫ x, phaseScore 1 (fun j => ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j)
              (interior (closedBall (0 : EuclSpace n) 1)) 0 x
            ∂(coolLaw 1 (fun j => ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j)
                (closedBall (0 : EuclSpace n) 1) 0)) ∧
      (∫ x, phaseScore 1 (fun j => ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j)
              (interior (closedBall (0 : EuclSpace n) 1)) 0 x ^ 2
            ∂(coolLaw 1 (fun j => ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j)
                (closedBall (0 : EuclSpace n) 1) 0))
        ≤ (1 + 2 / (n : ℝ))
          * (∫ x, phaseScore 1 (fun j => ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j)
                (interior (closedBall (0 : EuclSpace n) 1)) 0 x
              ∂(coolLaw 1 (fun j => ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j)
                  (closedBall (0 : EuclSpace n) 1) 0)) ^ 2 := by
  have hn0 : 0 < n := by omega
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hσ : ∀ j, (0 : ℝ) < ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j := fun j => by positivity
  have hball : ball (0 : EuclSpace n) 1 ⊆ closedBall (0 : EuclSpace n) 1 :=
    ball_subset_closedBall
  have hfin : volume (closedBall (0 : EuclSpace n) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hlog := two_div_add_two_le_log hn0
  have hmul : ((n : ℝ) + 2) * (2 / ((n : ℝ) + 2))
      ≤ ((n : ℝ) + 2) * Real.log (1 + 2 / (n : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have heq2 : ((n : ℝ) + 2) * (2 / ((n : ℝ) + 2)) = 2 := by field_simp
  have hflat : (1 : ℝ) ^ 2
      ≤ 2 * (((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ 0) * Real.log (1 + 2 / (n : ℝ)) := by
    simp only [pow_zero, mul_one, one_pow]
    nlinarith
  refine ⟨one_le_integral_phaseScore_interior_coolLaw_terminal hσ
      (convex_closedBall _ _) hball hfin (by norm_num), ?_⟩
  exact coolLaw_interior_sq_moment_le_terminal_flat hσ (convex_closedBall _ _) hball hfin
    (R := 1) subset_rfl (by norm_num) hn0 hflat

/-- **Non-vacuity of `coolLaw_interior_sq_moment_le_all`**, the `∀ i` glue.  Same body and
same schedule as above but with `m = 2`, so the bundle is exercised on **both** branches:
`i = 0` is interior (`0 + 1 < 2`, the logconcavity bound) and every `i ≥ 1` is terminal (the
flat bound).  `hrate` holds by construction and `hflat` at every index follows from the
`j = 0` case because `(1 + 1/n)ʲ ≥ 1`. -/
theorem coolLaw_interior_sq_moment_le_all_witness (hn : 3 ≤ n) (i : ℕ) :
    ∫ x, phaseScore 2 (fun j => ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j)
            (interior (closedBall (0 : EuclSpace n) 1)) i x ^ 2
          ∂(coolLaw 2 (fun j => ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j)
              (closedBall (0 : EuclSpace n) 1) i)
      ≤ (1 + 2 / (n : ℝ))
        * (∫ x, phaseScore 2 (fun j => ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j)
              (interior (closedBall (0 : EuclSpace n) 1)) i x
            ∂(coolLaw 2 (fun j => ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j)
                (closedBall (0 : EuclSpace n) 1) i)) ^ 2 := by
  have hn0 : 0 < n := by omega
  have hN : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hσ : ∀ j, (0 : ℝ) < ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j := fun j => by positivity
  have hball : ball (0 : EuclSpace n) 1 ⊆ closedBall (0 : EuclSpace n) 1 :=
    ball_subset_closedBall
  have hfin : volume (closedBall (0 : EuclSpace n) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hrate : ∀ j, ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ (j + 1)
      = ((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j * (1 + 1 / (n : ℝ)) := by
    intro j; rw [pow_succ]; ring
  have hlog := two_div_add_two_le_log hn0
  have hq : (2 : ℝ) ≤ ((n : ℝ) + 2) * Real.log (1 + 2 / (n : ℝ)) := by
    have hmul : ((n : ℝ) + 2) * (2 / ((n : ℝ) + 2))
        ≤ ((n : ℝ) + 2) * Real.log (1 + 2 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have heq2 : ((n : ℝ) + 2) * (2 / ((n : ℝ) + 2)) = 2 := by field_simp
    linarith
  have hflat : ∀ j : ℕ, 2 ≤ j + 1 →
      (1 : ℝ) ^ 2 ≤ 2 * (((n : ℝ) + 2) * (1 + 1 / (n : ℝ)) ^ j)
        * Real.log (1 + 2 / (n : ℝ)) := by
    intro j _
    have hpow : (1 : ℝ) ≤ (1 + 1 / (n : ℝ)) ^ j :=
      one_le_pow₀ (by have : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
                      linarith)
    have hstep : (2 : ℝ) * 1
        ≤ (((n : ℝ) + 2) * Real.log (1 + 2 / (n : ℝ))) * (1 + 1 / (n : ℝ)) ^ j :=
      mul_le_mul hq hpow zero_le_one (by linarith)
    nlinarith [hstep]
  exact coolLaw_interior_sq_moment_le_all hσ (convex_closedBall _ _) hball hfin
    (R := 1) subset_rfl hn hrate hflat i

/-- Non-vacuity of the `hphase_var_of_tvLe_of_flat` bundle — **degenerate on purpose**
(zero phases); see the section docstring. -/
theorem hphase_var_of_tvLe_of_flat_witness (hn : 3 ≤ n) :
    ∀ (K : Set (EuclSpace n)) (ε p : ℝ), 0 < ε → 0 < p → p < 1 → Convex ℝ K →
      Metric.ball (0 : EuclSpace n) 1 ⊆ K → volume K ≠ ⊤ → ∀ (_j : ℕ) (i : Fin 0),
      ∫ x, phaseScore 0 (fun _ => (1 : ℝ)) (interior K) (i : ℕ) (id x) ^ 2
          ∂(Measure.dirac (0 : EuclSpace n))
        ≤ (1 + varBudget (ε / 2) / ((0 : ℕ) : ℝ))
            * (∫ x, phaseScore 0 (fun _ => (1 : ℝ)) (interior K) (i : ℕ) (id x)
                ∂(Measure.dirac (0 : EuclSpace n))) ^ 2 :=
  hphase_var_of_tvLe_of_flat (EuclSpace n) hn (fun _ _ _ => 0) (fun _ _ _ _ => 1)
    (fun _ _ => Measure.dirac 0) (fun _ _ _ _ _ => id) (fun _ _ _ => 1) (fun _ _ _ _ _ => 0)
    (fun _ _ _ _ => one_pos) (fun _ _ _ _ _ => measurable_id)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0) (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)
    (fun _ _ _ _ _ _ _ _ _ _ i => i.elim0)

end Witness

end Arlib.GaussianCooling

/-! ## Axiom audit (`CLAUDE.md` §4)

Every declaration above must depend on exactly `[propext, Classical.choice, Quot.sound]`. -/

#print axioms Arlib.GaussianCooling.coolWeight_congr
#print axioms Arlib.GaussianCooling.chain_congr
#print axioms Arlib.GaussianCooling.coolLaw_congr
#print axioms Arlib.GaussianCooling.coolRatio_congr
#print axioms Arlib.GaussianCooling.phaseScore_congr
#print axioms Arlib.GaussianCooling.one_le_integral_phaseScore_interior_coolLaw_terminal
#print axioms Arlib.GaussianCooling.coolLaw_interior_sq_moment_le_terminal
#print axioms Arlib.GaussianCooling.coolLaw_interior_sq_moment_le_terminal_flat
#print axioms Arlib.GaussianCooling.coolLaw_interior_sq_moment_le_all
#print axioms Arlib.GaussianCooling.hphase_var_of_tvLe_of_flat
#print axioms Arlib.GaussianCooling.terminal_interior_sq_moment_unbounded
#print axioms Arlib.GaussianCooling.hterm_not_dischargeable
#print axioms Arlib.GaussianCooling.two_div_add_two_le_log
#print axioms Arlib.GaussianCooling.coolLaw_interior_sq_moment_le_terminal_flat_witness
#print axioms Arlib.GaussianCooling.coolLaw_interior_sq_moment_le_all_witness
#print axioms Arlib.GaussianCooling.hphase_var_of_tvLe_of_flat_witness
