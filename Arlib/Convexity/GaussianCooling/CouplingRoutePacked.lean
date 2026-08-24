/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.CouplingRoute

/-!
# Coupling all `k` samples at every Gaussian-cooling phase

`CouplingRoute` uses one coordinate of `RunSpace E r m` for every run and phase.  The
accelerated Cousins--Vempala estimator needs `k` independent samples at each such
coordinate.  This file packs those samples into the coordinate type `Fin k → E` and
tensorizes total variation once more.  Thus the coupling failure budget is the honest
`r * m * k` times the per-sample error.
-/

namespace Arlib.GaussianCooling

open MeasureTheory
open scoped ENNReal

variable {r m k : ℕ} {E : Type*} [MeasurableSpace E]

/-- The law of the `k` independent samples packed into run `j`, phase `i`. -/
noncomputable def packedPhaseLaw
    (ν : Fin r → Fin m → Fin k → Measure E) (j : Fin r) (i : Fin m) :
    Measure (Fin k → E) :=
  Measure.pi (ν j i)

instance packedPhaseLaw_isProbabilityMeasure
    (ν : Fin r → Fin m → Fin k → Measure E)
    [∀ j i l, IsProbabilityMeasure (ν j i l)] (j : Fin r) (i : Fin m) :
    IsProbabilityMeasure (packedPhaseLaw ν j i) := by
  unfold packedPhaseLaw
  infer_instance

/-- Packing `k` samples tensorizes their individual TV bounds additively. -/
theorem tvLe_packedPhaseLaw_const
    {ν ν' : Fin r → Fin m → Fin k → Measure E}
    [∀ j i l, IsProbabilityMeasure (ν j i l)]
    [∀ j i l, IsProbabilityMeasure (ν' j i l)]
    {b : ℝ≥0∞} (h : ∀ j i l, TVLe (ν j i l) (ν' j i l) b) (j : Fin r) (i : Fin m) :
    TVLe (packedPhaseLaw ν j i) (packedPhaseLaw ν' j i) ((k : ℕ) * b) := by
  have hpi := TVLe.pi (fun l => h j i l)
  simpa [packedPhaseLaw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hpi

/-- The exact coupling route for `r` runs, `m` phases, and `k` independent samples per
phase.  If the ideal packed estimator succeeds with probability at least `q`, replacing
every elementary sample by a law within TV `b` costs at most `r*m*k*b` in success
probability. -/
theorem le_measureReal_packedRun_of_failure_budget
    {ν ν' : Fin r → Fin m → Fin k → Measure E}
    [hν : ∀ j i l, IsProbabilityMeasure (ν j i l)]
    [hν' : ∀ j i l, IsProbabilityMeasure (ν' j i l)]
    {b : ℝ≥0∞} (hb : b ≠ ⊤) (htv : ∀ j i l, TVLe (ν j i l) (ν' j i l) b)
    {ρ : ℝ} (hρ : (((r * m * k : ℕ) : ℝ) * b.toReal) ≤ ρ)
    {V : Arlib.Probability.RunSpace (Fin k → E) r m → ℝ} (hV : Measurable V)
    {vol acc q : ℝ}
    (hgood : q ≤ (Arlib.Probability.runMeasure (packedPhaseLaw ν')).real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol}) :
    q - ρ ≤ (Arlib.Probability.runMeasure (packedPhaseLaw ν)).real
      {ω | (1 - acc) * vol ≤ V ω ∧ V ω ≤ (1 + acc) * vol} := by
  let bk : ℝ≥0∞ := (k : ℕ) * b
  have hbk : bk ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) hb
  have hphase : ∀ j i,
      TVLe (packedPhaseLaw ν j i) (packedPhaseLaw ν' j i) bk :=
    fun j i => tvLe_packedPhaseLaw_const htv j i
  have hbudget : (((r * m : ℕ) : ℝ) * bk.toReal) ≤ ρ := by
    rw [show bk.toReal = (k : ℝ) * b.toReal by
      simp [bk, ENNReal.toReal_mul]]
    norm_num at hρ ⊢
    nlinarith
  exact le_measureReal_runMeasure_of_failure_budget
    (ν := packedPhaseLaw ν) (ν' := packedPhaseLaw ν') hbk hphase hbudget hV hgood

end Arlib.GaussianCooling

#print axioms Arlib.GaussianCooling.tvLe_packedPhaseLaw_const
#print axioms Arlib.GaussianCooling.le_measureReal_packedRun_of_failure_budget
