/-
Copyright (c) 2026 ArLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArLib contributors
-/
import Arlib.Convexity.BFArbitraryHeightSelector

/-!
# BF case 1: the small midpoint roof calculation

This is the deterministic profile calculation after the arbitrary-height pencil has selected a
lower roof.  When both endpoint values of the profile vanish, choose the pencil height at
`1/2` sufficiently small.  Any affine roof through that height which retains both endpoints is
uniformly small and therefore creates an affine core longer than the prescribed proper core.
-/

open Set

namespace Arlib

variable {m : ℕ}

theorem affineRoof_midpoint_uniform_le {u v tau : ℝ}
    (hpivot : u * (1 / 2) + v = tau) (h₀ : 0 ≤ v) (h₁ : 0 ≤ u + v) :
    ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ u * t + v ∧ u * t + v ≤ 2 * tau := by
  have hsum : v + (u + v) = 2 * tau := by linarith
  intro t ht
  have heq : u * t + v = (1 - t) * v + t * (u + v) := by ring
  rw [heq]
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) h₀) (mul_nonneg ht.1 h₁)
  · have hleft : (1 - t) * v ≤ v := by
      nlinarith [mul_nonneg ht.1 h₀]
    have hright : t * (u + v) ≤ u + v := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) h₁]
    linarith

/-- **The exact strict-improvement calculation in BF endpoint case 1.** -/
theorem affineRoof_caseOne_longer_core {psi : ℝ → ℝ}
    (hpsi : ConcaveOn ℝ (Icc (0 : ℝ) 1) psi)
    (hpsi0 : psi 0 = 0) (hpsi1 : psi 1 = 0)
    (hpsipos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < psi t)
    {a b : ℝ} (hab0 : 0 ≤ b - a) (hab : b - a < 1) :
    ∃ delta tau : ℝ, 0 < delta ∧ delta < 1 / 2 ∧ 0 < tau ∧
      b - a < (1 - delta) - delta ∧
      ∀ u v : ℝ, u * (1 / 2) + v = tau → 0 ≤ v → 0 ≤ u + v →
        profileBody (coordinateSimplex m) psi ∩ simplexRoof (fun t => u * t + v) =
            profileBody (coordinateSimplex m) (fun t => min (psi t) (u * t + v)) ∧
        ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t => min (psi t) (u * t + v)) ∧
        min (psi 0) v = 0 ∧ min (psi 1) (u + v) = 0 ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, 0 < min (psi t) (u * t + v)) ∧
        b - a < (1 - delta) - delta ∧
        ProfileAffineOn (fun t => min (psi t) (u * t + v)) delta (1 - delta) := by
  let delta : ℝ := (1 - (b - a)) / 4
  have hdelta0 : 0 < delta := by dsimp [delta]; linarith
  have hdeltahalf : delta < 1 / 2 := by dsimp [delta]; linarith
  have hdeltalt : delta < 1 - delta := by linarith
  have hpdelta : 0 < psi delta := hpsipos delta ⟨hdelta0, by linarith⟩
  have hpone : 0 < psi (1 - delta) := hpsipos (1 - delta) ⟨by linarith, by linarith⟩
  let tau : ℝ := min (psi delta) (psi (1 - delta)) / 4
  have htau : 0 < tau := by dsimp [tau]; positivity
  have hlong : b - a < (1 - delta) - delta := by dsimp [delta]; linarith
  refine ⟨delta, tau, hdelta0, hdeltahalf, htau, hlong, ?_⟩
  intro u v hpivot h₀ h₁
  have hroof := affineRoof_midpoint_uniform_le hpivot h₀ h₁
  have hbelow : ∀ t ∈ Icc delta (1 - delta), u * t + v ≤ psi t := by
    intro t ht
    have ht01 : t ∈ Icc (0 : ℝ) 1 := ⟨hdelta0.le.trans ht.1, ht.2.trans (by linarith)⟩
    have hpsiCore : min (psi delta) (psi (1 - delta)) ≤ psi t :=
      hpsi.min_le_of_mem_Icc
        ⟨hdelta0.le, by linarith⟩ ⟨by linarith, by linarith⟩ ht
    have hroofLe := (hroof t ht01).2
    dsimp [tau] at hroofLe
    linarith [lt_min hpdelta hpone]
  have hroofpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < u * t + v := by
    intro t ht
    have heq : u * t + v = (1 - t) * v + t * (u + v) := by ring
    have hsum : 0 < v + (u + v) := by
      have := hpivot
      linarith
    rw [heq]
    rcases lt_or_eq_of_le h₀ with hv | rfl
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht.2) hv)
        (mul_nonneg ht.1.le h₁)
    · have hu : 0 < u := by linarith
      simpa using mul_pos ht.1 hu
  exact affineRoof_cut_longer_affine_core (m := m) hpsi hpsi0 hpsi1 hpsipos
    hlong h₀ h₁ hroofpos hbelow

/-- **The strict-improvement calculation in BF endpoint case 2.**  When only the left
endpoint vanishes, put the pencil point at `(sigma, sigma * psi 1)`.  Every affine roof through
that point which retains both endpoints lies below the concave profile on `[sigma,1]`. -/
theorem affineRoof_caseTwo_longer_core {psi : ℝ → ℝ}
    (hpsi : ConcaveOn ℝ (Icc (0 : ℝ) 1) psi)
    (hpsi0 : psi 0 = 0) (hpsi1 : 0 < psi 1)
    (hpsipos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < psi t)
    {a b : ℝ} (hab0 : 0 ≤ b - a) (hab : b - a < 1) :
    ∃ sigma tau : ℝ, 0 < sigma ∧ sigma < 1 ∧ 0 < tau ∧
      b - a < 1 - sigma ∧ tau = sigma * psi 1 ∧
      ∀ u v : ℝ, u * sigma + v = tau → 0 ≤ v → 0 ≤ u + v →
        ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t => min (psi t) (u * t + v)) ∧
        min (psi 0) v = 0 ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, 0 < min (psi t) (u * t + v)) ∧
        b - a < 1 - sigma ∧
        ProfileAffineOn (fun t => min (psi t) (u * t + v)) sigma 1 := by
  let sigma : ℝ := (1 - (b - a)) / 2
  have hsigma0 : 0 < sigma := by dsimp [sigma]; linarith
  have hsigma1 : sigma < 1 := by dsimp [sigma]; linarith
  have hlong : b - a < 1 - sigma := by dsimp [sigma]; linarith
  let tau : ℝ := sigma * psi 1
  have htau : 0 < tau := mul_pos hsigma0 hpsi1
  refine ⟨sigma, tau, hsigma0, hsigma1, htau, hlong, rfl, ?_⟩
  intro u v hpivot h₀ h₁
  have hroofpos : ∀ t ∈ Ioo (0 : ℝ) 1, 0 < u * t + v := by
    intro t ht
    have heq : u * t + v = (1 - t) * v + t * (u + v) := by ring
    have hpivpos : 0 < (1 - sigma) * v + sigma * (u + v) := by
      have heq' : (1 - sigma) * v + sigma * (u + v) = u * sigma + v := by ring
      rw [heq', hpivot]
      exact htau
    rw [heq]
    rcases lt_or_eq_of_le h₀ with hv | rfl
    · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht.2) hv)
        (mul_nonneg ht.1.le h₁)
    · have hu : 0 < u := by
        have hsu : 0 < sigma * u := by simpa [mul_comm] using hpivpos
        rcases (mul_pos_iff.mp hsu) with hpos | hneg
        · exact hpos.2
        · exact False.elim ((not_lt_of_ge hsigma0.le) hneg.1)
      simpa using mul_pos ht.1 hu
  have hpsiSigma : u * sigma + v ≤ psi sigma := by
    rw [hpivot, show tau = sigma * psi 1 from rfl]
    have hc := hpsi.2 (⟨le_rfl, by norm_num⟩ : (0 : ℝ) ∈ Icc 0 1)
      (⟨by norm_num, le_rfl⟩ : (1 : ℝ) ∈ Icc 0 1)
      (sub_nonneg.mpr hsigma1.le) hsigma0.le (by ring)
    simpa [smul_eq_mul, hpsi0] using hc
  have hroof1 : u + v ≤ psi 1 := by
    have hp : u * sigma + v = sigma * psi 1 := by simpa [tau] using hpivot
    nlinarith [mul_nonneg (sub_pos.mpr hsigma1).le h₀]
  have hdiff : ConcaveOn ℝ (Icc (0 : ℝ) 1)
      (fun t => psi t - (u * t + v)) := by
    have haff : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => u * t + v) := by
      refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
      intro x hx y hy p q hp hq hpq
      dsimp only [smul_eq_mul]
      nlinarith
    exact hpsi.sub haff
  have hbelow : ∀ t ∈ Icc sigma 1, u * t + v ≤ psi t := by
    intro t ht
    have hmin := hdiff.min_le_of_mem_Icc
      (⟨hsigma0.le, hsigma1.le⟩ : sigma ∈ Icc (0 : ℝ) 1)
      (⟨by norm_num, le_rfl⟩ : (1 : ℝ) ∈ Icc (0 : ℝ) 1) ht
    have h₂ : 0 ≤ min (psi sigma - (u * sigma + v)) (psi 1 - (u * 1 + v)) :=
      le_min (sub_nonneg.mpr hpsiSigma) (by simpa using sub_nonneg.mpr hroof1)
    linarith
  refine ⟨concaveOn_min_affineRoof hpsi u v, ?_, ?_, hlong,
    profileAffineOn_min_affineRoof hbelow⟩
  · rw [hpsi0, min_eq_left h₀]
  · intro t ht
    exact lt_min (hpsipos t ht) (hroofpos t ht)

end Arlib

#print axioms Arlib.affineRoof_midpoint_uniform_le
#print axioms Arlib.affineRoof_caseOne_longer_core
#print axioms Arlib.affineRoof_caseTwo_longer_core
