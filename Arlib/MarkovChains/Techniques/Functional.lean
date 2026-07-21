/-
Copyright (c) 2026 Kuldeep S. Meel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kuldeep S. Meel
-/
/-
# The `L²(μ)` functional calculus: expectation, inner product, variance

The functional-analytic side of the spectral-independence machinery is carried
out entirely in `L²(μ)` for a distribution `μ` on a finite type.  This module
sets up the three functionals used everywhere downstream and the identities
relating them.

* `Ex μ f` — expectation `∑ x, μ x * f x`.
* `ip μ f g` — inner product `⟪f, g⟫_μ = ∑ x, μ x * f x * g x`.
* `Var μ f` — variance `μ((f - μ(f))²)`.

The key identities, all elementary algebra over a finite sum:

* `Var_eq_ip_sub_sq` — `Var μ f = ⟪f, f⟫_μ - (μ f)²`;
* `Var_eq_pair` — the *pair form* `Var μ f = ½ ∑ x, ∑ y, μ x * μ y * (f x - f y)²`,
  which is what makes variance directly comparable to a Dirichlet form;
* `Var_eq_ip_self_of_mean_zero` — on mean-zero functions variance *is* the
  squared norm, which is why almost every proof below starts by centering `f`.

We also record that `ip μ` is a positive semidefinite symmetric bilinear form
(`isBilin_ip`, `ip_comm`, `ip_self_nonneg`), so that `psd_cauchy_schwarz` from
`Arlib.MarkovChains.Bilinear` applies to it directly.

Everything here is proved from first principles with no `sorry`.
-/
import Arlib.MarkovChains.Techniques.Chain
import Arlib.MarkovChains.Techniques.Bilinear

namespace Arlib.MarkovChains

open scoped BigOperators
open Finset

variable {Ω : Type*} [Fintype Ω]

/-! ## Expectation -/

/-- The expectation `μ(f) = ∑ x, μ x * f x`. -/
def Ex (μ : FinDist Ω) (f : Ω → ℝ) : ℝ := ∑ x, μ x * f x

theorem Ex_apply (μ : FinDist Ω) (f : Ω → ℝ) : Ex μ f = ∑ x, μ x * f x := rfl

@[simp] theorem Ex_const (μ : FinDist Ω) (c : ℝ) : Ex μ (fun _ => c) = c :=
  μ.sum_coe_mul_const c

theorem Ex_add (μ : FinDist Ω) (f g : Ω → ℝ) :
    Ex μ (fun x => f x + g x) = Ex μ f + Ex μ g := by
  simp only [Ex, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem Ex_sub (μ : FinDist Ω) (f g : Ω → ℝ) :
    Ex μ (fun x => f x - g x) = Ex μ f - Ex μ g := by
  simp only [Ex, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem Ex_smul (μ : FinDist Ω) (c : ℝ) (f : Ω → ℝ) :
    Ex μ (fun x => c * f x) = c * Ex μ f := by
  simp only [Ex, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem Ex_sub_const (μ : FinDist Ω) (f : Ω → ℝ) (c : ℝ) :
    Ex μ (fun x => f x - c) = Ex μ f - c := by
  rw [Ex_sub, Ex_const]

theorem Ex_nonneg {μ : FinDist Ω} {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ Ex μ f :=
  Finset.sum_nonneg fun x _ => mul_nonneg (μ.coe_nonneg x) (hf x)

theorem Ex_mono {μ : FinDist Ω} {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : Ex μ f ≤ Ex μ g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.coe_nonneg x)

/-- Stationarity says exactly that the chain preserves expectations. -/
theorem Ex_act_of_stationary {μ : FinDist Ω} {P : FinChain Ω} (h : Stationary μ P)
    (f : Ω → ℝ) : Ex μ (P.act f) = Ex μ f := by
  simp only [Ex, FinKernel.act]
  calc ∑ x, μ x * ∑ y, P x y * f y
      = ∑ x, ∑ y, μ x * P x y * f y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    _ = ∑ y, ∑ x, μ x * P x y * f y := Finset.sum_comm
    _ = ∑ y, μ y * f y := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [← Finset.sum_mul, h y]

/-! ## Inner product -/

/-- The `L²(μ)` inner product `⟪f, g⟫_μ = ∑ x, μ x * f x * g x`. -/
def ip (μ : FinDist Ω) (f g : Ω → ℝ) : ℝ := ∑ x, μ x * f x * g x

theorem ip_apply (μ : FinDist Ω) (f g : Ω → ℝ) : ip μ f g = ∑ x, μ x * f x * g x := rfl

theorem ip_comm (μ : FinDist Ω) (f g : Ω → ℝ) : ip μ f g = ip μ g f :=
  Finset.sum_congr rfl fun x _ => by ring

theorem ip_self_nonneg (μ : FinDist Ω) (f : Ω → ℝ) : 0 ≤ ip μ f f :=
  Finset.sum_nonneg fun x _ => by
    have : μ x * f x * f x = μ x * (f x) ^ 2 := by ring
    rw [this]; exact mul_nonneg (μ.coe_nonneg x) (sq_nonneg _)

theorem ip_eq_Ex_mul (μ : FinDist Ω) (f g : Ω → ℝ) :
    ip μ f g = Ex μ (fun x => f x * g x) :=
  Finset.sum_congr rfl fun x _ => by ring

@[simp] theorem ip_one_right (μ : FinDist Ω) (f : Ω → ℝ) :
    ip μ f (fun _ => 1) = Ex μ f :=
  Finset.sum_congr rfl fun x _ => by ring

/-- `ip μ` is a bilinear form, so `psd_cauchy_schwarz` applies to it. -/
theorem isBilin_ip (μ : FinDist Ω) : IsBilin (ip μ) := isBilin_weighted _

/-- **Cauchy–Schwarz in `L²(μ)`.** -/
theorem ip_sq_le (μ : FinDist Ω) (f g : Ω → ℝ) :
    ip μ f g ^ 2 ≤ ip μ f f * ip μ g g :=
  psd_cauchy_schwarz (isBilin_ip μ) (ip_comm μ) (ip_self_nonneg μ) f g

/-! ## Variance -/

/-- The variance `Var_μ(f) = μ((f - μ(f))²)`. -/
def Var (μ : FinDist Ω) (f : Ω → ℝ) : ℝ := Ex μ (fun x => (f x - Ex μ f) ^ 2)

theorem Var_apply (μ : FinDist Ω) (f : Ω → ℝ) :
    Var μ f = ∑ x, μ x * (f x - Ex μ f) ^ 2 := rfl

theorem Var_nonneg (μ : FinDist Ω) (f : Ω → ℝ) : 0 ≤ Var μ f :=
  Ex_nonneg fun _ => sq_nonneg _

/-- `Var_μ(f) = ⟪f, f⟫_μ - (μ f)²`. -/
theorem Var_eq_ip_sub_sq (μ : FinDist Ω) (f : Ω → ℝ) :
    Var μ f = ip μ f f - (Ex μ f) ^ 2 := by
  have key : ∀ x, μ x * (f x - Ex μ f) ^ 2
      = μ x * f x * f x - 2 * Ex μ f * (μ x * f x) + (Ex μ f) ^ 2 * μ x := by
    intro x; ring
  rw [Var_apply, Finset.sum_congr rfl fun x _ => key x]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [μ.sum_coe]
  simp only [ip, Ex, mul_one]
  ring

@[simp] theorem Var_const (μ : FinDist Ω) (c : ℝ) : Var μ (fun _ => c) = 0 := by
  simp [Var]

/-- Variance is unchanged by subtracting a constant. -/
theorem Var_sub_const (μ : FinDist Ω) (f : Ω → ℝ) (c : ℝ) :
    Var μ (fun x => f x - c) = Var μ f := by
  simp only [Var, Ex_sub_const]
  exact Finset.sum_congr rfl fun x _ => by ring_nf

/-- On a mean-zero function, variance is the squared `L²(μ)` norm. -/
theorem Var_eq_ip_self_of_mean_zero {μ : FinDist Ω} {f : Ω → ℝ} (h : Ex μ f = 0) :
    Var μ f = ip μ f f := by
  rw [Var_eq_ip_sub_sq, h]; ring

/-- The *centering* of `f`: `f - μ(f)`.  Has mean zero and the same variance. -/
theorem Ex_center (μ : FinDist Ω) (f : Ω → ℝ) : Ex μ (fun x => f x - Ex μ f) = 0 := by
  rw [Ex_sub_const]; ring

theorem Var_eq_ip_center (μ : FinDist Ω) (f : Ω → ℝ) :
    Var μ f = ip μ (fun x => f x - Ex μ f) (fun x => f x - Ex μ f) := by
  rw [← Var_eq_ip_self_of_mean_zero (Ex_center μ f), Var_sub_const]

/-- **Pair form of the variance.**
`Var_μ(f) = ½ ∑_{x, y} μ(x) μ(y) (f x - f y)²`.  This is the identity that makes
variance directly comparable with a Dirichlet form. -/
theorem Var_eq_pair (μ : FinDist Ω) (f : Ω → ℝ) :
    Var μ f = (1 / 2) * ∑ x, ∑ y, μ x * μ y * (f x - f y) ^ 2 := by
  have expand : ∀ x y : Ω, μ x * μ y * (f x - f y) ^ 2
      = μ y * (μ x * f x * f x) - 2 * (μ x * f x) * (μ y * f y)
        + μ x * (μ y * f y * f y) := by
    intro x y; ring
  have inner : ∀ x : Ω, ∑ y, μ x * μ y * (f x - f y) ^ 2
      = (μ x * f x * f x) - 2 * (μ x * f x) * Ex μ f + μ x * ip μ f f := by
    intro x
    rw [Finset.sum_congr rfl fun y _ => expand x y]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      ← Finset.mul_sum, μ.sum_coe]
    simp only [Ex, ip]
    ring
  have hA : ∑ x, μ x * f x * f x = ip μ f f := rfl
  have hB : ∑ x, 2 * (μ x * f x) * Ex μ f = 2 * Ex μ f * Ex μ f := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    rfl
  have hC : ∑ x, μ x * ip μ f f = ip μ f f := by
    rw [← Finset.sum_mul, μ.sum_coe, one_mul]
  calc Var μ f = ip μ f f - (Ex μ f) ^ 2 := Var_eq_ip_sub_sq μ f
    _ = (1 / 2) * (ip μ f f - 2 * Ex μ f * Ex μ f + ip μ f f) := by ring
    _ = (1 / 2) * ∑ x, ∑ y, μ x * μ y * (f x - f y) ^ 2 := by
        congr 1
        rw [Finset.sum_congr rfl fun x _ => inner x, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, hA, hB, hC]

/-- Variance is monotone under a pointwise bound on the pair form; specialised
form used when comparing two distributions on the same space. -/
theorem Var_le_ip_self (μ : FinDist Ω) (f : Ω → ℝ) : Var μ f ≤ ip μ f f := by
  rw [Var_eq_ip_sub_sq]
  nlinarith [sq_nonneg (Ex μ f)]

/-! ## χ²-divergence -/

/-- The relative density `ν / μ` of `ν` with respect to `μ`, defined to be `0`
where `μ` vanishes. -/
noncomputable def relDensity (ν μ : FinDist Ω) : Ω → ℝ :=
  fun x => if μ x = 0 then 0 else ν x / μ x

/-- The χ²-divergence `D_{χ²}(ν ‖ μ) = Var_μ(ν/μ)`. -/
noncomputable def chiSq (ν μ : FinDist Ω) : ℝ := Var μ (relDensity ν μ)

theorem chiSq_nonneg (ν μ : FinDist Ω) : 0 ≤ chiSq ν μ := Var_nonneg _ _

/-- If `ν` is absolutely continuous with respect to `μ` then the relative
density has `μ`-mean `1`. -/
theorem Ex_relDensity {ν μ : FinDist Ω} (hac : ∀ x, μ x = 0 → ν x = 0) :
    Ex μ (relDensity ν μ) = 1 := by
  rw [Ex_apply]
  have : ∀ x : Ω, μ x * relDensity ν μ x = ν x := by
    intro x
    by_cases hx : μ x = 0
    · simp [relDensity, hx, hac x hx]
    · field_simp [relDensity, hx]
  rw [Finset.sum_congr rfl fun x _ => this x, ν.sum_coe]

/-- With absolute continuity, `D_{χ²}(ν ‖ μ) = ∑ x, (ν x - μ x)² / μ x`
in the form `⟪g, g⟫_μ - 1` for `g = ν/μ`. -/
theorem chiSq_eq_ip_sub_one {ν μ : FinDist Ω} (hac : ∀ x, μ x = 0 → ν x = 0) :
    chiSq ν μ = ip μ (relDensity ν μ) (relDensity ν μ) - 1 := by
  rw [chiSq, Var_eq_ip_sub_sq, Ex_relDensity hac]; norm_num

end Arlib.MarkovChains
