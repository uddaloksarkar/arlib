import Arlib.Convexity.GaussianCooling.WarmSpeedy

/-! Warmness of a raw cooling draw scaled into the interior. -/

namespace Arlib.GaussianCooling

open MeasureTheory Metric Set
open Arlib.MarkovChains
open scoped ENNReal Pointwise

variable {n m : Nat}

/-- Scaling a Gaussian restricted to `K` into `c K` changes variance to `c²s` and
introduces the inverse Jacobian `c⁻ⁿ`. -/
theorem map_smul_gaussian_restrict {K : Set (EuclSpace n)} (hK : MeasurableSet K)
    {c : Real} (hc : 0 < c) (s : Real) :
    Measure.map (fun x : EuclSpace n ↦ c • x)
        ((volume.restrict K).withDensity (gaussianWeight s)) =
      ENNReal.ofReal ((c⁻¹) ^ n) •
        (volume.restrict (c • K)).withDensity (gaussianWeight (c ^ 2 * s)) := by
  have hi : 0 < c⁻¹ := inv_pos.mpr hc
  have h := map_inv_smul_gaussian_restrict
    (K := c • K) (measurableSet_smul_set hK hc.ne') hi s
  simpa [inv_inv, hc.ne', div_eq_mul_inv, mul_comm] using h

/-- Exact normalized law of a scaled cooling draw. -/
theorem map_smul_coolLaw_eq_condOn {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (EuclSpace n)} (hK : MeasurableSet K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m) {c : Real} (hc : 0 < c) :
    Measure.map (fun x : EuclSpace n ↦ c • x) (coolLaw m sigmaSq K i) =
      Arlib.condOn
        ((volume.restrict (c • K)).withDensity (gaussianWeight (c ^ 2 * sigmaSq i)))
        Set.univ := by
  rw [coolLaw_eq_condOn_gaussianRestrict hsigma hK hball hfin hi,
    Arlib.map_condOn_univ (measurable_const_smul c),
    map_smul_gaussian_restrict hK hc,
    Arlib.condOn_smul
      (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.mpr hc) n)).ne' ENNReal.ofReal_ne_top]

/-- A raw draw scaled by `c` is `c⁻ⁿ`-warm for its unscaled cooling law.  This is the
Jacobian cost; the colder scaled Gaussian density only helps. -/
theorem isWarm_map_smul_coolLaw_self {sigmaSq : Nat → Real}
    (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (EuclSpace n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i < m) {c : Real} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Arlib.IsWarm (ENNReal.ofReal ((c⁻¹) ^ n))
      (Measure.map (fun x : EuclSpace n ↦ c • x) (coolLaw m sigmaSq K i))
      (coolLaw m sigmaSq K i) := by
  have h0K : (0 : EuclSpace n) ∈ K := hball (mem_ball_self one_pos)
  have hcK : c • K ⊆ K := smul_subset_of_convex hKc h0K hc0.le hc1
  have hcKm : MeasurableSet (c • K) := measurableSet_smul_set hK hc0.ne'
  let cold : Measure (EuclSpace n) :=
    (volume.restrict (c • K)).withDensity (gaussianWeight (c ^ 2 * sigmaSq i))
  let warm : Measure (EuclSpace n) :=
    (volume.restrict K).withDensity (gaussianWeight (sigmaSq i))
  have hc2 : 0 < c ^ 2 * sigmaSq i := mul_pos (sq_pos_of_pos hc0) (hsigma i)
  have hcvar : c ^ 2 * sigmaSq i ≤ sigmaSq i := by
    have hc2le : c ^ 2 ≤ 1 := by nlinarith
    nlinarith [hsigma i]
  have hbase : cold ≤ warm := by
    dsimp only [cold, warm]
    rw [← restrict_withDensity hcKm, ← restrict_withDensity hK]
    rw [Measure.le_iff]
    intro S hS
    rw [Measure.restrict_apply hS, Measure.restrict_apply hS,
      withDensity_apply _ (hS.inter hcKm), withDensity_apply _ (hS.inter hK)]
    apply lintegral_mono'
      (Measure.restrict_mono (Set.inter_subset_inter_right S hcK) le_rfl)
    intro x
    exact gaussianWeight_mono_variance hc2 hcvar x
  intro S hS
  rw [map_smul_coolLaw_eq_condOn hsigma hK hball hfin hi hc0,
    coolLaw_eq_condOn_gaussianRestrict hsigma hK hball hfin hi,
    Arlib.condOn_def, Arlib.condOn_def, Measure.restrict_univ,
    Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  simp only [Measure.restrict_univ]
  change (cold Set.univ)⁻¹ * cold S ≤
    ENNReal.ofReal ((c⁻¹) ^ n) * ((warm Set.univ)⁻¹ * warm S)
  have hmass := congrArg (fun mu : Measure (EuclSpace n) ↦ mu Set.univ)
    (map_smul_gaussian_restrict hK hc0 (sigmaSq i))
  rw [Measure.map_apply (measurable_const_smul c) MeasurableSet.univ,
    Set.preimage_univ, Measure.smul_apply, smul_eq_mul] at hmass
  change warm Set.univ = ENNReal.ofReal ((c⁻¹) ^ n) * cold Set.univ at hmass
  have ha0 : ENNReal.ofReal ((c⁻¹) ^ n) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (pow_pos (inv_pos.mpr hc0) n)).ne'
  have hatop : ENNReal.ofReal ((c⁻¹) ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [hmass, ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop)]
  have hcancel : ENNReal.ofReal ((c⁻¹) ^ n) *
      (ENNReal.ofReal ((c⁻¹) ^ n))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel ha0 hatop
  calc
    (cold Set.univ)⁻¹ * cold S ≤ (cold Set.univ)⁻¹ * warm S :=
      mul_le_mul_left' (hbase S) _
    _ = ENNReal.ofReal ((c⁻¹) ^ n) *
        (((ENNReal.ofReal ((c⁻¹) ^ n))⁻¹ * (cold Set.univ)⁻¹) * warm S) := by
      symm
      calc
        ENNReal.ofReal ((c⁻¹) ^ n) *
            (((ENNReal.ofReal ((c⁻¹) ^ n))⁻¹ * (cold Set.univ)⁻¹) * warm S) =
            (ENNReal.ofReal ((c⁻¹) ^ n) *
              (ENNReal.ofReal ((c⁻¹) ^ n))⁻¹) *
              ((cold Set.univ)⁻¹ * warm S) := by ac_rfl
        _ = (cold Set.univ)⁻¹ * warm S := by rw [hcancel, one_mul]

/-- The proposed scaled raw seed is valid.  Its exact warm constant for the next speedy
target is `c⁻ⁿ e`: `c⁻ⁿ` is the scaling Jacobian and `e` is the consecutive cooling
step.  No additional conditioning draw is required. -/
theorem isWarm_map_smul_coolLaw_succ_ellGaussianProb
    {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (EuclSpace n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 ≤ cc)
    (hcc : cc ≤ 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {c delta : Real} (hc0 : 0 < c) (hc1 : c < 1)
    (hdelta : 0 < delta) (hdeltac : delta ≤ 1 - c) :
    Arlib.IsWarm
      (ENNReal.ofReal ((c⁻¹) ^ n) * ENNReal.ofReal (Real.exp 1))
      (Measure.map (fun x : EuclSpace n ↦ c • x) (coolLaw m sigmaSq K i))
      (ellGaussianProb K delta (sigmaSq (i + 1))) := by
  have him : i < m := Nat.lt_of_succ_lt hi
  have hself := isWarm_map_smul_coolLaw_self hsigma hK hKc hball hfin him hc0 hc1.le
  have hnext := isWarm_coolLaw_succ_exp hi hK hfin hKc hball hsigma
    hcc1 hcc hsched
  have hgauss := hself.trans hnext
  have hcKm : MeasurableSet (c • K) := measurableSet_smul_set hK hc0.ne'
  have hsupp : Measure.map (fun x : EuclSpace n ↦ c • x)
      (coolLaw m sigmaSq K i) ((c • K)ᶜ) = 0 := by
    rw [map_smul_coolLaw_eq_condOn hsigma hK hball hfin him hc0,
      Arlib.condOn_apply _ MeasurableSet.univ hcKm.compl, inter_univ]
    have hempty : (c • K)ᶜ ∩ c • K = (∅ : Set (EuclSpace n)) := compl_inter_self _
    rw [withDensity_apply _ hcKm.compl, Measure.restrict_restrict hcKm.compl,
      hempty, Measure.restrict_empty]
    simp
  rw [coolLaw_eq_uniformOn_gaussianWeight hsigma hK hball hfin hi] at hgauss
  exact isWarm_ellGaussianProb_of_supported_on_shrunken hK hKc hball
    hc0 hc1 hdelta hdeltac hsupp hgauss

/-- At the source shrink `c = 1 - 1/(2n)`, the Jacobian is at most `2`, hence the
scaled raw seed is dimension-free `2e`-warm for the next speedy target. -/
theorem isWarm_standardScaledRaw_coolLaw_succ_ellGaussianProb
    (hn : 1 ≤ n) {sigmaSq : Nat → Real} (hsigma : ∀ j, 0 < sigmaSq j)
    {K : Set (EuclSpace n)} (hK : MeasurableSet K) (hKc : Convex Real K)
    (hball : ball (0 : EuclSpace n) 1 ⊆ K) (hfin : volume K ≠ ⊤)
    {i : Nat} (hi : i + 1 < m) {cc : Real} (hcc1 : 1 ≤ cc)
    (hcc : cc ≤ 1 + 2 / (n : Real))
    (hsched : sigmaSq (i + 1) = cc * sigmaSq i)
    {delta : Real} (hdelta : 0 < delta) (hdeltan : delta ≤ 1 / (2 * (n : Real))) :
    Arlib.IsWarm (ENNReal.ofReal (2 * Real.exp 1))
      (Measure.map
        (fun x : EuclSpace n ↦ (1 - 1 / (2 * (n : Real))) • x)
        (coolLaw m sigmaSq K i))
      (ellGaussianProb K delta (sigmaSq (i + 1))) := by
  have hnreal : (0 : Real) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnone : (1 : Real) ≤ n := by exact_mod_cast hn
  let c : Real := 1 - 1 / (2 * (n : Real))
  have hc0 : 0 < c := by
    dsimp [c]
    have hhalf : 1 / (2 * (n : Real)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hc1 : c < 1 := by
    dsimp [c]
    have : 0 < 1 / (2 * (n : Real)) := by positivity
    linarith
  have hdc : delta ≤ 1 - c := by simpa [c] using hdeltan
  have hraw := isWarm_map_smul_coolLaw_succ_ellGaussianProb hsigma hK hKc hball hfin
    hi hcc1 hcc hsched hc0 hc1 hdelta hdc
  have hcpow : (1 / 2 : Real) ≤ c ^ n := by
    dsimp [c]
    exact half_le_one_sub_inv_two_mul_pow hn
  have hcinv : (c⁻¹) ^ n ≤ 2 := by
    rw [inv_pow]
    exact (inv_le_comm₀ (pow_pos hc0 n) (by norm_num : (0 : Real) < 2)).2 (by
      norm_num
      exact hcpow)
  apply hraw.mono
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (c⁻¹) ^ n)]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcinv (Real.exp_pos 1).le)

end Arlib.GaussianCooling

#print axioms Arlib.GaussianCooling.map_smul_gaussian_restrict
#print axioms Arlib.GaussianCooling.isWarm_map_smul_coolLaw_self
#print axioms Arlib.GaussianCooling.isWarm_map_smul_coolLaw_succ_ellGaussianProb
#print axioms Arlib.GaussianCooling.isWarm_standardScaledRaw_coolLaw_succ_ellGaussianProb
