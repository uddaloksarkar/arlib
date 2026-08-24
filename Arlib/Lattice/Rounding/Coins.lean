/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Lattice.Rounding.RoundLaw
import Mathlib.Probability.ProductMeasure
import Mathlib.NumberTheory.Real.Irrational

/-!
# Randomized rounding as a coin-consuming function, and its adequacy

`Arlib.Lattice.Rounding.roundLaw` is a *law*: it says what the distribution of
the rounded lattice point is, but it is not a function of any randomness, so
"the rounding step costs `n` coins" is not statable about it.  This file supplies
the missing object.

## The realisation

* `Arlib.Lattice.Rounding.roundCoin a u = ⌊a⌋ + (if u < Int.fract a then 1 else 0)`
  — one coordinate, one coin `u`;
* `Arlib.Lattice.Rounding.roundCoins p u i = roundCoin (p i) (u i)` — `n`
  coordinates, `n` coins, one per coordinate.

## The adequacy theorem

`Arlib.Lattice.Rounding.map_coinLaw_roundCoins`:

  `(coinLaw n).map (roundCoins p) = roundLaw p`,

where `coinLaw n` is `n` independent uniform draws on `(0,1]`.  Without this the
coin version would be a *different* algorithm and the coin count would attach to
nothing.  The stream form
`Arlib.Lattice.Rounding.map_streamLaw_roundStream` says the same for
`roundStream p : (ℕ → ℝ) → (Fin n → ℤ)`, the shape a cost model that reads a
coin *sequence* consumes.

## The coin count

`Arlib.Lattice.Rounding.roundStream_congr`: two coin sequences agreeing on the
first `n` entries give the same rounded point — the unfolded form of "reads at
most `n` coins".  `Arlib.Lattice.Rounding.exists_roundStream_ne_of_lt` is its
sharpness: for each `k < n` with `Int.fract (p k) > 0`, coin `k` is genuinely
read.  So the cost is `n`, derived rather than asserted.

## What a coin is

The coin here is a *uniform real*, and that is forced.
`Arlib.Lattice.Rounding.map_bitLaw_ne_tentInt`: no function of `N` **fair bits**
has the rounding law of a coordinate whose fractional part is irrational, since
every event of `N` fair bits has probability a multiple of `2⁻ᴺ`
(`Arlib.Lattice.Rounding.bitLaw_apply`); the witness
`Arlib.Lattice.Rounding.irrational_fract_sqrt_two` makes this non-vacuous.  The
converse `Arlib.Lattice.Rounding.map_bitLaw_bitRound` shows the obstruction is
exactly tight: a *dyadic* fractional part `k / 2ᴺ` — the case of an input given
in `N`-bit binary — is realised exactly by `N` bits per coordinate.  So the
`O(n)` coin flips of Kannan–Vempala's Theorem 1 are `n` draws from a uniform
source; a bounded number of bits per coordinate suffices only in the dyadic case.
-/

namespace Arlib.Lattice.Rounding

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-! ## The unit coin -/

/-- **One coin**: a uniform draw on `(0,1]`. -/
noncomputable def unitCoin : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

instance isProbabilityMeasure_unitCoin : IsProbabilityMeasure unitCoin := by
  constructor
  rw [unitCoin, Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num

/-- The coin's lower tail: `Pr[u < t] = t` for `t ∈ [0,1]`. -/
theorem unitCoin_Iio {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    unitCoin (Set.Iio t) = ENNReal.ofReal t := by
  have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Iio t = Set.Ioo 0 t := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, le_trans h2.le ht1⟩, h2⟩
  rw [unitCoin, Measure.restrict_apply measurableSet_Iio, Set.inter_comm, hset,
    Real.volume_Ioo, sub_zero]

/-- The coin's upper tail: `Pr[u ≥ t] = 1 − t` for `t ∈ [0,1]`. -/
theorem unitCoin_Ici {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    unitCoin (Set.Ici t) = ENNReal.ofReal (1 - t) := by
  have hc : Set.Ici t = (Set.Iio t)ᶜ := by ext u; simp
  rw [hc, prob_compl_eq_one_sub measurableSet_Iio, unitCoin_Iio ht0 ht1,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ ht0]

/-! ## The one-coordinate realisation -/

/-- **Randomized rounding of one coordinate, as a function of one coin**:
`⌊a⌋ + Bernoulli(a − ⌊a⌋)`, with the Bernoulli realised by comparing the coin to
the fractional part. -/
noncomputable def roundCoin (a u : ℝ) : ℤ := ⌊a⌋ + (if u < Int.fract a then 1 else 0)

theorem measurable_roundCoin (a : ℝ) : Measurable (roundCoin a) := by
  refine measurable_const.add ?_
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const

/-- The coin lands on `⌊a⌋` exactly when it is at least the fractional part. -/
theorem roundCoin_preimage_floor (a : ℝ) :
    roundCoin a ⁻¹' {⌊a⌋} = Set.Ici (Int.fract a) := by
  ext u
  simp only [Set.mem_preimage, Set.mem_singleton_iff, roundCoin, Set.mem_Ici]
  by_cases h : u < Int.fract a <;> simp [h, not_lt.mp]

/-- The coin lands on `⌊a⌋ + 1` exactly when it is below the fractional part. -/
theorem roundCoin_preimage_floor_succ (a : ℝ) :
    roundCoin a ⁻¹' {⌊a⌋ + 1} = Set.Iio (Int.fract a) := by
  ext u
  simp only [Set.mem_preimage, Set.mem_singleton_iff, roundCoin, Set.mem_Iio]
  by_cases h : u < Int.fract a <;> simp [h]

/-- Only `⌊a⌋` and `⌊a⌋ + 1` are hit. -/
theorem roundCoin_preimage_eq_empty (a : ℝ) {m : ℤ} (h1 : m ≠ ⌊a⌋) (h2 : m ≠ ⌊a⌋ + 1) :
    roundCoin a ⁻¹' {m} = ∅ := by
  ext u
  simp only [Set.mem_preimage, Set.mem_singleton_iff, roundCoin, Set.mem_empty_iff_false,
    iff_false]
  by_cases h : u < Int.fract a <;> simp [h] <;> omega

/-- **Adequacy in one coordinate**: the law of the coin realisation is the
declarative one-dimensional rounding law `Arlib.Lattice.Rounding.tentInt`. -/
theorem map_unitCoin_roundCoin (a : ℝ) : unitCoin.map (roundCoin a) = tentInt a := by
  have hf0 : 0 ≤ Int.fract a := Int.fract_nonneg a
  have hf1 : Int.fract a ≤ 1 := (Int.fract_lt_one a).le
  refine Measure.ext_of_singleton fun m => ?_
  rw [Measure.map_apply (measurable_roundCoin a) (measurableSet_singleton m),
    tentInt_singleton]
  by_cases h1 : m = ⌊a⌋
  · subst h1
    rw [roundCoin_preimage_floor, unitCoin_Ici hf0 hf1, tent_sub_floor, Int.self_sub_floor]
  · by_cases h2 : m = ⌊a⌋ + 1
    · subst h2
      rw [roundCoin_preimage_floor_succ, unitCoin_Iio hf0 hf1, tent_sub_floor_succ,
        Int.self_sub_floor]
    · rw [roundCoin_preimage_eq_empty a h1 h2, measure_empty,
        tent_eq_zero_of_ne_floor a m h1 h2, ENNReal.ofReal_zero]

/-! ## The `n`-coordinate realisation: `n` coins, one per coordinate -/

variable {n : ℕ}

/-- **`n` independent coins.** -/
noncomputable def coinLaw (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => unitCoin

instance isProbabilityMeasure_coinLaw (n : ℕ) : IsProbabilityMeasure (coinLaw n) := by
  rw [coinLaw]; infer_instance

/-- **Randomized rounding of `p ∈ ℝⁿ`, as a function of `n` coins**: coordinate
`i` is rounded using coin `i`, and no other coin. -/
noncomputable def roundCoins (p : Fin n → ℝ) (u : Fin n → ℝ) : Fin n → ℤ :=
  fun i => roundCoin (p i) (u i)

theorem measurable_roundCoins (p : Fin n → ℝ) : Measurable (roundCoins p) :=
  measurable_pi_iff.2 fun i => (measurable_roundCoin (p i)).comp (measurable_pi_apply i)

/-- **The adequacy theorem, `n` coordinates**: the `n`-coin realisation of the
rounding step pushes the coin law forward to exactly the declarative rounding law
`Arlib.Lattice.Rounding.roundLaw`.  This is what makes the coin count a cost *of
the rounding step* rather than of some other algorithm. -/
theorem measurePreserving_roundCoins (p : Fin n → ℝ) :
    MeasurePreserving (roundCoins p) (coinLaw n) (roundLaw p) :=
  measurePreserving_pi (fun _ => unitCoin) (fun i => tentInt (p i))
    (fun i => ⟨measurable_roundCoin (p i), map_unitCoin_roundCoin (p i)⟩)

/-- **The adequacy theorem**, in pushforward form. -/
theorem map_coinLaw_roundCoins (p : Fin n → ℝ) :
    (coinLaw n).map (roundCoins p) = roundLaw p :=
  (measurePreserving_roundCoins p).map_eq

/-! ## The stream form: reading `n` coins off a coin sequence

A cost model that counts coins reads them off a *sequence* `c : ℕ → ℝ`; the
rounding step reads the first `n` entries and nothing else.  Everything above
transfers along the projection `Arlib.Lattice.Rounding.measurePreserving_finProj`.
-/

/-- **The first `n` coordinates of an infinite product of probability measures
carry the finite product measure.**  Nothing here is about rounding. -/
theorem measurePreserving_finProj {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (fun c : ℕ → α => fun i : Fin n => c (i : ℕ))
      (Measure.infinitePi fun _ : ℕ => μ) (Measure.pi fun _ : Fin n => μ) := by
  classical
  have hmeas : Measurable (fun c : ℕ → α => fun i : Fin n => c (i : ℕ)) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply (i : ℕ)
  refine ⟨hmeas, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  set t : ℕ → Set α := fun j => if h : j < n then s ⟨j, h⟩ else Set.univ with ht
  have hpre : (fun c : ℕ → α => fun i : Fin n => c (i : ℕ)) ⁻¹' (Set.univ.pi s)
      = Set.pi (↑(Finset.range n)) t := by
    ext c
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Finset.coe_range,
      Set.mem_Iio, ht]
    constructor
    · intro h j hj; rw [dif_pos hj]; exact h ⟨j, hj⟩
    · intro h i
      have := h (i : ℕ) i.isLt
      rwa [dif_pos i.isLt, Fin.eta] at this
  have hmt : ∀ j ∈ Finset.range n, MeasurableSet (t j) := by
    intro j _
    by_cases hj : j < n
    · rw [ht]; simpa [dif_pos hj] using hs ⟨j, hj⟩
    · simp [ht, dif_neg hj]
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre,
    Measure.infinitePi_pi (fun _ : ℕ => μ) hmt, ← Fin.prod_univ_eq_prod_range (fun j => μ (t j)) n]
  exact Finset.prod_congr rfl fun i _ => by rw [ht]; simp

/-- **`n` independent coins, read off an infinite coin sequence.** -/
noncomputable def streamLaw : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => unitCoin

instance isProbabilityMeasure_streamLaw : IsProbabilityMeasure streamLaw := by
  rw [streamLaw]; infer_instance

/-- **The rounding step as a function of a coin sequence**: coordinate `i` reads
coin `i`. -/
noncomputable def roundStream (p : Fin n → ℝ) (c : ℕ → ℝ) : Fin n → ℤ :=
  fun i => roundCoin (p i) (c (i : ℕ))

theorem roundStream_eq (p : Fin n → ℝ) (c : ℕ → ℝ) :
    roundStream p c = roundCoins p (fun i : Fin n => c (i : ℕ)) := rfl

theorem measurable_roundStream (p : Fin n → ℝ) : Measurable (roundStream p) :=
  (measurable_roundCoins p).comp (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

/-- **The adequacy theorem, stream form**: the law of the rounded point produced
from a sequence of independent coins is `Arlib.Lattice.Rounding.roundLaw`. -/
theorem measurePreserving_roundStream (p : Fin n → ℝ) :
    MeasurePreserving (roundStream p) streamLaw (roundLaw p) :=
  (measurePreserving_roundCoins p).comp (measurePreserving_finProj unitCoin n)

/-- **The adequacy theorem, stream form**, in pushforward form. -/
theorem map_streamLaw_roundStream (p : Fin n → ℝ) :
    streamLaw.map (roundStream p) = roundLaw p :=
  (measurePreserving_roundStream p).map_eq

/-! ## The coin count

`Arlib.Lattice.Rounding.roundStream_congr` is the unfolded statement
"`roundStream p` reads at most the first `n` coins", and
`Arlib.Lattice.Rounding.exists_roundStream_ne_of_lt` is its sharpness: for every
`k < n` the output genuinely depends on coin `k`.  Together they pin the coin
cost of the rounding step at exactly `n`.
-/

/-- **`roundStream p` reads at most `n` coins**: two coin sequences agreeing on
the first `n` entries produce the same rounded point. -/
theorem roundStream_congr (p : Fin n → ℝ) {c c' : ℕ → ℝ} (h : ∀ j < n, c j = c' j) :
    roundStream p c = roundStream p c' := by
  funext i
  rw [roundStream, roundStream, h (i : ℕ) i.isLt]

/-- **Sharpness: coin `k` really is read**, for every `k < n` whose coordinate is
not already an integer.  Two sequences agreeing on the first `k` entries (and
differing only at entry `k`) give different rounded points, so no budget smaller
than `n` suffices. -/
theorem exists_roundStream_ne_of_lt (p : Fin n → ℝ) {k : ℕ} (hk : k < n)
    (hp : 0 < Int.fract (p ⟨k, hk⟩)) :
    ∃ c c' : ℕ → ℝ, (∀ j < k, c j = c' j) ∧ roundStream p c ≠ roundStream p c' := by
  refine ⟨fun _ => 0, fun j => if j = k then 1 else 0, fun j hj => by simp [Nat.ne_of_lt hj], ?_⟩
  intro hcontra
  have h := congrFun hcontra ⟨k, hk⟩
  simp only [roundStream, roundCoin, if_true] at h
  rw [if_pos hp, if_neg (not_lt.2 (Int.fract_lt_one (p ⟨k, hk⟩)).le)] at h
  omega

/-! ## Why the coin has to be a real draw, not a bounded number of bits

`Arlib.Lattice.Rounding.unitCoin` is a *uniform real*, i.e. an unbounded amount of
entropy.  That is not a modelling convenience: `Bernoulli(t)` for an arbitrary
real `t` cannot be produced by any function of finitely many **fair bits**,
because every event of `N` fair bits has probability a multiple of `2⁻ᴺ`.  The
statements below make that precise, so the "one coin per coordinate" count is
honest about what a coin is.

(`Arlib.Probability.coin` is the library's other fair coin — the two-atom measure
`½·δ₀ + ½·δ₁` on `ℝ`, used as a non-degeneracy witness for run plumbing.  It is
not reused here only because the obstruction argument needs to count *atoms of a
finite space*, which `Fin N → Bool` provides directly and `ℝ` does not.)
-/

/-- **One fair bit.** -/
noncomputable def fairBit : Measure Bool := (2 : ℝ≥0∞)⁻¹ • Measure.count

theorem count_univ_bool : (Measure.count : Measure Bool) Set.univ = 2 := by
  rw [Measure.count_apply_finite _ Set.finite_univ]
  simp

instance isProbabilityMeasure_fairBit : IsProbabilityMeasure fairBit := by
  constructor
  rw [fairBit, Measure.smul_apply, smul_eq_mul, count_univ_bool]
  rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]

@[simp] theorem fairBit_singleton (b : Bool) : fairBit {b} = 2⁻¹ := by
  rw [fairBit, Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one]

/-- **`N` independent fair bits** — a finite-precision randomness source. -/
noncomputable def bitLaw (N : ℕ) : Measure (Fin N → Bool) := Measure.pi fun _ => fairBit

instance isProbabilityMeasure_bitLaw (N : ℕ) : IsProbabilityMeasure (bitLaw N) := by
  rw [bitLaw]; infer_instance

/-- `N` fair bits form the uniform measure on the `2ᴺ` bit strings. -/
theorem bitLaw_eq_smul_count (N : ℕ) :
    bitLaw N = ((2 : ℝ≥0∞) ^ N)⁻¹ • Measure.count := by
  refine Measure.ext_of_singleton fun x => ?_
  have hbox : ({x} : Set (Fin N → Bool)) = Set.univ.pi (fun i => ({x i} : Set Bool)) := by
    ext w
    constructor
    · rintro rfl; intro i _; rfl
    · intro hw; funext i; exact hw i (Set.mem_univ i)
  rw [Measure.smul_apply, smul_eq_mul, Measure.count_singleton, mul_one, bitLaw, hbox,
    Measure.pi_pi]
  simp [Finset.prod_const, ENNReal.inv_pow]

/-- **Every event of `N` fair bits has probability a multiple of `2⁻ᴺ`** — the
whole obstruction in one line. -/
theorem bitLaw_apply (N : ℕ) (s : Set (Fin N → Bool)) :
    bitLaw N s = (s.toFinite.toFinset.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ N)⁻¹ := by
  rw [bitLaw_eq_smul_count, Measure.smul_apply, smul_eq_mul,
    Measure.count_apply_finite _ s.toFinite, mul_comm]

/-- **The dyadic obstruction**: if some function of `N` fair bits has the
one-dimensional rounding law of `a`, then the fractional part of `a` is a dyadic
rational with denominator `2ᴺ`. -/
theorem exists_fract_eq_of_map_bitLaw (a : ℝ) (N : ℕ) (f : (Fin N → Bool) → ℤ)
    (h : (bitLaw N).map f = tentInt a) :
    ∃ k : ℕ, Int.fract a = (k : ℝ) / 2 ^ N := by
  have hmf : Measurable f := Measurable.of_discrete
  have hpt : (bitLaw N).map f {⌊a⌋ + 1} = tentInt a {⌊a⌋ + 1} := by rw [h]
  rw [Measure.map_apply hmf (measurableSet_singleton _), tentInt_singleton,
    tent_sub_floor_succ, Int.self_sub_floor, bitLaw_apply] at hpt
  refine ⟨(f ⁻¹' {⌊a⌋ + 1}).toFinite.toFinset.card, ?_⟩
  have := congrArg ENNReal.toReal hpt
  rwa [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (Int.fract_nonneg a), eq_comm,
    ← div_eq_mul_inv] at this

/-- **No finite fair-bit source realises the rounding of an irrational-fraction
coordinate.**  Hence "one coin per coordinate" must mean one *uniform real* draw
(equivalently, an unbounded fair-bit stream), not a bounded number of bits. -/
theorem map_bitLaw_ne_tentInt (a : ℝ) (ha : Irrational (Int.fract a)) (N : ℕ)
    (f : (Fin N → Bool) → ℤ) : (bitLaw N).map f ≠ tentInt a := by
  intro h
  obtain ⟨k, hk⟩ := exists_fract_eq_of_map_bitLaw a N f h
  refine (Rat.not_irrational ((k : ℚ) / 2 ^ N)) ?_
  have hcast : (((k : ℚ) / 2 ^ N : ℚ) : ℝ) = (k : ℝ) / 2 ^ N := by push_cast; ring
  rw [hcast, ← hk]
  exact ha

/-- The same obstruction for the `n`-dimensional law, via one marginal. -/
theorem map_bitLaw_ne_roundLaw (p : Fin n → ℝ) (i : Fin n) (ha : Irrational (Int.fract (p i)))
    (N : ℕ) (F : (Fin N → Bool) → (Fin n → ℤ)) : (bitLaw N).map F ≠ roundLaw p := by
  intro h
  refine map_bitLaw_ne_tentInt (p i) ha N (fun x => F x i) ?_
  rw [show (fun x => F x i) = Function.eval i ∘ F from rfl,
    ← Measure.map_map (measurable_pi_apply i) Measurable.of_discrete, h]
  exact (measurePreserving_roundLaw_eval p i).map_eq

/-! ### The converse: dyadic fractional parts *are* realisable from `N` bits

The obstruction is exactly tight.  If `Int.fract a = k / 2ᴺ` — the case of an
input given in `N`-bit binary, which is what an implementation actually has —
then reading the `N` bits as a number and comparing with `k` realises the law
exactly.  So "bits suffice ⟺ the fractional part is dyadic", and the uniform-real
coin of the first half of this file is the general-`a` substitute for that. -/

/-- Reading `N` bits as a number in `Fin (2ᴺ)`. -/
def bitEquiv (N : ℕ) : (Fin N → Bool) ≃ Fin (2 ^ N) :=
  (Equiv.arrowCongr (Equiv.refl (Fin N)) finTwoEquiv.symm).trans finFunctionFinEquiv

/-- **The `N`-bit realisation**: round up iff the number read off the bits is
below `2ᴺ · Int.fract a`.  It is adequate exactly in the dyadic case — see
`Arlib.Lattice.Rounding.map_bitLaw_bitRound`, whose hypothesis
`Int.fract a = k / 2ᴺ` cannot be dropped by
`Arlib.Lattice.Rounding.map_bitLaw_ne_tentInt`. -/
noncomputable def bitRound (a : ℝ) (N : ℕ) (x : Fin N → Bool) : ℤ :=
  ⌊a⌋ + (if ((bitEquiv N x : ℕ) : ℝ) < Int.fract a * 2 ^ N then 1 else 0)

theorem card_filter_val_lt (M k : ℕ) (hk : k ≤ M) :
    (Finset.univ.filter (fun y : Fin M => (y : ℕ) < k)).card = k := by
  have hset : (Finset.univ.filter (fun y : Fin M => (y : ℕ) < k))
      = (Finset.range k).attachFin (fun m hm => lt_of_lt_of_le (Finset.mem_range.1 hm) hk) := by
    ext y
    simp [Finset.mem_attachFin]
  rw [hset, Finset.card_attachFin, Finset.card_range]

/-- The bit string read as a number is uniform, so exactly `k` of the `2ᴺ` strings
are below `k`. -/
theorem card_filter_bitVal_lt (N k : ℕ) (hk : k ≤ 2 ^ N) :
    (Finset.univ.filter (fun x : Fin N → Bool => ((bitEquiv N x : ℕ)) < k)).card = k := by
  have hbij : (Finset.univ.filter (fun x : Fin N → Bool => ((bitEquiv N x : ℕ)) < k)).card
      = (Finset.univ.filter (fun y : Fin (2 ^ N) => (y : ℕ) < k)).card :=
    Finset.card_bij' (fun x _ => bitEquiv N x) (fun y _ => (bitEquiv N).symm y)
      (fun x hx => by simpa using (Finset.mem_filter.1 hx).2)
      (fun y hy => by simpa using (Finset.mem_filter.1 hy).2)
      (fun x _ => by simp) (fun y _ => by simp)
  rw [hbij, card_filter_val_lt (2 ^ N) k hk]

/-- The mass of an explicitly described set of bit strings. -/
theorem bitLaw_setOf (N : ℕ) (q : (Fin N → Bool) → Prop) [DecidablePred q] :
    bitLaw N {x | q x} = ((Finset.univ.filter q).card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ N)⁻¹ := by
  rw [bitLaw_apply]
  have hfin : {x | q x}.toFinite.toFinset = Finset.univ.filter q := by ext x; simp
  rw [hfin]

/-- Turning a count of bit strings into a mass. -/
theorem natCast_mul_inv_two_pow (m N : ℕ) :
    ((m : ℝ≥0∞)) * ((2 : ℝ≥0∞) ^ N)⁻¹ = ENNReal.ofReal ((m : ℝ) / 2 ^ N) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, div_eq_mul_inv]

/-- **The `N`-bit realisation is adequate for a dyadic fractional part.** -/
theorem map_bitLaw_bitRound (a : ℝ) (N k : ℕ) (hk : Int.fract a = (k : ℝ) / 2 ^ N) :
    (bitLaw N).map (bitRound a N) = tentInt a := by
  classical
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have hkle : k ≤ 2 ^ N := by
    have h1 : (k : ℝ) / 2 ^ N < 1 := hk ▸ Int.fract_lt_one a
    have : (k : ℝ) < 2 ^ N := by
      rw [div_lt_one hpos] at h1; exact h1
    exact_mod_cast this.le
  have hmul : Int.fract a * 2 ^ N = (k : ℝ) := by
    rw [hk, div_mul_cancel₀ _ (ne_of_gt hpos)]
  have hcond : ∀ x : Fin N → Bool,
      (((bitEquiv N x : ℕ) : ℝ) < Int.fract a * 2 ^ N) ↔ ((bitEquiv N x : ℕ) < k) := by
    intro x; rw [hmul]; exact_mod_cast Iff.rfl
  have hup : bitRound a N ⁻¹' {⌊a⌋ + 1} = {x | ((bitEquiv N x : ℕ)) < k} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, bitRound, Set.mem_setOf_eq]
    rw [← hcond x]
    by_cases h : ((bitEquiv N x : ℕ) : ℝ) < Int.fract a * 2 ^ N <;> simp [h]
  have hdown : bitRound a N ⁻¹' {⌊a⌋} = {x | ¬ ((bitEquiv N x : ℕ)) < k} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, bitRound, Set.mem_setOf_eq]
    rw [← hcond x]
    by_cases h : ((bitEquiv N x : ℕ) : ℝ) < Int.fract a * 2 ^ N <;> simp [h]
  have hcompl : (Finset.univ.filter (fun x : Fin N → Bool => ¬ ((bitEquiv N x : ℕ)) < k)).card
      = 2 ^ N - k := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin N → Bool)))
      (p := fun x => ((bitEquiv N x : ℕ)) < k)
    have hcard : (Finset.univ : Finset (Fin N → Bool)).card = 2 ^ N := by simp
    rw [card_filter_bitVal_lt N k hkle, hcard] at hsum
    omega
  refine Measure.ext_of_singleton fun m => ?_
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton m), tentInt_singleton]
  by_cases h1 : m = ⌊a⌋
  · subst h1
    rw [hdown, bitLaw_setOf, hcompl, natCast_mul_inv_two_pow, tent_sub_floor, Int.self_sub_floor,
      hk]
    congr 1
    rw [Nat.cast_sub hkle]
    push_cast
    field_simp
  · by_cases h2 : m = ⌊a⌋ + 1
    · subst h2
      rw [hup, bitLaw_setOf, card_filter_bitVal_lt N k hkle, natCast_mul_inv_two_pow,
        tent_sub_floor_succ, Int.self_sub_floor, hk]
    · have : bitRound a N ⁻¹' {m} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, bitRound, Set.mem_empty_iff_false,
          iff_false]
        by_cases h : ((bitEquiv N x : ℕ) : ℝ) < Int.fract a * 2 ^ N <;> simp [h] <;> omega
      rw [this, measure_empty, tent_eq_zero_of_ne_floor a m h1 h2, ENNReal.ofReal_zero]

/-- The obstruction is not vacuous: `⌊√2⌋ = 1`, so `Int.fract √2 = √2 − 1` is
irrational. -/
theorem irrational_fract_sqrt_two : Irrational (Int.fract (Real.sqrt 2)) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hfloor : ⌊Real.sqrt 2⌋ = 1 := by
    refine Int.floor_eq_iff.2 ⟨by push_cast; nlinarith, by push_cast; nlinarith⟩
  rw [← Int.self_sub_floor, hfloor]
  exact_mod_cast irrational_sqrt_two.sub_intCast 1

end Arlib.Lattice.Rounding
