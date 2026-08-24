/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Arlib.Convexity.GaussianCooling.ChunkedVarBudget

/-!
# Flattening the chunked Gaussian-cooling schedule

`ChunkedVarBudget.lean` constructs genuine recursively concatenated chunks.  This file
flattens their dependent `(chunk, local phase)` indexing into the `ℕ → ℝ` variance schedule
used by the Gaussian-cooling estimator.
-/

namespace Arlib.GaussianCooling.Chunked

open scoped BigOperators

/-- Prefix sum of the numbers of phases in chunks strictly before `j`. -/
noncomputable def adaptiveChunkOffset (N s₀ : ℝ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => adaptiveChunkOffset N s₀ j + adaptiveChunkPhases N s₀ j

@[simp] theorem adaptiveChunkOffset_zero (N s₀ : ℝ) : adaptiveChunkOffset N s₀ 0 = 0 := rfl

theorem adaptiveChunkOffset_succ (N s₀ : ℝ) (j : ℕ) :
    adaptiveChunkOffset N s₀ (j + 1) =
      adaptiveChunkOffset N s₀ j + adaptiveChunkPhases N s₀ j := rfl

/-- Prefix offsets agree with the total phase count defined in `ChunkedVarBudget`. -/
theorem adaptiveChunkOffset_eq_totalPhases (N s₀ : ℝ) : ∀ J : ℕ,
    adaptiveChunkOffset N s₀ J = adaptiveTotalPhases N s₀ J := by
  intro J
  induction J with
  | zero => simp [adaptiveTotalPhases]
  | succ J ih =>
      rw [adaptiveChunkOffset_succ, adaptiveTotalPhases, Finset.sum_range_succ]
      simpa [adaptiveTotalPhases] using congrArg
        (fun q => q + adaptiveChunkPhases N s₀ J) ih

/-- Offsets strictly increase because every actual chunk has a positive phase count. -/
theorem adaptiveChunkOffset_lt_succ {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    adaptiveChunkOffset N s₀ j < adaptiveChunkOffset N s₀ (j + 1) := by
  rw [adaptiveChunkOffset_succ]
  exact Nat.lt_add_of_pos_right (adaptiveChunkPhases_pos hN hs j)

theorem strictMono_adaptiveChunkOffset {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) :
    StrictMono (adaptiveChunkOffset N s₀) := by
  exact strictMono_nat_of_lt_succ (adaptiveChunkOffset_lt_succ hN hs)

/-- The offset of chunk `j` is at least `j`, hence offsets are unbounded. -/
theorem le_adaptiveChunkOffset {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) :
    ∀ j : ℕ, j ≤ adaptiveChunkOffset N s₀ j := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
      rw [adaptiveChunkOffset_succ]
      have hp := adaptiveChunkPhases_pos hN hs j
      omega

/-- Every global phase lies before the end offset of some chunk. -/
theorem exists_lt_adaptiveChunkOffset_succ {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀)
    (i : ℕ) : ∃ j : ℕ, i < adaptiveChunkOffset N s₀ (j + 1) := by
  refine ⟨i, ?_⟩
  have := le_adaptiveChunkOffset hN hs (i + 1)
  omega

/-- The unique chunk containing global phase `i`, chosen as the first chunk whose end
offset is strictly larger than `i`. -/
noncomputable def adaptivePhaseChunk (N s₀ : ℝ) (i : ℕ) : ℕ := by
  classical
  exact if h : ∃ j : ℕ, i < adaptiveChunkOffset N s₀ (j + 1) then Nat.find h else 0

/-- A global phase is before the end of its located chunk. -/
theorem adaptivePhaseChunk_upper {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (i : ℕ) :
    i < adaptiveChunkOffset N s₀ (adaptivePhaseChunk N s₀ i + 1) := by
  have hex := exists_lt_adaptiveChunkOffset_succ hN hs i
  rw [adaptivePhaseChunk, dif_pos hex]
  exact Nat.find_spec hex

/-- A global phase is at or after the start of its located chunk. -/
theorem adaptivePhaseChunk_lower {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (i : ℕ) :
    adaptiveChunkOffset N s₀ (adaptivePhaseChunk N s₀ i) ≤ i := by
  have hex := exists_lt_adaptiveChunkOffset_succ hN hs i
  rw [adaptivePhaseChunk, dif_pos hex]
  by_cases hj : Nat.find hex = 0
  · simp [hj]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj
    rw [hk]
    have hnot := Nat.find_min hex (show k < Nat.find hex by omega)
    simp only [not_lt] at hnot
    exact hnot

/-- Local phase index inside the chunk containing global phase `i`. -/
noncomputable def adaptiveLocalPhase (N s₀ : ℝ) (i : ℕ) : ℕ :=
  i - adaptiveChunkOffset N s₀ (adaptivePhaseChunk N s₀ i)

/-- The local phase index is in range. -/
theorem adaptiveLocalPhase_lt {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (i : ℕ) :
    adaptiveLocalPhase N s₀ i < adaptiveChunkPhases N s₀ (adaptivePhaseChunk N s₀ i) := by
  have hu := adaptivePhaseChunk_upper hN hs i
  have hl := adaptivePhaseChunk_lower hN hs i
  rw [adaptiveChunkOffset_succ] at hu
  unfold adaptiveLocalPhase
  omega

/-- Recombining the chunk offset and local index recovers the global phase. -/
theorem adaptiveChunkOffset_add_local {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (i : ℕ) :
    adaptiveChunkOffset N s₀ (adaptivePhaseChunk N s₀ i) + adaptiveLocalPhase N s₀ i = i := by
  unfold adaptiveLocalPhase
  have hl := adaptivePhaseChunk_lower hN hs i
  omega

/-- The flattened variance schedule. -/
noncomputable def adaptiveSigmaSq (N s₀ : ℝ) (i : ℕ) : ℝ :=
  geomSchedule (adaptiveChunkStart N s₀ (adaptivePhaseChunk N s₀ i))
    (adaptiveChunkRate N s₀ (adaptivePhaseChunk N s₀ i))
    (adaptiveLocalPhase N s₀ i)

/-- The flattened schedule is positive. -/
theorem adaptiveSigmaSq_pos {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (i : ℕ) :
    0 < adaptiveSigmaSq N s₀ i := by
  unfold adaptiveSigmaSq
  exact geomSchedule_pos (adaptiveChunkStart_pos hN hs _)
    (by linarith [adaptiveChunkRate_pos hN hs (adaptivePhaseChunk N s₀ i)]) _

/-- The flattened phase at a chunk's starting offset is exactly that chunk's start. -/
theorem adaptivePhaseChunk_offset {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    adaptivePhaseChunk N s₀ (adaptiveChunkOffset N s₀ j) = j := by
  apply le_antisymm
  · have hex := exists_lt_adaptiveChunkOffset_succ hN hs (adaptiveChunkOffset N s₀ j)
    rw [adaptivePhaseChunk, dif_pos hex]
    exact Nat.find_min' hex (adaptiveChunkOffset_lt_succ hN hs j)
  · by_contra hlt
    have hu := adaptivePhaseChunk_upper hN hs (adaptiveChunkOffset N s₀ j)
    have hmono := (strictMono_adaptiveChunkOffset hN hs).monotone
      (show adaptivePhaseChunk N s₀ (adaptiveChunkOffset N s₀ j) + 1 ≤ j by omega)
    omega

theorem adaptiveLocalPhase_offset {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    adaptiveLocalPhase N s₀ (adaptiveChunkOffset N s₀ j) = 0 := by
  simp [adaptiveLocalPhase, adaptivePhaseChunk_offset hN hs j]

theorem adaptiveSigmaSq_offset {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    adaptiveSigmaSq N s₀ (adaptiveChunkOffset N s₀ j) = adaptiveChunkStart N s₀ j := by
  simp [adaptiveSigmaSq, adaptivePhaseChunk_offset hN hs j,
    adaptiveLocalPhase_offset hN hs j]

/-- A phase written as `chunk offset + local index` is located in that chunk. -/
theorem adaptivePhaseChunk_offset_add {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀)
    {j t : ℕ} (ht : t < adaptiveChunkPhases N s₀ j) :
    adaptivePhaseChunk N s₀ (adaptiveChunkOffset N s₀ j + t) = j := by
  apply le_antisymm
  · have hex := exists_lt_adaptiveChunkOffset_succ hN hs
      (adaptiveChunkOffset N s₀ j + t)
    rw [adaptivePhaseChunk, dif_pos hex]
    apply Nat.find_min' hex
    rw [adaptiveChunkOffset_succ]
    omega
  · by_contra hlt
    have hu := adaptivePhaseChunk_upper hN hs (adaptiveChunkOffset N s₀ j + t)
    have hmono := (strictMono_adaptiveChunkOffset hN hs).monotone
      (show adaptivePhaseChunk N s₀ (adaptiveChunkOffset N s₀ j + t) + 1 ≤ j by omega)
    omega

theorem adaptiveLocalPhase_offset_add {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀)
    {j t : ℕ} (ht : t < adaptiveChunkPhases N s₀ j) :
    adaptiveLocalPhase N s₀ (adaptiveChunkOffset N s₀ j + t) = t := by
  rw [adaptiveLocalPhase, adaptivePhaseChunk_offset_add hN hs ht]
  omega

/-- Explicit intra-chunk flattening formula. -/
theorem adaptiveSigmaSq_offset_add {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀)
    {j t : ℕ} (ht : t < adaptiveChunkPhases N s₀ j) :
    adaptiveSigmaSq N s₀ (adaptiveChunkOffset N s₀ j + t) =
      geomSchedule (adaptiveChunkStart N s₀ j) (adaptiveChunkRate N s₀ j) t := by
  simp [adaptiveSigmaSq, adaptivePhaseChunk_offset_add hN hs ht,
    adaptiveLocalPhase_offset_add hN hs ht]

/-! ## Successor equations -/

/-- Away from a chunk boundary, the successor phase stays in the same chunk. -/
theorem adaptivePhaseChunk_succ_of_lt_end {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀)
    {i : ℕ} (hi : i + 1 < adaptiveChunkOffset N s₀ (adaptivePhaseChunk N s₀ i + 1)) :
    adaptivePhaseChunk N s₀ (i + 1) = adaptivePhaseChunk N s₀ i := by
  apply le_antisymm
  · have hex := exists_lt_adaptiveChunkOffset_succ hN hs (i + 1)
    rw [adaptivePhaseChunk, dif_pos hex]
    exact Nat.find_min' hex hi
  · have hlower := adaptivePhaseChunk_lower hN hs i
    by_contra hlt
    have hle : adaptivePhaseChunk N s₀ (i + 1) < adaptivePhaseChunk N s₀ i := by omega
    have hu' := adaptivePhaseChunk_upper hN hs (i + 1)
    have hmono := (strictMono_adaptiveChunkOffset hN hs).monotone
      (show adaptivePhaseChunk N s₀ (i + 1) + 1 ≤ adaptivePhaseChunk N s₀ i by omega)
    omega

/-- Away from a boundary, the local phase increments by one. -/
theorem adaptiveLocalPhase_succ_of_lt_end {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀)
    {i : ℕ} (hi : i + 1 < adaptiveChunkOffset N s₀ (adaptivePhaseChunk N s₀ i + 1)) :
    adaptiveLocalPhase N s₀ (i + 1) = adaptiveLocalPhase N s₀ i + 1 := by
  rw [adaptiveLocalPhase, adaptiveLocalPhase,
    adaptivePhaseChunk_succ_of_lt_end hN hs hi]
  have hlower := adaptivePhaseChunk_lower hN hs i
  omega

/-- At the end of a chunk, the successor phase is the next chunk's starting offset. -/
theorem adaptivePhaseChunk_succ_of_eq_end {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀)
    {i : ℕ} (hi : i + 1 = adaptiveChunkOffset N s₀ (adaptivePhaseChunk N s₀ i + 1)) :
    adaptivePhaseChunk N s₀ (i + 1) = adaptivePhaseChunk N s₀ i + 1 := by
  rw [hi]
  exact adaptivePhaseChunk_offset hN hs _

/-- The global successor equation, including the boundary between chunks. -/
theorem adaptiveSigmaSq_succ {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (i : ℕ) :
    adaptiveSigmaSq N s₀ (i + 1) = adaptiveSigmaSq N s₀ i *
      (1 + adaptiveChunkRate N s₀ (adaptivePhaseChunk N s₀ i)) := by
  have hu := adaptivePhaseChunk_upper hN hs i
  by_cases hi : i + 1 <
      adaptiveChunkOffset N s₀ (adaptivePhaseChunk N s₀ i + 1)
  · unfold adaptiveSigmaSq
    rw [adaptivePhaseChunk_succ_of_lt_end hN hs hi,
      adaptiveLocalPhase_succ_of_lt_end hN hs hi]
    simp only [geomSchedule, pow_succ]
    ring
  · have hieq : i + 1 =
        adaptiveChunkOffset N s₀ (adaptivePhaseChunk N s₀ i + 1) := by omega
    rw [hieq, adaptiveSigmaSq_offset hN hs]
    rw [adaptiveChunkStart_succ]
    unfold adaptiveSigmaSq
    have hlocal : adaptiveLocalPhase N s₀ i + 1 =
        adaptiveChunkPhases N s₀ (adaptivePhaseChunk N s₀ i) := by
      rw [adaptiveChunkOffset_succ] at hieq
      have hoff := adaptiveChunkOffset_add_local hN hs i
      omega
    rw [← hlocal]
    simp only [geomSchedule, pow_succ]
    ring

/-- Chunk `j` starts at its global offset in the flattened schedule. -/
theorem adaptiveSigmaSq_cools_at_offsets {N s₀ : ℝ} (hN : 0 < N) (hs : 0 < s₀) (j : ℕ) :
    adaptiveSigmaSq N s₀ (adaptiveChunkOffset N s₀ j) = adaptiveChunkStart N s₀ j :=
  adaptiveSigmaSq_offset hN hs j

/-! ## Axiom audit -/

#print axioms Arlib.GaussianCooling.Chunked.adaptivePhaseChunk_lower
#print axioms Arlib.GaussianCooling.Chunked.adaptivePhaseChunk_offset
#print axioms Arlib.GaussianCooling.Chunked.adaptiveSigmaSq_offset_add
#print axioms Arlib.GaussianCooling.Chunked.adaptiveSigmaSq_pos
#print axioms Arlib.GaussianCooling.Chunked.adaptiveSigmaSq_succ
#print axioms Arlib.GaussianCooling.Chunked.adaptiveSigmaSq_cools_at_offsets

end Arlib.GaussianCooling.Chunked
