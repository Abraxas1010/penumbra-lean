import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.UDTSynthesis.ClockRateField
import HeytingLean.Bridge.AlMayahi.UDTSynthesis.MassGenerationGap
import HeytingLean.Bridge.AlMayahi.UDTSynthesis.GapDecompositionBridge
import HeytingLean.Eigen.SafEDMD

/-!
# Bridge.AlMayahi.UDTSynthesis.SparseProjectionField

Sparse projection field structure connecting the UDT clock-rate field χ
to the gap decomposition via finite-grid discretization.

The clock-rate field χ = dt/dτ has inherently sparse deviation structure:
in most of spacetime χ ≈ 1 (flat space), with deviations concentrated
at gravitational wells (χ < 1, time runs slower) and at specific
measurement configurations. When discretized on a spatial grid for
numerical simulation of the τ-potential φ(r) = 1/τ(r), the deviation
vector is sparse — most entries are near zero.

This module formalizes:
- Grid discretization of χ into a finite deviation vector
- Trapped energy: nucleus gap of the deviation vector (where χ < 1)
- Sparse projection fields: grids where most points have small deviation
- Connection to gap decomposition: trapped energy → Δ_gate component
-/

open scoped BigOperators

namespace HeytingLean.Bridge.AlMayahi.UDTSynthesis

open HeytingLean.Eigen

/-- Grid sample of a clock-rate field: evaluate χ at n discrete spatial points.
This is the fundamental discretization step connecting continuous χ to
finite-dimensional algebra. -/
structure GridSample (n : ℕ) where
  crf : ClockRateField
  gridPoints : Fin n → ℝ

/-- Deviation vector: χ(τᵢ) - 1 at each grid point. Measures departure
from flat-space (χ = 1) at each spatial location. -/
def deviationVector {n : ℕ} (gs : GridSample n) : Fin n → ℝ :=
  fun i => gs.crf.χ (gs.gridPoints i) - 1

/-- All deviations are > -1 because χ > 0 everywhere. -/
theorem deviationVector_gt_neg_one {n : ℕ} (gs : GridSample n) (i : Fin n) :
    -1 < deviationVector gs i := by
  simp only [deviationVector]
  linarith [gs.crf.χ_pos (gs.gridPoints i)]

/-- At any grid point mapping to origin, deviation is zero. -/
theorem deviationVector_at_origin {n : ℕ} (gs : GridSample n)
    (i : Fin n) (h : gs.gridPoints i = 0) :
    deviationVector gs i = 0 := by
  simp [deviationVector, h, gs.crf.χ_flat]

/-- For the flat field, all deviations are zero. -/
theorem flat_deviation_zero {n : ℕ} (pts : Fin n → ℝ) (i : Fin n) :
    deviationVector ⟨flatClockRateField, pts⟩ i = 0 := by
  simp [deviationVector, flatClockRateField]

/-- Negative deviation ↔ χ < 1: time runs slower (gravitational well). -/
theorem deviation_neg_iff_slow {n : ℕ} (gs : GridSample n) (i : Fin n) :
    deviationVector gs i < 0 ↔ gs.crf.χ (gs.gridPoints i) < 1 := by
  simp only [deviationVector, sub_neg]

/-- Positive deviation ↔ χ > 1. -/
theorem deviation_pos_iff_fast {n : ℕ} (gs : GridSample n) (i : Fin n) :
    0 < deviationVector gs i ↔ 1 < gs.crf.χ (gs.gridPoints i) := by
  simp only [deviationVector, sub_pos]

/-- Deviation energy: total squared deviation across the grid. -/
def deviationEnergy {n : ℕ} (gs : GridSample n) : ℝ :=
  sqSum (deviationVector gs)

/-- Deviation energy is nonneg. -/
theorem deviationEnergy_nonneg {n : ℕ} (gs : GridSample n) :
    0 ≤ deviationEnergy gs := by
  unfold deviationEnergy sqSum
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- Flat field has zero deviation energy. -/
theorem flat_deviationEnergy_zero {n : ℕ} (pts : Fin n → ℝ) :
    deviationEnergy ⟨flatClockRateField, pts⟩ = 0 := by
  unfold deviationEnergy sqSum
  simp [flat_deviation_zero]

/-- Trapped energy: nucleus gap of the deviation vector.
Measures total squared energy at grid points where χ < 1. -/
def deviationTrappedEnergy {n : ℕ} (gs : GridSample n) : ℝ :=
  nucleusGap n (deviationVector gs)

/-- Trapped energy is bounded by total deviation energy. -/
theorem deviationTrappedEnergy_le {n : ℕ} (gs : GridSample n) :
    deviationTrappedEnergy gs ≤ deviationEnergy gs :=
  nucleusGap_le_sqSum n (deviationVector gs)

/-- Trapped energy is nonneg. -/
theorem deviationTrappedEnergy_nonneg {n : ℕ} (gs : GridSample n) :
    0 ≤ deviationTrappedEnergy gs :=
  nucleusGap_nonneg n (deviationVector gs)

/-- If all grid points have χ ≥ 1 (no gravitational wells),
trapped energy is zero (all components in free regime). -/
theorem deviationTrappedEnergy_zero_of_χ_ge_one {n : ℕ} (gs : GridSample n)
    (h : ∀ i, 1 ≤ gs.crf.χ (gs.gridPoints i)) :
    deviationTrappedEnergy gs = 0 := by
  apply nucleusGap_zero_of_nonneg
  intro i
  simp only [deviationVector]
  linarith [h i]

/-- If some grid point has χ < 1, trapped energy is positive. -/
theorem deviationTrappedEnergy_pos_of_slow {n : ℕ} (gs : GridSample n)
    (h : ∃ i, gs.crf.χ (gs.gridPoints i) < 1) :
    0 < deviationTrappedEnergy gs := by
  unfold deviationTrappedEnergy
  rw [nucleusGap_pos_iff_trapped]
  obtain ⟨i, hi⟩ := h
  exact ⟨i, (deviation_neg_iff_slow gs i).mpr hi⟩

/-- Build a gap decomposition from a grid sample: the gate gap
is the deviation's trapped energy. -/
def gapFromGridSample {n : ℕ} (gs : GridSample n)
    (Δ_quant Δ_recon : ℝ) (hq : 0 ≤ Δ_quant) (hr : 0 ≤ Δ_recon) :
    GapDecomposition :=
  gapFromNucleus (deviationVector gs) Δ_quant Δ_recon hq hr

/-- The gate gap from a grid sample equals the trapped energy. -/
theorem gapFromGridSample_gate_eq {n : ℕ} (gs : GridSample n)
    (Δ_quant Δ_recon : ℝ) (hq : 0 ≤ Δ_quant) (hr : 0 ≤ Δ_recon) :
    (gapFromGridSample gs Δ_quant Δ_recon hq hr).Δ_gate =
      deviationTrappedEnergy gs :=
  rfl

/-- When there are slow grid points, the total gap from the grid sample
is positive (the Hossenfelder no-go constraint in discretized form). -/
theorem gridSample_positive_gap {n : ℕ} (gs : GridSample n)
    (Δ_quant Δ_recon : ℝ) (hq : 0 ≤ Δ_quant) (hr : 0 ≤ Δ_recon)
    (hslow : ∃ i, gs.crf.χ (gs.gridPoints i) < 1) :
    0 < totalGap (gapFromGridSample gs Δ_quant Δ_recon hq hr) := by
  have htrapped : ∃ i, deviationVector gs i < 0 := by
    obtain ⟨i, hi⟩ := hslow
    exact ⟨i, (deviation_neg_iff_slow gs i).mpr hi⟩
  exact hossenfelder_gap_from_nucleus (deviationVector gs) Δ_quant Δ_recon hq hr htrapped

/-- A sparse projection field: a grid sample where at most k grid points
have deviation exceeding ε in absolute value. This captures the physical
fact that χ ≈ 1 across most of spacetime. -/
structure SparseProjectionField (n : ℕ) extends GridSample n where
  ε : ℝ
  ε_pos : 0 < ε
  k : ℕ
  k_le_n : k ≤ n
  sparse : ∀ S : Finset (Fin n),
    (∀ i ∈ S, ε ≤ |deviationVector { crf := crf, gridPoints := gridPoints } i|) → S.card ≤ k

/-- Density ratio: fraction of grid points with significant deviation. -/
noncomputable def sparseFieldDensity {n : ℕ} (sp : SparseProjectionField n) : ℝ :=
  if n = 0 then 0 else (sp.k : ℝ) / (n : ℝ)

/-- Density is nonneg. -/
theorem sparseFieldDensity_nonneg {n : ℕ} (sp : SparseProjectionField n) :
    0 ≤ sparseFieldDensity sp := by
  unfold sparseFieldDensity
  split_ifs
  · exact le_refl 0
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Density is at most 1. -/
theorem sparseFieldDensity_le_one {n : ℕ} (sp : SparseProjectionField n) :
    sparseFieldDensity sp ≤ 1 := by
  unfold sparseFieldDensity
  split_ifs with h
  · exact zero_le_one
  · rw [div_le_one (Nat.cast_pos.mpr (by omega))]
    exact_mod_cast sp.k_le_n

/-- The flat field is 0-sparse for any ε > 0. -/
def flatSparseField (n : ℕ) (pts : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    SparseProjectionField n where
  crf := flatClockRateField
  gridPoints := pts
  ε := ε
  ε_pos := hε
  k := 0
  k_le_n := Nat.zero_le n
  sparse := by
    intro S hS
    suffices h : S = ∅ by simp [h]
    by_contra hne
    have ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hdev := hS i hi
    simp [deviationVector, flatClockRateField] at hdev
    linarith

/-- The flat sparse field has zero density. -/
theorem flatSparseField_density_zero (n : ℕ) (hn : n ≠ 0)
    (pts : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    sparseFieldDensity (flatSparseField n pts ε hε) = 0 := by
  simp [sparseFieldDensity, hn]

/-- Deviation energy is bounded by grid size times max squared deviation.
This is the key structural bound: sparse fields have bounded energy
because most deviations are small (< ε), so the energy concentrates
in the few active grid points. -/
theorem deviationEnergy_le_n_mul_maxSq {n : ℕ} (gs : GridSample n)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ i, |deviationVector gs i| ≤ M) :
    deviationEnergy gs ≤ (n : ℝ) * M ^ 2 := by
  unfold deviationEnergy sqSum
  have hle : ∀ i, (deviationVector gs i) ^ 2 ≤ M ^ 2 := by
    intro i
    rw [← sq_abs]
    exact sq_le_sq' (by linarith [abs_nonneg (deviationVector gs i)]) (hbound i)
  calc ∑ i, (deviationVector gs i) ^ 2
      ≤ ∑ _i : Fin n, M ^ 2 := Finset.sum_le_sum (fun i _ => hle i)
    _ = (n : ℝ) * M ^ 2 := by
        simp [Finset.sum_const, nsmul_eq_mul]

end HeytingLean.Bridge.AlMayahi.UDTSynthesis
