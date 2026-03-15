import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.UDTSynthesis.SparseProjectionField
import HeytingLean.Bridge.AlMayahi.UDTSynthesis.GapDecompositionBridge
import HeytingLean.Bridge.Veselov.HybridZeckendorf.DensityBounds

/-!
# Bridge.AlMayahi.UDTSynthesis.HZComputationalBridge

Bridge connecting the UDT clock-rate field's sparse deviation structure
to Vladimir Veselov's Hybrid Zeckendorf (HZ) arithmetic system.

## Physical Motivation

The clock-rate field χ = dt/dτ has inherently sparse deviations from unity:
in flat spacetime χ = 1, with deviations only at gravitational wells and
specific measurement configurations. When discretized on a spatial grid
for numerical simulation of the τ-potential φ(r) = 1/τ(r), the
intermediate values are sparse numbers — exactly the regime where HZ
arithmetic provides significant speedup (crossover at ρ ≈ 3×10⁻⁴ in
the sparse regime, with 44.8× speedup at 1M bits).

## Algebraic Framework

This module formalizes the SELECTION CRITERION connecting:
- The `SparseProjectionField` (deviation sparsity of χ)
- The HZ `density_upper_bound` (bounded representation efficiency)
- The `GapDecomposition` (gap structure in sparse regime)

The `ArithmeticSelector` is a predicate, not an implementation: it
characterizes WHEN HZ should be chosen based on operand density,
without hard-coding physical constants (per project policy).
-/

namespace HeytingLean.Bridge.AlMayahi.UDTSynthesis

open HeytingLean.Bridge.Veselov.HybridZeckendorf

/-- Arithmetic backend mode: Hybrid Zeckendorf or Standard (GMP-like). -/
inductive ArithmeticMode
  | hz        -- Hybrid Zeckendorf (sparse-efficient)
  | standard  -- Standard positional (dense-efficient)
  deriving DecidableEq, Repr

/-- Arithmetic modes are distinct. -/
theorem hz_ne_standard : ArithmeticMode.hz ≠ ArithmeticMode.standard := by decide

/-- Sparsity regime: parameterization of when HZ is advantageous.
ρ_crossover is the density threshold below which HZ outperforms standard.
No physical constants are hard-coded; these are regime parameters. -/
structure SparsityRegime where
  ρ_crossover : ℝ
  ρ_crossover_pos : 0 < ρ_crossover
  ρ_crossover_lt_one : ρ_crossover < 1

/-- Select arithmetic mode based on measured density vs crossover threshold. -/
noncomputable def selectArithmetic (regime : SparsityRegime) (ρ : ℝ) : ArithmeticMode :=
  if ρ < regime.ρ_crossover then .hz else .standard

/-- In the sparse regime (ρ < ρ_crossover), HZ is selected. -/
theorem selectArithmetic_hz (regime : SparsityRegime) (ρ : ℝ)
    (h : ρ < regime.ρ_crossover) :
    selectArithmetic regime ρ = .hz := by
  unfold selectArithmetic
  rw [if_pos h]

/-- In the dense regime (ρ_crossover ≤ ρ), standard is selected. -/
theorem selectArithmetic_standard (regime : SparsityRegime) (ρ : ℝ)
    (h : regime.ρ_crossover ≤ ρ) :
    selectArithmetic regime ρ = .standard := by
  unfold selectArithmetic
  rw [if_neg (not_lt.mpr h)]

/-- The selection is monotone: if ρ₁ < ρ₂ and ρ₂ selects HZ,
then ρ₁ also selects HZ. -/
theorem selectArithmetic_monotone (regime : SparsityRegime) {ρ₁ ρ₂ : ℝ}
    (h : ρ₁ ≤ ρ₂) (h₂ : selectArithmetic regime ρ₂ = .hz) :
    selectArithmetic regime ρ₁ = .hz := by
  unfold selectArithmetic at *
  split_ifs at h₂ with h₂'
  · rw [if_pos (lt_of_le_of_lt h h₂')]

/-- The flat field always selects HZ (density = 0 < any positive crossover). -/
theorem flat_selects_hz (regime : SparsityRegime) (n : ℕ) (hn : n ≠ 0)
    (pts : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    selectArithmetic regime
      (sparseFieldDensity (flatSparseField n pts ε hε)) = .hz := by
  rw [flatSparseField_density_zero n hn pts ε hε]
  exact selectArithmetic_hz regime 0 regime.ρ_crossover_pos

/-- A sparse projection field selects HZ when its density is below crossover. -/
theorem sparseField_selects_hz {n : ℕ} (regime : SparsityRegime)
    (sp : SparseProjectionField n)
    (h : sparseFieldDensity sp < regime.ρ_crossover) :
    selectArithmetic regime (sparseFieldDensity sp) = .hz :=
  selectArithmetic_hz regime (sparseFieldDensity sp) h

/-- HZ density bound reference: for any canonical HybridNumber X with
positive evaluation, the density is bounded logarithmically.
Re-exported from the HZ system for discoverability from the UDT context. -/
theorem hz_density_bound (X : HybridNumber) (hX : IsCanonical X)
    (hpos : 0 < eval X) :
    density X ≤ (Real.logb 1000 (eval X) + 2) :=
  density_upper_bound X hX hpos

/-- Composition: analysis of a sparse τ-field with HZ arithmetic selection
and gap decomposition. Packages the key objects that together justify
using HZ arithmetic for sparse τ-potential computation. -/
structure HZGapAnalysis (n : ℕ) where
  sparseField : SparseProjectionField n
  regime : SparsityRegime
  Δ_quant : ℝ
  Δ_recon : ℝ
  hq : 0 ≤ Δ_quant
  hr : 0 ≤ Δ_recon
  sparse_enough : sparseFieldDensity sparseField < regime.ρ_crossover

/-- The gap decomposition from an HZ gap analysis. -/
def HZGapAnalysis.gapDecomp {n : ℕ} (a : HZGapAnalysis n) : GapDecomposition :=
  gapFromGridSample a.sparseField.toGridSample a.Δ_quant a.Δ_recon a.hq a.hr

/-- The arithmetic mode selected for an HZ gap analysis is always HZ. -/
theorem HZGapAnalysis.selects_hz {n : ℕ} (a : HZGapAnalysis n) :
    selectArithmetic a.regime (sparseFieldDensity a.sparseField) = .hz :=
  sparseField_selects_hz a.regime a.sparseField a.sparse_enough

/-- When the sparse field has gravitational wells (χ < 1 at some grid point),
the total gap from the HZ gap analysis is positive. This is the
Hossenfelder no-go constraint in the HZ-discretized setting. -/
theorem HZGapAnalysis.positive_gap {n : ℕ} (a : HZGapAnalysis n)
    (hslow : ∃ i, a.sparseField.crf.χ (a.sparseField.gridPoints i) < 1) :
    0 < totalGap a.gapDecomp :=
  gridSample_positive_gap a.sparseField.toGridSample a.Δ_quant a.Δ_recon a.hq a.hr hslow

/-- The gate gap component of the HZ analysis equals the trapped energy
of the deviation vector. The HZ-efficient sparse bulk has small
gate gap, while the dense boundary layer (gravitational wells)
concentrates the trapped energy. -/
theorem HZGapAnalysis.gate_eq_trapped {n : ℕ} (a : HZGapAnalysis n) :
    a.gapDecomp.Δ_gate = deviationTrappedEnergy a.sparseField.toGridSample :=
  gapFromGridSample_gate_eq a.sparseField.toGridSample a.Δ_quant a.Δ_recon a.hq a.hr

end HeytingLean.Bridge.AlMayahi.UDTSynthesis
