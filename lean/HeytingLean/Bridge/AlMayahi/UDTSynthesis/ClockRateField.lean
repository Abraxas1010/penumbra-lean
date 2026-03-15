import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.TauEpoch.ProjectionOperator

/-!
# Bridge.AlMayahi.UDTSynthesis.ClockRateField

Clock-rate field `χ : ℝ → ℝ` from UDT paper Appendix D.1, equation `t = χ(τ)·τ`.

The clock-rate field maps the internal proper time coordinate `τ` to the
observable clock time `t` via `t = χ(τ) · τ`. The field `χ` encodes the
local time-dilation structure: in flat space `χ = 1` so `t = τ`.

This module connects the clock-rate field to the existing `ProjectionOperator`
from the τ-Epoch formalization.
-/

namespace HeytingLean.Bridge.AlMayahi.UDTSynthesis

open HeytingLean.Bridge.AlMayahi.TauEpoch

/-- Clock-rate field structure from UDT Appendix D.1. -/
structure ClockRateField where
  χ : ℝ → ℝ
  χ_pos : ∀ τ, 0 < χ τ
  χ_flat : χ 0 = 1

/-- Clock projection: observable time as a function of proper time. -/
def clockProjection (crf : ClockRateField) (τ : ℝ) : ℝ :=
  crf.χ τ * τ

/-- At the origin, clock projection is zero (identity at origin). -/
theorem clockProjection_zero (crf : ClockRateField) :
    clockProjection crf 0 = 0 := by
  simp [clockProjection]

/-- If `χ` is monotone and `χ(0) = 1 > 0`, then `clockProjection` is
monotone on the nonneg reals. We prove the stronger local statement:
for `0 ≤ τ₁ ≤ τ₂`, if `χ` is monotone then `t₁ ≤ t₂`. -/
theorem clockProjection_monotone_nonneg (crf : ClockRateField)
    (hχ_mono : Monotone crf.χ)
    {τ₁ τ₂ : ℝ} (h₁ : 0 ≤ τ₁) (h₂ : τ₁ ≤ τ₂) :
    clockProjection crf τ₁ ≤ clockProjection crf τ₂ := by
  unfold clockProjection
  have hχ₁ : 0 < crf.χ τ₁ := crf.χ_pos τ₁
  have hχ₂_ge : crf.χ τ₁ ≤ crf.χ τ₂ := hχ_mono h₂
  calc crf.χ τ₁ * τ₁
      ≤ crf.χ τ₂ * τ₁ := by exact mul_le_mul_of_nonneg_right hχ₂_ge h₁
    _ ≤ crf.χ τ₂ * τ₂ := by exact mul_le_mul_of_nonneg_left h₂ (le_of_lt (crf.χ_pos τ₂))

/-- The flat clock-rate field: `χ(τ) = 1` for all `τ`. -/
def flatClockRateField : ClockRateField where
  χ := fun _ => 1
  χ_pos := fun _ => one_pos
  χ_flat := rfl

/-- Under the flat field, `t = τ`. -/
theorem clockProjection_flat (τ : ℝ) :
    clockProjection flatClockRateField τ = τ := by
  simp [clockProjection, flatClockRateField]

/-- Given a clock-rate field χ and a ProjectionOperator Π, the composition
`Π(χ(τ))` maps from internal time through the clock-rate field, then
applies the two-clock correction. This is the fundamental composition
linking τ-Epoch projection to UDT clock dilation. -/
noncomputable def projectedClockRate (crf : ClockRateField)
    (P : ProjectionOperator) (τ : ℝ) : ℝ :=
  P.eval (crf.χ τ)

/-- When χ = 1 (flat space), the projected clock rate equals Π(1) = 1. -/
theorem projectedClockRate_flat_eq_one (P : ProjectionOperator) :
    projectedClockRate flatClockRateField P 0 = 1 := by
  simp [projectedClockRate, flatClockRateField, ProjectionOperator.eval_one]

/-- Clock-rate deviation: the extent to which χ differs from 1 at a given τ. -/
def clockRateDeviation (crf : ClockRateField) (τ : ℝ) : ℝ :=
  crf.χ τ - 1

/-- At the origin, the deviation is zero (flat-space limit). -/
theorem clockRateDeviation_zero (crf : ClockRateField) :
    clockRateDeviation crf 0 = 0 := by
  simp [clockRateDeviation, crf.χ_flat]

/-- The clock-rate field is always positive, so the deviation is always > -1. -/
theorem clockRateDeviation_gt_neg_one (crf : ClockRateField) (τ : ℝ) :
    -1 < clockRateDeviation crf τ := by
  unfold clockRateDeviation
  have := crf.χ_pos τ
  linarith

end HeytingLean.Bridge.AlMayahi.UDTSynthesis
