import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.UDTRecovery.TauFieldCore

/-!
# Bridge.AlMayahi.UDTRecovery.GravityRecovery

Weak-field gravity and causality surfaces for the UDT recovery layer.

The recoveries in this module are intentionally weak-field and explicit:

- a unit upper bound on `χ` yields `clockProjection ≤ τ`
- an explicit speed bound on `χ` yields `causalVelocity ≤ c`
- inverse-square and inverse-radius scalings are stated honestly
- redshift is modeled as a positive ratio of local clock rates

This does not prove full GR or Schwarzschild geometry.
-/

namespace HeytingLean.Bridge.AlMayahi.UDTRecovery

open HeytingLean.Bridge.AlMayahi.UDTSynthesis

/-- Weak-field gravity model driven by a clock-rate field and positive constants. -/
structure GravityModel where
  constants : RecoveryConstants
  clock : ClockRateField
  K : ℝ
  K_nonneg : 0 ≤ K
  clock_sub_luminal : ∀ τ, 0 < τ → clock.χ τ ≤ constants.c

/-- Observable propagation speed extracted from the clock projection. -/
noncomputable def causalVelocity (M : GravityModel) (τ : ℝ) : ℝ :=
  clockProjection M.clock τ / τ

theorem causalVelocity_eq_clockRate (M : GravityModel) {τ : ℝ} (hτ : τ ≠ 0) :
    causalVelocity M τ = M.clock.χ τ := by
  unfold causalVelocity clockProjection
  field_simp [hτ]

/-- An explicit local clock bound `χ ≤ 1` forces the projected clock to not
outrun proper time. This is an assumption-level weak-field inequality, not a
derived time-dilation law. -/
theorem clockProjection_le_tau_of_unit_clock_bound (M : GravityModel) {τ : ℝ}
    (hτ : 0 ≤ τ) (hslow : M.clock.χ τ ≤ 1) :
    clockProjection M.clock τ ≤ τ := by
  unfold clockProjection
  calc
    M.clock.χ τ * τ ≤ 1 * τ := by
      exact mul_le_mul_of_nonneg_right hslow hτ
    _ = τ := by ring

/-- An explicit subluminal bound on `χ` yields the corresponding observable
velocity bound. -/
theorem causalVelocity_le_c_of_clock_bound (M : GravityModel) {τ : ℝ}
    (hτ : 0 < τ) :
    causalVelocity M τ ≤ M.constants.c := by
  rw [causalVelocity_eq_clockRate M hτ.ne']
  exact M.clock_sub_luminal τ hτ

/-- Weak-field redshift ratio between two clock-rate samples. -/
noncomputable def redshiftRatio (M : GravityModel) (τ_emit τ_obs : ℝ) : ℝ :=
  M.clock.χ τ_obs / M.clock.χ τ_emit

/-- The redshift ratio is positive because the clock-rate field is positive. -/
theorem redshiftRatio_pos (M : GravityModel) (τ_emit τ_obs : ℝ) :
    0 < redshiftRatio M τ_emit τ_obs := by
  unfold redshiftRatio
  exact div_pos (M.clock.χ_pos τ_obs) (M.clock.χ_pos τ_emit)

/-- Weak-field inverse-radius potential surface. -/
noncomputable def weakFieldPotential (M : GravityModel) (r : ℝ) : ℝ :=
  -M.K / r

/-- Weak-field inverse-square acceleration surface. -/
noncomputable def inverseSquareAcceleration (M : GravityModel) (r : ℝ) : ℝ :=
  M.K / r ^ 2

theorem inverseSquareAcceleration_nonneg (M : GravityModel) {r : ℝ} (hr : r ≠ 0) :
    0 ≤ inverseSquareAcceleration M r := by
  unfold inverseSquareAcceleration
  have hsq : 0 < r ^ 2 := by
    nlinarith [sq_pos_of_ne_zero hr]
  exact div_nonneg M.K_nonneg hsq.le

theorem weak_field_potential_halves_at_double_radius (M : GravityModel) {r : ℝ}
    (hr : r ≠ 0) :
    weakFieldPotential M (2 * r) = weakFieldPotential M r / 2 := by
  unfold weakFieldPotential
  field_simp [hr]

theorem newtonian_limit_of_inverse_square (M : GravityModel) {r : ℝ}
    (hr : r ≠ 0) :
    inverseSquareAcceleration M (2 * r) = inverseSquareAcceleration M r / 4 := by
  unfold inverseSquareAcceleration
  field_simp [hr]
  norm_num

end HeytingLean.Bridge.AlMayahi.UDTRecovery
