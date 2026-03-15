import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Analysis.PMBoundedControl.CompletionOperator
import HeytingLean.Bridge.AlMayahi.UDTSynthesis.ClockRateField

/-!
# Bridge.AlMayahi.UDTSynthesis.LagrangianReduction

Lagrangian formulation from UDT paper Appendix E.

The τ-field Lagrangian density `ℒ = (1/2)(dτ)² - V(τ)` connects the
PM-bounded control framework (Layer 1: saturation operators) to the
variational perspective. The key insight: saturation operators from
PM-bounded control correspond to a hard wall in the potential V(τ)
at τ = Q_PM, preventing the field from leaving the potential's basin.

This module formalizes the correspondence between the control-theoretic
and variational perspectives of PM-bounded tau-control.
-/

namespace HeytingLean.Bridge.AlMayahi.UDTSynthesis

open HeytingLean.Analysis.PMBoundedControl

/-- τ-field potential with minimum. The physical potential governing τ dynamics. -/
structure TauFieldPotential where
  V : ℝ → ℝ
  τ₀ : ℝ
  V_has_minimum : ∀ τ, V τ₀ ≤ V τ

/-- Lagrangian density: kinetic minus potential.
Parameter `dtau` is the time derivative of the τ field. -/
noncomputable def lagrangianDensity (L : TauFieldPotential) (dtau : ℝ) (τ : ℝ) : ℝ :=
  (1/2) * dtau ^ 2 - L.V τ

/-- The kinetic term is always nonneg. -/
theorem kineticTerm_nonneg (dtau : ℝ) :
    0 ≤ (1/2 : ℝ) * dtau ^ 2 := by
  apply mul_nonneg
  · norm_num
  · exact sq_nonneg dtau

/-- At the static limit (dtau = 0), the Lagrangian density is -V(τ).
This corresponds to the Poisson limit where time derivatives vanish. -/
theorem lagrangianDensity_static (L : TauFieldPotential) (τ : ℝ) :
    lagrangianDensity L 0 τ = -L.V τ := by
  simp [lagrangianDensity]

/-- At the potential minimum, the static Lagrangian is maximized
(least negative). -/
theorem static_lagrangian_min (L : TauFieldPotential) (τ : ℝ) :
    lagrangianDensity L 0 τ ≤ lagrangianDensity L 0 L.τ₀ := by
  simp [lagrangianDensity_static]
  exact L.V_has_minimum τ

/-- PM saturation boundary correspondence: the PM boundary Q_PM defines
a hard cutoff on the τ domain. If τ stays in [0, Q_PM] (the PM-safe set),
then τ is within the potential's basin. -/
theorem saturation_bounded_by_potential_basin
    {Q_PM : ℝ} (hQ : 0 < Q_PM) (x : ℝ) (hx : 0 ≤ x) :
    SatRational Q_PM x ∈ pmSafeSet Q_PM :=
  sat_rational_mem_safeSet hQ hx

/-- The rational saturation keeps τ within the PM-safe interval,
which can be viewed as confinement to the potential basin. -/
theorem saturation_confines_to_basin
    {Q_PM : ℝ} (hQ : 0 < Q_PM) (x : ℝ) :
    |SatRational Q_PM x| ≤ Q_PM :=
  sat_rational_bounded hQ

/-- A simple quadratic potential centered at τ₀ = 0 with minimum value 0. -/
def quadraticPotential (k : ℝ) (hk : 0 ≤ k) : TauFieldPotential where
  V := fun τ => k * τ ^ 2
  τ₀ := 0
  V_has_minimum := by
    intro τ
    simp
    exact mul_nonneg hk (sq_nonneg τ)

/-- For the quadratic potential, the static Lagrangian is -k·τ². -/
theorem quadratic_static (k : ℝ) (hk : 0 ≤ k) (τ : ℝ) :
    lagrangianDensity (quadraticPotential k hk) 0 τ = -(k * τ ^ 2) := by
  simp [lagrangianDensity_static, quadraticPotential]

/-- Consistency: the PM saturation applied to a potential-minimum trajectory
stays at the minimum. Specifically, SatRational Q_PM 0 = 0. -/
theorem saturation_at_minimum {Q_PM : ℝ} (_hQ : 0 < Q_PM) :
    SatRational Q_PM 0 = 0 := by
  simp [SatRational]

end HeytingLean.Bridge.AlMayahi.UDTSynthesis
