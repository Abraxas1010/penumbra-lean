import Mathlib
import HeytingLean.Analysis.PMBoundedControl.CompletionOperator

/-!
# PM Risk Functionals and Scalar Benchmark

This module formalizes the risk-functional layer used by PM-bounded τ-control.
The scalar benchmark is handled at the level of explicit profiles rather than a
full ODE existence/uniqueness development.
-/

namespace HeytingLean
namespace Analysis
namespace PMBoundedControl

noncomputable section

/-- Abstract risk metric on a state space. -/
class RiskFunctional (α : Type*) where
  risk : α → ℝ

/-- Positive PM boundary. -/
structure PMBoundary where
  Q_PM : ℝ
  pos : 0 < Q_PM

/-- The trajectory stays below the PM boundary. -/
def PMBoundedInvariant {α : Type*} (Q : α → ℝ) (B : PMBoundary) (u : ι → α) : Prop :=
  ∀ t, Q (u t) ≤ B.Q_PM

/-- A simple total penalty modeling `Ψ(q)` in the tokamak risk proxy. -/
def safetyPenalty (q : ℝ) : ℝ :=
  1 / (1 + q)

/-- Tokamak risk proxy from the PM-bounded τ-control paper. -/
def TokamakRisk (β_local q T : ℝ) : ℝ :=
  β_local * safetyPenalty q * (1 + T)

theorem safety_penalty_nonneg {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ safetyPenalty q := by
  unfold safetyPenalty
  positivity

theorem tokamak_risk_nonneg {β_local q T : ℝ}
    (hβ : 0 ≤ β_local) (hq : 0 ≤ q) (hT : 0 ≤ T) :
    0 ≤ TokamakRisk β_local q T := by
  unfold TokamakRisk
  have hpen : 0 ≤ safetyPenalty q := safety_penalty_nonneg hq
  positivity

theorem tokamak_risk_monotone_beta {β₁ β₂ q T : ℝ}
    (hβ : β₁ ≤ β₂) (hq : 0 ≤ q) (hT : 0 ≤ T) :
    TokamakRisk β₁ q T ≤ TokamakRisk β₂ q T := by
  unfold TokamakRisk
  have hfac : 0 ≤ safetyPenalty q * (1 + T) := by
    have hpen : 0 ≤ safetyPenalty q := safety_penalty_nonneg hq
    positivity
  nlinarith

/-- Central invariant: if risk is pointwise dominated by a PM-completed source,
then the PM boundary is preserved along the trajectory. -/
theorem pm_invariant_of_completion {α ι : Type*} (Q : α → ℝ) (B : PMBoundary)
    (u : ι → α) (source completed : α → ℝ)
    (hcompleted : ∀ a, completed a = SatRational B.Q_PM (source a))
    (hdom : ∀ t, Q (u t) ≤ |completed (u t)|) :
    PMBoundedInvariant Q B u := by
  intro t
  specialize hdom t
  rw [hcompleted] at hdom
  exact le_trans hdom (sat_rational_bounded B.pos)

/-- Explicit classical benchmark profile for the scalar blow-up model `u' = u^3`
with initial condition `u(0) = u₀`. -/
def classicalBlowupProfile (u₀ t : ℝ) : ℝ :=
  u₀ / Real.sqrt (1 - 2 * u₀^2 * t)

/-- Blow-up time of the classical benchmark profile. -/
def classicalBlowupTime (u₀ : ℝ) : ℝ :=
  1 / (2 * u₀^2)

/-- PM-completed benchmark profile obtained by saturating the classical one. -/
def completedScalarProfile (Q_PM u₀ t : ℝ) : ℝ :=
  SatRational Q_PM (classicalBlowupProfile u₀ t)

theorem classical_blowup_denominator_zero (u₀ : ℝ) (hu₀ : u₀ ≠ 0) :
    1 - 2 * u₀^2 * classicalBlowupTime u₀ = 0 := by
  unfold classicalBlowupTime
  field_simp [hu₀]
  ring

theorem scalar_bounded_completed {Q_PM u₀ t : ℝ} (hQ : 0 < Q_PM) :
    |completedScalarProfile Q_PM u₀ t| ≤ Q_PM := by
  unfold completedScalarProfile
  exact sat_rational_bounded hQ

/-- In the classical regime, the completed source differs from the raw source by
a controlled relative error. -/
theorem risk_classical_regime {Q_PM ε s : ℝ} (hQ : 0 < Q_PM) (hε : 0 < ε)
    (hs : |s| < ε * Q_PM) :
    |SatRational Q_PM s - s| ≤ ε * |s| := by
  exact sat_rational_identity_regime hQ hε hs

end

end PMBoundedControl
end Analysis
end HeytingLean
