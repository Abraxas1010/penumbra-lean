import Mathlib
import HeytingLean.Analysis.PMBoundedControl.RiskFunctional

/-!
# τ-Progression and Effective Step Control
-/

namespace HeytingLean
namespace Analysis
namespace PMBoundedControl

noncomputable section

/-- Internal progression density from the PM-bounded τ-control paper. -/
def progressionDensity (Q Q_PM ε : ℝ) : ℝ :=
  1 + (Q / Q_PM) / max ε (1 - Q / Q_PM)

/-- Effective step size after τ-dilation. -/
def effectiveStep (Δσ ρ : ℝ) : ℝ :=
  Δσ / ρ

/-- One-step explicit completed update. -/
def completedUpdate (u : ℝ) (L N_PM : ℝ → ℝ) (Δσ_eff : ℝ) : ℝ :=
  u + Δσ_eff * (L u + N_PM u)

theorem progression_density_ge_one {Q Q_PM ε : ℝ}
    (hQ : 0 ≤ Q) (hQPM : 0 < Q_PM) (hε : 0 < ε) :
    1 ≤ progressionDensity Q Q_PM ε := by
  unfold progressionDensity
  have hfrac : 0 ≤ (Q / Q_PM) / max ε (1 - Q / Q_PM) := by
    positivity
  linarith

theorem effective_step_le_external {Δσ ρ : ℝ}
    (hΔσ : 0 ≤ Δσ) (hρ : 1 ≤ ρ) :
    effectiveStep Δσ ρ ≤ Δσ := by
  unfold effectiveStep
  have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  exact (div_le_iff₀ hρpos).2 (by nlinarith)

theorem effective_step_vanishes_of_large_density {Δσ ρ ε : ℝ}
    (_hΔσ : 0 ≤ Δσ) (hε : 0 < ε) (hρpos : 0 < ρ) (hρ : Δσ / ε ≤ ρ) :
    effectiveStep Δσ ρ ≤ ε := by
  unfold effectiveStep
  have hmul : Δσ ≤ ρ * ε := (div_le_iff₀ hε).1 hρ
  exact (div_le_iff₀ hρpos).2 (by simpa [mul_comm] using hmul)

/-- Error decomposition for the completed update relative to a classical update
at the same effective step. -/
theorem completed_update_error_bound (u Δσ_eff : ℝ) (L N N_PM : ℝ → ℝ) :
    |completedUpdate u L N_PM Δσ_eff - completedUpdate u L N Δσ_eff|
      ≤ |Δσ_eff| * |N_PM u - N u| := by
  have hEq :
      completedUpdate u L N_PM Δσ_eff - completedUpdate u L N Δσ_eff =
        Δσ_eff * (N_PM u - N u) := by
    unfold completedUpdate
    ring
  rw [hEq, abs_mul]

/-- In the safe regime, replacing the source by its PM completion incurs only the
scalar saturation error. -/
theorem completed_update_preserves_classical {Q_PM ε Δσ_eff u : ℝ}
    (hQ : 0 < Q_PM) (hε : 0 < ε) (hs : |u^3| < ε * Q_PM) :
    |completedUpdate u (fun z => z) (fun z => SatRational Q_PM (z^3)) Δσ_eff
      - completedUpdate u (fun z => z) (fun z => z^3) Δσ_eff|
      ≤ |Δσ_eff| * (ε * |u^3|) := by
  have hsat : |SatRational Q_PM (u^3) - u^3| ≤ ε * |u^3| := by
    simpa using sat_rational_identity_regime hQ hε hs
  have hbound := completed_update_error_bound u Δσ_eff (fun z => z) (fun z => z^3)
      (fun z => SatRational Q_PM (z^3))
  exact le_trans hbound (by
    have habs : 0 ≤ |Δσ_eff| := abs_nonneg Δσ_eff
    nlinarith)

end

end PMBoundedControl
end Analysis
end HeytingLean
