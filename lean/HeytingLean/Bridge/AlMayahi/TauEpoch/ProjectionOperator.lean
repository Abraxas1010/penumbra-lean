import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Bridge.AlMayahi.TauEpoch.ProjectionOperator

Two-Clock projection operator
`Π(x) = 1 + β (x - 1) + γ (x - 1)^2`.
-/

namespace HeytingLean.Bridge.AlMayahi.TauEpoch

/-- Parametric projection operator used by the Two-Clock model. -/
structure ProjectionOperator where
  β : ℝ
  γ : ℝ := 0
  order : ℕ := 1

/-- Evaluate the operator at ratio `x = τ_method / t`. -/
noncomputable def ProjectionOperator.eval (P : ProjectionOperator) (x : ℝ) : ℝ :=
  1 + P.β * (x - 1) + P.γ * (x - 1) ^ 2

@[simp] theorem ProjectionOperator.eval_one (P : ProjectionOperator) :
    P.eval 1 = 1 := by
  simp [ProjectionOperator.eval]

/-- Leading-order monotonicity: for `γ = 0`, positive `β` makes `Π` monotone in `x`. -/
theorem ProjectionOperator.mono_of_nonneg_beta
    (P : ProjectionOperator) (hβ : 0 ≤ P.β) (hγ : P.γ = 0) :
    Monotone P.eval := by
  intro x y hxy
  simp [ProjectionOperator.eval, hγ]
  have hshift : x - 1 ≤ y - 1 := sub_le_sub_right hxy 1
  exact mul_le_mul_of_nonneg_left hshift hβ

end HeytingLean.Bridge.AlMayahi.TauEpoch
