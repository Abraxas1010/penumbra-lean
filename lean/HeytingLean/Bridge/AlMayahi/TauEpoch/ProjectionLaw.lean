import HeytingLean.Bridge.AlMayahi.TauEpoch.ProjectionOperator
import HeytingLean.Bridge.AlMayahi.TauEpoch.TauProxy

/-!
# Bridge.AlMayahi.TauEpoch.ProjectionLaw

Two-Clock Projection Law:
`C_obs = C_true * Π(τ_method / t)`.

Formalized as a model structure (not an axiom).
-/

namespace HeytingLean.Bridge.AlMayahi.TauEpoch

/-- Central Two-Clock model container. -/
structure TwoClockModel where
  C_true : ℝ
  projOp : ProjectionOperator
  tauAssignment : DomainKind → TauProxyAssignment
  proxiesValid : ∀ k, ValidTauProxy (tauAssignment k)

/-- Model prediction at a fixed ratio `τ_method / t`. -/
noncomputable def TwoClockModel.predict (m : TwoClockModel) (tauRatio : ℝ) : ℝ :=
  m.C_true * m.projOp.eval tauRatio

@[simp] theorem TwoClockModel.predict_at_unity (m : TwoClockModel) :
    m.predict 1 = m.C_true := by
  simp [TwoClockModel.predict]

/-- Offset relative to the true value. -/
noncomputable def TwoClockModel.offset (m : TwoClockModel) (tauRatio : ℝ) : ℝ :=
  m.predict tauRatio - m.C_true

/-- At leading order (`γ = 0`) and nonnegative `C_true`, offsets are ordered by `tauRatio`. -/
theorem TwoClockModel.offset_mono_of_nonneg
    (m : TwoClockModel)
    (hC : 0 ≤ m.C_true)
    (hβ : 0 ≤ m.projOp.β)
    (hγ : m.projOp.γ = 0) :
    Monotone (fun r => m.offset r) := by
  intro r₁ r₂ hr
  unfold TwoClockModel.offset TwoClockModel.predict
  simp [ProjectionOperator.eval, hγ]
  have hshift : r₁ - 1 ≤ r₂ - 1 := sub_le_sub_right hr 1
  have hmul : m.projOp.β * (r₁ - 1) ≤ m.projOp.β * (r₂ - 1) :=
    mul_le_mul_of_nonneg_left hshift hβ
  have hinside : 1 + m.projOp.β * (r₁ - 1) ≤ 1 + m.projOp.β * (r₂ - 1) :=
    add_le_add_left hmul 1
  exact mul_le_mul_of_nonneg_left hinside hC

/-- Sign-direction form of the projection law at leading order. -/
theorem TwoClockModel.sign_prediction
    (m : TwoClockModel)
    (hC : 0 ≤ m.C_true)
    (hβ : 0 ≤ m.projOp.β)
    (hγ : m.projOp.γ = 0)
    {r : ℝ} :
    (1 ≤ r → m.C_true ≤ m.predict r) ∧ (r ≤ 1 → m.predict r ≤ m.C_true) := by
  constructor
  · intro hr
    unfold TwoClockModel.predict
    simp [ProjectionOperator.eval, hγ]
    have hshift : 0 ≤ r - 1 := sub_nonneg.mpr hr
    have hmul : 0 ≤ m.projOp.β * (r - 1) := mul_nonneg hβ hshift
    have hinside : (1 : ℝ) ≤ 1 + m.projOp.β * (r - 1) := by
      exact le_add_of_nonneg_right hmul
    have hscale : m.C_true * 1 ≤ m.C_true * (1 + m.projOp.β * (r - 1)) :=
      mul_le_mul_of_nonneg_left hinside hC
    simpa using hscale
  · intro hr
    unfold TwoClockModel.predict
    simp [ProjectionOperator.eval, hγ]
    have hshift : r - 1 ≤ 0 := sub_nonpos.mpr hr
    have hmul : m.projOp.β * (r - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ hshift
    have hinside : 1 + m.projOp.β * (r - 1) ≤ (1 : ℝ) := by
      exact add_le_of_nonpos_right hmul
    have hscale : m.C_true * (1 + m.projOp.β * (r - 1)) ≤ m.C_true * 1 :=
      mul_le_mul_of_nonneg_left hinside hC
    simpa using hscale

end HeytingLean.Bridge.AlMayahi.TauEpoch
