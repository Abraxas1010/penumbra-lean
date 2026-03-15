import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.UDTRecovery.TauFieldCore
import HeytingLean.Bridge.AlMayahi.UDTSynthesis.MassGenerationGap

/-!
# Bridge.AlMayahi.UDTRecovery.MassEnergyRecovery

Mass-energy bridges attached to the existing `AsymmetryGap` and nucleus-gap
machinery.

The key theorem here is honest and parameterized:

- if `Δτ > 0`, then the rest-energy definition induced by
  `m = h / (c² Δτ)` satisfies `E_rest = h / Δτ`

This is the cleanest place where a genuine `E = mc²`-style identity can be
stated in the current finite-dimensional UDT stack.
-/

namespace HeytingLean.Bridge.AlMayahi.UDTRecovery

open HeytingLean.Bridge.AlMayahi.UDTSynthesis

/-- Energy-frequency bridge `E = h / τ`. -/
noncomputable def tauEnergy (K : RecoveryConstants) (τ : ℝ) : ℝ :=
  K.h / τ

/-- Rest mass induced by the asymmetry gap `Δτ`. -/
noncomputable def restMassOfGap (K : RecoveryConstants) (g : AsymmetryGap) : ℝ :=
  K.h / (K.c ^ 2 * g.Δτ)

/-- Rest energy induced by the asymmetry gap. -/
noncomputable def restEnergyOfGap (K : RecoveryConstants) (g : AsymmetryGap) : ℝ :=
  restMassOfGap K g * K.c ^ 2

theorem planck_einstein_of_tau_frequency (K : RecoveryConstants) {τ : ℝ} (hτ : 0 < τ) :
    tauEnergy K τ = K.h * nuTau τ := by
  simp only [tauEnergy, nuTau, tauRate]
  field_simp [hτ.ne']

theorem rest_energy_of_asymmetry_gap (K : RecoveryConstants) (g : AsymmetryGap)
    (hgap : 0 < g.Δτ) :
    restEnergyOfGap K g = tauEnergy K g.Δτ := by
  unfold restEnergyOfGap restMassOfGap tauEnergy
  field_simp [K.c_pos.ne', hgap.ne']

theorem massive_of_trapped_component {n : ℕ} {v : Fin n → ℝ}
    (htrap : ∃ i, v i < 0) :
    0 < nucleusGap n v := by
  exact (nucleusGap_pos_iff_trapped v).mpr htrap

theorem gap_energy_positive (K : RecoveryConstants) (g : AsymmetryGap)
    (hgap : 0 < g.Δτ) :
    0 < tauEnergy K g.Δτ := by
  unfold tauEnergy
  exact div_pos K.h_pos hgap

end HeytingLean.Bridge.AlMayahi.UDTRecovery
