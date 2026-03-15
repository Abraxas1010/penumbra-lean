import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.UDTRecovery.TauFieldCore
import HeytingLean.Eigen.SafEDMD

/-!
# Bridge.AlMayahi.UDTRecovery.QuantumRecovery

Finite-dimensional quantum-recovery surfaces for the UDT layer.

This module gives:

- a finite-state wavefunction carrier with amplitude and phase
- norm-squared / Born-weight definitions
- a genuine finite-sum Born normalization theorem
- a coordinatewise real linear evolution surface (NOT the complex
  Schrödinger equation — requires complex amplitudes for that)
- an explicit open status for Bell closure

It does not claim a full Hilbert-space, continuum Schrödinger, or Bell proof.
The Schrödinger equation is iℏ∂ψ/∂t = Hψ with complex-valued ψ; the surface
here uses real amplitudes only, so it is a real linear evolution proxy.
-/

open scoped BigOperators

namespace HeytingLean.Bridge.AlMayahi.UDTRecovery

open HeytingLean.Eigen

/-- Finite-state τ-wavefunction with real amplitudes and phases. -/
structure TauWavefunction (n : ℕ) where
  amp : Fin n → ℝ
  phase : Fin n → ℝ

/-- Squared norm proxy for the amplitude carrier. -/
def waveNormSq {n : ℕ} (ψ : TauWavefunction n) : ℝ :=
  sqSum ψ.amp

theorem waveNormSq_nonneg {n : ℕ} (ψ : TauWavefunction n) :
    0 ≤ waveNormSq ψ := by
  unfold waveNormSq sqSum
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Born weight for a basis coordinate. -/
noncomputable def bornWeight {n : ℕ} (ψ : TauWavefunction n) (i : Fin n) : ℝ :=
  (ψ.amp i) ^ 2 / waveNormSq ψ

theorem bornWeight_nonneg {n : ℕ} (ψ : TauWavefunction n) (hnorm : 0 < waveNormSq ψ)
    (i : Fin n) :
    0 ≤ bornWeight ψ i := by
  unfold bornWeight
  exact div_nonneg (sq_nonneg _) hnorm.le

theorem born_normalization_surface {n : ℕ} (ψ : TauWavefunction n)
    (hnorm : 0 < waveNormSq ψ) :
    ∑ i, bornWeight ψ i = 1 := by
  have hsum :
      (∑ i, bornWeight ψ i) = (∑ i, (ψ.amp i) ^ 2) / waveNormSq ψ := by
    unfold bornWeight waveNormSq sqSum
    simpa using
      (Finset.sum_div Finset.univ (fun i : Fin n => (ψ.amp i) ^ 2) (∑ i, (ψ.amp i) ^ 2)).symm
  rw [hsum]
  have hsumPos : 0 < ∑ i, (ψ.amp i) ^ 2 := by
    simpa [waveNormSq, sqSum] using hnorm
  unfold waveNormSq sqSum
  field_simp [hsumPos.ne']

/-- Finite-dimensional real linear evolution surface.

This is a REAL-amplitude proxy for quantum evolution. The true Schrödinger
equation is iℏ∂ψ/∂t = Hψ with complex ψ; this surface omits the imaginary
unit and uses real amplitudes only. Upgrading to complex amplitudes is open. -/
structure QuantumEvolution (n : ℕ) where
  ψ : TauWavefunction n
  dψ : Fin n → ℝ
  Hψ : Fin n → ℝ
  ħ : ℝ
  ħ_pos : 0 < ħ

/-- Coordinatewise real linear evolution surface `ħ dψ = Hψ`.

This is NOT the Schrödinger equation (which requires complex amplitudes).
It is the real-amplitude analogue that serves as a landing target for
future complex-valued formalization. -/
def SatisfiesRealLinearEvolution {n : ℕ} (e : QuantumEvolution n) : Prop :=
  ∀ i, e.ħ * e.dψ i = e.Hψ i

/-- Explicit status surface for Bell closure. -/
inductive BellClosureStatus
  | open
  | parameterized
  deriving DecidableEq, Repr

/-- The current UDT recovery layer does not close Bell's theorem. -/
def bellClosureStatus : BellClosureStatus := .open

end HeytingLean.Bridge.AlMayahi.UDTRecovery
