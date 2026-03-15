import Mathlib.Algebra.BigOperators.Ring.Finset
import HeytingLean.Generative.PrimeStability.StabilityHierarchy
import HeytingLean.Bridge.AlMayahi.UDTRecovery.QuantumRecovery
import HeytingLean.Eigen.NucleusReLU
import HeytingLean.Eigen.SafEDMD

open scoped BigOperators

namespace HeytingLean.Generative.PrimeStability

open HeytingLean.Bridge.AlMayahi.UDTRecovery
open HeytingLean.Eigen

inductive ProjectionType
  | boolean
  | heyting
  deriving DecidableEq, Repr

noncomputable def projectionClassification {α : Type*} (rc : RotationalClosure α) : ProjectionType :=
  if rc.period = 1 then .boolean else .heyting

theorem identity_projects_boolean {α : Type*} (rc : RotationalClosure α)
    (h : IdentityClosure rc) :
    projectionClassification rc = .boolean := by
  simpa [projectionClassification, h]

theorem massive_projects_heyting {α : Type*} (rc : RotationalClosure α)
    (h : hasTrappedAsymmetry rc) :
    projectionClassification rc = .heyting := by
  simp [projectionClassification, hasTrappedAsymmetry] at h ⊢
  omega

def measurementProjection (n : ℕ) (i : Fin n) (v : Fin n → ℝ) : Fin n → ℝ :=
  fun j => if j = i then v j else 0

noncomputable def survivingFraction {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (_hv : 0 < ∑ j, (v j) ^ 2) : ℝ :=
  (v i) ^ 2 / ∑ j, (v j) ^ 2

theorem measurementProjection_apply_self {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    measurementProjection n i v i = v i := by
  simp [measurementProjection]

theorem measurementProjection_apply_ne {n : ℕ} (v : Fin n → ℝ) {i j : Fin n}
    (hij : j ≠ i) :
    measurementProjection n i v j = 0 := by
  simp [measurementProjection, hij]

theorem measurementProjection_sqSum {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    sqSum (measurementProjection n i v) = (v i) ^ 2 := by
  unfold sqSum measurementProjection
  classical
  simp

theorem survivingFraction_nonneg {n : ℕ} (v : Fin n → ℝ) (i : Fin n)
    (hv : 0 < ∑ j, (v j) ^ 2) :
    0 ≤ survivingFraction v i hv := by
  unfold survivingFraction
  exact div_nonneg (sq_nonneg _) hv.le

theorem born_weight_eq_surviving_fraction {n : ℕ} (ψ : TauWavefunction n)
    (hψ : 0 < waveNormSq ψ) (i : Fin n) :
    bornWeight ψ i = survivingFraction ψ.amp i (by
      simpa [waveNormSq, sqSum] using hψ) := by
  rfl

def reluWavefunction {n : ℕ} (v : Fin n → ℝ) : TauWavefunction n where
  amp := reluNucleus n v
  phase := fun _ => 0

theorem relu_gap_matches_born_structure {n : ℕ} (v : Fin n → ℝ)
    (i : Fin n) (hv : 0 < sqSum (reluNucleus n v)) :
    bornWeight (reluWavefunction v) i =
      survivingFraction (fun j => relu (v j)) i (by
        simpa [reluWavefunction, waveNormSq, sqSum, relu] using hv) := by
  simpa [reluWavefunction, reluNucleus, relu] using
    (born_weight_eq_surviving_fraction (ψ := reluWavefunction v)
      (hψ := by simpa [reluWavefunction, waveNormSq, sqSum] using hv) i)

end HeytingLean.Generative.PrimeStability
