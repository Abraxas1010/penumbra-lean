import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import HeytingLean.Quantum.Contextuality.MerminPeresRealization

noncomputable section

namespace HeytingLean.Generative.SpinorBridge

open Matrix Complex
open HeytingLean.Quantum.Contextuality

abbrev Mat2 := HeytingLean.Quantum.Contextuality.Mat2

/-- Pauli spin matrix `σ_x`. -/
def pauliX : Mat2 :=
  Quantum.Contextuality.Pauli.σx

/-- Pauli spin matrix `σ_y`. -/
def pauliY : Mat2 :=
  Quantum.Contextuality.Pauli.σy

/-- Pauli spin matrix `σ_z`. -/
def pauliZ : Mat2 :=
  Quantum.Contextuality.Pauli.σz

theorem pauliX_trace : Matrix.trace pauliX = 0 := by
  simp [pauliX, Quantum.Contextuality.Pauli.σx, Matrix.trace]

theorem pauliY_trace : Matrix.trace pauliY = 0 := by
  simp [pauliY, Quantum.Contextuality.Pauli.σy, Matrix.trace]

theorem pauliZ_trace : Matrix.trace pauliZ = 0 := by
  simp [pauliZ, Quantum.Contextuality.Pauli.σz, Matrix.trace]

theorem pauliX_hermitian : pauliX.conjTranspose = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Quantum.Contextuality.Pauli.σx, Matrix.conjTranspose_apply]

theorem pauliY_hermitian : pauliY.conjTranspose = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliY, Quantum.Contextuality.Pauli.σy, Matrix.conjTranspose_apply]

theorem pauliZ_hermitian : pauliZ.conjTranspose = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliZ, Quantum.Contextuality.Pauli.σz, Matrix.conjTranspose_apply]

theorem pauliX_sq : pauliX * pauliX = 1 := by
  simpa [pauliX] using Quantum.Contextuality.Pauli.σx_sq

theorem pauliY_sq : pauliY * pauliY = 1 := by
  simpa [pauliY] using Quantum.Contextuality.Pauli.σy_sq

theorem pauliZ_sq : pauliZ * pauliZ = 1 := by
  simpa [pauliZ] using Quantum.Contextuality.Pauli.σz_sq

theorem pauliX_mul_pauliY :
    pauliX * pauliY = (Complex.I : ℂ) • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Quantum.Contextuality.Pauli.σx,
      Quantum.Contextuality.Pauli.σy, Quantum.Contextuality.Pauli.σz, Matrix.mul_apply]

theorem pauliY_mul_pauliX :
    pauliY * pauliX = (-Complex.I : ℂ) • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Quantum.Contextuality.Pauli.σx,
      Quantum.Contextuality.Pauli.σy, Quantum.Contextuality.Pauli.σz, Matrix.mul_apply]

theorem pauliY_mul_pauliZ :
    pauliY * pauliZ = (Complex.I : ℂ) • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Quantum.Contextuality.Pauli.σx,
      Quantum.Contextuality.Pauli.σy, Quantum.Contextuality.Pauli.σz, Matrix.mul_apply]

theorem pauliZ_mul_pauliY :
    pauliZ * pauliY = (-Complex.I : ℂ) • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, pauliY, pauliZ, Quantum.Contextuality.Pauli.σx,
      Quantum.Contextuality.Pauli.σy, Quantum.Contextuality.Pauli.σz, Matrix.mul_apply]

theorem pauliZ_mul_pauliX :
    pauliZ * pauliX = (Complex.I : ℂ) • pauliY := by
  simpa [pauliX, pauliY, pauliZ] using Quantum.Contextuality.Pauli.σz_mul_σx

theorem pauliX_mul_pauliZ :
    pauliX * pauliZ = (-Complex.I : ℂ) • pauliY := by
  simpa [pauliX, pauliY, pauliZ] using Quantum.Contextuality.Pauli.σx_mul_σz

theorem pauli_commutator_XY :
    pauliX * pauliY - pauliY * pauliX = (2 * Complex.I) • pauliZ := by
  calc
    pauliX * pauliY - pauliY * pauliX
        = ((Complex.I : ℂ) - (-Complex.I : ℂ)) • pauliZ := by
            simp [pauliX_mul_pauliY, pauliY_mul_pauliX, sub_eq_add_neg, add_smul]
    _ = (2 * Complex.I) • pauliZ := by ring_nf

theorem pauli_commutator_YZ :
    pauliY * pauliZ - pauliZ * pauliY = (2 * Complex.I) • pauliX := by
  calc
    pauliY * pauliZ - pauliZ * pauliY
        = ((Complex.I : ℂ) - (-Complex.I : ℂ)) • pauliX := by
            simp [pauliY_mul_pauliZ, pauliZ_mul_pauliY, sub_eq_add_neg, add_smul]
    _ = (2 * Complex.I) • pauliX := by ring_nf

theorem pauli_commutator_ZX :
    pauliZ * pauliX - pauliX * pauliZ = (2 * Complex.I) • pauliY := by
  calc
    pauliZ * pauliX - pauliX * pauliZ
        = ((Complex.I : ℂ) - (-Complex.I : ℂ)) • pauliY := by
            simp [pauliZ_mul_pauliX, pauliX_mul_pauliZ, sub_eq_add_neg, add_smul]
    _ = (2 * Complex.I) • pauliY := by ring_nf

inductive SU2Generator
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

/-- The concrete matrix carried by each Pauli generator. -/
def generatorMatrix : SU2Generator → Mat2
  | .x => pauliX
  | .y => pauliY
  | .z => pauliZ

theorem pauliX_ne_pauliY : pauliX ≠ pauliY := by
  intro h
  have h01 := congrArg (fun M : Mat2 => M 0 1) h
  have him := congrArg Complex.im h01
  simp [pauliX, pauliY, Quantum.Contextuality.Pauli.σx, Quantum.Contextuality.Pauli.σy] at him

theorem pauliX_ne_pauliZ : pauliX ≠ pauliZ := by
  intro h
  have h01 := congrArg (fun M : Mat2 => M 0 1) h
  simp [pauliX, pauliZ, Quantum.Contextuality.Pauli.σx, Quantum.Contextuality.Pauli.σz] at h01

theorem pauliY_ne_pauliZ : pauliY ≠ pauliZ := by
  intro h
  have h01 := congrArg (fun M : Mat2 => M 0 1) h
  simp [pauliY, pauliZ, Quantum.Contextuality.Pauli.σy, Quantum.Contextuality.Pauli.σz] at h01

theorem generatorMatrix_injective : Function.Injective generatorMatrix := by
  intro a b h
  cases a <;> cases b <;> try rfl
  · exfalso
    exact pauliX_ne_pauliY (by simpa [generatorMatrix] using h)
  · exfalso
    exact pauliX_ne_pauliZ (by simpa [generatorMatrix] using h)
  · exfalso
    exact pauliX_ne_pauliY (by simpa [generatorMatrix] using h.symm)
  · exfalso
    exact pauliY_ne_pauliZ (by simpa [generatorMatrix] using h)
  · exfalso
    exact pauliX_ne_pauliZ (by simpa [generatorMatrix] using h.symm)
  · exfalso
    exact pauliY_ne_pauliZ (by simpa [generatorMatrix] using h.symm)

theorem su2_generator_count : Fintype.card SU2Generator = 3 := by
  decide

end HeytingLean.Generative.SpinorBridge
