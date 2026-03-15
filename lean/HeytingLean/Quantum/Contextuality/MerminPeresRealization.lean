import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Tactic

/-!
Mermin–Peres square: explicit two-qubit matrix realization (Mathlib-only).

This module defines the Pauli matrices and packages the standard 3×3
Mermin–Peres observables, proving the six row/column operator-product
constraints:

* all three rows multiply to `1`,
* the first two columns multiply to `1`,
* the last column multiplies to `-1`.

This is the “quantum realization layer” that can be paired with the purely
combinatorial parity obstruction in
`HeytingLean.LoF.CryptoSheaf.Quantum.MerminPeres`.
-/

noncomputable section

namespace HeytingLean
namespace Quantum
namespace Contextuality

open Matrix Complex
open scoped BigOperators Kronecker

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℂ
abbrev Mat2x2 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

namespace Pauli

def σx : Mat2 :=
  fun i j =>
    if i = 0 ∧ j = 1 then (1 : ℂ)
    else if i = 1 ∧ j = 0 then (1 : ℂ)
    else 0

def σy : Mat2 :=
  fun i j =>
    if i = 0 ∧ j = 1 then (-Complex.I : ℂ)
    else if i = 1 ∧ j = 0 then (Complex.I : ℂ)
    else 0

def σz : Mat2 :=
  fun i j =>
    if i = 0 ∧ j = 0 then (1 : ℂ)
    else if i = 1 ∧ j = 1 then (-1 : ℂ)
    else 0

lemma σx_sq : σx * σx = (1 : Mat2) := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, Matrix.mul_apply]

lemma σy_sq : σy * σy = (1 : Mat2) := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σy, Matrix.mul_apply]

lemma σz_sq : σz * σz = (1 : Mat2) := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σz, Matrix.mul_apply]

lemma σz_mul_σx : σz * σx = (Complex.I : ℂ) • σy := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, σy, σz, Matrix.mul_apply]

lemma σx_mul_σz : σx * σz = (-Complex.I : ℂ) • σy := by
  classical
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σx, σy, σz, Matrix.mul_apply]

end Pauli

namespace MerminPeres

open Pauli

private lemma card_twoQubit : Fintype.card (Fin 2 × Fin 2) = 4 := by
  simp

private def twoQubitEquiv : (Fin 2 × Fin 2) ≃ Fin 4 :=
  by
    simpa [card_twoQubit] using (Fintype.equivFin (Fin 2 × Fin 2))

private def toMat4 : Mat2x2 ≃ₐ[ℂ] Mat4 :=
  Matrix.reindexAlgEquiv ℂ ℂ twoQubitEquiv

private lemma kron_mul (A B C D : Mat2) :
    (A ⊗ₖ B : Mat2x2) * (C ⊗ₖ D) = (A * C) ⊗ₖ (B * D) := by
  simpa using
    (Matrix.mul_kronecker_mul (A := A) (B := C) (A' := B) (B' := D)).symm

-- The 3×3 Mermin–Peres observables (two-qubit operators), on the product index.
def P11 : Mat2x2 := Pauli.σz ⊗ₖ (1 : Mat2)
def P12 : Mat2x2 := (1 : Mat2) ⊗ₖ Pauli.σz
def P13 : Mat2x2 := Pauli.σz ⊗ₖ Pauli.σz

def P21 : Mat2x2 := (1 : Mat2) ⊗ₖ Pauli.σx
def P22 : Mat2x2 := Pauli.σx ⊗ₖ (1 : Mat2)
def P23 : Mat2x2 := Pauli.σx ⊗ₖ Pauli.σx

def P31 : Mat2x2 := Pauli.σz ⊗ₖ Pauli.σx
def P32 : Mat2x2 := Pauli.σx ⊗ₖ Pauli.σz
def P33 : Mat2x2 := Pauli.σy ⊗ₖ Pauli.σy

-- Transport to `Fin 4` via the algebra equivalence `toMat4`.
def O11 : Mat4 := toMat4 P11
def O12 : Mat4 := toMat4 P12
def O13 : Mat4 := toMat4 P13

def O21 : Mat4 := toMat4 P21
def O22 : Mat4 := toMat4 P22
def O23 : Mat4 := toMat4 P23

def O31 : Mat4 := toMat4 P31
def O32 : Mat4 := toMat4 P32
def O33 : Mat4 := toMat4 P33

theorem row1_prodP : P11 * P12 * P13 = (1 : Mat2x2) := by
  classical
  unfold P11 P12 P13
  calc
    (Pauli.σz ⊗ₖ (1 : Mat2) : Mat2x2) * ((1 : Mat2) ⊗ₖ Pauli.σz) * (Pauli.σz ⊗ₖ Pauli.σz)
        = ((Pauli.σz * 1) ⊗ₖ ((1 : Mat2) * Pauli.σz)) * (Pauli.σz ⊗ₖ Pauli.σz) := by
            simp [kron_mul]
    _ = (Pauli.σz ⊗ₖ Pauli.σz) * (Pauli.σz ⊗ₖ Pauli.σz) := by
          simp
    _ = (Pauli.σz * Pauli.σz) ⊗ₖ (Pauli.σz * Pauli.σz) := by
          simp [kron_mul]
    _ = (1 : Mat2x2) := by
          simp [Pauli.σz_sq]

theorem row2_prodP : P21 * P22 * P23 = (1 : Mat2x2) := by
  classical
  unfold P21 P22 P23
  calc
    ((1 : Mat2) ⊗ₖ Pauli.σx : Mat2x2) * (Pauli.σx ⊗ₖ (1 : Mat2)) * (Pauli.σx ⊗ₖ Pauli.σx)
        = (((1 : Mat2) * Pauli.σx) ⊗ₖ (Pauli.σx * (1 : Mat2))) * (Pauli.σx ⊗ₖ Pauli.σx) := by
            simp [kron_mul]
    _ = (Pauli.σx ⊗ₖ Pauli.σx) * (Pauli.σx ⊗ₖ Pauli.σx) := by
          simp
    _ = (Pauli.σx * Pauli.σx) ⊗ₖ (Pauli.σx * Pauli.σx) := by
          simp [kron_mul]
    _ = (1 : Mat2x2) := by
          simp [Pauli.σx_sq]

theorem row3_prodP : P31 * P32 * P33 = (1 : Mat2x2) := by
  classical
  unfold P31 P32 P33
  have hcancel :
      (Pauli.σz * Pauli.σx) ⊗ₖ (Pauli.σx * Pauli.σz) =
        (Pauli.σy ⊗ₖ Pauli.σy : Mat2x2) := by
    calc
      (Pauli.σz * Pauli.σx) ⊗ₖ (Pauli.σx * Pauli.σz)
          = ((Complex.I : ℂ) • Pauli.σy) ⊗ₖ ((-Complex.I : ℂ) • Pauli.σy) := by
              simp [Pauli.σz_mul_σx, Pauli.σx_mul_σz]
      _ = (Complex.I : ℂ) • (Pauli.σy ⊗ₖ ((-Complex.I : ℂ) • Pauli.σy) : Mat2x2) := by
            simp [Matrix.smul_kronecker]
      _ = (Complex.I : ℂ) • ((-Complex.I : ℂ) • (Pauli.σy ⊗ₖ Pauli.σy : Mat2x2)) := by
            refine congrArg (fun M : Mat2x2 => (Complex.I : ℂ) • M) ?_
            simpa using
              (Matrix.kronecker_smul (r := (-Complex.I : ℂ)) (A := Pauli.σy) (B := Pauli.σy))
      _ = ((Complex.I : ℂ) * (-Complex.I : ℂ)) • (Pauli.σy ⊗ₖ Pauli.σy : Mat2x2) := by
            simp [smul_smul]
      _ = (Pauli.σy ⊗ₖ Pauli.σy : Mat2x2) := by
            simp
  calc
    (Pauli.σz ⊗ₖ Pauli.σx : Mat2x2) * (Pauli.σx ⊗ₖ Pauli.σz) * (Pauli.σy ⊗ₖ Pauli.σy)
        = ((Pauli.σz * Pauli.σx) ⊗ₖ (Pauli.σx * Pauli.σz)) * (Pauli.σy ⊗ₖ Pauli.σy) := by
            simp [kron_mul]
    _ = (Pauli.σy ⊗ₖ Pauli.σy) * (Pauli.σy ⊗ₖ Pauli.σy) := by
          simp [hcancel]
    _ = (Pauli.σy * Pauli.σy) ⊗ₖ (Pauli.σy * Pauli.σy) := by
          simp [kron_mul]
    _ = (1 : Mat2x2) := by
          simp [Pauli.σy_sq]

theorem col1_prodP : P11 * P21 * P31 = (1 : Mat2x2) := by
  classical
  unfold P11 P21 P31
  calc
    (Pauli.σz ⊗ₖ (1 : Mat2) : Mat2x2) * ((1 : Mat2) ⊗ₖ Pauli.σx) * (Pauli.σz ⊗ₖ Pauli.σx)
        = ((Pauli.σz * (1 : Mat2)) ⊗ₖ ((1 : Mat2) * Pauli.σx)) * (Pauli.σz ⊗ₖ Pauli.σx) := by
            simp [kron_mul]
    _ = (Pauli.σz ⊗ₖ Pauli.σx) * (Pauli.σz ⊗ₖ Pauli.σx) := by
          simp
    _ = (Pauli.σz * Pauli.σz) ⊗ₖ (Pauli.σx * Pauli.σx) := by
          simp [kron_mul]
    _ = (1 : Mat2x2) := by
          simp [Pauli.σz_sq, Pauli.σx_sq]

theorem col2_prodP : P12 * P22 * P32 = (1 : Mat2x2) := by
  classical
  unfold P12 P22 P32
  calc
    ((1 : Mat2) ⊗ₖ Pauli.σz : Mat2x2) * (Pauli.σx ⊗ₖ (1 : Mat2)) * (Pauli.σx ⊗ₖ Pauli.σz)
        = (((1 : Mat2) * Pauli.σx) ⊗ₖ (Pauli.σz * (1 : Mat2))) * (Pauli.σx ⊗ₖ Pauli.σz) := by
            simp [kron_mul]
    _ = (Pauli.σx ⊗ₖ Pauli.σz) * (Pauli.σx ⊗ₖ Pauli.σz) := by
          simp
    _ = (Pauli.σx * Pauli.σx) ⊗ₖ (Pauli.σz * Pauli.σz) := by
          simp [kron_mul]
    _ = (1 : Mat2x2) := by
          simp [Pauli.σx_sq, Pauli.σz_sq]

theorem col3_prodP : P13 * P23 * P33 = (-1 : Mat2x2) := by
  classical
  unfold P13 P23 P33
  have hsquare :
      (Pauli.σz * Pauli.σx) ⊗ₖ (Pauli.σz * Pauli.σx) =
        ((-1 : ℂ) • (Pauli.σy ⊗ₖ Pauli.σy : Mat2x2)) := by
    calc
      (Pauli.σz * Pauli.σx) ⊗ₖ (Pauli.σz * Pauli.σx)
          = ((Complex.I : ℂ) • Pauli.σy) ⊗ₖ ((Complex.I : ℂ) • Pauli.σy) := by
              simp [Pauli.σz_mul_σx]
      _ = (Complex.I : ℂ) • (Pauli.σy ⊗ₖ ((Complex.I : ℂ) • Pauli.σy) : Mat2x2) := by
            simp [Matrix.smul_kronecker]
      _ = (Complex.I : ℂ) • ((Complex.I : ℂ) • (Pauli.σy ⊗ₖ Pauli.σy : Mat2x2)) := by
            simp [Matrix.kronecker_smul]
      _ = ((Complex.I : ℂ) * (Complex.I : ℂ)) • (Pauli.σy ⊗ₖ Pauli.σy : Mat2x2) := by
            simp [smul_smul]
      _ = (-1 : ℂ) • (Pauli.σy ⊗ₖ Pauli.σy : Mat2x2) := by
            simp
  calc
    (Pauli.σz ⊗ₖ Pauli.σz : Mat2x2) * (Pauli.σx ⊗ₖ Pauli.σx) * (Pauli.σy ⊗ₖ Pauli.σy)
        = ((Pauli.σz * Pauli.σx) ⊗ₖ (Pauli.σz * Pauli.σx)) * (Pauli.σy ⊗ₖ Pauli.σy) := by
            simp [kron_mul]
    _ = ((-1 : ℂ) • (Pauli.σy ⊗ₖ Pauli.σy : Mat2x2)) * (Pauli.σy ⊗ₖ Pauli.σy) := by
          simp [hsquare]
    _ = (-1 : Mat2x2) := by
          -- Use `σy^2 = 1`.
          simp [Pauli.σy_sq, kron_mul]

theorem row1_prod : O11 * O12 * O13 = (1 : Mat4) := by
  classical
  have h := congrArg (fun M => toMat4 M) row1_prodP
  simpa [O11, O12, O13, mul_assoc] using h

theorem row2_prod : O21 * O22 * O23 = (1 : Mat4) := by
  classical
  have h := congrArg (fun M => toMat4 M) row2_prodP
  simpa [O21, O22, O23, mul_assoc] using h

theorem row3_prod : O31 * O32 * O33 = (1 : Mat4) := by
  classical
  have h := congrArg (fun M => toMat4 M) row3_prodP
  simpa [O31, O32, O33, mul_assoc] using h

theorem col1_prod : O11 * O21 * O31 = (1 : Mat4) := by
  classical
  have h := congrArg (fun M => toMat4 M) col1_prodP
  simpa [O11, O21, O31, mul_assoc] using h

theorem col2_prod : O12 * O22 * O32 = (1 : Mat4) := by
  classical
  have h := congrArg (fun M => toMat4 M) col2_prodP
  simpa [O12, O22, O32, mul_assoc] using h

theorem col3_prod : O13 * O23 * O33 = (-1 : Mat4) := by
  classical
  have h := congrArg (fun M => toMat4 M) col3_prodP
  simpa [O13, O23, O33, mul_assoc] using h

end MerminPeres

end Contextuality
end Quantum
end HeytingLean
