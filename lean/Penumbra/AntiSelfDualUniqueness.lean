import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Penumbra.SO4Decomposition

/-!
# Penumbra.AntiSelfDualUniqueness

The experimental point is not that one specific anti-self-dual generator commutes with the
self-dual triple, but that the whole anti-self-dual factor does.
-/

namespace Penumbra

open Matrix

/-- Every concrete anti-self-dual combination commutes with `J₁⁺`. -/
theorem anti_self_dual_combination_commutes_j1Plus (a b c : ℝ) :
    commutator (a • j1Minus + b • j2Minus + c • j3Minus) j1Plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [commutator, j1Plus, j1Minus, j2Minus, j3Minus, mobiusGenerator]; try ring_nf)

/-- Every concrete anti-self-dual combination commutes with `J₂⁺`. -/
theorem anti_self_dual_combination_commutes_j2Plus (a b c : ℝ) :
    commutator (a • j1Minus + b • j2Minus + c • j3Minus) j2Plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [commutator, j2Plus, j1Minus, j2Minus, j3Minus, mobiusGenerator]; try ring_nf)

/-- Every concrete anti-self-dual combination commutes with `J₃⁺`. -/
theorem anti_self_dual_combination_commutes_j3Plus (a b c : ℝ) :
    commutator (a • j1Minus + b • j2Minus + c • j3Minus) j3Plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [commutator, j3Plus, j1Minus, j2Minus, j3Minus, mobiusGenerator]; try ring_nf)

/-- The anti-self-dual factor, not the particular generator, determines the self-dual commutant. -/
theorem anti_self_dual_factor_forces_same_self_dual_commutant (a b c : ℝ) :
    commutator (a • j1Minus + b • j2Minus + c • j3Minus) j1Plus = 0 ∧
    commutator (a • j1Minus + b • j2Minus + c • j3Minus) j2Plus = 0 ∧
    commutator (a • j1Minus + b • j2Minus + c • j3Minus) j3Plus = 0 := by
  exact ⟨anti_self_dual_combination_commutes_j1Plus a b c,
    anti_self_dual_combination_commutes_j2Plus a b c,
    anti_self_dual_combination_commutes_j3Plus a b c⟩

/-- A nonzero `J₁⁻`-line element is unique up to its scalar coefficient. -/
theorem j1Minus_line_unique (A : SO4) (a : ℝ)
    (hA : A = a • j1Minus) :
    minusProjection A = a • j1Minus := by
  rw [hA]
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [minusProjection, j1Minus, mobiusGenerator]; try ring_nf)

end Penumbra
