import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Penumbra.ReentryNonOrientable

/-!
# Penumbra.MobiusSO4Embedding

This module embeds the Möbius half-twist into the concrete `so(4)` matrices used by the Rust
extension. The important fact is explicit: the Möbius generator lies in the anti-self-dual factor,
while the three self-dual basis elements commute with it.
-/

namespace Penumbra

open Matrix

abbrev SO4 := Matrix (Fin 4) (Fin 4) ℝ

/-- Matrix commutator. -/
def commutator (A B : SO4) : SO4 := A * B - B * A

/-- The Möbius half-twist generator used by the extension experiment. -/
def mobiusGenerator : SO4 :=
  !![0, -1, 0, 0;
     1,  0, 0, 0;
     0,  0, 0, 1;
     0,  0, -1, 0]

/-- The self-dual `J₁⁺` generator. -/
def j1Plus : SO4 :=
  !![0, -1, 0, 0;
     1,  0, 0, 0;
     0,  0, 0, -1;
     0,  0, 1, 0]

/-- The self-dual `J₂⁺` generator. -/
def j2Plus : SO4 :=
  !![0, 0, -1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0, -1, 0, 0]

/-- The self-dual `J₃⁺` generator. -/
def j3Plus : SO4 :=
  !![0, 0, 0, -1;
     0, 0, -1, 0;
     0, 1, 0, 0;
     1, 0, 0, 0]

/-- The Möbius generator is the concrete anti-self-dual `J₁⁻`. -/
def j1Minus : SO4 := mobiusGenerator

/-- The orientable control keeps both local planes aligned and matches the self-dual `J₁⁺`
generator used by the Rust negative-control surface. -/
def orientableGenerator : SO4 := j1Plus

/-- A concrete embedding from two-sheet traversal data into the `SO(4)` generators used by the
Rust experiment. Identity-like traversal stays on the orientable branch, Möbius swapping picks the
anti-self-dual half-twist, and degenerate maps collapse to `0`. -/
def traversalGenerator (cycle : Sheet → Sheet) : SO4 :=
  match cycle Sheet.left, cycle Sheet.right with
  | Sheet.right, Sheet.left => mobiusGenerator
  | Sheet.left, Sheet.right => orientableGenerator
  | _, _ => 0

/-- The Möbius generator commutes with the first self-dual basis element. -/
theorem mobius_commutes_j1Plus : commutator mobiusGenerator j1Plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutator, mobiusGenerator, j1Plus]

/-- The Möbius generator commutes with the second self-dual basis element. -/
theorem mobius_commutes_j2Plus : commutator mobiusGenerator j2Plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutator, mobiusGenerator, j2Plus]

/-- The Möbius generator commutes with the third self-dual basis element. -/
theorem mobius_commutes_j3Plus : commutator mobiusGenerator j3Plus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutator, mobiusGenerator, j3Plus]

/-- The Möbius generator is explicitly the anti-self-dual basis element used in the decomposition. -/
theorem mobius_in_su2_minus : mobiusGenerator = j1Minus := rfl

/-- The orientable control used in Rust is exactly the self-dual `J₁⁺` generator. -/
theorem orientable_generator_eq_j1Plus : orientableGenerator = j1Plus := rfl

/-- A Möbius traversal selects the anti-self-dual generator in the concrete embedding. -/
theorem mobius_traversal_generator_eq (cycle : Sheet → Sheet) (h : IsMobiusTraversal cycle) :
    traversalGenerator cycle = mobiusGenerator := by
  rcases h with ⟨hLeft, hRight⟩
  simp [traversalGenerator, hLeft, hRight]

/-- The canonical Möbius traversal lands in the anti-self-dual factor. -/
theorem mobius_traversal_lands_in_anti_self_dual_factor (cycle : Sheet → Sheet)
    (h : IsMobiusTraversal cycle) :
    traversalGenerator cycle = j1Minus := by
  rw [mobius_traversal_generator_eq cycle h, mobius_in_su2_minus]

/-- The commutant of the Möbius anti-self-dual generator contains the full self-dual triple. -/
theorem anti_self_dual_commutant_contains_su2plus :
    commutator mobiusGenerator j1Plus = 0 ∧
    commutator mobiusGenerator j2Plus = 0 ∧
    commutator mobiusGenerator j3Plus = 0 := by
  exact ⟨mobius_commutes_j1Plus, mobius_commutes_j2Plus, mobius_commutes_j3Plus⟩

/-- Once the traversal is Möbius, its embedded generator commutes with the full self-dual triple. -/
theorem mobius_traversal_commutant_contains_su2plus (cycle : Sheet → Sheet)
    (h : IsMobiusTraversal cycle) :
    commutator (traversalGenerator cycle) j1Plus = 0 ∧
    commutator (traversalGenerator cycle) j2Plus = 0 ∧
    commutator (traversalGenerator cycle) j3Plus = 0 := by
  rw [mobius_traversal_generator_eq cycle h]
  exact anti_self_dual_commutant_contains_su2plus

end Penumbra
