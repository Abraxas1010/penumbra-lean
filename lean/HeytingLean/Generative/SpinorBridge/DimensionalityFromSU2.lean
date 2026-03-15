import HeytingLean.Generative.SpinorBridge.SU2Core
import HeytingLean.Generative.SpinorBridge.ClebschGordanCoupling
import HeytingLean.Generative.SpatialClosure

namespace HeytingLean.Generative.SpinorBridge

open HeytingLean.Generative

/-- Enumerate the three spatial axes by the three Pauli generators. -/
def generatorIndex : SU2Generator ≃ Fin 3 where
  toFun
    | .x => 0
    | .y => 1
    | .z => 2
  invFun
    | 0 => .x
    | 1 => .y
    | _ => .z
  left_inv := by intro g; cases g <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem generatorIndex_bijective :
    Function.Bijective generatorIndex := by
  exact generatorIndex.bijective

theorem generator_count_via_equiv :
    Fintype.card SU2Generator = 3 := by
  simpa using Fintype.card_congr generatorIndex

/-- The three Pauli generators provide three involutive spatial axes. -/
theorem three_axes_from_three_generators :
    Fintype.card SU2Generator = 3 ∧
    pauliX * pauliX = 1 ∧
    pauliY * pauliY = 1 ∧
    pauliZ * pauliZ = 1 := by
  exact ⟨generator_count_via_equiv, pauliX_sq, pauliY_sq, pauliZ_sq⟩

/-- Numeric count bridge: SpatialClosure fixes `level2.dim = 3`, and the Pauli
generator enumeration also yields `3`; this theorem identifies those counts. -/
theorem spatial_dimension_eq_su2_generator_count :
    level2.dim = Fintype.card SU2Generator := by
  simp [level2, generator_count_via_equiv]

/-- The axis-plus-two-stabilization count agrees with the three Pauli directions. -/
theorem emergence_generator_alignment :
    1 + level2.stabilizations = level2.dim ∧
      level2.dim = Fintype.card SU2Generator := by
  exact ⟨frame_directions_eq_dim level2, spatial_dimension_eq_su2_generator_count⟩

end HeytingLean.Generative.SpinorBridge
