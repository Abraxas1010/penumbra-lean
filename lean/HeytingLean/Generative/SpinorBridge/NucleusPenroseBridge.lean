import HeytingLean.Generative.SpinorBridge.ComplexificationBarrier
import HeytingLean.Generative.WolframBridge.GapTransport

namespace HeytingLean.Generative.SpinorBridge

open HeytingLean.Core
open HeytingLean.Generative
open HeytingLean.Generative.WolframBridge
open HeytingLean.HossenfelderNoGo.HeytingBoundary

/-- Pack the algebraic correspondences proved by the spinor bridge. -/
structure PenroseCorrespondence where
  spinor_state_space :
    ∀ ax : OscillationAxis, Nonempty (OscillationSupport ax ≃ Fin 2)
  dimensionality :
    level2.dim = Fintype.card SU2Generator
  complexification :
    emergenceStatus 2 = .barrier ∧
      Fintype.card SL2CGenerator = 2 * Fintype.card SU2Generator

def penroseCorrespondence : PenroseCorrespondence where
  spinor_state_space := fun ax => ⟨oscillationStates ax⟩
  dimensionality := spatial_dimension_eq_su2_generator_count
  complexification := ⟨level2_barrier, complexification_doubles_generators⟩

theorem non_boolean_is_aperiodic
    {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : BoundaryNucleus L) (hBridge : BooleanBoundaryBridge N) :
    ¬ NucleusInvariant N ∧ (∃ a : L, boundaryGap N a ≠ ∅) := by
  exact ⟨hossenfelder_not_nucleusInvariant N hBridge, gap_nonzero_at_boundary N hBridge⟩

theorem spinor_penrose_bridge_summary
    {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : BoundaryNucleus L) (hBridge : BooleanBoundaryBridge N) :
    (∀ ax : OscillationAxis, Nonempty (OscillationSupport ax ≃ Fin 2)) ∧
      level2.dim = Fintype.card SU2Generator ∧
      emergenceStatus 2 = .barrier ∧
      Fintype.card SL2CGenerator = 2 * Fintype.card SU2Generator ∧
      (¬ NucleusInvariant N) ∧
      (∃ a : L, boundaryGap N a ≠ ∅) := by
  exact ⟨penroseCorrespondence.spinor_state_space, penroseCorrespondence.dimensionality,
    penroseCorrespondence.complexification.1, penroseCorrespondence.complexification.2,
    hossenfelder_not_nucleusInvariant N hBridge, gap_nonzero_at_boundary N hBridge⟩

end HeytingLean.Generative.SpinorBridge
