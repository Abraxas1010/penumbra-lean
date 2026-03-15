import HeytingLean.Generative.WolframBridge.WolframCorrespondence
import HeytingLean.Generative.WolframBridge.GapTransport

namespace HeytingLean.Generative.WolframBridge

open HeytingLean.HossenfelderNoGo.HeytingBoundary

/-- A packaged pair of Wolfram bridge witnesses, one for each canonical counterexample. -/
structure WolframHeytingBridgeWitness where
  ce1Bridge :
    WolframFixedPointBridge HeytingLean.WPP.Wolfram.Counterexamples.CE1.sys
  ce2Bridge :
    WolframFixedPointBridge HeytingLean.WPP.Wolfram.Counterexamples.CE2.sys

theorem hossenfelder_and_graft_share_fixed_point_predicate
    {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : BoundaryNucleus L) (n : Nat) (z : Int) :
    (isBoolean N ↔ NucleusInvariant N) ∧
    (isBoolean (HeytingLean.NucleusGrafting.graftBoundaryNucleus (n := n) z) ↔
      NucleusInvariant (HeytingLean.NucleusGrafting.graftBoundaryNucleus (n := n) z)) := by
  exact ⟨hossenfelder_isBoolean_iff_nucleusInvariant N,
    graft_isBoolean_iff_nucleusInvariant (n := n) z⟩

theorem wolfram_side_uses_explicit_bridge
    (W : WolframHeytingBridgeWitness) :
    (¬ NucleusInvariant W.ce1Bridge.nucleus) ∧
      NucleusInvariant W.ce2Bridge.nucleus := by
  exact wolfram_fixed_point_separation W.ce1Bridge W.ce2Bridge

theorem wolfram_hossenfelder_grafting_share_fixed_point_obstruction
    {L : Type*} [SemilatticeInf L] [OrderBot L]
    (W : WolframHeytingBridgeWitness)
    (N : BoundaryNucleus L) (hBridge : BooleanBoundaryBridge N)
    (n : Nat) (z : Int) :
    (¬ NucleusInvariant W.ce1Bridge.nucleus) ∧
    NucleusInvariant W.ce2Bridge.nucleus ∧
    (¬ NucleusInvariant N) ∧
    (∃ a : L, boundaryGap N a ≠ ∅) ∧
    (¬ NucleusInvariant (HeytingLean.NucleusGrafting.graftBoundaryNucleus (n := n) z)) ∧
    boundaryGap (HeytingLean.NucleusGrafting.graftBoundaryNucleus (n := n) z)
      (∅ : Set (HeytingLean.NucleusGrafting.ActivationVector n)) ≠ ∅ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (wolfram_side_uses_explicit_bridge W).1
  · exact (wolfram_side_uses_explicit_bridge W).2
  · exact hossenfelder_not_nucleusInvariant N hBridge
  · exact gap_nonzero_at_boundary N hBridge
  · exact graft_not_nucleusInvariant (n := n) z
  · exact HeytingLean.NucleusGrafting.boundaryGap_bot_nonempty (n := n) z

end HeytingLean.Generative.WolframBridge
