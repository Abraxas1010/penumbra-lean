import HeytingLean.Generative.WolframBridge.FixedPointPredicate
import HeytingLean.HossenfelderNoGo.HeytingBoundary.GapNonZero
import HeytingLean.NucleusGrafting.BoundaryConnection

namespace HeytingLean.Generative.WolframBridge

open HeytingLean.HossenfelderNoGo.HeytingBoundary
open HeytingLean.NucleusGrafting

theorem hossenfelder_not_nucleusInvariant
    {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : BoundaryNucleus L) (hBridge : BooleanBoundaryBridge N) :
    ¬ NucleusInvariant N := by
  intro hInv
  have hBool : isBoolean N :=
    (hossenfelder_isBoolean_iff_nucleusInvariant N).2 hInv
  exact boundary_necessarily_non_boolean N hBridge hBool

theorem graft_isBoolean_iff_nucleusInvariant {n : Nat} (z : Int) :
    isBoolean (graftBoundaryNucleus (n := n) z) ↔
      NucleusInvariant (graftBoundaryNucleus (n := n) z) :=
  hossenfelder_isBoolean_iff_nucleusInvariant _

theorem graft_not_nucleusInvariant {n : Nat} (z : Int) :
    ¬ NucleusInvariant (graftBoundaryNucleus (n := n) z) := by
  intro hInv
  have hBool : isBoolean (graftBoundaryNucleus (n := n) z) :=
    (graft_isBoolean_iff_nucleusInvariant (n := n) z).2 hInv
  exact graftBoundaryNucleus_not_boolean (n := n) z hBool

end HeytingLean.Generative.WolframBridge
