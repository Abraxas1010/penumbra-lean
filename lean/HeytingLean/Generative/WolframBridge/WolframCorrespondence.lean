import HeytingLean.Generative.WolframBridge.FixedPointPredicate
import HeytingLean.Bridge.Wolfram.CausalInvariance
import HeytingLean.Bridges.MirandaWolframHeyting

namespace HeytingLean.Generative.WolframBridge

universe u v

open HeytingLean

/-- Honest bridge: a specific Wolfram system is interpreted by a specific nucleus model.
This is a bridge hypothesis, not a definitional identity. -/
structure WolframFixedPointBridge
    {V : Type u} {P : Type v}
    (sys : HeytingLean.WPP.Wolfram.System V P) [DecidableEq V] where
  Carrier : Type*
  instSemilatticeInf : SemilatticeInf Carrier
  instOrderBot : OrderBot Carrier
  nucleus : HeytingLean.Core.Nucleus Carrier
  causalInvariant_iff_nucleusInvariant :
    HeytingLean.WPP.Wolfram.Properties.CausalInvariant (sys := sys) ↔
      NucleusInvariant nucleus

attribute [instance] WolframFixedPointBridge.instSemilatticeInf
attribute [instance] WolframFixedPointBridge.instOrderBot

theorem ce1_not_nucleusInvariant
    (B : WolframFixedPointBridge HeytingLean.WPP.Wolfram.Counterexamples.CE1.sys) :
    ¬ NucleusInvariant B.nucleus := by
  intro hInv
  have hCausal :
      HeytingLean.WPP.Wolfram.Properties.CausalInvariant
        (sys := HeytingLean.WPP.Wolfram.Counterexamples.CE1.sys) :=
    (B.causalInvariant_iff_nucleusInvariant).2 hInv
  exact HeytingLean.Bridge.Wolfram.ce1_not_causalInvariant hCausal

theorem ce2_nucleusInvariant
    (B : WolframFixedPointBridge HeytingLean.WPP.Wolfram.Counterexamples.CE2.sys) :
    NucleusInvariant B.nucleus := by
  exact (B.causalInvariant_iff_nucleusInvariant).1
    HeytingLean.Bridge.Wolfram.ce2_causalInvariant

theorem ce1_has_moved_point
    (B : WolframFixedPointBridge HeytingLean.WPP.Wolfram.Counterexamples.CE1.sys) :
    ∃ x, B.nucleus.R x ≠ x := by
  exact (not_nucleusInvariant_iff_exists_moved B.nucleus).mp (ce1_not_nucleusInvariant B)

theorem wolfram_fixed_point_separation
    (B1 : WolframFixedPointBridge HeytingLean.WPP.Wolfram.Counterexamples.CE1.sys)
    (B2 : WolframFixedPointBridge HeytingLean.WPP.Wolfram.Counterexamples.CE2.sys) :
    (¬ NucleusInvariant B1.nucleus) ∧ NucleusInvariant B2.nucleus := by
  exact ⟨ce1_not_nucleusInvariant B1, ce2_nucleusInvariant B2⟩

end HeytingLean.Generative.WolframBridge
