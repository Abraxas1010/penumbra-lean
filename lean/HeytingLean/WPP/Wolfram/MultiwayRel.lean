import HeytingLean.WPP.MultiwayRel
import HeytingLean.WPP.Wolfram.ConfluenceTheory

/-!
# Wolfram systems as relation-based WPP multiway rules (beyond finiteness)

For finite pattern/vertex types we provide a `Finset`-based enumerator in
`HeytingLean.WPP.Wolfram.Multiway` and can instantiate `WppRule`.

This file provides the enumeration-free companion: any Wolfram system induces a
`WppRel` via its one-step rewrite relation `System.Step`, so we can talk about
cones, kernels, and reachability nuclei on *infinite* state spaces as well.
-/

namespace HeytingLean
namespace WPP
namespace Wolfram

namespace System

universe u v

variable {V : Type u} {P : Type v} (sys : System V P)
variable [DecidableEq V]

/-- View a Wolfram system as a relation-based WPP multiway rule (no enumeration). -/
def toWppRel : WppRel (HGraph V) where
  stepRel := Step (sys := sys)

@[simp] theorem toWppRel_stepRel {s t : HGraph V} :
    (sys.toWppRel).stepRel s t ↔ Step (sys := sys) s t := Iff.rfl

@[simp] theorem toWppRel_stepStar_iff {s t : HGraph V} :
    WppRel.StepStar (R := sys.toWppRel) s t ↔ StepStar (sys := sys) s t := Iff.rfl

end System

end Wolfram
end WPP
end HeytingLean

