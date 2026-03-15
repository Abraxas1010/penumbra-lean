import HeytingLean.WPP.MultiwayRel
import HeytingLean.WPP.Wolfram.MultiwayRel
import HeytingLean.MirandaDynamics.TKFT.Reaching
import HeytingLean.MirandaDynamics.FixedPoint.PeriodicNucleus

/-!
# Miranda/Wolfram/Heyting bridge lemmas (library-only)

This file connects three spines already present in the repo:

* WPP relation-based multiway semantics (`WppRel`);
* Miranda TKFT reaching relations (`ReachingRel`);
* Fixed-point characterization of union nuclei (MirandaDynamics.FixedPoint).

The goal is a minimal, axioms-free bridge that lets us reuse algebraic
fixed-point reasoning across the WPP and Miranda layers.
-/

namespace HeytingLean

namespace WPP
namespace WppRel

universe u

variable {State : Type u}

/-- View a WPP relation as a Miranda TKFT reaching relation. -/
def toReachingRel (R : WppRel State) : MirandaDynamics.TKFT.ReachingRel State State :=
  ⟨R.stepRel⟩

@[simp] theorem toReachingRel_rel (R : WppRel State) (s t : State) :
    (R.toReachingRel).rel s t ↔ R.stepRel s t := Iff.rfl

/-- Fixed-point characterization of the reachability nucleus:
`reachabilityNucleus U = U` iff all unreachable states are already in `U`. -/
theorem reachabilityNucleus_fixed_iff (R : WppRel State) (s₀ : State) (U : Set State) :
    (reachabilityNucleus (R := R) s₀) U = U ↔ unreachableFrom (R := R) s₀ ⊆ U := by
  constructor
  · intro h x hxU
    have hx : x ∈ (reachabilityNucleus (R := R) s₀) U := Or.inr hxU
    simp [h] at hx
    exact hx
  · intro h
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx
      · exact h hx
    · intro hx
      exact Or.inl hx

end WppRel
end WPP

namespace WPP
namespace Wolfram
namespace System

universe u v

variable {V : Type u} {P : Type v} (sys : System V P) [DecidableEq V]

/-- Wolfram systems as Miranda TKFT reaching relations (via WPP relation). -/
def toReachingRel : MirandaDynamics.TKFT.ReachingRel (HGraph V) (HGraph V) :=
  (sys.toWppRel).toReachingRel

@[simp] theorem toReachingRel_rel {s t : HGraph V} :
    (sys.toReachingRel).rel s t ↔ Step (sys := sys) s t := Iff.rfl

end System
end Wolfram
end WPP

end HeytingLean
