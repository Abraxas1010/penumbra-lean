import Mathlib.Order.Nucleus
import Mathlib.Data.Set.Lattice
import HeytingLean.Bridges.Flow

/-!
# MirandaDynamics.FixedPoint: “periodic/loop nucleus” (Lean spine)

Many Miranda-style statements relate:

* halting (computation),
* periodicity / closed orbits (dynamics),
* fixed points of a closure operator (algebra/logic).

Re-proving the geometric content (billiards/contact/Navier–Stokes) is out of scope here.
But we can mechanize a clean *algebraic* fact that is ubiquitous in this project:

> A closure operator on sets given by union with a fixed set `U` is a `Nucleus`,
> and its fixed points are exactly the supersets of `U`.

We then specialize `U` to the existing “loop set” predicate over `FlowTraj`
(`HeytingLean.Bridges.Flow.loopSet`), yielding a concrete “periodic nucleus”.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace FixedPoint

open Set

universe u

section UnionNucleus

variable {α : Type u}

/-- The generic “union with U” nucleus on `Set α`. -/
def unionNucleus (U : Set α) : Nucleus (Set α) where
  toInfHom :=
  { toFun := fun S => S ∪ U
    map_inf' := by
      intro S T
      ext x; constructor <;> intro hx
      · rcases hx with hx | hx
        · exact And.intro (Or.inl hx.1) (Or.inl hx.2)
        · exact And.intro (Or.inr hx) (Or.inr hx)
      · rcases hx with ⟨h1, h2⟩
        cases h1 with
        | inl hS =>
          cases h2 with
          | inl hT => exact Or.inl ⟨hS, hT⟩
          | inr hU => exact Or.inr hU
        | inr hU => exact Or.inr hU }
  idempotent' := by
    intro S
    intro x hx
    rcases hx with hx | hx
    · rcases hx with hx | hx
      · exact Or.inl hx
      · exact Or.inr hx
    · exact Or.inr hx
  le_apply' := by
    intro S x hx
    exact Or.inl hx

/-- Characterize fixed points of `unionNucleus`: they are exactly the supersets of `U`. -/
theorem isFixedPoint_unionNucleus_iff (U S : Set α) :
    unionNucleus (α := α) U S = S ↔ U ⊆ S := by
  constructor
  · intro h x hxU
    have : x ∈ unionNucleus (α := α) U S := Or.inr hxU
    simpa [h] using this
  · intro h
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact hx
      · exact h hx
    · intro hx
      exact Or.inl hx

end UnionNucleus

/-! ## Specialization: the repo’s existing “loop nucleus” on trajectories -/

namespace Flow

open HeytingLean.Bridges

abbrev FlowTraj := Bridges.FlowTraj

/-- A convenient alias: the existing “loop nucleus” is a union nucleus. -/
def periodicNucleus (posTol dirCosTol : Float) : Nucleus (Set FlowTraj) :=
  unionNucleus (α := FlowTraj) (Bridges.Flow.loopSet posTol dirCosTol)

theorem periodicNucleus_eq_flowNucleusOsc (posTol dirCosTol : Float) :
    periodicNucleus posTol dirCosTol = Bridges.Flow.flowNucleusOsc posTol dirCosTol := by
  rfl

end Flow

end FixedPoint
end MirandaDynamics
end HeytingLean

