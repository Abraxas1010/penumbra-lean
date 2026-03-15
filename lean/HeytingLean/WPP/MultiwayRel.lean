import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Relation
import Mathlib.Order.Nucleus

/-!
# WPP.MultiwayRel — relation-based multiway semantics (enumeration-free)

`HeytingLean.WPP.Multiway` is intentionally **finite**: one-step successors are a `Finset`.
For many mathematical settings (e.g. infinite state spaces), we still want a *multiway*
semantics, but without committing to an enumerator.

This module provides the enumeration-free companion interface:

* `WppRel` is a one-step **relation** `stepRel : State → State → Prop`;
* `StepStar` is its reflexive–transitive closure (`Relation.ReflTransGen`);
* `JR` is the forward-invariance **kernel** on `Set State`:
  `JR(U) = { s | forwardCone(s) ⊆ U }`;
* `reachabilityNucleus` packages the repo's **inflationary nucleus** convention by
  unioning a fixed “unreachable” set into every predicate.

This file is used to model Wolfram systems “beyond finiteness”, where we can reason about
reachability/cones without a bounded finite exploration.
-/

namespace HeytingLean
namespace WPP

open Set

universe u

/-- Enumeration-free multiway interface: a one-step relation on states. -/
structure WppRel (State : Type u) where
  stepRel : State → State → Prop

namespace WppRel

variable {State : Type u} (R : WppRel State)

/-- Reflexive–transitive closure of the one-step relation. -/
abbrev StepStar : State → State → Prop :=
  Relation.ReflTransGen R.stepRel

/-- Forward cone of a state under the relation. -/
def cone (s : State) : Set State := fun t => StepStar (R := R) s t

/-- Kernel view: `JR U s` means the forward cone of `s` is contained in `U`. -/
def JR (U : Set State) : Set State := fun s => ∀ t, StepStar (R := R) s t → U t

namespace JR

variable {R}

lemma mono : Monotone (JR (R := R)) := by
  intro U V hUV s hs t hst
  exact hUV (hs _ hst)

lemma contractive (U : Set State) : JR (R := R) U ⊆ U := by
  intro s hs
  exact hs s (Relation.ReflTransGen.refl)

lemma idem (U : Set State) : JR (R := R) (JR (R := R) U) = JR (R := R) U := by
  ext s
  constructor
  · intro hs t hst
    exact (contractive (R := R) (U := U)) (hs t hst)
  · intro hs t hst u htu
    exact hs u (Relation.ReflTransGen.trans hst htu)

lemma inf (U V : Set State) :
    JR (R := R) (U ∩ V) = JR (R := R) U ∩ JR (R := R) V := by
  ext s
  constructor
  · intro hs
    refine And.intro ?_ ?_
    · intro t hst
      exact (hs t hst).1
    · intro t hst
      exact (hs t hst).2
  · rintro ⟨hsU, hsV⟩ t hst
    exact And.intro (hsU t hst) (hsV t hst)

end JR

/-! ## Inflationary nucleus packaging (LoF convention) -/

section Nucleus

variable (s₀ : State)

/-- States unreachable from the chosen base state `s₀`. -/
def unreachableFrom : Set State :=
  {s | ¬ StepStar (R := R) s₀ s}

/-- Inflationary nucleus on predicates: “treat unreachable states as vacuously admissible”
by unioning them into every predicate. -/
def reachabilityNucleus : Nucleus (Set State) where
  toFun U := U ∪ unreachableFrom (R := R) s₀
  map_inf' U V := by
    ext s
    constructor
    · intro hs
      rcases hs with hs | hunr
      · exact ⟨Or.inl hs.1, Or.inl hs.2⟩
      · exact ⟨Or.inr hunr, Or.inr hunr⟩
    · rintro ⟨hsU, hsV⟩
      cases hsU with
      | inl hsU =>
          cases hsV with
          | inl hsV => exact Or.inl ⟨hsU, hsV⟩
          | inr hunr => exact Or.inr hunr
      | inr hunr =>
          exact Or.inr hunr
  idempotent' U := by
    intro s hs
    rcases hs with hs | hunr
    · exact hs
    · exact Or.inr hunr
  le_apply' U := by
    intro s hs
    exact Or.inl hs

@[simp] lemma reachabilityNucleus_apply (U : Set State) :
    reachabilityNucleus (R := R) s₀ U = U ∪ unreachableFrom (R := R) s₀ := rfl

end Nucleus

end WppRel

end WPP
end HeytingLean

