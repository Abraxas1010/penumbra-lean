import HeytingLean.MirandaDynamics.TKFT.Reaching
import HeytingLean.MirandaDynamics.Undecidability.Transfers

/-!
# MirandaDynamics: external-results interfaces (no axioms)

The Miranda/TKFT/billiards/fluids papers supply deep geometric and analytic constructions.
Re-proving those constructions in Lean is a major project.

To keep the formalization honest *and* usable, we package the boundary to external results as
explicit Lean **structures** (not axioms). Downstream theorems can then be stated as:

> `∀ h : ExternalConstruction …, …`

so that:
- Lean checks the logic downstream of the construction,
- the construction itself is clearly marked as “external data”,
- there is no hidden postulate or proof-gap dependency.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace External

open TKFT
open Undecidability

universe u v

/-! ## TKFT-style reaching functions (as relations, with a principled upgrade to `Part`) -/

/-- A TKFT-style reaching relation, together with a uniqueness hypothesis that allows it to be
viewed as a (chosen) partial function. -/
structure TKFTConstruction (α : Type u) (β : Type v) : Type (max u v) where
  reach : TKFT.ReachingRel α β
  functional : TKFT.ReachingRel.Functional reach

/-- The associated reaching function, obtained by choice from the reaching relation. -/
noncomputable def reachingFunction {α : Type u} {β : Type v} (h : TKFTConstruction α β) :
    α → Part β :=
  TKFT.ReachingRel.toPart (R := h.reach) h.functional

theorem reachingFunction_spec {α : Type u} {β : Type v} (h : TKFTConstruction α β) (a : α) (b : β) :
    b ∈ reachingFunction h a ↔ h.reach.rel a b :=
  TKFT.ReachingRel.toPart_spec (R := h.reach) h.functional a b

/-- A constructive “inverse-on-image” view that does not require choice. -/
def reachingImage {α : Type u} {β : Type v} (h : TKFTConstruction α β) (a : α) : Type v :=
  TKFT.ReachingRel.Image h.reach a

/-! ## Undecidability transfer boundary (halting → physical predicate) -/

/-- Package the sole ingredient needed for the undecidability-transfer step:
a computable many-one reduction from halting to some predicate `P`. -/
structure HaltingReduction {β : Type v} [Primcodable β] (n : ℕ) (P : β → Prop) : Type (max v 1) where
  red : Undecidability.ManyOne (p := Undecidability.Halting.Halts n) (q := P)

theorem not_computable_of_haltingReduction {β : Type v} [Primcodable β] {P : β → Prop} (n : ℕ)
    (h : HaltingReduction (β := β) n P) : ¬ComputablePred P :=
  Undecidability.Halting.not_computable_of_halting_reduces (n := n) h.red

end External
end MirandaDynamics
end HeytingLean
