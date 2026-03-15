import Mathlib.Data.Part
import HeytingLean.Rel.Basic

/-!
# MirandaDynamics.TKFT: reaching relations/functions (Lean spine)

The TKFT papers formalize computation via **reaching functions** on (clean) dynamical bordisms.

Re-proving the analytic/differential-topological constructions is out of scope for this repo in the
near term. What we *can* mechanize now, without axioms:

1. A minimal, abstract notion of a **reaching relation** `α ↝ β`.
2. Relational composition (gluing bordisms) and identity (tube bordism) laws.
3. A principled “reaching function” as a `Part β` when the output is unique.

This file is the reusable spine needed to state and audit Miranda-style results in Lean.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace TKFT

universe u v w

/-- A TKFT-style reaching relation between “input boundary” `α` and “output boundary” `β`. -/
structure ReachingRel (α : Type u) (β : Type v) : Type (max u v) where
  rel : HeytingLean.Rel.HRel α β

namespace ReachingRel

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*}

/-- Extensionality for reaching relations. -/
@[ext] theorem ext {R S : ReachingRel α β} (h : ∀ a b, R.rel a b ↔ S.rel a b) : R = S := by
  cases R with
  | mk r =>
    cases S with
    | mk s =>
      have : r = s := funext (fun a => funext (fun b => propext (h a b)))
      cases this
      rfl

/-- Identity reaching relation (“tube bordism”). -/
def id (α : Type u) : ReachingRel α α :=
  ⟨HeytingLean.Rel.RelOps.unit α⟩

/-- Relational composition (“gluing bordisms along the shared boundary”). -/
def comp (R : ReachingRel α β) (S : ReachingRel β γ) : ReachingRel α γ :=
  ⟨HeytingLean.Rel.RelOps.tensor R.rel S.rel⟩

@[simp] theorem id_rel (a b : α) : (id α).rel a b ↔ a = b := Iff.rfl

theorem id_left (R : ReachingRel α β) : comp (id α) R = R := by
  ext a b
  constructor
  · rintro ⟨a', ha, hR⟩
    simpa [id, comp, HeytingLean.Rel.RelOps.unit] using (show a' = a from ha.symm ▸ rfl) ▸ hR
  · intro hR
    refine ⟨a, rfl, hR⟩

theorem id_right (R : ReachingRel α β) : comp R (id β) = R := by
  ext a b
  constructor
  · rintro ⟨b', hR, hb⟩
    simpa [id, comp, HeytingLean.Rel.RelOps.unit] using hb ▸ hR
  · intro hR
    refine ⟨b, hR, rfl⟩

theorem assoc (R : ReachingRel α β) (S : ReachingRel β γ) (T : ReachingRel γ δ) :
    comp (comp R S) T = comp R (comp S T) := by
  ext a d
  constructor
  · rintro ⟨c, ⟨b, hR, hS⟩, hT⟩
    exact ⟨b, hR, ⟨c, hS, hT⟩⟩
  · rintro ⟨b, hR, ⟨c, hS, hT⟩⟩
    exact ⟨c, ⟨b, hR, hS⟩, hT⟩

/-! ## Reaching relations as (partial) functions -/

/-- Functional output hypothesis: for each input there is at most one reachable output. -/
def Functional (R : ReachingRel α β) : Prop :=
  ∀ a b₁ b₂, R.rel a b₁ → R.rel a b₂ → b₁ = b₂

/-- Witness-carrying “inverse-on-image” view: a reachable output together with its proof. -/
def Image (R : ReachingRel α β) (a : α) : Type v :=
  { b : β // R.rel a b }

namespace Image

variable (R : ReachingRel α β) (a : α)

@[simp] theorem mk_rel (b : β) (h : R.rel a b) : (⟨b, h⟩ : R.Image a).1 = b := rfl

end Image

/-- A reaching *partial function* derived from a reaching relation, assuming uniqueness of outputs.

This definition is intentionally `noncomputable`: it upgrades an existence statement into chosen
output data (the same “choice vs image” split used elsewhere in the repo). -/
noncomputable def toPart (R : ReachingRel α β) (_hFun : R.Functional) : α → Part β := by
  classical
  intro a
  refine ⟨(∃ b, R.rel a b), fun h => Classical.choose h⟩

theorem toPart_spec {R : ReachingRel α β} (hFun : R.Functional) (a : α) (b : β) :
    b ∈ (toPart (R := R) hFun a) ↔ R.rel a b := by
  classical
  constructor
  · rintro ⟨hDom, hb⟩
    have h0 : R.rel a (Classical.choose hDom) := Classical.choose_spec hDom
    exact hb ▸ h0
  · intro hR
    refine ⟨⟨b, hR⟩, ?_⟩
    -- show chosen output equals `b`
    show Classical.choose ⟨b, hR⟩ = b
    exact hFun a (Classical.choose ⟨b, hR⟩) b (Classical.choose_spec ⟨b, hR⟩) hR

end ReachingRel

end TKFT
end MirandaDynamics
end HeytingLean
