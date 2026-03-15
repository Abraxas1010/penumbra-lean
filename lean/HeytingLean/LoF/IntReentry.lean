import HeytingLean.LoF.PrimaryAlgebra

namespace HeytingLean
namespace LoF

/-- Interior-style nucleus on a primary algebra.

R as logic-extraction (domain-specific interior): `act : α → α` plays the
role of a stabilization operator that extracts the domain’s self-consistent
core. Its fixed points form the Heyting algebra `Ω_R` (constructive logic of
stable configurations). Laws: deflationary, idempotent, monotone, and
∧-preserving. -/
structure IntNucleus (α : Type u) [PrimaryAlgebra α] where
  act : α → α
  monotone : Monotone act
  idempotent : ∀ a, act (act a) = act a
  apply_le : ∀ a, act a ≤ a
  map_inf : ∀ a b, act (a ⊓ b) = act a ⊓ act b

namespace IntNucleus

variable {α : Type u} [PrimaryAlgebra α]

@[simp] lemma apply_inf (N : IntNucleus α) (a b : α) :
    N.act (a ⊓ b) = N.act a ⊓ N.act b := N.map_inf a b

@[simp] lemma idem (N : IntNucleus α) (a : α) : N.act (N.act a) = N.act a :=
  N.idempotent a

end IntNucleus

/-- Interior-style re-entry packaging. -/
structure IntReentry (α : Type u) [PrimaryAlgebra α] where
  nucleus : IntNucleus α

namespace IntReentry

variable {α : Type u} [PrimaryAlgebra α]

instance : CoeFun (IntReentry α) (fun _ => α → α) where
  coe R := R.nucleus.act

@[simp] lemma coe_nucleus (R : IntReentry α) : R.nucleus.act = R := rfl

@[simp] lemma idempotent (R : IntReentry α) (a : α) : R (R a) = R a :=
  R.nucleus.idempotent _

@[simp] lemma apply_le (R : IntReentry α) (a : α) : R a ≤ a :=
  R.nucleus.apply_le a

lemma map_inf (R : IntReentry α) (a b : α) : R (a ⊓ b) = R a ⊓ R b :=
  R.nucleus.map_inf a b

/-- Fixed points of the interior nucleus. -/
abbrev Omega (R : IntReentry α) : Type u := {a : α // R a = a}

namespace Omega

variable (R : IntReentry α)

def mk (a : α) (h : R a = a) : R.Omega := ⟨a, h⟩

@[simp] lemma coe_mk (a : α) (h : R a = a) : ((mk (R := R) a h : R.Omega) : α) = a := rfl

@[simp] lemma apply_coe (a : R.Omega) : R (a : α) = a := by
  simpa using a.property

end Omega

end IntReentry

end LoF
end HeytingLean
