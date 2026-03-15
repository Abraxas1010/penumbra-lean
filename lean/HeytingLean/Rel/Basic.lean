import Mathlib.CategoryTheory.Grothendieck

/-!
# Rel.Basic

`Prop`-valued relations (a.k.a. profunctors between discrete categories) and their basic operations.

This is a shared core used by:
- `HeytingLean.VETT.Rel` (Phase 10 strict VETT model), and
- `HeytingLean.MirandaDynamics.TKFT` (reaching relations / gluing as relational composition).
-/

namespace HeytingLean
namespace Rel

universe u₁ v₁ u₂ v₂ u₃ v₃

/-- `Prop`-valued relations (discrete-category profunctors). -/
def HRel (α : Type u₁) (β : Type v₁) : Type (max u₁ v₁) :=
  α → β → Prop

namespace RelOps

/-- Restrict a relation along functions `f` and `g` by pre/post-composition. -/
def restrict {α : Type u₁} {β : Type v₁} {α' : Type u₂} {β' : Type v₂}
    (R : HRel α β) (f : α' → α) (g : β' → β) : HRel α' β' :=
  fun a' b' => R (f a') (g b')

@[simp] theorem restrict_apply {α : Type u₁} {β : Type v₁} {α' : Type u₂} {β' : Type v₂}
    (R : HRel α β) (f : α' → α) (g : β' → β) (a' : α') (b' : β') :
    restrict R f g a' b' = R (f a') (g b') :=
  rfl

theorem restrict_id {α : Type u₁} {β : Type v₁} (R : HRel α β) :
    restrict R (fun x => x) (fun y => y) = R :=
  rfl

theorem restrict_comp {α : Type u₁} {β : Type v₁} {α' : Type u₂} {β' : Type v₂}
    {α'' : Type u₃} {β'' : Type v₃}
    (R : HRel α β) (f : α' → α) (g : β' → β) (f' : α'' → α') (g' : β'' → β') :
    restrict (restrict R f g) f' g' = restrict R (fun x => f (f' x)) (fun y => g (g' y)) :=
  rfl

/-- Unit proarrow: equality relation. -/
def unit (α : Type u₁) : HRel α α :=
  fun x y => x = y

@[simp] theorem unit_apply (α : Type u₁) (x y : α) : unit α x y = (x = y) := rfl

/-- “Hom proarrow” induced by two maps into a common codomain. -/
def homProarrow {C : Type u₁} {D₀ : Type u₂} {D₁ : Type u₃} (f : D₀ → C) (g : D₁ → C) :
    HRel D₀ D₁ :=
  fun d₀ d₁ => f d₀ = g d₁

/-- Tensor / profunctor composition (existential composition). -/
def tensor {α : Type u₁} {β : Type v₁} {γ : Type u₂} (P : HRel α β) (Q : HRel β γ) : HRel α γ :=
  fun a c => ∃ b, P a b ∧ Q b c

/-- Nullary product (terminal) proarrow: always true. -/
def top {α : Type u₁} {β : Type v₁} : HRel α β :=
  fun _ _ => True

/-- Binary product of relations: pointwise conjunction. -/
def prod {α : Type u₁} {β : Type v₁} (P Q : HRel α β) : HRel α β :=
  fun a b => P a b ∧ Q a b

/-- Covariant hom (right lifting / end in the `Prop`-valued setting). -/
def covHom {A : Type u₁} {B : Type v₁} {C : Type u₂} (P : HRel A B) (Q : HRel C B) : HRel C A :=
  fun c a => ∀ b, P a b → Q c b

/-- Contravariant hom (left lifting / end in the `Prop`-valued setting). -/
def contraHom {A : Type u₁} {B : Type v₁} {C : Type u₂} (P : HRel A B) (Q : HRel A C) : HRel B C :=
  fun b c => ∀ a, P a b → Q a c

/-!
## Strict restriction commutation

In this strict model these are definitional equalities.
-/

theorem tensor_restrict_strict {A : Type u₁} {B : Type v₁} {C : Type u₂}
    {A' : Type u₃} {C' : Type v₂}
    (P : HRel A B) (Q : HRel B C) (f : A' → A) (g : C' → C) :
    restrict (tensor P Q) f g = tensor (restrict P f (fun x => x)) (restrict Q (fun x => x) g) :=
  rfl

theorem covHom_restrict_strict {A : Type u₁} {B : Type v₁} {C : Type u₂}
    {A' : Type u₃} {C' : Type v₂}
    (P : HRel A B) (Q : HRel C B) (f : C' → C) (g : A' → A) :
    restrict (covHom P Q) f g = covHom (restrict P g (fun x => x)) (restrict Q f (fun x => x)) :=
  rfl

theorem contraHom_restrict_strict {A : Type u₁} {B : Type v₁} {C : Type u₂}
    {B' : Type u₃} {C' : Type v₂}
    (P : HRel A B) (Q : HRel A C) (f : B' → B) (g : C' → C) :
    restrict (contraHom P Q) f g = contraHom (restrict P (fun x => x) f) (restrict Q (fun x => x) g) :=
  rfl

theorem top_restrict_strict {A : Type u₁} {B : Type v₁} {A' : Type u₂} {B' : Type v₂}
    (f : A' → A) (g : B' → B) :
    restrict (top : HRel A B) f g = (top : HRel A' B') :=
  rfl

theorem prod_restrict_strict {A : Type u₁} {B : Type v₁} {A' : Type u₂} {B' : Type v₂}
    (P Q : HRel A B) (f : A' → A) (g : B' → B) :
    restrict (prod P Q) f g = prod (restrict P f g) (restrict Q f g) :=
  rfl

theorem unit_restrict_strict {C : Type u₁} {D₀ : Type u₂} {D₁ : Type u₃}
    (f : D₀ → C) (g : D₁ → C) :
    restrict (unit C) f g = homProarrow f g :=
  rfl

end RelOps

end Rel
end HeytingLean

