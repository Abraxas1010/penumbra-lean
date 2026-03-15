import HeytingLean.Magma.Separation.MagmaticClass

namespace HeytingLean.Magma.Separation

open HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A]

def magmatic_completion (φ : Magma A → Prop) : Magma A → Prop :=
  fun x => ∃ y, φ y ∧ x ≤ y

theorem completion_is_magmatic (φ : Magma A → Prop) :
    MagmaticClass { x | magmatic_completion φ x } := by
  intro x hx y hy
  rcases hx with ⟨z, hz, hxz⟩
  exact ⟨z, hz, u.le_trans hy hxz⟩

theorem completion_class_eq (φ : Magma A → Prop) :
    { x | magmatic_completion φ x } =
    { x | ∃ y, y ∈ { z | φ z } ∧ x ≤ y } := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, hxy⟩

end HeytingLean.Magma.Separation
