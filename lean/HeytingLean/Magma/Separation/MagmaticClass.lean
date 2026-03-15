import HeytingLean.Magma.Function

namespace HeytingLean.Magma.Separation

open HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A]

def MagmaticClass (X : Set (Magma A)) : Prop :=
  ∀ ⦃x : Magma A⦄, x ∈ X → ∀ ⦃y : Magma A⦄, y ≤ x → y ∈ X

def ScaleInvariant (φ : Magma A → Prop) : Prop :=
  ∀ ⦃x : Magma A⦄, φ x → ∀ ⦃y : Magma A⦄, y ≤ x → φ y

theorem scaleInvariant_iff_magmatic (φ : Magma A → Prop) :
    ScaleInvariant φ ↔ MagmaticClass { x | φ x } := by
  rfl

class SeparationPresentation (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A]
    [PairEncoding A] [ProductEncoding A] where
  realize : ∀ {X : Set (Magma A)}, X.Nonempty → MagmaticClass X → Magma A
  mem_realize : ∀ {X : Set (Magma A)} (hN : X.Nonempty) (hM : MagmaticClass X) {x : Magma A},
    x ∈ realize hN hM ↔ x ∈ X

end HeytingLean.Magma.Separation
