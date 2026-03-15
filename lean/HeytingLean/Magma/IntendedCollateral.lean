import HeytingLean.Magma.OrderedPair

namespace HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A]

/-- A generated magma together with its intended generators. -/
structure GeneratedMagma (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A] where
  generators : Set (Magma A)
  magma : Magma A
  generators_subset : ∀ ⦃x : Magma A⦄, x ∈ generators → x ≤ magma

def intended (g : GeneratedMagma A) : Set (Magma A) := g.generators

def collateral (g : GeneratedMagma A) : Set (Magma A) :=
  { x | x ≤ g.magma ∧ x ∉ g.generators }

theorem intended_subset (g : GeneratedMagma A) {x : Magma A} (hx : x ∈ intended g) :
    x ≤ g.magma :=
  g.generators_subset hx

theorem collateral_subset (g : GeneratedMagma A) {x : Magma A} (hx : x ∈ collateral g) :
    x ≤ g.magma :=
  hx.1

theorem collateral_nonempty (g : GeneratedMagma A)
    (h : ∃ x : Magma A, x ≤ g.magma ∧ x ∉ g.generators) :
    (collateral g).Nonempty := by
  rcases h with ⟨x, hx, hnot⟩
  exact ⟨x, hx, hnot⟩

end HeytingLean.Magma
