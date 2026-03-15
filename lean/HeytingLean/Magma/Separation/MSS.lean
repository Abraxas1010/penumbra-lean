import HeytingLean.Magma.Separation.MagmaticCompletion

namespace HeytingLean.Magma.Separation

open HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A] [PairEncoding A] [ProductEncoding A]
  [SeparationPresentation A]

theorem magmatic_separation_scheme
    (φ : Magma A → Prop) (hMag : MagmaticClass { x | φ x })
    (u0 : Magma A) (hNonempty : ∃ x, x ∈ u0 ∧ φ x) :
    ∃ m : Magma A, ∀ x : Magma A, x ∈ m ↔ x ∈ u0 ∧ φ x := by
  let X : Set (Magma A) := { x | x ∈ u0 ∧ φ x }
  have hX_nonempty : X.Nonempty := by
    rcases hNonempty with ⟨x, hx, hφ⟩
    exact ⟨x, hx, hφ⟩
  have hX_mag : MagmaticClass X := by
    intro x hx y hy
    exact ⟨u.lower_mem hx.1 hy, hMag hx.2 hy⟩
  refine ⟨SeparationPresentation.realize hX_nonempty hX_mag, ?_⟩
  intro x
  simpa [X] using (SeparationPresentation.mem_realize hX_nonempty hX_mag (x := x))

end HeytingLean.Magma.Separation
