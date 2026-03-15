import HeytingLean.Magma.Relation

namespace HeytingLean.Magma

open Classical

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A]

structure MagmaticSemiFunction (a₀ a₁ : A) (h : Incomparable a₀ a₁) (x y : Magma A)
    extends MagmaticRelation a₀ a₁ h x y where
  intended_functional : ∀ ⦃z w₁ w₂ : Magma A⦄,
    (z, w₁) ∈ intendedPairs → (z, w₂) ∈ intendedPairs → w₁ = w₂

structure MagmaticFunction (a₀ a₁ : A) (h : Incomparable a₀ a₁) (x y : Magma A)
    extends MagmaticSemiFunction a₀ a₁ h x y where
  has_greatest : ∀ ⦃z : Magma A⦄, z ∈ toMagmaticRelation.dom →
    ∃ w, (z, w) ∈ intendedPairs ∧ ∀ w', (z, w') ∈ intendedPairs → w' ≤ w

theorem disjoint_domain_implies_function (a₀ a₁ : A) (h : Incomparable a₀ a₁)
    {x y : Magma A} (F : MagmaticSemiFunction a₀ a₁ h x y)
    (_h_disj : Pairwise fun z z' : Magma A => z ≠ z') :
    ∃ G : MagmaticFunction a₀ a₁ h x y,
      G.toMagmaticSemiFunction.toMagmaticRelation.intendedPairs = F.intendedPairs := by
  classical
  refine ⟨{ toMagmaticSemiFunction := F, has_greatest := ?_ }, rfl⟩
  intro z hz
  rcases hz with ⟨w, hw⟩
  refine ⟨w, hw, ?_⟩
  intro w' hw'
  simpa [F.intended_functional hw' hw] using u.le_refl w'

end HeytingLean.Magma
