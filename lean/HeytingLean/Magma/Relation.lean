import HeytingLean.Magma.Product

namespace HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A]

structure MagmaticRelation (a₀ a₁ : A) (h : Incomparable a₀ a₁) (x y : Magma A) where
  intendedPairs : Set (Magma A × Magma A)
  fst_subset : ∀ ⦃z w : Magma A⦄, (z, w) ∈ intendedPairs → z ≤ x
  snd_subset : ∀ ⦃z w : Magma A⦄, (z, w) ∈ intendedPairs → w ≤ y

def MagmaticRelation.dom {a₀ a₁ : A} {h : Incomparable a₀ a₁} {x y : Magma A}
    (R : MagmaticRelation a₀ a₁ h x y) : Set (Magma A) :=
  { z | ∃ w, (z, w) ∈ R.intendedPairs }

def MagmaticRelation.ran {a₀ a₁ : A} {h : Incomparable a₀ a₁} {x y : Magma A}
    (R : MagmaticRelation a₀ a₁ h x y) : Set (Magma A) :=
  { w | ∃ z, (z, w) ∈ R.intendedPairs }

theorem MagmaticRelation.dom_subset {a₀ a₁ : A} {h : Incomparable a₀ a₁}
    {x y : Magma A} (R : MagmaticRelation a₀ a₁ h x y) {z : Magma A}
    (hz : z ∈ R.dom) : z ≤ x := by
  rcases hz with ⟨w, hw⟩
  exact R.fst_subset hw

theorem MagmaticRelation.ran_subset {a₀ a₁ : A} {h : Incomparable a₀ a₁}
    {x y : Magma A} (R : MagmaticRelation a₀ a₁ h x y) {w : Magma A}
    (hw : w ∈ R.ran) : w ≤ y := by
  rcases hw with ⟨z, hz⟩
  exact R.snd_subset hz

end HeytingLean.Magma
