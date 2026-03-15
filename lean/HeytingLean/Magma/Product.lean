import HeytingLean.Magma.IntendedCollateral

namespace HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A] [PairEncoding A]

class ProductEncoding (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A] [PairEncoding A] where
  product : A → A → Magma A → Magma A → Magma A
  pair_sub_product : ∀ {a₀ a₁ : A} (h : Incomparable a₀ a₁) {x y : Magma A},
    magmatic_pair a₀ a₁ h x y ≤ product a₀ a₁ x y
  product_mono : ∀ {a₀ a₁ : A} {x x' y y' : Magma A},
    x ≤ x' → y ≤ y' → product a₀ a₁ x y ≤ product a₀ a₁ x' y'

variable [ProductEncoding A]

def magmatic_product (a₀ a₁ : A) (_h : Incomparable a₀ a₁) (x y : Magma A) : Magma A :=
  ProductEncoding.product a₀ a₁ x y

def weak_product (a₀ a₁ : A) (h : Incomparable a₀ a₁) (x y : Magma A) : Set (Magma A) :=
  { p | ∃ z w, z ≤ x ∧ w ≤ y ∧ p = magmatic_pair a₀ a₁ h z w }

theorem product_same_pairs (a₀ a₁ : A) (h : Incomparable a₀ a₁) (x y : Magma A)
    {p : Magma A} (hp : p ∈ weak_product a₀ a₁ h x y) :
    p ≤ magmatic_product a₀ a₁ h x y := by
  rcases hp with ⟨z, w, hz, hw, rfl⟩
  exact u.le_trans
    (ProductEncoding.pair_sub_product h)
    (ProductEncoding.product_mono hz hw)

end HeytingLean.Magma
