import HeytingLean.Magma.Function
import HeytingLean.Magma.Separation.MagmaticClass
import HeytingLean.Core.Nucleus

namespace HeytingLean.Magma.Bridge

open HeytingLean
open HeytingLean.Magma
open HeytingLean.Magma.Separation

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A] [PairEncoding A] [ProductEncoding A]

def familyOf (x : Magma A) : Set (Magma A) := { y | y ≤ x }

def ResolvesCollateralAt (a₀ a₁ : A) (h : Incomparable a₀ a₁)
    (x y : Magma A) (F : MagmaticSemiFunction a₀ a₁ h x y) : Prop :=
  ∃ G : MagmaticFunction a₀ a₁ h x y, G.intendedPairs = F.intendedPairs

structure MagmaticNucleus (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A]
    [PairEncoding A] [ProductEncoding A] where
  nucleus : Core.Nucleus (Set (Magma A))
  preserves_magmatic : ∀ x : Magma A, MagmaticClass (nucleus.R (familyOf x))
  resolves_on_fixed :
    ∀ {a₀ a₁ : A} (h : Incomparable a₀ a₁) {x y : Magma A},
      nucleus.R (familyOf x) = familyOf x →
      nucleus.R (familyOf y) = familyOf y →
      (F : MagmaticSemiFunction a₀ a₁ h x y) →
      ResolvesCollateralAt (a₀ := a₀) (a₁ := a₁) h x y F

def omega_R (N : MagmaticNucleus A) : Set (Magma A) :=
  { x | N.nucleus.R (familyOf x) = familyOf x }

def irreducible_complement (N : MagmaticNucleus A) : Set (Magma A) :=
  { x | x ∉ omega_R N }

theorem fixed_core_magmatic (N : MagmaticNucleus A) (x : Magma A) :
    MagmaticClass (N.nucleus.R (familyOf x)) :=
  N.preserves_magmatic x

end HeytingLean.Magma.Bridge
