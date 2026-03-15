import HeytingLean.Magma.Bridge.NucleusProjection

namespace HeytingLean.Magma.Bridge

open HeytingLean
open HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A] [PairEncoding A] [ProductEncoding A]

def heyting_gap (N : MagmaticNucleus A) (x : Magma A) : Set (Magma A) :=
  N.nucleus.R (familyOf x) \ familyOf x

theorem gap_zero_iff_fixed (N : MagmaticNucleus A) (x : Magma A) :
    heyting_gap N x = ∅ ↔ x ∈ omega_R N := by
  constructor
  · intro hGap
    show N.nucleus.R (familyOf x) = familyOf x
    apply Set.Subset.antisymm
    · intro y hy
      by_cases hyfam : y ∈ familyOf x
      · exact hyfam
      · have hygap : y ∈ heyting_gap N x := ⟨hy, hyfam⟩
        have : y ∉ heyting_gap N x := by simp [hGap]
        exact False.elim (this hygap)
    · intro y hy
      exact N.nucleus.extensive (familyOf x) hy
  · intro hFix
    have hEq : N.nucleus.R (familyOf x) = familyOf x := hFix
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hyFam : y ∈ familyOf x := by simpa [hEq] using hy.1
    exact hy.2 hyFam

def intrinsically_irreducible (x : Magma A) : Prop :=
  ∀ N : MagmaticNucleus A, heyting_gap N x ≠ ∅

end HeytingLean.Magma.Bridge
