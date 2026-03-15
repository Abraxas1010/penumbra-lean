import HeytingLean.Magma.Bridge.NucleusProjection
import HeytingLean.Magma.Bridge.HeytingGapMeasure
import HeytingLean.Magma.Separation.MSS

namespace HeytingLean.Magma.Bridge

open HeytingLean.Magma
open HeytingLean.Magma.Separation

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A] [PairEncoding A] [ProductEncoding A]

def ComputationallyIrreducible (N : MagmaticNucleus A) (x : Magma A) : Prop :=
  x ∉ omega_R N

theorem irreducible_nonempty (N : MagmaticNucleus A)
    (h : ∃ x : Magma A, x ∉ omega_R N) :
    (irreducible_complement N).Nonempty := h

theorem irreducible_has_nonzero_gap (N : MagmaticNucleus A) {x : Magma A}
    (hx : x ∈ irreducible_complement N) :
    heyting_gap N x ≠ ∅ := by
  intro hGap
  exact hx ((gap_zero_iff_fixed N x).1 hGap)

end HeytingLean.Magma.Bridge
