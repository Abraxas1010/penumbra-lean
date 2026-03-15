import HeytingLean.HossenfelderNoGo.HeytingBoundary.GapNonZero

namespace HeytingLean.HossenfelderNoGo.HeytingBoundary

/-- A ratcheted family of boundary nuclei. Higher levels are weaker in the order on `L`. -/
structure NucleusFamily (L : Type*) [SemilatticeInf L] [OrderBot L] where
  nucleusAt : ℕ → BoundaryNucleus L
  weakening : ∀ n m, n ≤ m → ∀ x, (nucleusAt m).R x ≤ (nucleusAt n).R x

theorem observer_dependent_gap
    {L : Type*} [SemilatticeInf L] [OrderBot L]
    (fam : NucleusFamily L) (n : ℕ)
    (hBridge : BooleanBoundaryBridge (fam.nucleusAt n)) :
    ∃ a : L, boundaryGap (fam.nucleusAt n) a ≠ ∅ :=
  gap_nonzero_at_boundary (fam.nucleusAt n) hBridge

end HeytingLean.HossenfelderNoGo.HeytingBoundary
