import HeytingLean.HossenfelderNoGo.HeytingBoundary.DynamicGap

namespace HeytingLean.HossenfelderNoGo.HeytingBoundary

/-- A gap band consists of a family of nuclei whose gaps remain nontrivial but globally bounded. -/
structure GapBand (L : Type*) [SemilatticeInf L] [OrderBot L] [OrderTop L] where
  family : NucleusFamily L
  gap_positive : ∀ n, ∃ a : L, boundaryGap (family.nucleusAt n) a ≠ ∅
  gap_bounded_above : ∃ a_max : L, ∀ n x, (family.nucleusAt n).R x ≤ a_max

/-- Every ratcheted nucleus family yields a canonical gap band using `⊤` as a coarse global
upper bound. -/
def GapBand.fromFamily
    {L : Type*} [SemilatticeInf L] [OrderBot L] [OrderTop L]
    (fam : NucleusFamily L)
    (hBridge : ∀ n, BooleanBoundaryBridge (fam.nucleusAt n)) : GapBand L where
  family := fam
  gap_positive := fun n => observer_dependent_gap fam n (hBridge n)
  gap_bounded_above := ⟨⊤, fun _ _ => le_top⟩

end HeytingLean.HossenfelderNoGo.HeytingBoundary
