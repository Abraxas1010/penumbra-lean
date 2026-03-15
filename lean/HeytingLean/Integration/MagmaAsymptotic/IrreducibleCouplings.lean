import HeytingLean.Integration.MagmaAsymptotic.NucleusPartition
import HeytingLean.AsymptoticSafety.Predictions.DarkMatter
import HeytingLean.Magma.Bridge.HeytingGapMeasure

namespace HeytingLean.Integration.MagmaAsymptotic

open HeytingLean.AsymptoticSafety

/-- The AS gap is the part of a region discarded by UV restriction. This is
the reductive analogue of the magmatic gap. -/
def heytingGap_AS (sys : BetaSystem) (S : CouplingRegion) : Set CouplingPoint :=
  carrier S \ carrier (orderNucleus sys S)

theorem gap_zero_iff_reducible (sys : BetaSystem) (S : CouplingRegion) :
    heytingGap_AS sys S = ∅ ↔ UVReducible sys S := by
  constructor
  · intro hGap
    apply Set.Subset.antisymm
    · intro x hx
      exact hx.1
    · intro x hx
      by_cases hxR : x ∈ carrier (orderNucleus sys S)
      · exact hxR
      · have hxGap : x ∈ heytingGap_AS sys S := ⟨hx, hxR⟩
        rw [hGap] at hxGap
        exact False.elim hxGap
  · intro hFix
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hxGap
    have hxR : x ∈ carrier (orderNucleus sys S) := by
      rw [hFix]
      exact hxGap.1
    exact hxGap.2 hxR

theorem portalPositive_has_nonzero_gap (sys : BetaSystem)
    (hscreen : PortalScreeningHypothesis sys) :
    heytingGap_AS sys portalPositiveRegion ≠ ∅ := by
  intro hGap
  have hFix : UVReducible sys portalPositiveRegion :=
    (gap_zero_iff_reducible sys portalPositiveRegion).1 hGap
  have hsubset : carrier portalPositiveRegion ⊆ uvSafeSet sys :=
    (fixed_region_iff_subset_uvSafe sys portalPositiveRegion).1 hFix
  exact portalTestPoint_not_uvSafe sys hscreen (hsubset portalTestPoint_mem_portalPositiveRegion)

theorem gap_analogy_statement (sys : BetaSystem) (S : CouplingRegion) :
    heytingGap_AS sys S ≠ ∅ ↔ UVIrreducible sys S := by
  constructor
  · intro hGap hFix
    exact hGap ((gap_zero_iff_reducible sys S).2 hFix)
  · intro hIrr hGap
    exact hIrr ((gap_zero_iff_reducible sys S).1 hGap)

end HeytingLean.Integration.MagmaAsymptotic
