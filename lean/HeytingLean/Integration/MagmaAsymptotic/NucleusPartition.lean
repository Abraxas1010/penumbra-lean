import HeytingLean.AsymptoticSafety.NucleusInstance
import HeytingLean.AsymptoticSafety.RGFlow
import HeytingLean.AsymptoticSafety.Predictions.DarkMatter
import HeytingLean.Magma.Bridge.NucleusProjection
import HeytingLean.Magma.Bridge.ComputationalIrreducibility

namespace HeytingLean.Integration.MagmaAsymptotic

open HeytingLean.AsymptoticSafety

/-- A coupling region is UV-reducible exactly when the AS nucleus fixes it. -/
def UVReducible (sys : BetaSystem) (S : CouplingRegion) : Prop :=
  orderNucleus sys S = S

/-- A coupling region is UV-irreducible exactly when the AS nucleus changes it. -/
def UVIrreducible (sys : BetaSystem) (S : CouplingRegion) : Prop :=
  orderNucleus sys S ≠ S

theorem as_nucleus_partitions (sys : BetaSystem) (S : CouplingRegion) :
    UVReducible sys S ∨ UVIrreducible sys S := by
  by_cases h : orderNucleus sys S = S
  · exact Or.inl h
  · exact Or.inr h

theorem uvSafe_is_reducible (sys : BetaSystem)
    (S : CouplingRegion) (h : carrier S ⊆ uvSafeSet sys) :
    UVReducible sys S := by
  exact (fixed_region_iff_subset_uvSafe sys S).2 h

/-- A concrete portal-positive coupling used to witness regions outside the
UV-safe locus under portal screening. -/
def portalTestPoint : CouplingPoint where
  G_Newton := 0
  cosmological := 0
  topYukawa := 0
  bottomYukawa := 0
  higgsQuartic := 0
  gaugeU1 := 0
  gaugeSU2 := 0
  gaugeSU3 := 0
  portalCoupling := 1

theorem portalTestPoint_mem_portalPositiveRegion :
    portalTestPoint ∈ carrier portalPositiveRegion := by
  show 0 < portalTestPoint.portalCoupling
  simp [portalTestPoint]

theorem portalTestPoint_not_uvSafe (sys : BetaSystem)
    (hscreen : PortalScreeningHypothesis sys) :
    portalTestPoint ∉ uvSafeSet sys := by
  intro hsafe
  have hzero := portal_zero_of_uvSafe_and_screening sys portalTestPoint hscreen hsafe
  simp [portalTestPoint] at hzero

theorem outside_uvSafe_may_be_irreducible (sys : BetaSystem)
    (hscreen : PortalScreeningHypothesis sys) :
    ∃ S : CouplingRegion, ¬(carrier S ⊆ uvSafeSet sys) ∧ UVIrreducible sys S := by
  refine ⟨portalPositiveRegion, ?_, ?_⟩
  · intro hsubset
    exact portalTestPoint_not_uvSafe sys hscreen (hsubset portalTestPoint_mem_portalPositiveRegion)
  · intro hfix
    have hsubset : carrier portalPositiveRegion ⊆ uvSafeSet sys :=
      (fixed_region_iff_subset_uvSafe sys portalPositiveRegion).1 hfix
    exact portalTestPoint_not_uvSafe sys hscreen (hsubset portalTestPoint_mem_portalPositiveRegion)

end HeytingLean.Integration.MagmaAsymptotic
