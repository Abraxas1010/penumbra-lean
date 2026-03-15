import HeytingLean.AsymptoticSafety.GravityMatter

namespace HeytingLean
namespace AsymptoticSafety

def portalPositiveSet : Set CouplingPoint := { g | 0 < g.portalCoupling }

def portalPositiveRegion : CouplingRegion := portalPositiveSet

def portalExclusionRegion (sys : BetaSystem) : CouplingRegion :=
  heytingNegation sys portalPositiveRegion

theorem no_simplest_WIMP (sys : BetaSystem)
    (hscreen : PortalScreeningHypothesis sys) :
    uvSafeSet sys ⊆ carrier (portalExclusionRegion sys) := by
  intro g hg
  have hz : g.portalCoupling = 0 := portal_zero_of_uvSafe_and_screening sys g hscreen hg
  refine ⟨?_, hg⟩
  change g ∈ (carrier portalPositiveRegion)ᶜ
  intro hpos
  have hnot : ¬ 0 < g.portalCoupling := by
    simp [hz]
  exact hnot hpos

end AsymptoticSafety
end HeytingLean
