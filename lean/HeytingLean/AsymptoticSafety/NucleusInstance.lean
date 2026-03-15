import Mathlib.Order.Nucleus
import Mathlib.Data.Set.Lattice
import HeytingLean.Core.Nucleus
import HeytingLean.AsymptoticSafety.FixedPoint

namespace HeytingLean
namespace AsymptoticSafety

open Set Order

/-- Coupling regions ordered by information content: smaller regions are higher. -/
abbrev CouplingRegion := OrderDual (Set CouplingPoint)

def carrier (U : CouplingRegion) : Set CouplingPoint := U

/-- The UV-safe locus carved out by the screened projection. -/
def uvSafeSet (sys : BetaSystem) : Set CouplingPoint :=
  { g | isUVSafe sys g }

/-- RG restriction onto the UV-safe locus. -/
def rgRestrict (sys : BetaSystem) : CouplingRegion → CouplingRegion :=
  fun U => ((carrier U ∩ uvSafeSet sys) : Set CouplingPoint)

def orderNucleus (sys : BetaSystem) : _root_.Nucleus CouplingRegion where
  toFun := rgRestrict sys
  map_inf' := by
    intro A B
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx, hs⟩
      cases hx with
      | inl hA => exact Or.inl ⟨hA, hs⟩
      | inr hB => exact Or.inr ⟨hB, hs⟩
    · intro hx
      rcases hx with hA | hB
      · exact ⟨Or.inl hA.1, hA.2⟩
      · exact ⟨Or.inr hB.1, hB.2⟩
  idempotent' := by
    intro A
    intro x hx
    exact ⟨hx, hx.2⟩
  le_apply' := by
    intro A
    intro x hx
    exact hx.1

def coreNucleus (sys : BetaSystem) : HeytingLean.Core.Nucleus CouplingRegion where
  R := rgRestrict sys
  extensive := by
    intro A
    intro x hx
    exact hx.1
  idempotent := by
    intro A
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, hx.2⟩
  meet_preserving := by
    intro A B
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx, hs⟩
      cases hx with
      | inl hA => exact Or.inl ⟨hA, hs⟩
      | inr hB => exact Or.inr ⟨hB, hs⟩
    · intro hx
      rcases hx with hA | hB
      · exact ⟨Or.inl hA.1, hA.2⟩
      · exact ⟨Or.inr hB.1, hB.2⟩

theorem fixed_region_iff_subset_uvSafe (sys : BetaSystem) (U : CouplingRegion) :
    orderNucleus sys U = U ↔ carrier U ⊆ uvSafeSet sys := by
  constructor
  · intro h x hx
    have hx' : x ∈ carrier ((orderNucleus sys) U) := by
      simpa [h] using hx
    exact hx'.2
  · intro hsubset
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, hsubset hx⟩

/-- Relative negation inside the RG-closed logic: safe complement of a region. -/
def heytingNegation (sys : BetaSystem) (U : CouplingRegion) : CouplingRegion :=
  orderNucleus sys ((carrier U)ᶜ : Set CouplingPoint)

theorem heytingNegation_carrier (sys : BetaSystem) (U : CouplingRegion) :
    carrier (heytingNegation sys U) = (carrier Uᶜ ∩ uvSafeSet sys) := by
  rfl

end AsymptoticSafety
end HeytingLean
