import HeytingLean.HossenfelderNoGo.HeytingBoundary.GapNonZero
import HeytingLean.AsymptoticSafety.ScaleSymmetry
import HeytingLean.Integration.MagmaAsymptotic.NucleusPreserved
import HeytingLean.Integration.MagmaAsymptotic.IrreducibleCouplings

namespace HeytingLean.HossenfelderNoGo.Bridge

open HeytingLean.AsymptoticSafety
open HeytingLean.HossenfelderNoGo.HeytingBoundary
open HeytingLean.Integration.MagmaAsymptotic

/-- The asymptotic-safety UV restriction is a boundary nucleus. -/
def asBoundaryNucleus (sys : BetaSystem) : BoundaryNucleus CouplingRegion :=
  coreNucleus sys

private def eichhornWitnessPoint : CouplingPoint :=
  { gravitationalFixedPoint eichhornBetaSystem.truncation with
    topYukawa := 1 }

private def eichhornWitnessRegion : CouplingRegion :=
  ({eichhornWitnessPoint} : Set CouplingPoint)

theorem as_boundary_non_boolean (sys : BetaSystem)
    (hBridge : BooleanBoundaryBridge (asBoundaryNucleus sys)) :
    ¬ isBoolean (asBoundaryNucleus sys) :=
  boundary_necessarily_non_boolean (asBoundaryNucleus sys) hBridge

theorem eichhorn_topYukawa_screened :
    eichhornBetaSystem.critical.topYukawa +
      eichhornBetaSystem.truncation.yukawaGravityShift ≤ 0 := by
  norm_num [eichhornBetaSystem, eichhornCriticalProfile, eichhornBenchmark]

private theorem eichhorn_witness_not_uv_safe :
    eichhornWitnessPoint ∉ uvSafeSet eichhornBetaSystem := by
  intro hsafe
  have htop :=
    topYukawa_zero_of_uvSafe_and_screening
      eichhornBetaSystem eichhornWitnessPoint eichhorn_topYukawa_screened
      (by simpa [uvSafeSet] using hsafe)
  norm_num [eichhornWitnessPoint, gravitationalFixedPoint] at htop

theorem eichhorn_nucleus_not_boolean :
    ¬ isBoolean (asBoundaryNucleus eichhornBetaSystem) := by
  intro hBool
  have hfix : rgRestrict eichhornBetaSystem eichhornWitnessRegion = eichhornWitnessRegion :=
    hBool eichhornWitnessRegion
  have hwitness_mem : eichhornWitnessPoint ∈ carrier eichhornWitnessRegion := by
    simp [eichhornWitnessRegion, carrier]
  have hwitness_mem_restrict : eichhornWitnessPoint ∈ carrier (rgRestrict eichhornBetaSystem eichhornWitnessRegion) := by
    simpa [hfix] using hwitness_mem
  have hwitness_safe : eichhornWitnessPoint ∈ uvSafeSet eichhornBetaSystem := by
    have hpair : eichhornWitnessPoint ∈ carrier eichhornWitnessRegion ∧
        eichhornWitnessPoint ∈ uvSafeSet eichhornBetaSystem := by
      simpa [rgRestrict, carrier] using hwitness_mem_restrict
    exact hpair.2
  exact eichhorn_witness_not_uv_safe hwitness_safe

/-- The existing asymptotic-safety Heyting gap is a concrete instance of the Hossenfelder
boundary-gap pattern. -/
theorem as_boundary_gap_nonempty (sys : BetaSystem) (hscreen : PortalScreeningHypothesis sys) :
    heytingGap_AS sys portalPositiveRegion ≠ ∅ :=
  portalPositive_has_nonzero_gap sys hscreen

end HeytingLean.HossenfelderNoGo.Bridge
