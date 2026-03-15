import HeytingLean.HossenfelderNoGo.HeytingBoundary.BandConstraint
import HeytingLean.AsymptoticSafety.ScaleSymmetry

namespace HeytingLean.HossenfelderNoGo.Bridge

open HeytingLean.AsymptoticSafety
open HeytingLean.HossenfelderNoGo.HeytingBoundary
open HeytingLean.Renormalization

/-- The asymptotic-safety dimensional ratchet inherits the Hossenfelder non-Boolean boundary at
the ultraviolet scale. -/
theorem uv_boundary_non_boolean (sys : BetaSystem)
    (hBridge : BooleanBoundaryBridge (nucleusAt (rgDimensionalRatchet sys) uvScale)) :
    ¬ isBoolean (nucleusAt (rgDimensionalRatchet sys) uvScale) :=
  boundary_necessarily_non_boolean _ hBridge

end HeytingLean.HossenfelderNoGo.Bridge
