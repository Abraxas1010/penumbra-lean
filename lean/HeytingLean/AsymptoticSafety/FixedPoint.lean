import HeytingLean.AsymptoticSafety.RGFlow

namespace HeytingLean
namespace AsymptoticSafety

/-- A fixed-point witness in the linearized truncation. -/
structure FixedPointWitness where
  system : BetaSystem
  point : CouplingPoint
  beta_vanishes : linearizedBeta system point = 0
  uv_safe : isUVSafe system point

/-- Canonical witness: the benchmark gravitational fixed point. -/
def gravitationalWitness (sys : BetaSystem) : FixedPointWitness where
  system := sys
  point := gravitationalFixedPoint sys.truncation
  beta_vanishes := linearizedBeta_at_fixedPoint sys
  uv_safe := gravitationalFixedPoint_isUVSafe sys

/-- A fixed-point witness sits at zero squared distance from itself. -/
theorem witness_zero_self_distance (w : FixedPointWitness) :
    squaredDistanceTo w.point w.point = 0 := by
  simp [squaredDistanceTo]

/-- Physical assumptions used by the higher prediction and exclusion theorems. -/
structure PhysicalAssumptions (sys : BetaSystem) where
  euclideanModel : EuclideanTruncation sys.truncation
  portalScreening : PortalScreeningHypothesis sys

theorem gravitationalWitness_respects_assumptions
    (sys : BetaSystem) :
    portalOff (gravitationalWitness sys).point := by
  exact gravitationalFixedPoint_portalOff sys.truncation

end AsymptoticSafety
end HeytingLean
