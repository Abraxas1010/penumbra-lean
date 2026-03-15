import HeytingLean.AsymptoticSafety.BetaFunctions

namespace HeytingLean
namespace AsymptoticSafety

/-- Euler/RK-style step control in the pure `ℝ` layer. -/
structure RGStepConfig where
  stepSize : ℝ

/-- One explicit Euler step for the linearized beta system. -/
def eulerStep (cfg : RGStepConfig) (sys : BetaSystem) (g : CouplingPoint) : CouplingPoint :=
  g + cfg.stepSize • linearizedBeta sys g

/-- Project screened directions to the UV-safe fixed-point values. -/
noncomputable def projectToUVSafe (sys : BetaSystem) (g : CouplingPoint) : CouplingPoint :=
  let fp := gravitationalFixedPoint sys.truncation
  {
    G_Newton := if sys.critical.G_Newton ≤ 0 then fp.G_Newton else g.G_Newton
    cosmological := if sys.critical.cosmological ≤ 0 then fp.cosmological else g.cosmological
    topYukawa := if sys.critical.topYukawa + sys.truncation.yukawaGravityShift ≤ 0
      then fp.topYukawa else g.topYukawa
    bottomYukawa := if sys.critical.bottomYukawa + sys.truncation.yukawaGravityShift ≤ 0
      then fp.bottomYukawa else g.bottomYukawa
    higgsQuartic := if sys.critical.higgsQuartic + sys.truncation.quarticGravityShift ≤ 0
      then fp.higgsQuartic else g.higgsQuartic
    gaugeU1 := if sys.critical.gaugeU1 ≤ 0 then fp.gaugeU1 else g.gaugeU1
    gaugeSU2 := if sys.critical.gaugeSU2 ≤ 0 then fp.gaugeSU2 else g.gaugeSU2
    gaugeSU3 := if sys.critical.gaugeSU3 ≤ 0 then fp.gaugeSU3 else g.gaugeSU3
    portalCoupling := if sys.critical.portalCoupling + sys.truncation.portalGravityShift ≤ 0
      then fp.portalCoupling else g.portalCoupling
  }

def isUVSafe (sys : BetaSystem) (g : CouplingPoint) : Prop :=
  projectToUVSafe sys g = g

theorem projectToUVSafe_idempotent (sys : BetaSystem) (g : CouplingPoint) :
    projectToUVSafe sys (projectToUVSafe sys g) = projectToUVSafe sys g := by
  ext
  · by_cases h : sys.critical.G_Newton ≤ 0 <;> simp [projectToUVSafe, h]
  · by_cases h : sys.critical.cosmological ≤ 0 <;> simp [projectToUVSafe, h]
  · by_cases h : sys.critical.topYukawa + sys.truncation.yukawaGravityShift ≤ 0
    <;> simp [projectToUVSafe, h]
  · by_cases h : sys.critical.bottomYukawa + sys.truncation.yukawaGravityShift ≤ 0
    <;> simp [projectToUVSafe, h]
  · by_cases h : sys.critical.higgsQuartic + sys.truncation.quarticGravityShift ≤ 0
    <;> simp [projectToUVSafe, h]
  · by_cases h : sys.critical.gaugeU1 ≤ 0 <;> simp [projectToUVSafe, h]
  · by_cases h : sys.critical.gaugeSU2 ≤ 0 <;> simp [projectToUVSafe, h]
  · by_cases h : sys.critical.gaugeSU3 ≤ 0 <;> simp [projectToUVSafe, h]
  · by_cases h : sys.critical.portalCoupling + sys.truncation.portalGravityShift ≤ 0
    <;> simp [projectToUVSafe, h]

theorem gravitationalFixedPoint_isUVSafe (sys : BetaSystem) :
    isUVSafe sys (gravitationalFixedPoint sys.truncation) := by
  simp [isUVSafe, projectToUVSafe, gravitationalFixedPoint]

theorem topYukawa_zero_of_uvSafe_and_screening
    (sys : BetaSystem) (g : CouplingPoint)
    (hscreen : sys.critical.topYukawa + sys.truncation.yukawaGravityShift ≤ 0)
    (hsafe : isUVSafe sys g) :
    g.topYukawa = 0 := by
  have htop := congrArg CouplingPoint.topYukawa hsafe
  simp [projectToUVSafe, gravitationalFixedPoint] at htop
  have hzero : 0 = g.topYukawa := by
    exact htop hscreen
  exact hzero.symm

theorem portal_zero_of_uvSafe_and_screening
    (sys : BetaSystem) (g : CouplingPoint)
    (hscreen : PortalScreeningHypothesis sys)
    (hsafe : isUVSafe sys g) :
    g.portalCoupling = 0 := by
  have hportal := congrArg CouplingPoint.portalCoupling hsafe
  simp [projectToUVSafe, gravitationalFixedPoint] at hportal
  have hzero : 0 = g.portalCoupling := by
    exact hportal hscreen
  exact hzero.symm

end AsymptoticSafety
end HeytingLean
