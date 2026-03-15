import HeytingLean.AsymptoticSafety.CouplingSpace

namespace HeytingLean
namespace AsymptoticSafety

/-- A diagonal linearized stability matrix encoded by critical exponents. -/
structure CriticalExponentProfile where
  G_Newton : ℝ
  cosmological : ℝ
  topYukawa : ℝ
  bottomYukawa : ℝ
  higgsQuartic : ℝ
  gaugeU1 : ℝ
  gaugeSU2 : ℝ
  gaugeSU3 : ℝ
  portalCoupling : ℝ
  source : String

/-- A benchmark critical-exponent profile with screened matter directions. -/
def eichhornCriticalProfile : CriticalExponentProfile where
  G_Newton := 2.0
  cosmological := 1.0
  topYukawa := -1.0
  bottomYukawa := -1.0
  higgsQuartic := -1.0
  gaugeU1 := -1.0
  gaugeSU2 := -1.0
  gaugeSU3 := -1.0
  portalCoupling := -1.0
  source := "Diagonalized critical exponents near the benchmark UV fixed point"

/-- Linearized RG data around a chosen truncation scheme. -/
structure BetaSystem where
  truncation : TruncationScheme
  critical : CriticalExponentProfile

/-- Canonical asymptotic-safety benchmark system used by the Hossenfelder bridge. -/
def eichhornBetaSystem : BetaSystem where
  truncation := eichhornBenchmark
  critical := eichhornCriticalProfile

/-- The linearized beta vector field around the gravitational fixed point. -/
def linearizedBeta (sys : BetaSystem) (g : CouplingPoint) : CouplingPoint :=
  let fp := gravitationalFixedPoint sys.truncation
  {
    G_Newton := sys.critical.G_Newton * (g.G_Newton - fp.G_Newton)
    cosmological := sys.critical.cosmological * (g.cosmological - fp.cosmological)
    topYukawa := (sys.critical.topYukawa + sys.truncation.yukawaGravityShift) *
      (g.topYukawa - fp.topYukawa)
    bottomYukawa := (sys.critical.bottomYukawa + sys.truncation.yukawaGravityShift) *
      (g.bottomYukawa - fp.bottomYukawa)
    higgsQuartic := (sys.critical.higgsQuartic + sys.truncation.quarticGravityShift) *
      (g.higgsQuartic - fp.higgsQuartic)
    gaugeU1 := sys.critical.gaugeU1 * (g.gaugeU1 - fp.gaugeU1)
    gaugeSU2 := sys.critical.gaugeSU2 * (g.gaugeSU2 - fp.gaugeSU2)
    gaugeSU3 := sys.critical.gaugeSU3 * (g.gaugeSU3 - fp.gaugeSU3)
    portalCoupling := (sys.critical.portalCoupling + sys.truncation.portalGravityShift) *
      (g.portalCoupling - fp.portalCoupling)
  }

theorem linearizedBeta_at_fixedPoint (sys : BetaSystem) :
    linearizedBeta sys (gravitationalFixedPoint sys.truncation) = 0 := by
  cases sys with
  | mk truncation critical =>
      ext <;> simp [linearizedBeta, gravitationalFixedPoint]

/-- A named physical assumption used by the portal-exclusion theorem. -/
def PortalScreeningHypothesis (sys : BetaSystem) : Prop :=
  sys.critical.portalCoupling + sys.truncation.portalGravityShift ≤ 0

theorem portal_beta_nonpos_of_screening
    (sys : BetaSystem) (g : CouplingPoint)
    (hscreen : PortalScreeningHypothesis sys)
    (hportal : 0 ≤ g.portalCoupling) :
    (linearizedBeta sys g).portalCoupling ≤ 0 := by
  have hcoeff : sys.critical.portalCoupling + sys.truncation.portalGravityShift ≤ 0 := hscreen
  have hdev : 0 ≤ g.portalCoupling - (gravitationalFixedPoint sys.truncation).portalCoupling := by
    simpa [gravitationalFixedPoint] using hportal
  simpa [linearizedBeta] using mul_nonpos_of_nonpos_of_nonneg hcoeff hdev

end AsymptoticSafety
end HeytingLean
