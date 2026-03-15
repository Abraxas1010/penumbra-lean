import Lean
import Mathlib.Data.Real.Basic

namespace HeytingLean
namespace AsymptoticSafety

open Lean

initialize physicalAssumptionAttr : TagAttribute ←
  registerTagAttribute `physical_assumption
    "Marks explicit physical assumptions used by the asymptotic-safety bridge."

initialize euclideanAttr : TagAttribute ←
  registerTagAttribute `euclidean
    "Marks Euclidean-signature assumptions used by the asymptotic-safety bridge."

/-- Experimental window carried as structured data rather than bare literals. -/
structure ExperimentalBand where
  central : ℝ
  tolerance : ℝ

def ExperimentalBand.Contains (band : ExperimentalBand) (value : ℝ) : Prop :=
  |value - band.central| ≤ band.tolerance

/-- Runtime-facing reference targets used by the prediction files. -/
structure ExperimentalTargets where
  topMass : ExperimentalBand
  higgsMass : ExperimentalBand
  topBottomRatio : ExperimentalBand
  neutrinoMassUpper : ℝ
  source : String

/-- Truncation-dependent constants. All floating values live here. -/
structure TruncationScheme where
  newtonStar : ℝ
  cosmologicalStar : ℝ
  gravitonEta : ℝ
  yukawaGravityShift : ℝ
  quarticGravityShift : ℝ
  portalGravityShift : ℝ
  signature : String
  source : String

/-- A compact benchmark truncation used by the sanity layer. -/
def eichhornBenchmark : TruncationScheme where
  newtonStar := 0.71
  cosmologicalStar := 0.19
  gravitonEta := -2.0
  yukawaGravityShift := -0.03
  quarticGravityShift := -0.01
  portalGravityShift := -0.02
  signature := "Euclidean"
  source := "Eichhorn-style linearized benchmark truncation"

/-- Standard-model target windows mentioned in the PM. -/
def eichhornTargets : ExperimentalTargets where
  topMass := ⟨171.0, 2.0⟩
  higgsMass := ⟨126.0, 5.0⟩
  topBottomRatio := ⟨41.0, 4.1⟩
  neutrinoMassUpper := 0.12
  source := "Linearized asymptotic-safety benchmark targets"

/-- A point in the 9-dimensional coupling space. -/
structure CouplingPoint where
  G_Newton : ℝ
  cosmological : ℝ
  topYukawa : ℝ
  bottomYukawa : ℝ
  higgsQuartic : ℝ
  gaugeU1 : ℝ
  gaugeSU2 : ℝ
  gaugeSU3 : ℝ
  portalCoupling : ℝ

@[ext] theorem CouplingPoint.ext
    {a b : CouplingPoint}
    (hG : a.G_Newton = b.G_Newton)
    (hC : a.cosmological = b.cosmological)
    (ht : a.topYukawa = b.topYukawa)
    (hb : a.bottomYukawa = b.bottomYukawa)
    (hh : a.higgsQuartic = b.higgsQuartic)
    (h1 : a.gaugeU1 = b.gaugeU1)
    (h2 : a.gaugeSU2 = b.gaugeSU2)
    (h3 : a.gaugeSU3 = b.gaugeSU3)
    (hp : a.portalCoupling = b.portalCoupling) :
    a = b := by
  cases a
  cases b
  cases hG
  cases hC
  cases ht
  cases hb
  cases hh
  cases h1
  cases h2
  cases h3
  cases hp
  rfl

instance : Zero CouplingPoint where
  zero := {
    G_Newton := 0
    cosmological := 0
    topYukawa := 0
    bottomYukawa := 0
    higgsQuartic := 0
    gaugeU1 := 0
    gaugeSU2 := 0
    gaugeSU3 := 0
    portalCoupling := 0
  }

@[simp] theorem zero_G_Newton : (0 : CouplingPoint).G_Newton = 0 := rfl
@[simp] theorem zero_cosmological : (0 : CouplingPoint).cosmological = 0 := rfl
@[simp] theorem zero_topYukawa : (0 : CouplingPoint).topYukawa = 0 := rfl
@[simp] theorem zero_bottomYukawa : (0 : CouplingPoint).bottomYukawa = 0 := rfl
@[simp] theorem zero_higgsQuartic : (0 : CouplingPoint).higgsQuartic = 0 := rfl
@[simp] theorem zero_gaugeU1 : (0 : CouplingPoint).gaugeU1 = 0 := rfl
@[simp] theorem zero_gaugeSU2 : (0 : CouplingPoint).gaugeSU2 = 0 := rfl
@[simp] theorem zero_gaugeSU3 : (0 : CouplingPoint).gaugeSU3 = 0 := rfl
@[simp] theorem zero_portalCoupling : (0 : CouplingPoint).portalCoupling = 0 := rfl

instance : Add CouplingPoint where
  add a b := {
    G_Newton := a.G_Newton + b.G_Newton
    cosmological := a.cosmological + b.cosmological
    topYukawa := a.topYukawa + b.topYukawa
    bottomYukawa := a.bottomYukawa + b.bottomYukawa
    higgsQuartic := a.higgsQuartic + b.higgsQuartic
    gaugeU1 := a.gaugeU1 + b.gaugeU1
    gaugeSU2 := a.gaugeSU2 + b.gaugeSU2
    gaugeSU3 := a.gaugeSU3 + b.gaugeSU3
    portalCoupling := a.portalCoupling + b.portalCoupling
  }

instance : Neg CouplingPoint where
  neg a := {
    G_Newton := -a.G_Newton
    cosmological := -a.cosmological
    topYukawa := -a.topYukawa
    bottomYukawa := -a.bottomYukawa
    higgsQuartic := -a.higgsQuartic
    gaugeU1 := -a.gaugeU1
    gaugeSU2 := -a.gaugeSU2
    gaugeSU3 := -a.gaugeSU3
    portalCoupling := -a.portalCoupling
  }

instance : Sub CouplingPoint where
  sub a b := a + (-b)

instance : SMul ℝ CouplingPoint where
  smul c a := {
    G_Newton := c * a.G_Newton
    cosmological := c * a.cosmological
    topYukawa := c * a.topYukawa
    bottomYukawa := c * a.bottomYukawa
    higgsQuartic := c * a.higgsQuartic
    gaugeU1 := c * a.gaugeU1
    gaugeSU2 := c * a.gaugeSU2
    gaugeSU3 := c * a.gaugeSU3
    portalCoupling := c * a.portalCoupling
  }

/-- The Gaussian matter fixed point anchored by a truncation scheme. -/
def gravitationalFixedPoint (ts : TruncationScheme) : CouplingPoint where
  G_Newton := ts.newtonStar
  cosmological := ts.cosmologicalStar
  topYukawa := 0
  bottomYukawa := 0
  higgsQuartic := 0
  gaugeU1 := 0
  gaugeSU2 := 0
  gaugeSU3 := 0
  portalCoupling := 0

/-- Squared Euclidean distance to a reference point. -/
def squaredDistanceTo (g ref : CouplingPoint) : ℝ :=
  (g.G_Newton - ref.G_Newton)^2 +
  (g.cosmological - ref.cosmological)^2 +
  (g.topYukawa - ref.topYukawa)^2 +
  (g.bottomYukawa - ref.bottomYukawa)^2 +
  (g.higgsQuartic - ref.higgsQuartic)^2 +
  (g.gaugeU1 - ref.gaugeU1)^2 +
  (g.gaugeSU2 - ref.gaugeSU2)^2 +
  (g.gaugeSU3 - ref.gaugeSU3)^2 +
  (g.portalCoupling - ref.portalCoupling)^2

/-- Euclidean-signature assumption, tracked as an explicit named predicate. -/
def EuclideanTruncation (ts : TruncationScheme) : Prop :=
  ts.signature = "Euclidean"

/-- The portal-closed surface used by the dark-matter exclusion theorem. -/
def portalOff (g : CouplingPoint) : Prop :=
  g.portalCoupling = 0

theorem gravitationalFixedPoint_portalOff (ts : TruncationScheme) :
    portalOff (gravitationalFixedPoint ts) := rfl

end AsymptoticSafety
end HeytingLean
