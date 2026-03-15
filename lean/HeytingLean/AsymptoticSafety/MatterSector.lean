import HeytingLean.AsymptoticSafety.FixedPoint

namespace HeytingLean
namespace AsymptoticSafety

/-- Minimal Standard-Model matter content summary. -/
structure MatterFieldContent where
  fermionGenerations : Nat
  scalarDoublets : Nat
  darkScalars : Nat

/-- Matter-sector parameters that backreact on the gravitational flow. -/
structure MatterSector where
  content : MatterFieldContent
  yukawaLift : ℝ
  quarticLift : ℝ
  portalLift : ℝ
  source : String

def gaussianMatterCompatible (g : CouplingPoint) : Prop :=
  g.topYukawa = 0 ∧
  g.bottomYukawa = 0 ∧
  g.higgsQuartic = 0 ∧
  g.gaugeU1 = 0 ∧
  g.gaugeSU2 = 0 ∧
  g.gaugeSU3 = 0 ∧
  g.portalCoupling = 0

def matterBackreaction (sector : MatterSector) : ℝ :=
  sector.yukawaLift * sector.content.fermionGenerations +
  sector.quarticLift * sector.content.scalarDoublets +
  sector.portalLift * sector.content.darkScalars

theorem gravitationalFixedPoint_gaussianMatterCompatible (ts : TruncationScheme) :
    gaussianMatterCompatible (gravitationalFixedPoint ts) := by
  simp [gaussianMatterCompatible, gravitationalFixedPoint]

theorem matter_matters (sector : MatterSector)
    (hgen : 0 < sector.content.fermionGenerations)
    (hy : 0 < sector.yukawaLift)
    (hq : 0 ≤ sector.quarticLift)
    (hp : 0 ≤ sector.portalLift) :
    0 < matterBackreaction sector := by
  have hgenR : (0 : ℝ) < sector.content.fermionGenerations := by
    exact_mod_cast hgen
  have hscalarR : (0 : ℝ) ≤ sector.content.scalarDoublets := by
    exact_mod_cast Nat.zero_le sector.content.scalarDoublets
  have hdarkR : (0 : ℝ) ≤ sector.content.darkScalars := by
    exact_mod_cast Nat.zero_le sector.content.darkScalars
  have hyterm : 0 < sector.yukawaLift * sector.content.fermionGenerations := by
    exact mul_pos hy hgenR
  have hqterm : 0 ≤ sector.quarticLift * sector.content.scalarDoublets := by
    exact mul_nonneg hq hscalarR
  have hpterm : 0 ≤ sector.portalLift * sector.content.darkScalars := by
    exact mul_nonneg hp hdarkR
  dsimp [matterBackreaction]
  exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hyterm hqterm) hpterm

end AsymptoticSafety
end HeytingLean
