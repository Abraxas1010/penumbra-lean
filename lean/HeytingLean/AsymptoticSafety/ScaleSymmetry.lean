import HeytingLean.Renormalization.DimensionalRatchet
import HeytingLean.AsymptoticSafety.NucleusInstance

namespace HeytingLean
namespace AsymptoticSafety

def scaleThreshold (s : Renormalization.RatchetScale) : ℝ :=
  s.level

def scaleSafeSet (sys : BetaSystem) (s : Renormalization.RatchetScale) : Set CouplingPoint :=
  let fp := gravitationalFixedPoint sys.truncation
  { g |
    (scaleThreshold s ≤ |sys.critical.G_Newton| → g.G_Newton = fp.G_Newton) ∧
    (scaleThreshold s ≤ |sys.critical.cosmological| → g.cosmological = fp.cosmological) ∧
    (scaleThreshold s ≤ |sys.critical.topYukawa + sys.truncation.yukawaGravityShift| →
      g.topYukawa = fp.topYukawa) ∧
    (scaleThreshold s ≤ |sys.critical.bottomYukawa + sys.truncation.yukawaGravityShift| →
      g.bottomYukawa = fp.bottomYukawa) ∧
    (scaleThreshold s ≤ |sys.critical.higgsQuartic + sys.truncation.quarticGravityShift| →
      g.higgsQuartic = fp.higgsQuartic) ∧
    (scaleThreshold s ≤ |sys.critical.gaugeU1| → g.gaugeU1 = fp.gaugeU1) ∧
    (scaleThreshold s ≤ |sys.critical.gaugeSU2| → g.gaugeSU2 = fp.gaugeSU2) ∧
    (scaleThreshold s ≤ |sys.critical.gaugeSU3| → g.gaugeSU3 = fp.gaugeSU3) ∧
    (scaleThreshold s ≤ |sys.critical.portalCoupling + sys.truncation.portalGravityShift| →
      g.portalCoupling = fp.portalCoupling) }

def rgRestrictAtScale (sys : BetaSystem) (s : Renormalization.RatchetScale) :
    CouplingRegion → CouplingRegion :=
  fun U => ((carrier U ∩ scaleSafeSet sys s) : Set CouplingPoint)

theorem gravitationalFixedPoint_mem_scaleSafeSet
    (sys : BetaSystem) (s : Renormalization.RatchetScale) :
    gravitationalFixedPoint sys.truncation ∈ scaleSafeSet sys s := by
  simp [scaleSafeSet, gravitationalFixedPoint]

theorem scaleSafeSet_mono (sys : BetaSystem)
    {s₁ s₂ : Renormalization.RatchetScale}
    (hs : s₁.level ≤ s₂.level) :
    scaleSafeSet sys s₁ ⊆ scaleSafeSet sys s₂ := by
  intro g hg
  rcases hg with
    ⟨hG, hC, ht, hb, hh, h1, h2, h3, hp⟩
  have hthreshold : scaleThreshold s₁ ≤ scaleThreshold s₂ := by
    show (s₁.level : ℝ) ≤ (s₂.level : ℝ)
    exact_mod_cast hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcoeff
    exact hG (le_trans hthreshold hcoeff)
  · intro hcoeff
    exact hC (le_trans hthreshold hcoeff)
  · intro hcoeff
    exact ht (le_trans hthreshold hcoeff)
  · intro hcoeff
    exact hb (le_trans hthreshold hcoeff)
  · intro hcoeff
    exact hh (le_trans hthreshold hcoeff)
  · intro hcoeff
    exact h1 (le_trans hthreshold hcoeff)
  · intro hcoeff
    exact h2 (le_trans hthreshold hcoeff)
  · intro hcoeff
    exact h3 (le_trans hthreshold hcoeff)
  · intro hcoeff
    exact hp (le_trans hthreshold hcoeff)

noncomputable def rgDimensionalRatchet (sys : BetaSystem) :
    Renormalization.DimensionalRatchet CouplingRegion where
  coarsen := rgRestrictAtScale sys
  extensive := by
    intro s U
    intro x hx
    exact hx.1
  idempotent := by
    intro s U
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, hx.2⟩
  meet_preserving := by
    intro s U V
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx, hs⟩
      cases hx with
      | inl hU => exact Or.inl ⟨hU, hs⟩
      | inr hV => exact Or.inr ⟨hV, hs⟩
    · intro hx
      rcases hx with hU | hV
      · exact ⟨Or.inl hU.1, hU.2⟩
      · exact ⟨Or.inr hV.1, hV.2⟩
  monotone_scale := by
    intro s₁ s₂ U hs
    intro x hx
    have hmono : x ∈ scaleSafeSet sys s₂ := (scaleSafeSet_mono sys hs) hx.2
    exact ⟨hx.1, hmono⟩

def uvScale : Renormalization.RatchetScale := ⟨0, 0⟩

theorem constructive_at_uv : Renormalization.logicAtScale uvScale = .constructive := by
  rfl

noncomputable def freeEnergyProxy (sys : BetaSystem) (g : CouplingPoint) : ℝ :=
  squaredDistanceTo (projectToUVSafe sys g) (gravitationalFixedPoint sys.truncation)

theorem freeEnergy_at_fixedPoint_zero (sys : BetaSystem) :
    freeEnergyProxy sys (gravitationalFixedPoint sys.truncation) = 0 := by
  simp [freeEnergyProxy, projectToUVSafe, gravitationalFixedPoint, squaredDistanceTo]

end AsymptoticSafety
end HeytingLean
