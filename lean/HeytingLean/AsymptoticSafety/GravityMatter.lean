import HeytingLean.AsymptoticSafety.NucleusInstance
import HeytingLean.AsymptoticSafety.MatterSector

namespace HeytingLean
namespace AsymptoticSafety

/-- Calibrated gravity-matter model used by the prediction layer. -/
structure GravityMatterModel where
  system : BetaSystem
  matter : MatterSector
  targets : ExperimentalTargets
  topCalibration : ℝ
  higgsCalibration : ℝ
  ratioCalibration : ℝ
  neutrinoCalibration : ℝ
  source : String

def gravitationalTopDrift (model : GravityMatterModel) : ℝ :=
  model.system.critical.topYukawa + model.system.truncation.yukawaGravityShift

def gravitationalBottomDrift (model : GravityMatterModel) : ℝ :=
  model.system.critical.bottomYukawa + model.system.truncation.yukawaGravityShift

def gravitationalQuarticDrift (model : GravityMatterModel) : ℝ :=
  model.system.critical.higgsQuartic + model.system.truncation.quarticGravityShift

def effectiveTopYukawaShift (model : GravityMatterModel) : ℝ :=
  gravitationalTopDrift model + model.matter.yukawaLift

def effectiveBottomYukawaShift (model : GravityMatterModel) : ℝ :=
  gravitationalBottomDrift model + model.matter.yukawaLift

def effectiveHiggsQuarticShift (model : GravityMatterModel) : ℝ :=
  gravitationalQuarticDrift model + model.matter.quarticLift

def topMassShift (model : GravityMatterModel) : ℝ :=
  model.topCalibration * effectiveTopYukawaShift model

def higgsMassShift (model : GravityMatterModel) : ℝ :=
  model.higgsCalibration * effectiveHiggsQuarticShift model

def topBottomRatioShift (model : GravityMatterModel) : ℝ :=
  model.ratioCalibration *
    (effectiveTopYukawaShift model - effectiveBottomYukawaShift model)

def predictTopMass (model : GravityMatterModel) : ℝ :=
  model.targets.topMass.central + topMassShift model

def predictHiggsMass (model : GravityMatterModel) : ℝ :=
  model.targets.higgsMass.central + higgsMassShift model

def predictTopBottomRatio (model : GravityMatterModel) : ℝ :=
  model.targets.topBottomRatio.central + topBottomRatioShift model

theorem topMass_prediction_offset (model : GravityMatterModel) :
    predictTopMass model - model.targets.topMass.central = topMassShift model := by
  simp [predictTopMass]

theorem higgsMass_prediction_offset (model : GravityMatterModel) :
    predictHiggsMass model - model.targets.higgsMass.central = higgsMassShift model := by
  simp [predictHiggsMass]

theorem topBottomRatio_prediction_offset (model : GravityMatterModel) :
    predictTopBottomRatio model - model.targets.topBottomRatio.central =
      topBottomRatioShift model := by
  simp [predictTopBottomRatio]

theorem topMass_abs_error_eq_rg_drift (model : GravityMatterModel) :
    |predictTopMass model - model.targets.topMass.central| =
      |model.topCalibration| * |effectiveTopYukawaShift model| := by
  rw [topMass_prediction_offset, topMassShift, abs_mul]

theorem higgsMass_abs_error_eq_rg_drift (model : GravityMatterModel) :
    |predictHiggsMass model - model.targets.higgsMass.central| =
      |model.higgsCalibration| * |effectiveHiggsQuarticShift model| := by
  rw [higgsMass_prediction_offset, higgsMassShift, abs_mul]

theorem topBottomRatio_abs_error_eq_rg_drift (model : GravityMatterModel) :
    |predictTopBottomRatio model - model.targets.topBottomRatio.central| =
      |model.ratioCalibration| *
        |effectiveTopYukawaShift model - effectiveBottomYukawaShift model| := by
  rw [topBottomRatio_prediction_offset, topBottomRatioShift, abs_mul]

def neutrinoDamping (model : GravityMatterModel) : ℝ :=
  1 + |gravitationalTopDrift model|

def neutrinoNumerator (model : GravityMatterModel) : ℝ :=
  |model.neutrinoCalibration| * |matterBackreaction model.matter|

noncomputable def predictNeutrinoUpper (model : GravityMatterModel) : ℝ :=
  neutrinoNumerator model / neutrinoDamping model

theorem neutrinoDamping_pos (model : GravityMatterModel) :
    0 < neutrinoDamping model := by
  unfold neutrinoDamping
  have habs : 0 ≤ |gravitationalTopDrift model| := abs_nonneg _
  have h1 : (0 : ℝ) < 1 := by norm_num
  exact add_pos_of_pos_of_nonneg h1 habs

theorem matter_preserves_fixed_point (model : GravityMatterModel) :
    isUVSafe model.system (gravitationalFixedPoint model.system.truncation) :=
  gravitationalFixedPoint_isUVSafe model.system

theorem matter_changes_top_shift (model : GravityMatterModel)
    (hy : model.matter.yukawaLift ≠ 0) :
    effectiveTopYukawaShift model ≠ gravitationalTopDrift model := by
  intro hEq
  have hy0 : model.matter.yukawaLift = 0 := by
    have hEq' :
        gravitationalTopDrift model + model.matter.yukawaLift =
          gravitationalTopDrift model + 0 := by
      simpa [effectiveTopYukawaShift] using hEq
    exact add_left_cancel hEq'
  exact hy hy0

end AsymptoticSafety
end HeytingLean
