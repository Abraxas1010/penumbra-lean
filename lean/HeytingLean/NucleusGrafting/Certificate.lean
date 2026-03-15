import HeytingLean.NucleusGrafting.BoundaryConnection
import HeytingLean.Eigen.SafEDMD

namespace HeytingLean
namespace NucleusGrafting

structure VerificationLayerEvidence where
  leanModules : List String
  leanTheorems : List String
  discreteArtifact : String
  numericArtifact : String

structure NucleusGraftingCertificate (n : Nat) where
  modelName : String
  graftLayer : String
  boundaryBand : HeytingLean.HossenfelderNoGo.HeytingBoundary.GapBand
      (Set (ActivationVector n))
  gap : GapDecomposition
  evidence : VerificationLayerEvidence
  hGapPositive : 0 < gap.total

theorem certificate_gap_nonzero {n : Nat} (c : NucleusGraftingCertificate n) :
    0 < c.gap.total := c.hGapPositive

theorem certificate_records_nonnegative_quantization {n : Nat}
    (c : NucleusGraftingCertificate n) :
    0 ≤ c.gap.quantization := c.gap.hQuantNonneg

theorem certificate_has_gap_witness {n : Nat}
    (c : NucleusGraftingCertificate n) (k : ℕ) :
    ∃ a : Set (ActivationVector n),
      HeytingLean.HossenfelderNoGo.HeytingBoundary.boundaryGap
          (c.boundaryBand.family.nucleusAt k) a ≠ ∅ :=
  c.boundaryBand.gap_positive k

end NucleusGrafting
end HeytingLean
