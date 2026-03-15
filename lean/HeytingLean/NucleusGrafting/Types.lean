import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice

namespace HeytingLean
namespace NucleusGrafting

structure LayerQuantParams where
  layerName : String
  scale : ℝ
  zeroPoint : Int
  latticeSpacing : ℝ
  hScalePos : 0 < scale
  hSpacingEq : latticeSpacing = scale

theorem latticeSpacing_pos (p : LayerQuantParams) : 0 < p.latticeSpacing := by
  rw [p.hSpacingEq]
  exact p.hScalePos

structure Phase1Summary where
  modelName : String
  fp32Accuracy : ℝ
  quantizedAccuracy : ℝ
  accuracyDrop : ℝ
  hDropNonneg : 0 ≤ accuracyDrop
  quantLayers : List LayerQuantParams

def acceptableAccuracyDrop (s : Phase1Summary) : Prop :=
  s.accuracyDrop < (5 : ℝ) / 100

theorem acceptableAccuracyDrop_of_lt
    (s : Phase1Summary)
    (h : s.accuracyDrop < (5 : ℝ) / 100) :
    acceptableAccuracyDrop s := h

abbrev ActivationVector (n : Nat) := Fin n → Int

def activationFixedSet {n : Nat} (z : Int) : Set (ActivationVector n) :=
  {v | ∀ i, z ≤ v i}

theorem activationFixedSet_nonempty {n : Nat} (z : Int) :
    (activationFixedSet (n := n) z).Nonempty := by
  refine ⟨fun _ => z, ?_⟩
  intro i
  exact le_rfl

theorem activationFixedSet_ne_empty {n : Nat} (z : Int) :
    activationFixedSet (n := n) z ≠ (∅ : Set (ActivationVector n)) := by
  intro hEmpty
  rw [Set.eq_empty_iff_forall_notMem] at hEmpty
  rcases activationFixedSet_nonempty (n := n) z with ⟨v, hv⟩
  exact hEmpty v hv

theorem activationFixedSet_mono {n : Nat} {z₁ z₂ : Int}
    (h : z₁ ≤ z₂) :
    activationFixedSet (n := n) z₂ ⊆ activationFixedSet (n := n) z₁ := by
  intro v hv i
  exact le_trans h (hv i)

structure GapDecomposition where
  quantization : ℝ
  gate : ℝ
  reconstruction : ℝ
  total : ℝ
  hQuantNonneg : 0 ≤ quantization
  hGateNonneg : 0 ≤ gate
  hReconNonneg : 0 ≤ reconstruction
  hTotalNonneg : 0 ≤ total
  hAdditive : total = quantization + gate + reconstruction

def componentUpperBound (g : GapDecomposition) : ℝ :=
  g.quantization + g.gate + g.reconstruction

theorem componentUpperBound_eq_total (g : GapDecomposition) :
    componentUpperBound g = g.total := by
  simpa [componentUpperBound] using g.hAdditive.symm

theorem componentUpperBound_nonneg (g : GapDecomposition) :
    0 ≤ componentUpperBound g := by
  rw [componentUpperBound_eq_total]
  exact g.hTotalNonneg

end NucleusGrafting
end HeytingLean
