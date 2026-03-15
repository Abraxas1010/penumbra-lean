import Mathlib.Data.Set.Lattice
import HeytingLean.NucleusGrafting.DiscreteLattice
import HeytingLean.HossenfelderNoGo.HeytingBoundary.BoundaryNucleus
import HeytingLean.HossenfelderNoGo.HeytingBoundary.DynamicGap
import HeytingLean.HossenfelderNoGo.HeytingBoundary.BandConstraint

namespace HeytingLean
namespace NucleusGrafting

open HeytingLean.HossenfelderNoGo.HeytingBoundary

def graftBoundaryNucleus {n : Nat} (z : Int) :
    BoundaryNucleus (Set (ActivationVector n)) where
  R U := U ∪ activationFixedSet (n := n) z
  extensive := by
    intro U
    exact Set.subset_union_left
  idempotent := by
    intro U
    ext v
    simp [activationFixedSet, Set.union_assoc]
  meet_preserving := by
    intro U V
    ext v
    by_cases hFixed : v ∈ activationFixedSet (n := n) z
    · simp [hFixed]
    · simp [hFixed]

theorem graftBoundaryNucleus_not_boolean {n : Nat} (z : Int) :
    ¬ isBoolean (graftBoundaryNucleus (n := n) z) := by
  intro hBool
  have hEmpty := hBool (∅ : Set (ActivationVector n))
  exact activationFixedSet_ne_empty (n := n) z (by
    simpa [graftBoundaryNucleus] using hEmpty)

theorem boundaryGap_bot_nonempty {n : Nat} (z : Int) :
    boundaryGap (graftBoundaryNucleus (n := n) z) (∅ : Set (ActivationVector n)) ≠ ∅ := by
  intro hEmpty
  rw [Set.eq_empty_iff_forall_notMem] at hEmpty
  have hMem : activationFixedSet (n := n) z ∈
      boundaryGap (graftBoundaryNucleus (n := n) z) (∅ : Set (ActivationVector n)) := by
    rw [mem_boundaryGap_iff]
    constructor
    · simp [graftBoundaryNucleus]
    · exact activationFixedSet_ne_empty (n := n) z
  exact hEmpty _ hMem

def bitwidthFamily {n : Nat} (zCoarse zFine : Int) (hLevels : zCoarse ≤ zFine) :
    NucleusFamily (Set (ActivationVector n)) where
  nucleusAt
    | 0 => graftBoundaryNucleus (n := n) zCoarse
    | _ => graftBoundaryNucleus (n := n) zFine
  weakening := by
    intro i j hij U
    cases i with
    | zero =>
        cases j with
        | zero =>
            exact le_rfl
        | succ j =>
            intro v hv
            rcases hv with hv | hv
            · exact Or.inl hv
            · exact Or.inr (activationFixedSet_mono (n := n) hLevels hv)
    | succ i =>
        cases j with
        | zero =>
            exact (Nat.not_succ_le_zero i hij).elim
        | succ j =>
            exact le_rfl

theorem bitwidthFamily_gap_positive {n : Nat}
    (zCoarse zFine : Int) (hLevels : zCoarse ≤ zFine) (k : ℕ) :
    ∃ a : Set (ActivationVector n),
      boundaryGap ((bitwidthFamily (n := n) zCoarse zFine hLevels).nucleusAt k) a ≠ ∅ := by
  cases k with
  | zero =>
      exact ⟨∅, boundaryGap_bot_nonempty (n := n) zCoarse⟩
  | succ k =>
      exact ⟨∅, boundaryGap_bot_nonempty (n := n) zFine⟩

def measuredGapBand {n : Nat} (zCoarse zFine : Int) (hLevels : zCoarse ≤ zFine) :
    GapBand (Set (ActivationVector n)) where
  family := bitwidthFamily (n := n) zCoarse zFine hLevels
  gap_positive := fun k => bitwidthFamily_gap_positive (n := n) zCoarse zFine hLevels k
  gap_bounded_above := ⟨⊤, by
    intro k U
    exact le_top⟩

def observedBoundaryGap (g : GapDecomposition) : ℝ := g.total

theorem observedBoundaryGap_nonneg (g : GapDecomposition) :
    0 ≤ observedBoundaryGap g := g.hTotalNonneg

structure DiscreteGateMeasurement where
  modelName : String
  layerName : String
  modifiedFraction : ℝ
  fixedFraction : ℝ
  heytingGap : ℝ
  hModifiedNonneg : 0 ≤ modifiedFraction
  hFixedNonneg : 0 ≤ fixedFraction
  hFixedLeOne : fixedFraction ≤ 1
  hGapNonneg : 0 ≤ heytingGap

def gateHasNontrivialBoundary (m : DiscreteGateMeasurement) : Prop :=
  0 < m.modifiedFraction ∧ 0 < m.heytingGap

theorem fixedFraction_le_one (m : DiscreteGateMeasurement) :
    m.fixedFraction ≤ 1 := m.hFixedLeOne

theorem gate_boundary_nontrivial_of_positive_gap
    (m : DiscreteGateMeasurement) (h : gateHasNontrivialBoundary m) :
    0 < m.heytingGap := h.2

end NucleusGrafting
end HeytingLean
