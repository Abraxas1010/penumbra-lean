import HeytingLean.HossenfelderNoGo.HeytingBoundary.BoundaryNucleus

namespace HeytingLean.HossenfelderNoGo.HeytingBoundary

open HeytingLean.HossenfelderNoGo.Networks

/-- The boundary nucleus cannot be Boolean: otherwise Hossenfelder's forbidden network would
exist. -/
theorem boundary_necessarily_non_boolean
    {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : BoundaryNucleus L)
    (hBridge : BooleanBoundaryBridge N) :
    ¬ isBoolean N := by
  intro hBool
  exact no_poincare_invariant_locally_finite_network (hBridge hBool)

/-- Some element has nonempty boundary gap. -/
theorem gap_nonzero_at_boundary
    {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : BoundaryNucleus L)
    (hBridge : BooleanBoundaryBridge N) :
    ∃ a : L, boundaryGap N a ≠ ∅ := by
  by_contra hGap
  push_neg at hGap
  have hBool : isBoolean N := by
    intro a
    by_contra hne
    have hmem : N.R a ∈ boundaryGap N a := by
      simp [boundaryGap, hne]
    have hempty : N.R a ∉ boundaryGap N a := by
      simp [hGap a]
    exact hempty hmem
  exact boundary_necessarily_non_boolean N hBridge hBool

/-- Therefore not every point is a fixed point of the nucleus. -/
theorem boundary_has_nontrivial_fixed_points
    {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : BoundaryNucleus L)
    (hBridge : BooleanBoundaryBridge N) :
    ∃ a : L, a ∉ N.fixedPoints := by
  obtain ⟨a, hGap⟩ := gap_nonzero_at_boundary N hBridge
  refine ⟨a, ?_⟩
  intro hfix
  have hEq : N.R a = a := (HeytingLean.Core.Nucleus.mem_fixedPoints N a).mp hfix
  have : boundaryGap N a = ∅ := by
    ext x
    simp [boundaryGap, hEq]
  exact hGap this

end HeytingLean.HossenfelderNoGo.HeytingBoundary
