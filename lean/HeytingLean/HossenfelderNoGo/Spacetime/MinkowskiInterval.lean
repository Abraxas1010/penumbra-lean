import Mathlib.Analysis.InnerProductSpace.Basic

namespace HeytingLean.HossenfelderNoGo.Spacetime

/-- A spacetime displacement in 1+1-dimensional Minkowski space. -/
structure SpacetimeDisplacement where
  Δt : ℝ
  Δx : ℝ

/-- The Minkowski interval (proper length squared) with spacelike-positive sign convention. -/
def minkowskiInterval (d : SpacetimeDisplacement) : ℝ :=
  -d.Δt ^ 2 + d.Δx ^ 2

/-- The hyperbola of constant proper length `α`. -/
def hyperbolaAt (α : ℝ) : Set SpacetimeDisplacement :=
  { d | minkowskiInterval d = α }

theorem minkowskiInterval_neg_time (d : SpacetimeDisplacement) :
    minkowskiInterval ⟨-d.Δt, d.Δx⟩ = minkowskiInterval d := by
  simp [minkowskiInterval]

theorem minkowskiInterval_neg_space (d : SpacetimeDisplacement) :
    minkowskiInterval ⟨d.Δt, -d.Δx⟩ = minkowskiInterval d := by
  simp [minkowskiInterval]

end HeytingLean.HossenfelderNoGo.Spacetime
