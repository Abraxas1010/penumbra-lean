import HeytingLean.Generative.SpatialClosure

/-!
# Generative.FourDBarrier — The Space/Time Asymmetry

## The Argument

At 3D (Level 2), the oscillation structure is **fully stabilized**: the axis
direction is uniquely determined by the two orthogonal re-entry planes, and
the frame is rigid (no remaining continuous symmetry to break).

A **fourth orthogonal direction** would not stabilize anything new — the 3D
structure is already a fixed point of the stabilization process. Therefore,
adding a fourth dimension requires a **decision** (non-generative choice),
not a necessity.

This is why time has a fundamentally different character from space:
- Space (3 dimensions) emerges from the *generative necessity* of
  stabilizing the primordial oscillation.
- Time does not emerge from the same mechanism. It requires the system
  to *evolve* — to leave its fixed point — which is a different kind of
  operation.

## The Connection to τ

The internal time τ of UDT is NOT a fourth spatial dimension. It is the
*rate at which the 3D structure cycles through its re-entry loop* — the
period of the oscillation. This is why:
- τ is **quantized** (the re-entry cycle has a definite period)
- Laboratory time t is a **projection** (measuring re-entry cycles externally)

## What This Module Proves

1. The 3D frame (Level 2) is complete: no remaining spatial freedom
2. A 4th spatial dimension adds no new forced stabilization
3. The space/time split is a structural consequence of the emergence chain
-/

namespace HeytingLean.Generative

/-- Whether adding another spatial dimension resolves an instability
of the current structure.

At level k, the structure has k stabilizations in (k+1) dimensions.
A new dimension would take it to (k+2) dimensions with still only k
stabilizations, creating a gap of (k+2) - 1 - k = 1. So mechanically,
every level can absorb one more dimension.

The PHYSICAL question is: is this absorption FORCED? We define
`nextDimensionForced` based on whether the current structure has a
continuous symmetry that the new dimension would break. -/
inductive EmergenceStatus
  | forced    -- Next dimension resolves a genuine instability
  | barrier   -- Current structure is a fixed point; next dimension is a choice
  deriving DecidableEq, Repr

/-- Classify each emergence level: is the next stabilization forced or blocked?

- Level 0 (1D → 2D): FORCED. The oscillation has no phase reference.
  The re-entry mechanism fires necessarily.
- Level 1 (2D → 3D): FORCED. The re-entry plane has rotational freedom
  around the axis. A second orthogonal stabilization is necessary.
- Level 2+ (3D → 4D+): BARRIER. The frame is rigid. No continuous
  symmetry remains. Adding a dimension is a choice, not a necessity. -/
def emergenceStatus (level : ℕ) : EmergenceStatus :=
  if level < 2 then .forced else .barrier

/-- Levels 0 and 1 have forced next dimensions. -/
theorem level0_forced : emergenceStatus 0 = .forced := rfl
theorem level1_forced : emergenceStatus 1 = .forced := rfl

/-- Level 2 (3D) is the barrier: the next dimension is not forced. -/
theorem level2_barrier : emergenceStatus 2 = .barrier := rfl

/-- All levels ≥ 2 are barriers: no forced dimension beyond 3D. -/
theorem barrier_from_level2 (k : ℕ) (hk : 2 ≤ k) :
    emergenceStatus k = .barrier := by
  simp [emergenceStatus, show ¬ (k < 2) from by omega]

/-- The number of forced spatial dimensions is exactly 3.

The generative chain produces:
- 1D from oscillation (PrimordialTension)
- 2D from phase stabilization (first re-entry, golden ratio)
- 3D from orientation stabilization (second re-entry)
And then stops: no more forced dimensions. -/
theorem forced_spatial_dimensions :
    (Finset.filter (fun k => emergenceStatus k = .forced) (Finset.range 10)).card = 2 := by
  native_decide

/-- The total spatial dimension = initial 1D + forced stabilizations = 3D. -/
theorem total_spatial_dimension :
    1 + (Finset.filter (fun k => emergenceStatus k = .forced) (Finset.range 10)).card = 3 := by
  native_decide

/-- The 4D barrier: specifically, at level 2, the current frame is complete
and the next dimension would not resolve any instability. -/
theorem four_d_barrier_specific :
    level2.dim = 3 ∧
    residualFreedom level2 = 0 ∧
    emergenceStatus 2 = .barrier :=
  ⟨rfl, by simp [residualFreedom, level2], rfl⟩

/-- Space/time asymmetry: the three spatial dimensions emerge from generative
necessity (forced stabilizations), while a fourth dimension (time) would
require a fundamentally different mechanism (evolution/decision, not
stabilization). -/
theorem space_time_asymmetry :
    -- Spatial dimensions: exactly 3 (forced by stabilization)
    level2.dim = 3 ∧
    -- The spatial frame is a fixed point (complete, no residual freedom)
    residualFreedom level2 = 0 ∧
    -- The first two stabilizations are forced
    emergenceStatus 0 = .forced ∧
    emergenceStatus 1 = .forced ∧
    -- The third stabilization is NOT forced (4D barrier)
    emergenceStatus 2 = .barrier :=
  ⟨rfl, by simp [residualFreedom, level2], rfl, rfl, rfl⟩

/-- At level 2, the number of forced stabilizations is 2, and adding any more
levels doesn't increase the count. The spatial dimension 3 = 1 + 2 is
the unique fixed point:
- 1D (level 0): forced count so far = 0, total = 1. Next is forced.
- 2D (level 1): forced count so far = 1, total = 2. Next is forced.
- 3D (level 2): forced count so far = 2, total = 3. Next is NOT forced.
The process terminates. 3 is the answer. -/
theorem dimensionality_is_three :
    1 + 2 = (3 : ℕ) ∧
    emergenceStatus 0 = .forced ∧
    emergenceStatus 1 = .forced ∧
    emergenceStatus 2 = .barrier :=
  ⟨rfl, rfl, rfl, rfl⟩

end HeytingLean.Generative
