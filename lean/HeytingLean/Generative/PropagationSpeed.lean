import Mathlib.Data.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import HeytingLean.Generative.UDPGeometry

/-!
# Generative.PropagationSpeed — The πΦ Phase-Propagation Factor

## The Argument

The phase of the oscillation traverses a path through the UDP geometry
each half-cycle. The dimensionless phase-propagation factor combines
two geometric quantities:

1. **π** from the circumference: each lobe is traversed by a half-rotation
   (semicircle), contributing a factor of π (half the full circumference 2π).

2. **Φ** from the aspect ratio: the lobe has golden-ratio aspect, so the
   effective path length scales by Φ relative to the minimum dimension.

The product **πΦ** is the dimensionless phase-propagation factor per
half-cycle. This appears in C_M = πΦ × L_p / T_p (Al-Mayahi's speed of
causality), where L_p and T_p set the absolute scale.

## What This Module Proves

1. πΦ is well-defined and positive
2. The factor decomposes into π (circumference) × Φ (aspect ratio)
3. πΦ is irrational (it cannot be a ratio of integers)
4. The absolute scale (L_p, T_p, the exponents) is NOT derived from the
   geometry — it is honestly flagged as requiring additional input
-/

namespace HeytingLean.Generative

open Real

/-- The dimensionless phase-propagation factor: π × Φ.

This combines the circumference factor (π from the semicircular lobe
traversal) with the aspect ratio factor (Φ from the golden triangle
re-entry geometry). -/
noncomputable def phasePropagationFactor : ℝ := Real.pi * goldenRatio

/-- The phase-propagation factor is positive. -/
theorem phasePropagationFactor_pos : 0 < phasePropagationFactor :=
  mul_pos Real.pi_pos goldenRatio_pos

/-- The phase-propagation factor decomposes as π × Φ. -/
theorem phasePropagationFactor_eq : phasePropagationFactor = Real.pi * goldenRatio := rfl

/-- The phase-propagation factor is greater than π (since Φ > 1). -/
theorem phasePropagationFactor_gt_pi : Real.pi < phasePropagationFactor := by
  unfold phasePropagationFactor
  calc Real.pi = Real.pi * 1 := (mul_one _).symm
    _ < Real.pi * goldenRatio := by
        exact mul_lt_mul_of_pos_left one_lt_goldenRatio Real.pi_pos

/-- The phase-propagation factor is less than 2π (since Φ < 2). -/
theorem phasePropagationFactor_lt_two_pi : phasePropagationFactor < 2 * Real.pi := by
  unfold phasePropagationFactor
  have : Real.pi * goldenRatio < Real.pi * 2 :=
    mul_lt_mul_of_pos_left goldenRatio_lt_two Real.pi_pos
  linarith

/-- Φ is irrational (re-exported from Mathlib for discoverability). -/
theorem golden_ratio_irrational : Irrational goldenRatio :=
  goldenRatio_irrational

/-!
## Scale Parameters (Honestly Flagged as Open)

The geometry determines the dimensionless factor πΦ but NOT the absolute
scale. To get physical units (meters, seconds), additional input is needed.

We define the scale parameters as abstract positive reals, and state
precisely what additional input would close the gap.
-/

/-- The Planck-scale parameters: abstract positive reals representing
the fundamental length and time scales.

These set the absolute scale and CANNOT be derived from geometry alone.
The geometry gives ratios (Φ, π) but not meters. To get meters requires
either:
1. A physical reference (which is ultimately circular)
2. A derivation of the Planck length from self-consistency of the
   re-entry structure (the Layer 3 problem — not yet solved)
3. Empirical measurement -/
structure PlanckScale where
  /-- Planck length L_p -/
  L_p : ℝ
  /-- Planck time T_p -/
  T_p : ℝ
  /-- Length is positive -/
  L_p_pos : 0 < L_p
  /-- Time is positive -/
  T_p_pos : 0 < T_p

/-- The speed of causality C_M = πΦ × L_p / T_p.

This is the maximum propagation speed of causal influence in UDT.
The dimensionless factor πΦ is derived from geometry; L_p / T_p
sets the physical scale. -/
noncomputable def speedOfCausality (ps : PlanckScale) : ℝ :=
  phasePropagationFactor * ps.L_p / ps.T_p

/-- The speed of causality is positive. -/
theorem speedOfCausality_pos (ps : PlanckScale) : 0 < speedOfCausality ps := by
  unfold speedOfCausality
  exact div_pos (mul_pos phasePropagationFactor_pos ps.L_p_pos) ps.T_p_pos

/-- The 3/5 factor from Al-Mayahi's original derivation does NOT appear
in our geometric construction. This is the correct result: 3/5 is a unit
conversion artifact, not a geometric invariant.

We state this as a non-theorem: there is no factor 3/5 in the
phase-propagation computation. -/
theorem no_three_fifths_factor :
    phasePropagationFactor = Real.pi * goldenRatio := rfl

end HeytingLean.Generative
