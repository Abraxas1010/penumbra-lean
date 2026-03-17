import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Penumbra.MonotoneTauLimit

This module captures the negative result behind the phase-2 tidal experiment: the concrete
Schwarzschild-derived detector weights are strictly positive on the radial half-line, so they
cannot reproduce interior nodes of excited hydrogen states.
-/

namespace Penumbra

/-- A strictly decreasing function that vanishes at `r` stays positive on the open interval
`(0,r)`. This is the abstract "no interior node before the first zero" witness used by the phase-2
negative result. -/
theorem monotone_no_interior_node {f : ℝ → ℝ} (hf : StrictAntiOn f (Set.Ici 0))
    (r : ℝ) (hr : 0 < r) (hfr : f r = 0) :
    ∀ s, 0 < s → s < r → 0 < f s := by
  intro s hs0 hsr
  have hsIci : s ∈ Set.Ici 0 := by simpa [Set.mem_Ici] using le_of_lt hs0
  have hrIci : r ∈ Set.Ici 0 := by simpa [Set.mem_Ici] using le_of_lt hr
  have hlt : f r < f s := hf hsIci hrIci hsr
  rw [hfr] at hlt
  linarith

/-- Closed-form gradient-squared detector weight for the Schwarzschild reciprocal phase deficit. -/
noncomputable def schwarzschildGradientWeight (rs r0 r : ℝ) : ℝ :=
  4 * rs^2 / (2 * (r0 + r) + rs)^4

/-- Closed-form Laplacian-squared detector weight for the same profile. -/
noncomputable def schwarzschildLaplacianWeight (rs r0 r : ℝ) : ℝ :=
  64 * rs^2 / (2 * (r0 + r) + rs)^6

/-- The Schwarzschild gradient weight is strictly positive for every positive radius. -/
theorem schwarzschild_gradient_positive {rs r0 r : ℝ}
    (hrs : 0 < rs) (hr0 : 0 ≤ r0) (hr : 0 ≤ r) :
    0 < schwarzschildGradientWeight rs r0 r := by
  have hden : 0 < (2 * (r0 + r) + rs)^4 := by
    have hbase : 0 < 2 * (r0 + r) + rs := by linarith
    positivity
  have hnum : 0 < 4 * rs^2 := by positivity
  unfold schwarzschildGradientWeight
  positivity

/-- The Schwarzschild Laplacian weight is also strictly positive for every positive radius. -/
theorem schwarzschild_laplacian_positive {rs r0 r : ℝ}
    (hrs : 0 < rs) (hr0 : 0 ≤ r0) (hr : 0 ≤ r) :
    0 < schwarzschildLaplacianWeight rs r0 r := by
  have hden : 0 < (2 * (r0 + r) + rs)^6 := by
    have hbase : 0 < 2 * (r0 + r) + rs := by linarith
    positivity
  have hnum : 0 < 64 * rs^2 := by positivity
  unfold schwarzschildLaplacianWeight
  positivity

/-- Consequently, neither the gradient nor the Laplacian detector family can realise an interior
radial node away from the origin. -/
theorem schwarzschild_detector_family_has_no_interior_node {rs r0 r : ℝ}
    (hrs : 0 < rs) (hr0 : 0 ≤ r0) (hr : 0 < r) :
    schwarzschildGradientWeight rs r0 r ≠ 0 ∧
      schwarzschildLaplacianWeight rs r0 r ≠ 0 := by
  constructor
  · have hpos := schwarzschild_gradient_positive hrs hr0 (le_of_lt hr)
    linarith
  · have hpos := schwarzschild_laplacian_positive hrs hr0 (le_of_lt hr)
    linarith

end Penumbra
