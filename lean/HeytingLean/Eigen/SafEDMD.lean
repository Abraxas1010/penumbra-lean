import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Order.Nucleus
import Mathlib.Tactic
import HeytingLean.Eigen.NucleusReLU

/-!
# SafEDMD Algebraic Ingredients

This module packages the nucleus-side algebra used by the SafEDMD integration.
The full spectral-norm comparison for data-driven error envelopes is numerical,
but the key finite-dimensional ingredients are formalized here:

- ReLU projection is idempotent and fixes the positive orthant.
- Every projected coordinate is nonnegative and bounded by the original absolute
  value.
- Componentwise squaring and finite sums cannot increase under the ReLU nucleus.
- The diagonal entries of projected Gram matrices are therefore bounded by the
  unprojected ones.
-/

open scoped BigOperators

namespace HeytingLean
namespace Eigen

variable {n m : ℕ}

/-- Sum of componentwise squares used as a finite-dimensional energy proxy. -/
def sqSum (v : Fin n → ℝ) : ℝ :=
  ∑ i, (v i)^2

/-- A diagonal Gram contribution after ReLU projection. -/
def projectedGramDiag (samples : Fin m → Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ s, (reluNucleus n (samples s) j)^2

/-- The ReLU nucleus is idempotent. -/
theorem relu_idempotent (v : Fin n → ℝ) :
    reluNucleus n (reluNucleus n v) = reluNucleus n v :=
  reluNucleus_idempotent n v

/-- Every ReLU-projected coordinate is nonnegative. -/
theorem relu_nonneg (v : Fin n → ℝ) (i : Fin n) :
    0 ≤ reluNucleus n v i := by
  change 0 ≤ max (v i) 0
  exact le_max_right _ _

/-- ReLU never exceeds the absolute value of the original coordinate. -/
theorem relu_component_le_abs (v : Fin n → ℝ) (i : Fin n) :
    reluNucleus n v i ≤ |v i| := by
  change max (v i) 0 ≤ |v i|
  exact max_le (le_abs_self _) (by simpa using abs_nonneg (v i))

/-- Squared coordinates do not increase under ReLU projection. -/
theorem relu_sq_le_sq (v : Fin n → ℝ) (i : Fin n) :
    (reluNucleus n v i)^2 ≤ (v i)^2 := by
  have hnon : 0 ≤ reluNucleus n v i := relu_nonneg v i
  have habs : reluNucleus n v i ≤ |v i| := relu_component_le_abs v i
  have hproj_abs : |reluNucleus n v i| ≤ |v i| := by
    simpa [abs_of_nonneg hnon] using habs
  exact sq_le_sq.2 hproj_abs

/-- The finite-dimensional square-sum energy cannot increase under ReLU. -/
theorem relu_sqSum_le_sqSum (v : Fin n → ℝ) :
    sqSum (reluNucleus n v) ≤ sqSum v := by
  unfold sqSum
  exact Finset.sum_le_sum (fun i _ => relu_sq_le_sq v i)

/-- The square-sum energy of a projected vector is nonnegative. -/
theorem relu_sqSum_nonneg (v : Fin n → ℝ) :
    0 ≤ sqSum (reluNucleus n v) := by
  unfold sqSum
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (reluNucleus n v i))

/-- ReLU fixes vectors that are already componentwise nonnegative. -/
theorem relu_eq_of_nonneg (v : Fin n → ℝ) (h : ∀ i, 0 ≤ v i) :
    reluNucleus n v = v := by
  funext i
  change max (v i) 0 = v i
  exact max_eq_left (h i)

/-- Meet preservation is inherited from the existing nucleus proof. -/
theorem relu_map_inf (v w : Fin n → ℝ) :
    reluNucleus n (v ⊓ w) = reluNucleus n v ⊓ reluNucleus n w :=
  reluNucleus_map_inf n v w

/-- Every diagonal Gram contribution after projection is nonnegative. -/
theorem projectedGramDiag_nonneg (samples : Fin m → Fin n → ℝ) (j : Fin n) :
    0 ≤ projectedGramDiag samples j := by
  unfold projectedGramDiag
  exact Finset.sum_nonneg (fun s _ => sq_nonneg (reluNucleus n (samples s) j))

/-- ReLU projection cannot increase diagonal Gram contributions. -/
theorem projectedGramDiag_le (samples : Fin m → Fin n → ℝ) (j : Fin n) :
    projectedGramDiag samples j ≤ ∑ s, (samples s j)^2 := by
  unfold projectedGramDiag
  exact Finset.sum_le_sum (fun s _ => relu_sq_le_sq (samples s) j)

end Eigen
end HeytingLean
