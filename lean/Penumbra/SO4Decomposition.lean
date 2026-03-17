import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Penumbra.MobiusSO4Embedding

/-!
# Penumbra.SO4Decomposition

Concrete `so(4) = su(2)⁺ ⊕ su(2)⁻` bookkeeping for the Penumbra embedding.
-/

namespace Penumbra

open Matrix

/-- The anti-self-dual `J₂⁻` basis element. -/
def j2Minus : SO4 :=
  !![0, 0, -1, 0;
     0, 0, 0, -1;
     1, 0, 0, 0;
     0, 1, 0, 0]

/-- The anti-self-dual `J₃⁻` basis element. -/
def j3Minus : SO4 :=
  !![0, 0, 0, -1;
     0, 0, 1, 0;
     0, -1, 0, 0;
     1, 0, 0, 0]

/-- Rebuild a skew `4 × 4` matrix from its six upper-triangular coordinates. -/
def skewOfCoords (a01 a02 a03 a12 a13 a23 : ℝ) : SO4 :=
  !![0, a01, a02, a03;
     -a01, 0, a12, a13;
     -a02, -a12, 0, a23;
     -a03, -a13, -a23, 0]

/-- Concrete projection onto the self-dual factor. -/
noncomputable def plusProjection (A : SO4) : SO4 :=
  let a01 := A 0 1
  let a02 := A 0 2
  let a03 := A 0 3
  let a12 := A 1 2
  let a13 := A 1 3
  let a23 := A 2 3
  let plus1 := (a01 + a23) / 2
  let plus2 := (a02 - a13) / 2
  let plus3 := (a03 + a12) / 2
  !![0, plus1, plus2, plus3;
     -plus1, 0, plus3, -plus2;
     -plus2, -plus3, 0, plus1;
     -plus3, plus2, -plus1, 0]

/-- Concrete projection onto the anti-self-dual factor. -/
noncomputable def minusProjection (A : SO4) : SO4 :=
  let a01 := A 0 1
  let a02 := A 0 2
  let a03 := A 0 3
  let a12 := A 1 2
  let a13 := A 1 3
  let a23 := A 2 3
  let minus1 := (a01 - a23) / 2
  let minus2 := (a02 + a13) / 2
  let minus3 := (a03 - a12) / 2
  !![0, minus1, minus2, minus3;
     -minus1, 0, -minus3, minus2;
     -minus2, minus3, 0, -minus1;
     -minus3, -minus2, minus1, 0]

/-- The concrete split recomposes the six skew coordinates exactly. -/
theorem plus_minus_recompose_coords (a01 a02 a03 a12 a13 a23 : ℝ) :
    plusProjection (skewOfCoords a01 a02 a03 a12 a13 a23) +
      minusProjection (skewOfCoords a01 a02 a03 a12 a13 a23) =
      skewOfCoords a01 a02 a03 a12 a13 a23 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [plusProjection, minusProjection, skewOfCoords]; try ring_nf)

/-- The Möbius generator lies entirely in the anti-self-dual factor. -/
theorem mobius_projection_split :
    plusProjection mobiusGenerator = 0 ∧ minusProjection mobiusGenerator = j1Minus := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> (simp [plusProjection, mobiusGenerator]; try ring_nf)
  · ext i j
    fin_cases i <;> fin_cases j <;> (simp [minusProjection, mobiusGenerator, j1Minus]; try ring_nf)

/-- Any anti-self-dual combination has zero self-dual projection. -/
theorem plusProjection_of_minus_combination (a b c : ℝ) :
    plusProjection (a • j1Minus + b • j2Minus + c • j3Minus) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> (simp [plusProjection, j1Minus, j2Minus, j3Minus, mobiusGenerator]; try ring_nf)

end Penumbra
