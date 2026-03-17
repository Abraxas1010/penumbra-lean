import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Penumbra.LyapunovClassifierBoundary

The Phase 4 Penumbra reduction collapses the Phase 3 taxonomy
`classical | nested | chaotic` to the binary partition
`integrable | chaotic`. On the concrete 14-substrate ensemble, that binary
partition is exactly the sign partition of the measured maximum Lyapunov
exponent.
-/

namespace Penumbra

noncomputable section

inductive Phase3Substrate where
  | tauField | rgFlow | neural | lorenz | harmonic | coulomb | standingWave
  | chua | standardMap | coupledOscillators | doublePendulum | henon | logistic | rossler
  deriving DecidableEq, Repr

inductive TernaryClass where
  | classical | nested | chaotic
  deriving DecidableEq, Repr

inductive BinaryClass where
  | integrable | chaotic
  deriving DecidableEq, Repr

def verifiedClass : Phase3Substrate → TernaryClass
  | .tauField => .classical
  | .rgFlow => .classical
  | .neural => .nested
  | .lorenz => .chaotic
  | .harmonic => .classical
  | .coulomb => .classical
  | .standingWave => .nested
  | .chua => .chaotic
  | .standardMap => .chaotic
  | .coupledOscillators => .nested
  | .doublePendulum => .chaotic
  | .henon => .chaotic
  | .logistic => .chaotic
  | .rossler => .chaotic

def projectBinary : TernaryClass → BinaryClass
  | .classical => .integrable
  | .nested => .integrable
  | .chaotic => .chaotic

def binaryClass : Phase3Substrate → BinaryClass := fun s => projectBinary (verifiedClass s)

def maxLyapunov : Phase3Substrate → ℝ
  | .tauField => 0
  | .rgFlow => 0
  | .neural => 0
  | .lorenz => 9 / 10
  | .harmonic => 0
  | .coulomb => 0
  | .standingWave => 0
  | .chua => 11 / 100
  | .standardMap => 7 / 10
  | .coupledOscillators => 0
  | .doublePendulum => 3 / 5
  | .henon => 2 / 5
  | .logistic => 1 / 2
  | .rossler => 7 / 100

def lyapunovSignClassifier (lam : ℝ) : BinaryClass :=
  if lam > 0 then .chaotic else .integrable

theorem maxLyapunov_nonnegative (s : Phase3Substrate) : 0 ≤ maxLyapunov s := by
  cases s <;> norm_num [maxLyapunov]

theorem maxLyapunov_positive_iff_chaotic (s : Phase3Substrate) :
    0 < maxLyapunov s ↔ binaryClass s = .chaotic := by
  cases s <;> simp [maxLyapunov, binaryClass, projectBinary, verifiedClass]

theorem lyapunov_classifier_matches_binary_projection (s : Phase3Substrate) :
    lyapunovSignClassifier (maxLyapunov s) = binaryClass s := by
  cases s <;> simp [lyapunovSignClassifier, maxLyapunov, binaryClass, projectBinary, verifiedClass]

theorem chaotic_iff_positive_lyapunov (s : Phase3Substrate) :
    lyapunovSignClassifier (maxLyapunov s) = .chaotic ↔ 0 < maxLyapunov s := by
  rw [lyapunov_classifier_matches_binary_projection]
  exact (maxLyapunov_positive_iff_chaotic s).symm

end

end Penumbra
