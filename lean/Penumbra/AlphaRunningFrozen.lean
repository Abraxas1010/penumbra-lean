import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Penumbra.AlphaRunningFrozen

The one-loop QED coupling used by the Penumbra running-coupling experiment clamps `Q²` below the
electron-mass threshold. On that concrete implementation surface, the coupling is exactly frozen:
for `Q² ≤ mₑ²`, one obtains `α(Q²) = α₀`.
-/

namespace Penumbra

noncomputable section

/-- The low-energy fine-structure constant. -/
def alphaZero : ℝ := 1 / 137.035999084

/-- Electron mass in MeV. -/
def electronMassMeV : ℝ := 0.510998950

/-- The clamped one-loop QED running coupling matching the Rust implementation. -/
def alphaRunning (q_squared : ℝ) : ℝ :=
  let me2 := electronMassMeV ^ 2
  let safe_q2 := max q_squared me2
  alphaZero / (1 - (alphaZero / (3 * Real.pi)) * Real.log (safe_q2 / me2))

/-- Below the electron-mass threshold, the running coupling is exactly frozen at `α₀`. -/
theorem alpha_running_frozen_below_electron_mass
    (q_squared : ℝ) (hq : q_squared ≤ electronMassMeV ^ 2) :
    alphaRunning q_squared = alphaZero := by
  unfold alphaRunning
  simp [hq, alphaZero]

/-- In particular, zero momentum transfer evaluates to the low-energy coupling. -/
theorem alpha_running_at_zero : alphaRunning 0 = alphaZero := by
  apply alpha_running_frozen_below_electron_mass
  positivity

end

end Penumbra
