import HeytingLean.LoF.Nucleus
import Mathlib.Tactic

namespace HeytingLean
namespace Logic
namespace Dialectic

open HeytingLean.LoF

variable {α : Type u} [PrimaryAlgebra α]

/-- Dialectic synthesis: close the union of thesis and antithesis under the re-entry nucleus. -/
def synth (R : Reentry α) (T A : α) : α :=
  R (T ⊔ A)

@[simp] lemma synth_idempotent (R : Reentry α) (T A : α) :
    R (synth (R := R) T A) = synth (R := R) T A :=
  Reentry.idempotent (R := R) (a := T ⊔ A)

lemma le_synth_left (R : Reentry α) (T A : α) :
    T ≤ synth (R := R) T A := by
  have hle : T ≤ T ⊔ A := le_sup_of_le_left le_rfl
  refine le_trans (Reentry.le_apply (R := R) (a := T)) ?_
  have hmono := R.monotone hle
  simpa [synth] using hmono

lemma le_synth_right (R : Reentry α) (T A : α) :
    A ≤ synth (R := R) T A := by
  have hle : A ≤ T ⊔ A := le_sup_of_le_right le_rfl
  refine le_trans (Reentry.le_apply (R := R) (a := A)) ?_
  have hmono := R.monotone hle
  simpa [synth] using hmono

lemma synth_le {R : Reentry α} {T A W : α}
    (hT : T ≤ W) (hA : A ≤ W) (hW : R W = W) :
    synth (R := R) T A ≤ W := by
  have hSup : T ⊔ A ≤ W := sup_le_iff.mpr ⟨hT, hA⟩
  have hmono := R.monotone hSup
  simpa [synth, hW] using hmono

/-! Convenience aliases to match the project terminology. -/

@[simp] lemma synthesis_fixed (R : Reentry α) (T A : α) :
    R (synth (R := R) T A) = synth (R := R) T A := by
  change R (R (T ⊔ A)) = R (T ⊔ A)
  exact Reentry.idempotent (R := R) (a := T ⊔ A)

lemma pole_left_to_synthesis (R : Reentry α) (T A : α) :
    T ≤ synth (R := R) T A :=
  le_synth_left (R := R) (T := T) (A := A)

lemma pole_right_to_synthesis (R : Reentry α) (T A : α) :
    A ≤ synth (R := R) T A :=
  le_synth_right (R := R) (T := T) (A := A)

lemma synthesis_least {R : Reentry α} {T A W : α}
    (hT : T ≤ W) (hA : A ≤ W) (hW : R W = W) :
    synth (R := R) T A ≤ W :=
  synth_le (R := R) (T := T) (A := A) (W := W) hT hA hW



/-- Synthesis specialised to the fixed-point lattice `Ω_R`. -/
def synthOmega (R : Reentry α) (T A : R.Omega) : R.Omega :=
  Reentry.Omega.mk (R := R)
    (synth (R := R) (T : α) (A : α))
    (synth_idempotent (R := R) (T := (T : α)) (A := (A : α)))

@[simp] lemma synthOmega_coe (R : Reentry α) (T A : R.Omega) :
    ((synthOmega (R := R) T A : R.Omega) : α) =
      synth (R := R) (T : α) (A : α) := rfl

lemma synthOmega_le {R : Reentry α} {T A W : R.Omega}
    (hT : T ≤ W) (hA : A ≤ W) :
    synthOmega (R := R) T A ≤ W := by
  change synth (R := R) (T : α) (A : α) ≤ (W : α)
  have hTW : (T : α) ≤ (W : α) := hT
  have hAW : (A : α) ≤ (W : α) := hA
  have hW : R (W : α) = (W : α) :=
    Reentry.Omega.apply_coe (R := R) (a := W)
  exact synth_le (R := R) hTW hAW hW

@[simp] lemma synthOmega_self (R : Reentry α) :
    synthOmega (R := R) R.eulerBoundary R.eulerBoundary =
      R.eulerBoundary := by
  apply le_antisymm
  · exact synthOmega_le (R := R) le_rfl le_rfl
  · change
      ((R.eulerBoundary : R.Omega) : α) ≤
        synth (R := R) ((R.eulerBoundary : R.Omega) : α)
          ((R.eulerBoundary : R.Omega) : α)
    exact le_synth_left (R := R)
      ((R.eulerBoundary : R.Omega) : α)
      ((R.eulerBoundary : R.Omega) : α)

/-! Primordial oscillation packaged and basic order facts. -/

/-- Synthesis specialised to the primordial poles (process/counter-process). -/
def oscillationOmega (R : Reentry α) : R.Omega :=
  synthOmega (R := R) R.process R.counterProcess

@[simp] lemma oscillationOmega_coe (R : Reentry α) :
    ((oscillationOmega (R := R) : R.Omega) : α)
      = synth (R := R) (R.primordial) (R.counter) := by
  simp [oscillationOmega, synthOmega, synth,
    Reentry.process_coe, Reentry.counterProcess_coe]

lemma le_synthOmega_left (R : Reentry α) (T A : R.Omega) :
    T ≤ synthOmega (R := R) T A := by
  change (T : α) ≤ synth (R := R) (T : α) (A : α)
  exact le_synth_left (R := R) (T := (T : α)) (A := (A : α))

lemma le_synthOmega_right (R : Reentry α) (T A : R.Omega) :
    A ≤ synthOmega (R := R) T A := by
  change (A : α) ≤ synth (R := R) (T : α) (A : α)
  exact le_synth_right (R := R) (T := (T : α)) (A := (A : α))

lemma eulerBoundary_le_oscillation (R : Reentry α) :
    R.eulerBoundary ≤ oscillationOmega (R := R) := by
  -- eulerBoundary = process, and process ≤ synth(process,counter)
  simpa [oscillationOmega, Reentry.eulerBoundary_eq_process]
    using (le_synthOmega_left (R := R) (T := R.process) (A := R.counterProcess))

end Dialectic
end Logic
end HeytingLean
