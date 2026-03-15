import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Find
import HeytingLean.LoF.IntReentry

namespace HeytingLean
namespace Generative

open HeytingLean.LoF
open scoped Classical

variable {α : Type u} [PrimaryAlgebra α]

namespace IntNucleusKit

/-- Iterate an interior nucleus `R` `n` times. -/
def ibreathe (R : IntReentry α) : ℕ → α → α
  | 0, a => a
  | Nat.succ n, a => R (ibreathe (R := R) n a)

@[simp] lemma ibreathe_zero (R : IntReentry α) (a : α) :
    ibreathe (R := R) 0 a = a := rfl

@[simp] lemma ibreathe_succ (R : IntReentry α) (n : ℕ) (a : α) :
    ibreathe (R := R) (n + 1) a = R (ibreathe (R := R) n a) := rfl

/-- Stabilisation after one extra step by idempotence. -/
private lemma iterate_stabilises (R : IntReentry α) (a : α) :
    ∃ n : ℕ, ibreathe (R := R) (n + 1) a = ibreathe (R := R) n a := by
  refine ⟨1, ?_⟩
  simp [ibreathe]

/-- Minimal breath count required for stabilisation. -/
noncomputable def ibirth (R : IntReentry α) (a : α) : ℕ :=
  Nat.find (iterate_stabilises (R := R) (a := a))

lemma ibirth_spec (R : IntReentry α) (a : α) :
    ibreathe (R := R) (ibirth (R := R) a + 1) a =
      ibreathe (R := R) (ibirth (R := R) a) a :=
  Nat.find_spec (iterate_stabilises (R := R) (a := a))

lemma ibirth_min (R : IntReentry α) (a : α) {m : ℕ}
    (hm : ibreathe (R := R) (m + 1) a = ibreathe (R := R) m a) :
    ibirth (R := R) a ≤ m :=
  Nat.find_min' (iterate_stabilises (R := R) (a := a)) hm

lemma ibirth_le_one (R : IntReentry α) (a : α) : ibirth (R := R) a ≤ 1 := by
  have : ibreathe (R := R) 2 a = ibreathe (R := R) 1 a := by
    simp [ibreathe]
  exact ibirth_min (R := R) (a := a) this

@[simp] lemma ibirth_eq_zero_iff (R : IntReentry α) (a : α) :
    ibirth (R := R) a = 0 ↔ R a = a := by
  constructor
  · intro h
    have := ibirth_spec (R := R) (a := a)
    simpa [ibreathe, h] using this
  · intro hfix
    have : ibreathe (R := R) 1 a = ibreathe (R := R) 0 a := by
      simp [ibreathe, hfix]
    have := ibirth_min (R := R) (a := a) (m := 0) this
    exact le_antisymm this (Nat.zero_le _)

@[simp] lemma ibirth_eq_zero_of_fixed (R : IntReentry α) {a : α}
    (h : R a = a) : ibirth (R := R) a = 0 :=
  (ibirth_eq_zero_iff (R := R) (a := a)).mpr h

/-- Interior-Occam: simply apply the interior nucleus (idempotent). -/
def ioccam (R : IntReentry α) (a : α) : α := R a

@[simp] lemma ioccam_idem (R : IntReentry α) (a : α) :
    R (ioccam (R := R) a) = ioccam (R := R) a := by
  simp [ioccam]

end IntNucleusKit

end Generative
end HeytingLean
