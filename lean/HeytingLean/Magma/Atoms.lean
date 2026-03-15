import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Basic

namespace HeytingLean.Magma

/-- Atoms carry the downward-directed preorder used in the lower topology. We
strengthen the PM's preorder sketch to a partial order so predecessor sets
determine their generators extensionally. -/
class MagmaticAtoms (A : Type*) extends PartialOrder A where
  /-- No atom is minimal: every atom has a strict predecessor. -/
  no_minimal : ∀ a : A, ∃ b : A, b ≤ a ∧ ¬ a ≤ b

variable {A : Type*} [MagmaticAtoms A]

/-- The predecessor set of an atom. -/
def predecessors (a : A) : Set A := { b : A | b ≤ a }

/-- Two atoms are incomparable when neither lies below the other. -/
def Incomparable (a₀ a₁ : A) : Prop := ¬ a₀ ≤ a₁ ∧ ¬ a₁ ≤ a₀

private noncomputable def predecessorChoice (a : A) : A :=
  Classical.choose (MagmaticAtoms.no_minimal a)

private theorem predecessorChoice_spec (a : A) :
    predecessorChoice a ≤ a ∧ ¬ a ≤ predecessorChoice a :=
  Classical.choose_spec (MagmaticAtoms.no_minimal a)

/-- A canonical infinite descending chain obtained by repeatedly choosing a
strict predecessor. -/
noncomputable def descendingChain (a : A) : ℕ → A
  | 0 => a
  | n + 1 => predecessorChoice (descendingChain a n)

theorem descendingChain_step (a : A) (n : ℕ) :
    descendingChain a (n + 1) ≤ descendingChain a n :=
  (predecessorChoice_spec _).1

theorem descendingChain_not_back (a : A) (n : ℕ) :
    ¬ descendingChain a n ≤ descendingChain a (n + 1) :=
  (predecessorChoice_spec _).2

theorem descendingChain_le (a : A) :
    ∀ {m n : ℕ}, m ≤ n → descendingChain a n ≤ descendingChain a m
  | _, _, hmn => by
      induction hmn with
      | refl => exact le_rfl
      | @step n h ih =>
          exact le_trans (descendingChain_step a n) ih

theorem descendingChain_injective (a : A) :
    Function.Injective (descendingChain a) := by
  intro m n hmn
  by_cases hlt : m < n
  · have htail : descendingChain a n ≤ descendingChain a (m + 1) :=
      descendingChain_le a (Nat.succ_le_of_lt hlt)
    have hbad : descendingChain a m ≤ descendingChain a (m + 1) := by
      simpa [hmn] using htail
    exact False.elim ((descendingChain_not_back a m) hbad)
  · by_cases hgt : n < m
    · have htail : descendingChain a m ≤ descendingChain a (n + 1) :=
        descendingChain_le a (Nat.succ_le_of_lt hgt)
      have hbad : descendingChain a n ≤ descendingChain a (n + 1) := by
        simpa [hmn] using htail
      exact False.elim ((descendingChain_not_back a n) hbad)
    · exact Nat.le_antisymm (Nat.not_lt.mp hgt) (Nat.not_lt.mp hlt)

theorem descendingChain_mem_predecessors (a : A) (n : ℕ) :
    descendingChain a n ∈ predecessors a := by
  exact descendingChain_le a (Nat.zero_le n)

theorem predecessors_infinite (a : A) : Set.Infinite (predecessors a) := by
  let f := descendingChain a
  have hRange : Set.Infinite (Set.range f) := Set.infinite_range_of_injective
    (descendingChain_injective a)
  have hsub : Set.range f ⊆ predecessors a := by
    intro x hx
    rcases hx with ⟨n, rfl⟩
    exact descendingChain_mem_predecessors a n
  exact hRange.mono hsub

theorem predecessors_eq_iff (a b : A) :
    predecessors a = predecessors b ↔ a = b := by
  constructor
  · intro h
    have ha : a ∈ predecessors a := by simp [predecessors]
    have hb : b ∈ predecessors b := by simp [predecessors]
    have hab' : a ∈ predecessors b := by simpa [h] using ha
    have hba' : b ∈ predecessors a := by simpa [h] using hb
    have hab : a ≤ b := by simpa [predecessors] using hab'
    have hba : b ≤ a := by simpa [predecessors] using hba'
    exact le_antisymm hab hba
  · intro h
    subst h
    rfl

/-- Existence of a pair of incomparable atoms is the second paper-level axiom
used by the ordered-pair construction. -/
axiom incomparable_pair_exists (A : Type*) [MagmaticAtoms A] :
    ∃ a₀ a₁ : A, Incomparable a₀ a₁

end HeytingLean.Magma
