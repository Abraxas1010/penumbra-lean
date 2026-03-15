import Mathlib.Data.Nat.Basic
import HeytingLean.LoF.Nucleus

namespace HeytingLean
namespace Epistemic

open Function HeytingLean.LoF
open scoped Classical

variable {α : Type u} [PrimaryAlgebra α]

/-- Iterate the nucleus `n` times, recording the number of breaths explicitly. -/
def breathe (R : Reentry α) : ℕ → α → α
  | 0, a => a
  | Nat.succ n, a => R (breathe (R := R) n a)

@[simp] lemma breathe_zero (R : Reentry α) (a : α) :
    breathe (R := R) 0 a = a := rfl

@[simp] lemma breathe_succ (R : Reentry α) (n : ℕ) (a : α) :
    breathe (R := R) (n + 1) a = R (breathe (R := R) n a) := rfl

/-- The iterated nucleus stabilises after a single extra breath thanks to idempotence. -/
private lemma iterate_stabilises (R : Reentry α) (a : α) :
    ∃ n : ℕ, breathe (R := R) (n + 1) a = breathe (R := R) n a := by
  refine ⟨1, ?_⟩
  calc
    breathe (R := R) 2 a = R (breathe (R := R) 1 a) := by simp [breathe]
    _ = R (R a) := by simp [breathe]
    _ = R a := Reentry.idempotent (R := R) (a := a)
    _ = breathe (R := R) 1 a := by simp [breathe]

/-- The **birthday** (minimal breath count) needed for `a` to stabilise under the nucleus. -/
noncomputable def birth (R : Reentry α) (a : α) : ℕ :=
  Nat.find (iterate_stabilises (R := R) (a := a))

/-- The birthday witnesses a fixed point: the `(n+1)` and `n` iterates coincide at `n = birth R a`. -/
lemma birth_spec (R : Reentry α) (a : α) :
    breathe (R := R) (birth R a + 1) a =
      breathe (R := R) (birth R a) a :=
  Nat.find_spec (iterate_stabilises (R := R) (a := a))

/-- Minimality: if stability occurs at step `m`, then `birth R a ≤ m`. -/
lemma birth_min (R : Reentry α) (a : α) {m : ℕ}
    (hm : breathe (R := R) (m + 1) a = breathe (R := R) m a) :
    birth R a ≤ m :=
  Nat.find_min' (iterate_stabilises (R := R) (a := a)) hm

/-- Every stability event happens within one breath thanks to idempotence of `R`. -/
lemma birth_le_one (R : Reentry α) (a : α) : birth R a ≤ 1 := by
  have h₁ : breathe (R := R) 2 a = breathe (R := R) 1 a := by
    calc
      breathe (R := R) 2 a = R (breathe (R := R) 1 a) := by simp [breathe]
      _ = R (R a) := by simp [breathe]
      _ = R a := Reentry.idempotent (R := R) (a := a)
      _ = breathe (R := R) 1 a := by simp [breathe]
  exact birth_min (R := R) (a := a) h₁

/-- Birthday zero characterises fixed points. -/
lemma birth_eq_zero_iff (R : Reentry α) (a : α) :
    birth R a = 0 ↔ R a = a := by
  constructor
  · intro h
    have hb := birth_spec (R := R) (a := a)
    have hb0 : birth R a = 0 := h
    have hspec := hb
    have hRa : R a = a := by
      have := hspec
      simp [breathe, hb0] at this
      exact this
    exact hRa
  · intro hfix
    have h₀ : breathe (R := R) 1 a = breathe (R := R) 0 a := by
      calc
        breathe (R := R) 1 a = R a := by simp [breathe]
        _ = a := hfix
        _ = breathe (R := R) 0 a := by simp [breathe]
    have hmin :=
      birth_min (R := R) (a := a) (m := 0) h₀
    exact le_antisymm hmin (Nat.zero_le _)

/-- Fixed points have birthday zero. -/
@[simp] lemma birth_eq_zero_of_fixed (R : Reentry α) {a : α}
    (h : R a = a) : birth R a = 0 :=
  (birth_eq_zero_iff (R := R) (a := a)).mpr h

/-- Conversely, birthday zero guarantees `a` is fixed by the nucleus. -/
lemma fixed_of_birth_zero (R : Reentry α) {a : α}
    (h : birth R a = 0) : R a = a :=
  (birth_eq_zero_iff (R := R) (a := a)).mp h

/-- Bottom already satisfies the nucleus, so its birthday is zero. -/
@[simp] lemma birth_bot (R : Reentry α) :
    birth R (⊥ : α) = 0 :=
  birth_eq_zero_of_fixed (R := R) (a := (⊥ : α)) R.map_bot

/-- Candidate explanations lying inside a specification `a`. -/
def occamCandidates (R : Reentry α) (a : α) : Set α :=
  {u | u ≤ a ∧ R u = u}

/-- Candidate explanations sit below their specification `a`. -/
lemma occamCandidate_le {R : Reentry α} {a u : α}
    (hu : u ∈ occamCandidates (R := R) a) : u ≤ a :=
  hu.1

/-- Candidate explanations are fixed by the nucleus. -/
lemma occamCandidate_fixed {R : Reentry α} {a u : α}
    (hu : u ∈ occamCandidates (R := R) a) : R u = u :=
  hu.2

/-- Witness existence for the minimal birthday among invariant explanations under `a`. -/
private lemma occamBirth_exists (R : Reentry α) (a : α) :
    ∃ n : ℕ, ∃ u, u ≤ a ∧ R u = u ∧ birth R u = n := by
  refine ⟨birth R (⊥ : α), ⊥, ?_⟩
  refine ⟨bot_le, R.map_bot, rfl⟩

/-- The minimal birthday attained by an invariant contained in `a`. -/
noncomputable def occamBirth (R : Reentry α) (a : α) : ℕ :=
  Nat.find (occamBirth_exists (R := R) (a := a))

/-- The minimal birthday is realised by some invariant below `a`. -/
lemma occamBirth_spec (R : Reentry α) (a : α) :
    ∃ u, u ≤ a ∧ R u = u ∧ birth R u = occamBirth (R := R) a :=
  Nat.find_spec (occamBirth_exists (R := R) (a := a))

/-- Minimality: any witness at birthday `m` bounds `occamBirth a` from above. -/
lemma occamBirth_min (R : Reentry α) (a : α) {m : ℕ}
    (hm : ∃ u, u ≤ a ∧ R u = u ∧ birth R u = m) :
    occamBirth (R := R) a ≤ m :=
  Nat.find_min' (occamBirth_exists (R := R) (a := a)) hm

/-- Because `⊥` is fixed, the minimal birthday attained inside `a` is always zero. -/
lemma occamBirth_zero (R : Reentry α) (a : α) :
    occamBirth (R := R) a = 0 := by
  have hbot :
      ∃ u, u ≤ a ∧ R u = u ∧ birth R u = 0 := by
    refine ⟨⊥, bot_le, R.map_bot, ?_⟩
    exact birth_bot (R := R)
  have hle := occamBirth_min (R := R) (a := a) hbot
  exact le_antisymm hle (Nat.zero_le _)

/-- Invariant explanations at the minimal birthday. -/
def occamMinimal (R : Reentry α) (a : α) : Set α :=
  {u | u ≤ a ∧ R u = u ∧ birth R u = occamBirth (R := R) a}

/-- `occamMinimal` coincides with all invariant candidates since every fixed point has birthday `0`. -/
lemma occamMinimal_eq_candidates (R : Reentry α) (a : α) :
    occamMinimal (R := R) a = occamCandidates (R := R) a := by
  ext u
  constructor
  · intro hu
    exact And.intro hu.1 hu.2.1
  · intro hu
    refine ⟨hu.1, hu.2, ?_⟩
    have : birth R u = 0 :=
      birth_eq_zero_of_fixed (R := R) (a := u) hu.2
    simpa [occamBirth_zero (R := R) (a := a)] using this

/-- Every minimal explanation is a candidate explanation. -/
lemma occamMinimal_subset (R : Reentry α) (a : α) :
    occamMinimal (R := R) a ⊆ occamCandidates (R := R) a := by
  intro u hu
  exact And.intro hu.1 hu.2.1

/-- There is always at least one minimal explanation (the infimum of candidates). -/
lemma occamMinimal_nonempty (R : Reentry α) (a : α) :
    (occamMinimal (R := R) a).Nonempty := by
  obtain ⟨u, hu⟩ := occamBirth_spec (R := R) (a := a)
  exact ⟨u, hu⟩

/-- The join of all minimal-birthday invariant explanations. -/
noncomputable def occamCore (R : Reentry α) (a : α) : α :=
  sSup (occamMinimal (R := R) a)

/-- The Occam core stays below the specification `a`. -/
lemma occamCore_le (R : Reentry α) (a : α) :
    occamCore (R := R) a ≤ a := by
  refine sSup_le ?_
  intro u hu
  exact (occamMinimal_subset (R := R) (a := a) hu).1

/-- Every minimal explanation is below the Occam core. -/
lemma le_occamCore_of_minimal (R : Reentry α) {a u : α}
    (hu : u ∈ occamMinimal (R := R) a) :
    u ≤ occamCore (R := R) a := by
  change u ≤ sSup _
  exact le_sSup hu

/-- The Occam reduction closes the minimal-birthday explanations back via `R`. -/
noncomputable def occam (R : Reentry α) (a : α) : α :=
  R (occamCore (R := R) a)

/-- Applying `occam` and then the nucleus stays below `R a`. -/
lemma occam_le_reentry (R : Reentry α) (a : α) :
    occam (R := R) a ≤ R a :=
  R.monotone (occamCore_le (R := R) a)

/-- The Occam reduction contains every minimal explanation. -/
lemma occam_contains_minimal (R : Reentry α) {a u : α}
    (hu : u ∈ occamMinimal (R := R) a) :
    u ≤ occam (R := R) a := by
  have hcore := le_occamCore_of_minimal (R := R) (a := a) hu
  have hmon := R.monotone hcore
  exact le_trans (Reentry.le_apply (R := R) (a := u)) hmon

/-- Any candidate explanation is contained in the Occam reduction. -/
lemma occam_contains_candidate (R : Reentry α) {a u : α}
    (hu_le : u ≤ a) (hu_fix : R u = u) :
    u ≤ occam (R := R) a := by
  have hb : birth R u = 0 :=
    birth_eq_zero_of_fixed (R := R) (a := u) hu_fix
  have hmem : u ∈ occamMinimal (R := R) a := by
    refine ⟨hu_le, hu_fix, ?_⟩
    simp [occamBirth_zero (R := R) (a := a), hb]
  exact occam_contains_minimal (R := R) (a := a) hmem

/-- `occam` is idempotent because it applies the nucleus to a fixed element. -/
lemma occam_idempotent (R : Reentry α) (a : α) :
    R (occam (R := R) a) = occam (R := R) a :=
  Reentry.idempotent (R := R) (a := occamCore (R := R) a)

/-- `occam` is monotone: enlarging the specification can only enlarge the reduction. -/
lemma occam_monotone (R : Reentry α) :
    Monotone (occam (R := R)) := by
  intro a b h
  have hSubset :
      occamMinimal (R := R) a ⊆ occamMinimal (R := R) b := by
    have hSubsetCandidates :
        occamCandidates (R := R) a ⊆ occamCandidates (R := R) b := by
      intro u hu
      exact And.intro (le_trans hu.1 h) hu.2
    intro u hu
    have : u ≤ a ∧ R u = u :=
      (occamMinimal_subset (R := R) (a := a) hu)
    have hCan : u ∈ occamCandidates (R := R) a := this
    have hCan' := hSubsetCandidates hCan
    have hb : birth R u = 0 :=
      birth_eq_zero_of_fixed (R := R) (a := u) this.2
    refine ⟨hCan'.1, hCan'.2, ?_⟩
    simp [occamBirth_zero (R := R) (a := b), hb]
  have hCore :
      occamCore (R := R) a ≤ occamCore (R := R) b :=
    sSup_le_sSup hSubset
  exact R.monotone hCore

/-- The output of `occam` is always fixed, so its birthday is zero. -/
lemma occam_birth (R : Reentry α) (a : α) :
    birth R (occam (R := R) a) = 0 :=
  birth_eq_zero_of_fixed (R := R) (a := occam (R := R) a)
    (occam_idempotent (R := R) (a := a))

@[simp] lemma birth_eulerBoundary (R : Reentry α) :
    birth R ((R.eulerBoundary : R.Omega) : α) = 0 :=
  birth_eq_zero_of_fixed (R := R)
    (a := ((R.eulerBoundary : R.Omega) : α))
    (Reentry.Omega.apply_coe (R := R) (a := R.eulerBoundary))

end Epistemic
end HeytingLean
