import HeytingLean.Magma.LowerTopology

namespace HeytingLean.Magma

open Classical

variable {A : Type*} [MagmaticAtoms A]

/-- The higher magmatic universe is represented abstractly: the lower-topology
presentation is concrete, while the recursive hierarchy is exposed through a
typeclass interface that records the paper's governing laws. -/
class MagmaticUniverse (A : Type*) [MagmaticAtoms A] where
  Magma : Type*
  instMembership : Membership Magma Magma
  instLE : LE Magma
  instPartialOrder : PartialOrder Magma
  le_refl : ∀ x : Magma, x ≤ x
  le_trans : ∀ {x y z : Magma}, x ≤ y → y ≤ z → x ≤ z
  le_antisymm : ∀ {x y : Magma}, x ≤ y → y ≤ x → x = y
  le_iff_member : ∀ {x y : Magma}, x ≤ y ↔ ∀ {z : Magma}, z ∈ x → z ∈ y
  member_mono : ∀ {x y z : Magma}, x ≤ y → z ∈ x → z ∈ y
  lower_mem : ∀ {x y z : Magma}, z ∈ x → y ≤ z → y ∈ x
  lift : LowerOpen A → Magma
  pr : Magma → Magma
  pr_spec : ∀ {x y : Magma}, y ∈ pr x ↔ y ≤ x
  level : Magma → Nat
  level_mono : ∀ {x y : Magma}, x ≤ y → level x ≤ level y
  level_strict : ∀ {x y : Magma}, y < x → level y < level x
  level_positive : ∀ x : Magma, 1 ≤ level x
  nonempty : ∀ x : Magma, ∃ y : Magma, y ∈ x
  no_minimal : ∀ x : Magma, ∃ y : Magma, y < x

attribute [instance] MagmaticUniverse.instMembership
attribute [instance] MagmaticUniverse.instLE
attribute [instance] MagmaticUniverse.instPartialOrder

set_option linter.dupNamespace false in
abbrev Magma (A : Type*) [MagmaticAtoms A] [u : MagmaticUniverse A] := u.Magma

namespace MagmaticUniverse

variable [u : MagmaticUniverse A]

@[simp] theorem mem_pr_iff {x y : Magma A} :
    y ∈ u.pr x ↔ y ≤ x :=
  u.pr_spec

theorem self_mem_pr (x : Magma A) : x ∈ u.pr x := by
  exact (u.pr_spec).2 (u.le_refl x)

theorem exists_strict_smaller (x : Magma A) : ∃ y : Magma A, y < x :=
  u.no_minimal x

abbrev hierarchyLevel (x : Magma A) : Nat := u.level x

theorem hierarchy_cumulative {x y : Magma A} (hxy : x ≤ y) :
    hierarchyLevel x ≤ hierarchyLevel y :=
  u.level_mono hxy

theorem strict_predecessor_drops_level {x y : Magma A} (hyx : y < x) :
    hierarchyLevel y < hierarchyLevel x :=
  u.level_strict hyx

theorem hierarchy_level_positive (x : Magma A) : 1 ≤ hierarchyLevel x :=
  u.level_positive x

end MagmaticUniverse

end HeytingLean.Magma
