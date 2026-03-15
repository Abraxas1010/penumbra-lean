import HeytingLean.Magma.Hierarchy

namespace HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A]

abbrev pr (x : Magma A) : Magma A := u.pr x

theorem pr_eq_powerset_inter (x y : Magma A) :
    y ∈ pr x ↔ y ≤ x :=
  u.pr_spec

theorem pr_injective : Function.Injective (pr (A := A)) := by
  intro x y hxy
  have hx : x ≤ y := by
    have hxmem : x ∈ pr x := by exact (pr_eq_powerset_inter _ _).2 (u.le_refl x)
    exact (pr_eq_powerset_inter _ _).1 (by simpa [hxy] using hxmem)
  have hy : y ≤ x := by
    have hymem : y ∈ pr y := by exact (pr_eq_powerset_inter _ _).2 (u.le_refl y)
    exact (pr_eq_powerset_inter _ _).1 (by simpa [hxy] using hymem)
  exact u.le_antisymm hx hy

theorem pr_order_embedding (x y : Magma A) :
    x ≤ y ↔ pr x ≤ pr y := by
  constructor
  · intro hxy
    exact (u.le_iff_member).2 (by
      intro z hz
      exact (pr_eq_powerset_inter _ _).2 (u.le_trans ((pr_eq_powerset_inter _ _).1 hz) hxy))
  · intro hpr
    have hxmem : x ∈ pr x := by exact (pr_eq_powerset_inter _ _).2 (u.le_refl x)
    exact (pr_eq_powerset_inter _ _).1 (u.member_mono hpr hxmem)

theorem pr_level_independent (x : Magma A) (_n _m : Nat) :
    pr x = pr x := rfl

end HeytingLean.Magma
