import HeytingLean.Magma.PredecessorMap

namespace HeytingLean.Magma

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A]

class PairEncoding (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A] where
  leftTag : A → Magma A → Magma A
  rightTag : A → Magma A → Magma A
  pair : A → A → Magma A → Magma A → Magma A
  leftTag_injective : ∀ {a : A} {x y : Magma A}, leftTag a x = leftTag a y → x = y
  rightTag_injective : ∀ {a : A} {x y : Magma A}, rightTag a x = rightTag a y → x = y
  left_mem_pair : ∀ {a₀ a₁ : A} {x y : Magma A},
    leftTag a₀ x ∈ pair a₀ a₁ x y
  right_mem_pair : ∀ {a₀ a₁ : A} {x y : Magma A},
    rightTag a₁ y ∈ pair a₀ a₁ x y
  mem_pair_cases : ∀ {a₀ a₁ : A} {x y z : Magma A},
    z ∈ pair a₀ a₁ x y → z ≤ leftTag a₀ x ∨ z ≤ rightTag a₁ y
  left_not_right : ∀ {a₀ a₁ : A} (_h : Incomparable a₀ a₁) {x y : Magma A},
    ¬ leftTag a₀ x ≤ rightTag a₁ y
  right_not_left : ∀ {a₀ a₁ : A} (_h : Incomparable a₀ a₁) {x y : Magma A},
    ¬ rightTag a₁ y ≤ leftTag a₀ x
  pair_mono : ∀ {a₀ a₁ : A} {x x' y y' : Magma A},
    x ≤ x' → y ≤ y' → pair a₀ a₁ x y ≤ pair a₀ a₁ x' y'

variable [PairEncoding A]

def pr2 (x : Magma A) : Magma A := pr (pr x)

def magmatic_pair (a₀ a₁ : A) (_h : Incomparable a₀ a₁) (x y : Magma A) : Magma A :=
  PairEncoding.pair a₀ a₁ x y

theorem collateral_subpairs (a₀ a₁ : A) (h : Incomparable a₀ a₁)
    {x y x' y' : Magma A} (hx : x' ≤ x) (hy : y' ≤ y) :
    magmatic_pair a₀ a₁ h x' y' ≤ magmatic_pair a₀ a₁ h x y :=
  PairEncoding.pair_mono hx hy

/-- Theorem 3.4 in the interface presentation: only the same-side case can
survive, while the two cross-side cases are excluded by the atom markers. -/
theorem pair_injective (a₀ a₁ : A) (h : Incomparable a₀ a₁)
    (x y x' y' : Magma A) :
    magmatic_pair a₀ a₁ h x y = magmatic_pair a₀ a₁ h x' y' ↔
      x = x' ∧ y = y' := by
  constructor
  · intro heq
    -- Case I: the left marker lands on the left marker, and the right marker on the right.
    have hxl_or_cross :
        PairEncoding.leftTag a₀ x ≤ PairEncoding.leftTag a₀ x' ∨
        PairEncoding.leftTag a₀ x ≤ PairEncoding.rightTag a₁ y' := by
      have hxmem : PairEncoding.leftTag a₀ x ∈ magmatic_pair a₀ a₁ h x' y' := by
        have hxmem0 : PairEncoding.leftTag a₀ x ∈ magmatic_pair a₀ a₁ h x y := by
          simpa [magmatic_pair] using
            (PairEncoding.left_mem_pair (a₀ := a₀) (a₁ := a₁) (x := x) (y := y))
        simpa [heq] using hxmem0
      simpa [magmatic_pair] using PairEncoding.mem_pair_cases hxmem
    have hxl : PairEncoding.leftTag a₀ x ≤ PairEncoding.leftTag a₀ x' := by
      cases hxl_or_cross with
      | inl hsame => exact hsame
      | inr hcross => exact False.elim (PairEncoding.left_not_right h hcross)
    have hxl'_or_cross :
        PairEncoding.leftTag a₀ x' ≤ PairEncoding.leftTag a₀ x ∨
        PairEncoding.leftTag a₀ x' ≤ PairEncoding.rightTag a₁ y := by
      have hxmem : PairEncoding.leftTag a₀ x' ∈ magmatic_pair a₀ a₁ h x y := by
        have hxmem0 : PairEncoding.leftTag a₀ x' ∈ magmatic_pair a₀ a₁ h x' y' := by
          simpa [magmatic_pair] using
            (PairEncoding.left_mem_pair (a₀ := a₀) (a₁ := a₁) (x := x') (y := y'))
        simpa [heq] using hxmem0
      simpa [magmatic_pair] using PairEncoding.mem_pair_cases hxmem
    have hxl' : PairEncoding.leftTag a₀ x' ≤ PairEncoding.leftTag a₀ x := by
      cases hxl'_or_cross with
      | inl hsame => exact hsame
      | inr hcross => exact False.elim (PairEncoding.left_not_right h hcross)
    have hx : x = x' := PairEncoding.leftTag_injective (u.le_antisymm hxl hxl')
    -- Case II: left-to-right is impossible by `left_not_right`.
    -- Case III: right-to-left is impossible by `right_not_left`.
    have hyr_or_cross :
        PairEncoding.rightTag a₁ y ≤ PairEncoding.leftTag a₀ x' ∨
        PairEncoding.rightTag a₁ y ≤ PairEncoding.rightTag a₁ y' := by
      have hymem : PairEncoding.rightTag a₁ y ∈ magmatic_pair a₀ a₁ h x' y' := by
        have hymem0 : PairEncoding.rightTag a₁ y ∈ magmatic_pair a₀ a₁ h x y := by
          simpa [magmatic_pair] using
            (PairEncoding.right_mem_pair (a₀ := a₀) (a₁ := a₁) (x := x) (y := y))
        simpa [heq] using hymem0
      simpa [magmatic_pair] using PairEncoding.mem_pair_cases hymem
    have hyr : PairEncoding.rightTag a₁ y ≤ PairEncoding.rightTag a₁ y' := by
      cases hyr_or_cross with
      | inl hcross => exact False.elim (PairEncoding.right_not_left h hcross)
      | inr hsame => exact hsame
    have hyr'_or_cross :
        PairEncoding.rightTag a₁ y' ≤ PairEncoding.leftTag a₀ x ∨
        PairEncoding.rightTag a₁ y' ≤ PairEncoding.rightTag a₁ y := by
      have hymem : PairEncoding.rightTag a₁ y' ∈ magmatic_pair a₀ a₁ h x y := by
        have hymem0 : PairEncoding.rightTag a₁ y' ∈ magmatic_pair a₀ a₁ h x' y' := by
          simpa [magmatic_pair] using
            (PairEncoding.right_mem_pair (a₀ := a₀) (a₁ := a₁) (x := x') (y := y'))
        simpa [heq] using hymem0
      simpa [magmatic_pair] using PairEncoding.mem_pair_cases hymem
    have hyr' : PairEncoding.rightTag a₁ y' ≤ PairEncoding.rightTag a₁ y := by
      cases hyr'_or_cross with
      | inl hcross => exact False.elim (PairEncoding.right_not_left h hcross)
      | inr hsame => exact hsame
    have hy : y = y' := PairEncoding.rightTag_injective (u.le_antisymm hyr hyr')
    exact ⟨hx, hy⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end HeytingLean.Magma
