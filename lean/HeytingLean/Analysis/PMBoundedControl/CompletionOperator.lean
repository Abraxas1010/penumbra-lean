import Mathlib

/-!
# PM-Bounded Completion Operators

Core scalar completion operators used by the PM-bounded τ-control formalization.
The rational variant carries the main algebraic proof load; the tanh variant is
included with boundedness/continuity facts needed by the later phases.
-/

namespace HeytingLean
namespace Analysis
namespace PMBoundedControl

noncomputable section

/-- Efficient rational saturation from the PM-bounded τ-control paper. -/
def SatRational (Q_PM : ℝ) (x : ℝ) : ℝ :=
  x / (1 + |x| / Q_PM)

/-- Smooth tanh saturation from the PM-bounded τ-control paper. -/
def SatTanh (Q_PM : ℝ) (x : ℝ) : ℝ :=
  Q_PM * Real.tanh (x / Q_PM)

/-- Bundled scalar completion operator with a positive PM boundary. -/
structure PMCompletion where
  Q_PM : ℝ
  pos : 0 < Q_PM
  sat : ℝ → ℝ
  bounded : ∀ x, |sat x| ≤ Q_PM

theorem sat_rational_denominator_pos {Q_PM x : ℝ} (hQ : 0 < Q_PM) :
    0 < 1 + |x| / Q_PM := by
  positivity

theorem sat_rational_nonneg {Q_PM x : ℝ} (hQ : 0 < Q_PM) (hx : 0 ≤ x) :
    0 ≤ SatRational Q_PM x := by
  unfold SatRational
  exact div_nonneg hx (le_of_lt (sat_rational_denominator_pos hQ))

theorem sat_rational_nonpos {Q_PM x : ℝ} (hQ : 0 < Q_PM) (hx : x ≤ 0) :
    SatRational Q_PM x ≤ 0 := by
  unfold SatRational
  exact div_nonpos_of_nonpos_of_nonneg hx (le_of_lt (sat_rational_denominator_pos hQ))

theorem sat_rational_odd {Q_PM x : ℝ} :
    SatRational Q_PM (-x) = -SatRational Q_PM x := by
  unfold SatRational
  simp [abs_neg, neg_div]

theorem sat_rational_continuous {Q_PM : ℝ} (hQ : 0 < Q_PM) :
    Continuous (SatRational Q_PM) := by
  simpa [SatRational] using
    (continuous_id.div (continuous_const.add (continuous_abs.div_const Q_PM))
      (fun x => ne_of_gt (sat_rational_denominator_pos hQ (x := x))))

theorem sat_rational_bounded {Q_PM x : ℝ} (hQ : 0 < Q_PM) :
    |SatRational Q_PM x| ≤ Q_PM := by
  have hden : 0 < 1 + |x| / Q_PM := sat_rational_denominator_pos hQ
  have habs :
      |SatRational Q_PM x| = |x| / (1 + |x| / Q_PM) := by
    unfold SatRational
    simp [abs_div, abs_of_pos hden]
  rw [habs]
  have hmul : |x| ≤ Q_PM * (1 + |x| / Q_PM) := by
    field_simp [hQ.ne']
    nlinarith [abs_nonneg x, hQ]
  exact (div_le_iff₀ hden).2 hmul

theorem sat_rational_fix_on_interval {Q_PM x : ℝ}
    (hQ : 0 < Q_PM) (hx0 : 0 ≤ x) (_hxQ : x ≤ Q_PM) :
    SatRational Q_PM x ≤ x := by
  unfold SatRational
  rw [abs_of_nonneg hx0]
  have hden : 1 ≤ 1 + x / Q_PM := by
    have : 0 ≤ x / Q_PM := by positivity
    linarith
  exact div_le_self hx0 hden

theorem sat_rational_monotone {Q_PM : ℝ} (hQ : 0 < Q_PM) :
    Monotone (SatRational Q_PM) := by
  intro x y hxy
  by_cases hx : 0 ≤ x
  · have hy : 0 ≤ y := le_trans hx hxy
    rw [SatRational, abs_of_nonneg hx, SatRational, abs_of_nonneg hy]
    have hdx : 0 < 1 + x / Q_PM := by positivity
    have hdy : 0 < 1 + y / Q_PM := by positivity
    have hcross : x * (1 + y / Q_PM) ≤ y * (1 + x / Q_PM) := by
      field_simp [hQ.ne']
      nlinarith
    exact (div_le_div_iff₀ hdx hdy).2 hcross
  · have hx' : x ≤ 0 := le_of_not_ge hx
    by_cases hy : y ≤ 0
    · have hnonneg :
          SatRational Q_PM (-y) ≤ SatRational Q_PM (-x) := by
        have hy0 : 0 ≤ -y := by linarith
        have hx0 : 0 ≤ -x := by linarith
        rw [SatRational, abs_of_nonneg hy0, SatRational, abs_of_nonneg hx0]
        have hdx : 0 < 1 + (-y) / Q_PM := by positivity
        have hdy : 0 < 1 + (-x) / Q_PM := by positivity
        have hcross : (-y) * (1 + (-x) / Q_PM) ≤ (-x) * (1 + (-y) / Q_PM) := by
          field_simp [hQ.ne']
          nlinarith
        exact (div_le_div_iff₀ hdx hdy).2 hcross
      have hrewrite : -SatRational Q_PM y ≤ -SatRational Q_PM x := by
        simpa [sat_rational_odd] using hnonneg
      linarith
    · have hy' : 0 ≤ y := le_of_lt (lt_of_not_ge hy)
      have hleft : SatRational Q_PM x ≤ 0 := sat_rational_nonpos hQ hx'
      have hright : 0 ≤ SatRational Q_PM y := sat_rational_nonneg hQ hy'
      linarith

theorem sat_rational_sub_self {Q_PM x : ℝ} (hQ : 0 < Q_PM) :
    SatRational Q_PM x - x = -(x * (|x| / Q_PM)) / (1 + |x| / Q_PM) := by
  have hQ0 : Q_PM ≠ 0 := ne_of_gt hQ
  unfold SatRational
  field_simp [hQ0]
  ring_nf

theorem sat_rational_identity_regime_bound {Q_PM x : ℝ} (hQ : 0 < Q_PM) :
    |SatRational Q_PM x - x| ≤ |x| * (|x| / Q_PM) := by
  have hden : 0 < 1 + |x| / Q_PM := sat_rational_denominator_pos hQ
  rw [sat_rational_sub_self hQ, abs_div, abs_neg, abs_mul, abs_of_pos hden]
  rw [abs_of_nonneg (show 0 ≤ |x| / Q_PM by positivity)]
  have hfrac :
      (|x| / Q_PM) / (1 + |x| / Q_PM) ≤ |x| / Q_PM := by
    have hnonneg : 0 ≤ |x| / Q_PM := by positivity
    have hone : 1 ≤ 1 + |x| / Q_PM := by
      have : 0 ≤ |x| / Q_PM := hnonneg
      linarith
    exact div_le_self hnonneg hone
  have habs : 0 ≤ |x| := abs_nonneg x
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (mul_le_mul_of_nonneg_left hfrac habs)

theorem sat_rational_identity_regime {Q_PM ε x : ℝ} (hQ : 0 < Q_PM) (_hε : 0 < ε)
    (hx : |x| < ε * Q_PM) :
    |SatRational Q_PM x - x| ≤ ε * |x| := by
  have hmain := sat_rational_identity_regime_bound hQ (x := x)
  have hratio : |x| / Q_PM < ε := by
    exact (div_lt_iff₀ hQ).2 hx
  have habs : 0 ≤ |x| := abs_nonneg x
  have hmul : |x| * (|x| / Q_PM) ≤ ε * |x| := by
    nlinarith
  calc
    |SatRational Q_PM x - x| ≤ |x| * (|x| / Q_PM) := hmain
    _ ≤ ε * |x| := by simpa [mul_comm] using hmul

theorem sat_tanh_continuous {Q_PM : ℝ} :
    Continuous (SatTanh Q_PM) := by
  unfold SatTanh
  refine Continuous.mul continuous_const ?_
  simpa [Real.tanh_eq_sinh_div_cosh] using
    (Real.continuous_sinh.comp (continuous_id.div_const Q_PM)).div
      (Real.continuous_cosh.comp (continuous_id.div_const Q_PM))
      (fun x => ne_of_gt (Real.cosh_pos (x / Q_PM)))

theorem sat_tanh_odd {Q_PM x : ℝ} :
    SatTanh Q_PM (-x) = -SatTanh Q_PM x := by
  unfold SatTanh
  simp [Real.tanh_neg, neg_div]

theorem sat_tanh_bounded {Q_PM x : ℝ} (hQ : 0 ≤ Q_PM) :
    |SatTanh Q_PM x| ≤ Q_PM := by
  unfold SatTanh
  rw [abs_mul, abs_of_nonneg hQ]
  have hcosh : 0 < Real.cosh (x / Q_PM) := Real.cosh_pos _
  have hup : Real.tanh (x / Q_PM) < 1 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact (div_lt_iff₀ hcosh).2 (by simpa using Real.sinh_lt_cosh (x / Q_PM))
  have hlow : -1 < Real.tanh (x / Q_PM) := by
    have hs : Real.sinh (-(x / Q_PM)) < Real.cosh (-(x / Q_PM)) := Real.sinh_lt_cosh (-(x / Q_PM))
    rw [Real.sinh_neg, Real.cosh_neg] at hs
    have : -(Real.tanh (x / Q_PM)) < 1 := by
      have hrewrite :
          -(Real.tanh (x / Q_PM)) = (-Real.sinh (x / Q_PM)) / Real.cosh (x / Q_PM) := by
        rw [Real.tanh_eq_sinh_div_cosh]
        ring
      rw [hrewrite]
      have hs' : -Real.sinh (x / Q_PM) < 1 * Real.cosh (x / Q_PM) := by simpa using hs
      exact (div_lt_iff₀ hcosh).2 hs'
    linarith
  have habs : |Real.tanh (x / Q_PM)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  nlinarith

/-- Hard PM boundary clamp. This is the genuinely idempotent boundary object that
supports an honest nucleus connection. -/
def pmBoundaryClamp (Q_PM x : ℝ) : ℝ :=
  min x Q_PM

/-- The PM-safe region on the nonnegative half-line. -/
def pmSafeSet (Q_PM : ℝ) : Set ℝ :=
  {x | 0 ≤ x ∧ x ≤ Q_PM}

/-- The honest `Order.Nucleus` connection for PM-bounded control: adjoining the
PM-safe region is a genuine closure operator on sets. The smooth saturations land in
that region but are not themselves idempotent nuclei. -/
def pmBoundaryNucleus (Q_PM : ℝ) : Nucleus (Set ℝ) where
  toFun S := S ∪ pmSafeSet Q_PM
  map_inf' S T := by
    ext x
    constructor
    · intro hx
      rcases hx with hx | hx
      · exact ⟨Or.inl hx.1, Or.inl hx.2⟩
      · exact ⟨Or.inr hx, Or.inr hx⟩
    · intro hx
      rcases hx with ⟨hxS, hxT⟩
      rcases hxS with hxS | hxI
      · rcases hxT with hxT | _hxI
        · exact Or.inl ⟨hxS, hxT⟩
        · exact Or.inr _hxI
      · exact Or.inr hxI
  idempotent' S := by
    intro x hx
    simpa [Set.union_assoc, Set.union_left_comm, Set.union_comm] using hx
  le_apply' S := by
    intro x hx
    exact Or.inl hx

theorem sat_rational_mem_safeSet {Q_PM x : ℝ} (hQ : 0 < Q_PM) (hx : 0 ≤ x) :
    SatRational Q_PM x ∈ pmSafeSet Q_PM := by
  constructor
  · exact sat_rational_nonneg hQ hx
  ·
    have hbound : |SatRational Q_PM x| ≤ Q_PM := sat_rational_bounded hQ
    have hnonneg : 0 ≤ SatRational Q_PM x := sat_rational_nonneg hQ hx
    simpa [abs_of_nonneg hnonneg] using hbound

theorem sat_rational_le_boundary_clamp {Q_PM x : ℝ}
    (hQ : 0 < Q_PM) (hx : 0 ≤ x) :
    SatRational Q_PM x ≤ pmBoundaryClamp Q_PM x := by
  have hle_x : SatRational Q_PM x ≤ x := by
    unfold SatRational
    rw [abs_of_nonneg hx]
    have hxdiv : 0 ≤ x / Q_PM := by positivity
    have hden : 1 ≤ 1 + x / Q_PM := by linarith
    exact div_le_self hx hden
  have hle_Q : SatRational Q_PM x ≤ Q_PM := by
    have hbound : |SatRational Q_PM x| ≤ Q_PM := sat_rational_bounded hQ
    have hnonneg : 0 ≤ SatRational Q_PM x := sat_rational_nonneg hQ hx
    simpa [abs_of_nonneg hnonneg] using hbound
  exact le_min hle_x hle_Q

theorem pmBoundaryNucleus_fix_safeSet {Q_PM : ℝ} :
    pmBoundaryNucleus Q_PM (pmSafeSet Q_PM) = pmSafeSet Q_PM := by
  ext x
  simp [pmBoundaryNucleus, pmSafeSet]

/-- Canonical bundled rational completion. -/
def rationalCompletion (Q_PM : ℝ) (hQ : 0 < Q_PM) : PMCompletion where
  Q_PM := Q_PM
  pos := hQ
  sat := SatRational Q_PM
  bounded := fun x => sat_rational_bounded hQ (x := x)

end

end PMBoundedControl
end Analysis
end HeytingLean
