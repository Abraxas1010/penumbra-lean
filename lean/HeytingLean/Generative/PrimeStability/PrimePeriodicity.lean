import HeytingLean.Generative.PrimeStability.RotationalClosure

/-!
# Generative.PrimeStability.PrimePeriodicity

Prime/composite periodicity controls decomposability because the only structure
recorded by a `SubClosure` is a proper nontrivial divisor of the parent period.
-/

namespace HeytingLean.Generative.PrimeStability

theorem decomposable_has_proper_divisor {α : Type*} (rc : RotationalClosure α)
    (hDec : Decomposable rc) :
    ∃ d, d ∣ rc.period ∧ 2 ≤ d ∧ d < rc.period := by
  rcases hDec with ⟨sub⟩
  exact ⟨sub.subPeriod, sub.divides, Nat.succ_le_of_lt sub.subPeriod_gt_one, sub.strict⟩

/-- Composite period is equivalent to admitting a proper nontrivial sub-cycle. -/
theorem composite_iff_decomposable {α : Type*} (rc : RotationalClosure α) :
    CompositeClosure rc ↔ Decomposable rc := by
  constructor
  · rintro ⟨hgt, hnotPrime⟩
    have htwo : 2 ≤ rc.period := Nat.succ_le_of_lt hgt
    rcases Nat.exists_dvd_of_not_prime2 htwo hnotPrime with ⟨d, hdvd, hd2, hdlt⟩
    refine ⟨{ subPeriod := d, subPeriod_gt_one := lt_of_lt_of_le (by decide : 1 < 2) hd2
            , divides := hdvd, strict := hdlt }⟩
  · intro hDec
    rcases decomposable_has_proper_divisor rc hDec with ⟨d, hdvd, hd2, hdlt⟩
    refine ⟨lt_of_lt_of_le (by decide : 1 < 2) (le_trans hd2 hdlt.le), ?_⟩
    exact Nat.not_prime_of_dvd_of_lt hdvd hd2 hdlt

/-- Prime period and non-decomposability are equivalent in the massive regime. -/
theorem irreducible_iff_not_decomposable {α : Type*} (rc : RotationalClosure α)
    (h1 : 1 < rc.period) :
    IrreducibleClosure rc ↔ ¬ Decomposable rc := by
  constructor
  · intro hPrime hDec
    have hComp : CompositeClosure rc := (composite_iff_decomposable rc).mpr hDec
    exact hComp.2 hPrime
  · intro hNotDec
    by_cases hPrime : Nat.Prime rc.period
    · exact hPrime
    · exfalso
      exact hNotDec ((composite_iff_decomposable rc).mp ⟨h1, hPrime⟩)

/-- In the trapped regime, stability is exactly prime periodicity. -/
theorem stable_iff_prime_period {α : Type*} (rc : RotationalClosure α)
    (hTrapped : hasTrappedAsymmetry rc) :
    IrreducibleClosure rc ↔ ¬ Decomposable rc :=
  irreducible_iff_not_decomposable rc hTrapped

/-- Every stable massive closure has prime period. -/
theorem stable_massive_has_prime_period {α : Type*} (rc : RotationalClosure α)
    (hMassive : hasTrappedAsymmetry rc) (hStable : ¬ Decomposable rc) :
    Nat.Prime rc.period :=
  (stable_iff_prime_period rc hMassive).mpr hStable

/-- `2` is the smallest prime above the massless threshold `1`. -/
theorem two_is_terminal_prime :
    ∀ p : ℕ, Nat.Prime p → 2 ≤ p :=
  fun _ hp => hp.two_le

end HeytingLean.Generative.PrimeStability
