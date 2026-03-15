import HeytingLean.Bridge.Veselov.HybridZeckendorf.Multiplication
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Tactic

/-!
# Bridge.Veselov.HybridZeckendorf.DensityBounds

Real-valued density control lemmas for HybridZeckendorf payloads.
-/

namespace HeytingLean.Bridge.Veselov.HybridZeckendorf

private theorem zeck_head_ge_two {a : Nat} {z : List Nat} (hz : List.IsZeckendorfRep (a :: z)) :
    2 ≤ a := by
  have hzChain : List.IsChain (fun x y : Nat => y + 2 ≤ x) (a :: (z ++ [0])) := by
    simpa [List.IsZeckendorfRep, List.cons_append] using hz
  have hcons := (List.isChain_cons_iff (fun x y : Nat => y + 2 ≤ x) a (z ++ [0])).1 hzChain
  have hzNonempty : z ++ [0] ≠ [] := by simp
  rcases hcons with hzNil | ⟨b, l', hab, _, _⟩
  · contradiction
  · exact le_trans (by omega : 2 ≤ b + 2) hab

private theorem zeck_tail {a : Nat} {z : List Nat} (hz : List.IsZeckendorfRep (a :: z)) :
    List.IsZeckendorfRep z := by
  have hzChain : List.IsChain (fun x y : Nat => y + 2 ≤ x) (a :: (z ++ [0])) := by
    simpa [List.IsZeckendorfRep, List.cons_append] using hz
  have htail : List.IsChain (fun x y : Nat => y + 2 ≤ x) (z ++ [0]) := hzChain.tail
  simpa [List.IsZeckendorfRep] using htail

private theorem length_le_lazyEvalFib_of_isZeckendorf :
    ∀ z : ZeckPayload, List.IsZeckendorfRep z → z.length ≤ lazyEvalFib z
  | [], _ => by simp [lazyEvalFib]
  | a :: z, hz => by
      have h2 : 2 ≤ a := zeck_head_ge_two hz
      have hfib : 1 ≤ Nat.fib a := by
        have hmono : Nat.fib 2 ≤ Nat.fib a := Nat.fib_mono h2
        simpa using hmono
      have hzTail : List.IsZeckendorfRep z := zeck_tail hz
      have ih : z.length ≤ lazyEvalFib z := length_le_lazyEvalFib_of_isZeckendorf z hzTail
      have hstep : z.length + 1 ≤ lazyEvalFib z + Nat.fib a := by omega
      simpa [lazyEvalFib, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep

/-- Single-level payload bound: canonical Zeckendorf index count is bounded by
its semantic value. -/
theorem supportCard_single_level_bound (z : ZeckPayload)
    (hz : List.IsZeckendorfRep z) (hpos : 0 < lazyEvalFib z) :
    (z.length : ℝ) ≤ lazyEvalFib z := by
  have _ : 0 < lazyEvalFib z := hpos
  exact_mod_cast length_le_lazyEvalFib_of_isZeckendorf z hz

private theorem levelEval_pos_of_canonical_support (X : HybridNumber) (hX : IsCanonical X)
    {i : Nat} (hi : i ∈ X.support) :
    0 < levelEval (X i) := by
  have hiNonzero : X i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hcanon : List.IsZeckendorfRep (X i) := hX i
  have hlenPos : 0 < (X i).length := List.length_pos_iff.mpr (by
    intro hnil
    have hzero : X i = (0 : ZeckPayload) := by simpa using hnil
    exact hiNonzero hzero)
  have hlenLe : (X i).length ≤ lazyEvalFib (X i) :=
    length_le_lazyEvalFib_of_isZeckendorf (X i) hcanon
  have hone : 1 ≤ levelEval (X i) := by
    exact le_trans (Nat.succ_le_iff.mpr hlenPos) hlenLe
  exact Nat.succ_le_iff.mp hone

/-- Weight hierarchy bound: active-level count is logarithmic in semantic value. -/
theorem active_levels_bound (X : HybridNumber) (hX : IsCanonical X) (hpos : 0 < eval X) :
    (X.support.card : ℝ) ≤ Real.logb 1000 (eval X) + 2 := by
  classical
  let s : Nat := X.support.sup id
  have hcardNat : X.support.card ≤ s + 1 := by
    have hsub : X.support ⊆ Finset.range (s + 1) := by
      intro i hi
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
    simpa using (Finset.card_le_card hsub)
  have hsNonempty : X.support.Nonempty := by
    by_contra hs
    have hempty : X.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have heval0 : eval X = 0 := by simp [eval, Finsupp.sum, hempty]
    exact (Nat.ne_of_gt hpos) heval0
  have hsMem : s ∈ X.support := by
    rcases Finset.sup_mem_of_nonempty (s := X.support) (f := id) hsNonempty with ⟨i, hi, his⟩
    have his' : i = s := by simpa [s] using his
    simpa [his'] using hi
  have hlevPos : 0 < levelEval (X s) := levelEval_pos_of_canonical_support X hX hsMem
  have hlevOne : 1 ≤ levelEval (X s) := Nat.succ_le_of_lt hlevPos
  have hterm_le_eval : levelEval (X s) * weight s ≤ eval X := by
    unfold eval Finsupp.sum
    simpa using
      (Finset.single_le_sum
        (s := X.support)
        (a := s)
        (f := fun j => levelEval (X j) * weight j)
        (by intro j hj; exact Nat.zero_le _)
        hsMem)
  have hweight_le_eval : weight s ≤ eval X := by
    have hweight_le_term : weight s ≤ levelEval (X s) * weight s := by
      calc
        weight s = 1 * weight s := by simp
        _ ≤ levelEval (X s) * weight s := Nat.mul_le_mul_right (weight s) hlevOne
    exact le_trans hweight_le_term hterm_le_eval
  cases hs : s with
  | zero =>
      have hcardOneNat : X.support.card ≤ 1 := by simpa [hs] using hcardNat
      have hcardOne : (X.support.card : ℝ) ≤ 1 := by exact_mod_cast hcardOneNat
      have hEvalOne : (1 : ℝ) ≤ eval X := by exact_mod_cast Nat.succ_le_of_lt hpos
      have hlog_nonneg : 0 ≤ Real.logb 1000 (eval X) := by
        exact Real.logb_nonneg (hb := by norm_num) hEvalOne
      nlinarith
  | succ k =>
      have hweight_le_eval' : weight (k + 1) ≤ eval X := by simpa [hs] using hweight_le_eval
      have hlogMono :
          Real.logb 1000 (weight (k + 1)) ≤ Real.logb 1000 (eval X) := by
        have hweightPos : 0 < (weight (k + 1) : ℝ) := by exact_mod_cast weight_pos (k + 1)
        exact Real.logb_le_logb_of_le (hb := by norm_num) hweightPos (by exact_mod_cast hweight_le_eval')
      have hlogWeight : Real.logb 1000 (weight (k + 1)) = (2 ^ k : ℝ) := by
        calc
          Real.logb 1000 (weight (k + 1))
              = Real.logb 1000 ((1000 : ℕ) ^ (2 ^ k)) := by simp [weight_closed]
          _ = Real.logb (1000 : ℝ) ((1000 : ℝ) ^ (2 ^ k)) := by norm_num
          _ = (2 ^ k : ℝ) * Real.logb (1000 : ℝ) (1000 : ℝ) := by
                simpa [Nat.cast_pow] using (Real.logb_pow (1000 : ℝ) (1000 : ℝ) (2 ^ k))
          _ = (2 ^ k : ℝ) := by simp
      have hkpow : (k : ℝ) ≤ (2 ^ k : ℝ) := by
        exact_mod_cast (Nat.le_of_lt k.lt_two_pow_self)
      have hcardSuccNat : X.support.card ≤ k + 2 := by simpa [hs] using hcardNat
      have hcardSucc : (X.support.card : ℝ) ≤ (k : ℝ) + 2 := by
        exact_mod_cast hcardSuccNat
      have hk_to_log : (k : ℝ) ≤ Real.logb 1000 (eval X) := by
        exact le_trans hkpow (by simpa [hlogWeight] using hlogMono)
      nlinarith

/-- Main density bound on active-level density. -/
theorem density_upper_bound (X : HybridNumber) (hX : IsCanonical X)
    (hpos : 0 < eval X) :
    density X ≤ (Real.logb 1000 (eval X) + 2) := by
  unfold density
  have hne : eval X ≠ 0 := Nat.ne_of_gt hpos
  simp [hne]
  by_cases hEvalOne : eval X = 1
  · simp [hEvalOne]
  · have hEvalTwo : 2 ≤ eval X := by omega
    have hlog2_gt_one : 1 < Real.logb Real.goldenRatio (2 : ℝ) := by
      have hlt :
          Real.logb Real.goldenRatio Real.goldenRatio < Real.logb Real.goldenRatio (2 : ℝ) :=
        Real.logb_lt_logb (hb := Real.one_lt_goldenRatio) Real.goldenRatio_pos Real.goldenRatio_lt_two
      simpa [Real.logb_self_eq_one Real.one_lt_goldenRatio] using hlt
    have hlog_ge_one : 1 ≤ Real.logb Real.goldenRatio (eval X) := by
      have hmono :
          Real.logb Real.goldenRatio (2 : ℝ) ≤ Real.logb Real.goldenRatio (eval X) := by
        have hEvalPos : 0 < (2 : ℝ) := by positivity
        exact Real.logb_le_logb_of_le (hb := Real.one_lt_goldenRatio) hEvalPos (by exact_mod_cast hEvalTwo)
      exact le_trans hlog2_gt_one.le hmono
    have hdiv_le_card :
        (X.support.card : ℝ) / Real.logb Real.goldenRatio (eval X) ≤ (X.support.card : ℝ) := by
      have hnum_nonneg : 0 ≤ (X.support.card : ℝ) := by positivity
      exact div_le_self hnum_nonneg hlog_ge_one
    exact le_trans hdiv_le_card (active_levels_bound X hX hpos)

end HeytingLean.Bridge.Veselov.HybridZeckendorf
