import HeytingLean.Bridge.Veselov.HybridZeckendorf.Addition
import Mathlib.Data.Real.GoldenRatio
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Bridge.Veselov.HybridZeckendorf.Multiplication

Stretch operations: parity/halving/doubling, multiplication, and density.
-/

namespace HeytingLean.Bridge.Veselov.HybridZeckendorf

/-- Double operation at semantic level. -/
noncomputable def doubleHybrid (X : HybridNumber) : HybridNumber :=
  add X X

/-- Positive hybrid levels carry even weights. -/
theorem weight_even_of_pos : ∀ {i : Nat}, 0 < i → 2 ∣ weight i
  | 0, h => (Nat.lt_irrefl 0 h).elim
  | 1, _ => ⟨500, by norm_num [weight]⟩
  | i + 2, _ => by
      have hprev : 2 ∣ weight (i + 1) := weight_even_of_pos (Nat.succ_pos _)
      have hmul : 2 ∣ weight (i + 1) * weight (i + 1) := dvd_mul_of_dvd_left hprev _
      simpa [weight, Nat.pow_two] using hmul

/-- Structural half of all positive-level contributions. -/
noncomputable def halfTailNat (X : HybridNumber) : Nat :=
  (X.erase 0).sum (fun i z => levelEval z * (weight i / 2))

theorem eval_erase_zero_even (X : HybridNumber) : 2 ∣ eval (X.erase 0) := by
  classical
  unfold eval Finsupp.sum
  refine Finset.dvd_sum ?_
  intro i hi
  have hi0 : i ≠ 0 := by
    intro h0
    subst h0
    simp [Finsupp.mem_support_iff] at hi
  exact dvd_mul_of_dvd_right (weight_even_of_pos (Nat.pos_of_ne_zero hi0)) _

theorem eval_erase_zero_eq_two_mul_halfTailNat (X : HybridNumber) :
    eval (X.erase 0) = 2 * halfTailNat X := by
  classical
  unfold eval halfTailNat Finsupp.sum
  calc
    ∑ i ∈ (X.erase 0).support, levelEval ((X.erase 0) i) * weight i
        = ∑ i ∈ (X.erase 0).support, 2 * (levelEval ((X.erase 0) i) * (weight i / 2)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi0 : i ≠ 0 := by
              intro h0
              subst h0
              simp [Finsupp.mem_support_iff] at hi
            have hdiv : 2 ∣ weight i := weight_even_of_pos (Nat.pos_of_ne_zero hi0)
            have hmul : 2 * (weight i / 2) = weight i := Nat.mul_div_cancel' hdiv
            calc
              levelEval ((X.erase 0) i) * weight i
                  = levelEval ((X.erase 0) i) * (2 * (weight i / 2)) := by rw [hmul]
              _ = 2 * (levelEval ((X.erase 0) i) * (weight i / 2)) := by
                    simp [Nat.mul_assoc, Nat.mul_comm]
    _ = ∑ i ∈ (X.erase 0).support,
          (levelEval ((X.erase 0) i) * (weight i / 2)
            + levelEval ((X.erase 0) i) * (weight i / 2)) := by
          simp [two_mul]
    _ = (∑ i ∈ (X.erase 0).support, levelEval ((X.erase 0) i) * (weight i / 2))
          + (∑ i ∈ (X.erase 0).support, levelEval ((X.erase 0) i) * (weight i / 2)) := by
          rw [Finset.sum_add_distrib]
    _ = 2 * (∑ i ∈ (X.erase 0).support, levelEval ((X.erase 0) i) * (weight i / 2)) := by
          simp [two_mul]

theorem eval_eq_level_zero_add_eval_erase_zero (X : HybridNumber) :
    eval X = levelEval (X 0) + eval (X.erase 0) := by
  calc
    eval X = eval (X.erase 0 + Finsupp.single 0 (X 0)) := by
      simpa using congrArg eval (Finsupp.erase_add_single 0 X).symm
    _ = eval (X.erase 0) + eval (Finsupp.single 0 (X 0)) := eval_add _ _
    _ = eval (X.erase 0) + levelEval (X 0) * weight 0 := by simp [eval_single]
    _ = levelEval (X 0) + eval (X.erase 0) := by simp [weight, Nat.add_comm]

/-- Halve operation by structural decomposition:
level `0` handles odd remainder; positive levels contribute an even tail. -/
noncomputable def halveHybrid (X : HybridNumber) : HybridNumber :=
  let level0Half := levelEval (X 0) / 2
  let tailHalf := halfTailNat X
  add (fromNat level0Half) (fromNat tailHalf)

/-- Parity query. -/
def isOddHybrid (X : HybridNumber) : Bool :=
  decide (eval X % 2 = 1)

theorem doubleHybrid_correct (X : HybridNumber) :
    eval (doubleHybrid X) = 2 * eval X := by
  calc
    eval (doubleHybrid X) = eval X + eval X := by
      simp [doubleHybrid, add_correct]
    _ = 2 * eval X := by
      rw [two_mul]

theorem halveHybrid_correct (X : HybridNumber) :
    eval (halveHybrid X) = eval X / 2 := by
  let a := levelEval (X 0)
  let b := halfTailNat X
  have htail : eval (X.erase 0) = 2 * b := by
    simpa [b] using eval_erase_zero_eq_two_mul_halfTailNat X
  have hsplit : eval X = a + eval (X.erase 0) := by
    simpa [a] using eval_eq_level_zero_add_eval_erase_zero X
  rcases eval_erase_zero_even X with ⟨k, hk⟩
  have hb : b = k := by
    have h2 : 2 * b = 2 * k := by rw [← htail, hk]
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < (2 : Nat)) h2
  calc
    eval (halveHybrid X) = a / 2 + b := by
      simp [halveHybrid, a, b, add_correct]
    _ = a / 2 + k := by
      rw [hb]
    _ = (a + 2 * k) / 2 := by
      have hdiv : (a + 2 * k) / 2 = a / 2 + k := by
        simpa [Nat.mul_comm] using (Nat.add_mul_div_right a k (by decide : 0 < (2 : Nat)))
      exact hdiv.symm
    _ = (a + eval (X.erase 0)) / 2 := by rw [hk]
    _ = eval X / 2 := by rw [hsplit]

/-- Repeated structural addition. -/
noncomputable def repeatAdd (A : HybridNumber) : Nat → HybridNumber
  | 0 => 0
  | n + 1 => add (repeatAdd A n) A

theorem repeatAdd_correct (A : HybridNumber) :
    ∀ n : Nat, eval (repeatAdd A n) = eval A * n
  | 0 => by simp [repeatAdd, eval]
  | n + 1 => by
      calc
        eval (repeatAdd A (n + 1))
            = eval (add (repeatAdd A n) A) := by simp [repeatAdd]
        _ = eval (repeatAdd A n) + eval A := add_correct _ _
        _ = eval A * n + eval A := by simp [repeatAdd_correct A n, Nat.mul_comm]
        _ = eval A * (n + 1) := by
              rw [Nat.mul_add, Nat.mul_one]

/-- Structural bounded multiplication fold over levels `0..n-1`.
The outer loop is support-bounded; the per-level multiplicity remains semantic
via `levelEval (B n) * weight n`. -/
noncomputable def multiplyUpTo (A B : HybridNumber) : Nat → HybridNumber
  | 0 => fromNat 0
  | n + 1 => add (multiplyUpTo A B n) (repeatAdd A (levelEval (B n) * weight n))

theorem multiplyUpTo_correct (A B : HybridNumber) :
    ∀ n : Nat,
      eval (multiplyUpTo A B n)
        = eval A * (∑ i ∈ Finset.range n, levelEval (B i) * weight i)
  | 0 => by
      simp [multiplyUpTo]
  | n + 1 => by
      calc
        eval (multiplyUpTo A B (n + 1))
            = eval (add (multiplyUpTo A B n) (repeatAdd A (levelEval (B n) * weight n))) := by
                simp [multiplyUpTo]
        _ = eval (multiplyUpTo A B n) + eval (repeatAdd A (levelEval (B n) * weight n)) := by
              simpa using add_correct (multiplyUpTo A B n) (repeatAdd A (levelEval (B n) * weight n))
        _ = eval A * (∑ i ∈ Finset.range n, levelEval (B i) * weight i)
              + eval A * (levelEval (B n) * weight n) := by
                simp [multiplyUpTo_correct A B n, repeatAdd_correct]
        _ = eval A * ((∑ i ∈ Finset.range n, levelEval (B i) * weight i) + (levelEval (B n) * weight n)) := by
              rw [Nat.mul_add]
        _ = eval A * (∑ i ∈ Finset.range (n + 1), levelEval (B i) * weight i) := by
              simp [Finset.sum_range_succ]

/-- Sum over bounded levels up to support depth matches semantic evaluation. -/
theorem sum_range_supportDepth_eq_eval (B : HybridNumber) :
    (∑ i ∈ Finset.range (B.support.sup id + 1), levelEval (B i) * weight i) = eval B := by
  have hsub : B.support ⊆ Finset.range (B.support.sup id + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have hsum :
      (∑ i ∈ B.support, levelEval (B i) * weight i)
        = (∑ i ∈ Finset.range (B.support.sup id + 1), levelEval (B i) * weight i) := by
    refine Finset.sum_subset hsub ?_
    intro i hiRange hiNotMem
    have hiZero : B i = 0 := Finsupp.notMem_support_iff.mp hiNotMem
    have hlevel0 : levelEval (B i) = 0 := by
      rw [hiZero]
      change (List.map Nat.fib ([] : List Nat)).sum = 0
      simp
    simp [hlevel0]
  calc
    (∑ i ∈ Finset.range (B.support.sup id + 1), levelEval (B i) * weight i)
        = (∑ i ∈ B.support, levelEval (B i) * weight i) := hsum.symm
    _ = eval B := by
          simp [eval, Finsupp.sum]

/-- Binary multiplication via structural bounded fold over support depth,
with per-level semantic multiplicities delegated to `repeatAdd`. -/
noncomputable def multiplyBinary (A B : HybridNumber) : HybridNumber :=
  multiplyUpTo A B (B.support.sup id + 1)

theorem multiplyBinary_correct (A B : HybridNumber) :
    eval (multiplyBinary A B) = eval A * eval B := by
  calc
    eval (multiplyBinary A B)
        = eval A * (∑ i ∈ Finset.range (B.support.sup id + 1), levelEval (B i) * weight i) := by
            simpa [multiplyBinary] using multiplyUpTo_correct A B (B.support.sup id + 1)
    _ = eval A * eval B := by
          rw [sum_range_supportDepth_eq_eval]

/-- Number of active indices across levels. -/
def supportCard (X : HybridNumber) : Nat :=
  X.sum (fun _ z => z.length)

/-- Density-like statistic from the paper's section 4 expression. -/
noncomputable def density (X : HybridNumber) : Real :=
  if eval X = 0 then 0 else (X.support.card : Real) / Real.logb Real.goldenRatio (eval X)

end HeytingLean.Bridge.Veselov.HybridZeckendorf
