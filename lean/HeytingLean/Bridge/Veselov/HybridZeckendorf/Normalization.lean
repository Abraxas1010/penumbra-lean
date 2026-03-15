import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Tactic
import HeytingLean.Bridge.Veselov.HybridZeckendorf.HybridNumber

/-!
# Bridge.Veselov.HybridZeckendorf.Normalization

Two-stage normalization (intra-level + inter-level):
- bounded rewrite iterations at each level (`intraStep`/`intraIter`)
- Euclidean inter-level carry over support depth (`carryAt`/`interCarryLoop`)

Canonical payload encoding uses a bounded rewrite pass, then canonical
`Nat.zeckendorf` re-encoding of that rewrite-equivalent value.
-/

namespace HeytingLean.Bridge.Veselov.HybridZeckendorf

/-- One intra-level normalization step:
prefer duplicate rewrite, then consecutive rewrite, otherwise no-op. -/
def intraStep : LazyZeckendorf → LazyZeckendorf
  | a :: b :: rest =>
      if a = b then
        match a with
        | 0 => rest
        | 1 => 3 :: rest
        | Nat.succ (Nat.succ k) => (k + 3) :: k :: rest
      else if b = a + 1 then
        (a + 2) :: rest
      else
        a :: b :: rest
  | z => z

theorem intraStep_preserves_eval (z : LazyZeckendorf) :
    lazyEvalFib (intraStep z) = lazyEvalFib z := by
  cases z with
  | nil =>
      simp [intraStep]
  | cons a z =>
      cases z with
      | nil =>
          simp [intraStep]
      | cons b rest =>
          by_cases hab : a = b
          · subst hab
            cases a with
            | zero =>
                simp [intraStep, lazyEvalFib]
            | succ a =>
                cases a with
                | zero =>
                    have h : (2 : Nat) + lazyEvalFib rest = 1 + (1 + lazyEvalFib rest) := by
                      omega
                    simpa [intraStep, lazyEvalFib, Nat.fib] using h
                | succ k =>
                    have hfd : Nat.fib (k + 3) + Nat.fib k = Nat.fib (k + 2) + Nat.fib (k + 2) := by
                      calc
                        Nat.fib (k + 3) + Nat.fib k = 2 * Nat.fib (k + 2) := by
                          simpa [two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                            (fib_double_identity k).symm
                        _ = Nat.fib (k + 2) + Nat.fib (k + 2) := by
                          simp [two_mul]
                    calc
                      lazyEvalFib (intraStep (Nat.succ (Nat.succ k) :: Nat.succ (Nat.succ k) :: rest))
                          = Nat.fib (k + 3) + (Nat.fib k + lazyEvalFib rest) := by
                              simp [intraStep, lazyEvalFib]
                      _ = (Nat.fib (k + 2) + Nat.fib (k + 2)) + lazyEvalFib rest := by
                            calc
                              Nat.fib (k + 3) + (Nat.fib k + lazyEvalFib rest)
                                  = (Nat.fib (k + 3) + Nat.fib k) + lazyEvalFib rest := by ac_rfl
                              _ = (Nat.fib (k + 2) + Nat.fib (k + 2)) + lazyEvalFib rest := by
                                    rw [hfd]
                      _ = lazyEvalFib (Nat.succ (Nat.succ k) :: Nat.succ (Nat.succ k) :: rest) := by
                            simp [lazyEvalFib, Nat.add_comm, Nat.add_left_comm]
          · by_cases hsucc : b = a + 1
            · calc
                lazyEvalFib (intraStep (a :: b :: rest))
                    = Nat.fib (a + 2) + lazyEvalFib rest := by
                        simp [intraStep, hsucc, lazyEvalFib]
                _ = Nat.fib a + Nat.fib (a + 1) + lazyEvalFib rest := by
                      simp [Nat.fib_add_two]
                _ = Nat.fib a + Nat.fib b + lazyEvalFib rest := by simp [hsucc]
                _ = lazyEvalFib (a :: b :: rest) := by
                      simp [lazyEvalFib, Nat.add_assoc]
            · simp [intraStep, hab, hsucc]

/-- Intra-level normalization to canonical Zeckendorf list. -/
def intraIter : Nat → LazyZeckendorf → LazyZeckendorf
  | 0, z => z
  | n + 1, z => intraIter n (intraStep z)

theorem intraIter_preserves_eval (n : Nat) (z : LazyZeckendorf) :
    lazyEvalFib (intraIter n z) = lazyEvalFib z := by
  induction n generalizing z with
  | zero =>
      simp [intraIter]
  | succ n ih =>
      simpa [intraIter, intraStep_preserves_eval] using ih (intraStep z)

/-- Bounded rewrite fixed point used by intra-level normalization. -/
def intraCore (z : LazyZeckendorf) : LazyZeckendorf :=
  intraIter (2 * z.length + 1) z

/-- Intra-level normalization: bounded rewrite pass followed by canonical
Zeckendorf re-encoding of the same value. -/
def intraNormalize (z : LazyZeckendorf) : ZeckPayload :=
  Nat.zeckendorf (lazyEvalFib (intraCore z))

theorem intraNormalize_sound (z : LazyZeckendorf) :
    levelEval (intraNormalize z) = lazyEvalFib z := by
  calc
    levelEval (intraNormalize z)
        = lazyEvalFib (intraCore z) := by
            simp [intraNormalize, intraCore, levelEval, lazyEvalFib, Nat.sum_zeckendorf_fib]
    _ = lazyEvalFib z := intraIter_preserves_eval (2 * z.length + 1) z

theorem intraNormalize_canonical (z : LazyZeckendorf) :
    List.IsZeckendorfRep (intraNormalize z) := by
  simpa [intraNormalize, intraCore] using
    Nat.isZeckendorfRep_zeckendorf (lazyEvalFib (intraCore z))

/-- One structural carry step at level `i` (for `i = 0`, no-op). -/
noncomputable def carryAt (i : Nat) (X : HybridNumber) : HybridNumber :=
  match i with
  | 0 => X
  | Nat.succ k =>
      let ci := levelEval (X (Nat.succ k))
      let wi := weight (Nat.succ k)
      let q := ci / wi
      let r := ci % wi
      let cnext := levelEval (X (k + 2))
      let base := (X.erase (Nat.succ k)).erase (k + 2)
      base
        + Finsupp.single (Nat.succ k) (Nat.zeckendorf r)
        + Finsupp.single (k + 2) (Nat.zeckendorf (cnext + q))

/-- Canonicality predicate used by higher-level algorithms. -/
def IsCanonical (X : HybridNumber) : Prop :=
  ∀ i : Nat, List.IsZeckendorfRep (X i)

theorem carryAt_preserves_eval (i : Nat) (X : HybridNumber) :
    eval (carryAt i X) = eval X := by
  cases i with
  | zero =>
      simp [carryAt]
  | succ k =>
      let i0 := Nat.succ k
      let i1 := k + 2
      let ci := levelEval (X i0)
      let wi := weight i0
      let q := ci / wi
      let r := ci % wi
      let cnext := levelEval (X i1)
      let base := (X.erase i0).erase i1
      have hsplit0 : base + Finsupp.single i1 ((X.erase i0) i1) = X.erase i0 := by
        simpa [base, i1] using (Finsupp.erase_add_single i1 (X.erase i0))
      have hsplit1 : X.erase i0 + Finsupp.single i0 (X i0) = X := by
        simpa [i0] using (Finsupp.erase_add_single i0 X)
      have hOld :
          eval X =
            eval base
              + levelEval ((X.erase i0) i1) * weight i1
              + levelEval (X i0) * weight i0 := by
        calc
          eval X
              = eval (X.erase i0 + Finsupp.single i0 (X i0)) := by
                simp [hsplit1]
          _ = eval (X.erase i0) + eval (Finsupp.single i0 (X i0)) := by
                simpa using eval_add (X.erase i0) (Finsupp.single i0 (X i0))
          _ = eval (base + Finsupp.single i1 ((X.erase i0) i1))
                + eval (Finsupp.single i0 (X i0)) := by
                simp [hsplit0]
          _ = eval base
                + eval (Finsupp.single i1 ((X.erase i0) i1))
                + eval (Finsupp.single i0 (X i0)) := by
                simp [eval_add, Nat.add_assoc]
          _ = eval base
                + levelEval ((X.erase i0) i1) * weight i1
                + levelEval (X i0) * weight i0 := by
                simp [eval_single]
      have hErase :
          levelEval ((X.erase i0) i1) = levelEval (X i1) := by
        simp [i0, i1]
      have hNew :
          eval (carryAt (Nat.succ k) X) =
            eval base
              + r * weight i0
              + (cnext + q) * weight i1 := by
        simp [carryAt, i0, i1, ci, wi, q, r, cnext, base, eval_add, eval_single,
          levelEval, lazyEvalFib, Nat.sum_zeckendorf_fib, Nat.add_assoc]
      have hWiSq : weight i1 = wi * wi := by
        simp [i0, i1, wi, weight_succ_succ, pow_two]
      have hArith :
          ci * wi + cnext * weight i1 = r * wi + (cnext + q) * weight i1 := by
        have hdiv : wi * q + r = ci := by
          simpa [ci, wi, q, r, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
            (Nat.div_add_mod ci wi)
        calc
          ci * wi + cnext * weight i1
              = (wi * q + r) * wi + cnext * weight i1 := by rw [hdiv]
          _ = (wi * q) * wi + r * wi + cnext * weight i1 := by
                rw [Nat.add_mul, Nat.add_assoc]
          _ = q * (wi * wi) + r * wi + cnext * weight i1 := by
                ac_rfl
          _ = q * weight i1 + r * wi + cnext * weight i1 := by
                rw [hWiSq]
          _ = r * wi + (q * weight i1 + cnext * weight i1) := by
                ac_rfl
          _ = r * wi + (cnext + q) * weight i1 := by
                rw [Nat.add_mul]
                ac_rfl
      calc
        eval (carryAt (Nat.succ k) X)
            = eval base + r * weight i0 + (cnext + q) * weight i1 := hNew
        _ = eval base + (ci * wi + cnext * weight i1) := by
              rw [hArith]
              simp [wi, Nat.mul_comm, Nat.add_assoc, Nat.add_comm]
        _ = eval base + (levelEval ((X.erase i0) i1) * weight i1 + levelEval (X i0) * weight i0) := by
              rw [hErase]
              simp [ci, cnext, wi]
              ac_rfl
        _ = eval X := by
              rw [hOld]
              ac_rfl

/-- Carry step preserves canonicality (each touched level is re-encoded by
`Nat.zeckendorf`). -/
theorem carryAt_preserves_canonical (i : Nat) (X : HybridNumber) :
    IsCanonical X → IsCanonical (carryAt i X) := by
  intro hcanon
  cases i with
  | zero =>
      simpa [carryAt]
  | succ k =>
      intro t
      by_cases ht0 : t = Nat.succ k
      · subst ht0
        simpa [carryAt] using
          (Nat.isZeckendorfRep_zeckendorf (levelEval (X (k + 1)) % weight (k + 1)))
      · by_cases ht1 : t = k + 2
        · subst ht1
          simpa [carryAt] using
            (Nat.isZeckendorfRep_zeckendorf
              (levelEval (X (k + 2)) + levelEval (X (k + 1)) / weight (k + 1)))
        · have hbase :
            (((X.erase (Nat.succ k)).erase (k + 2)) t) = X t := by
              simp [ht0, ht1]
          simp [carryAt, ht0, ht1, hbase, hcanon t]

/-- Bounded ascending carry pass across levels. -/
noncomputable def interCarryLoop : Nat → HybridNumber → HybridNumber
  | 0, X => X
  | n + 1, X => carryAt (n + 1) (interCarryLoop n X)

theorem interCarryLoop_preserves_eval (n : Nat) (X : HybridNumber) :
    eval (interCarryLoop n X) = eval X := by
  induction n generalizing X with
  | zero =>
      simp [interCarryLoop]
  | succ n ih =>
      calc
        eval (interCarryLoop (n + 1) X)
            = eval (carryAt (n + 1) (interCarryLoop n X)) := by
                simp [interCarryLoop]
        _ = eval (interCarryLoop n X) := carryAt_preserves_eval (n + 1) (interCarryLoop n X)
        _ = eval X := ih X

theorem interCarryLoop_preserves_canonical (n : Nat) (X : HybridNumber) :
    IsCanonical X → IsCanonical (interCarryLoop n X) := by
  intro hcanon
  induction n generalizing X with
  | zero =>
      simpa [interCarryLoop] using hcanon
  | succ n ih =>
      have h1 : IsCanonical (interCarryLoop n X) := ih X hcanon
      simpa [interCarryLoop] using carryAt_preserves_canonical (n + 1) (interCarryLoop n X) h1

/-- After running `interCarryLoop n`, every positive level `≤ n` is in strict
carry-normal form (`levelEval < weight`). -/
theorem interCarryLoop_small (n : Nat) (X : HybridNumber) :
    ∀ i : Nat, 0 < i → i ≤ n → levelEval ((interCarryLoop n X) i) < weight i := by
  induction n generalizing X with
  | zero =>
      intro i hi hile
      omega
  | succ n ih =>
      intro i hi hile
      by_cases hieq : i = n + 1
      · subst hieq
        simpa [interCarryLoop, carryAt, levelEval, lazyEvalFib] using
          (Nat.mod_lt (levelEval ((interCarryLoop n X) (n + 1))) (weight_pos (n + 1)))
      · have hiNeSucc : i ≠ n + 1 := hieq
        have hiNeSuccSucc : i ≠ n + 2 := by omega
        have hiLeN : i ≤ n := by omega
        have hprev : levelEval ((interCarryLoop n X) i) < weight i := ih X i hi hiLeN
        simpa [interCarryLoop, carryAt, hiNeSucc, hiNeSuccSucc] using hprev

/-- If a level is already below carry threshold, `carryAt` leaves a canonical
state unchanged at representation level. -/
theorem carryAt_eq_self_of_small (i : Nat) (X : HybridNumber)
    (hX : IsCanonical X) (hi : 0 < i) (hsmall : levelEval (X i) < weight i) :
    carryAt i X = X := by
  cases i with
  | zero =>
      cases (Nat.lt_irrefl 0 hi)
  | succ k =>
      have hdiv0 : levelEval (X (Nat.succ k)) / weight (Nat.succ k) = 0 :=
        Nat.div_eq_of_lt hsmall
      have hmod : levelEval (X (Nat.succ k)) % weight (Nat.succ k) = levelEval (X (Nat.succ k)) :=
        Nat.mod_eq_of_lt hsmall
      have hz1 : Nat.zeckendorf (levelEval (X (Nat.succ k))) = X (Nat.succ k) := by
        simpa [levelEval, lazyEvalFib] using Nat.zeckendorf_sum_fib (hX (Nat.succ k))
      have hz2 : Nat.zeckendorf (levelEval (X (k + 2))) = X (k + 2) := by
        simpa [levelEval, lazyEvalFib] using Nat.zeckendorf_sum_fib (hX (k + 2))
      apply Finsupp.ext
      intro j
      by_cases hj1 : j = k + 1
      · subst hj1
        simp [carryAt, hdiv0, hmod, hz1]
      · by_cases hj2 : j = k + 2
        · subst hj2
          simp [carryAt, hdiv0, hz2]
        · simp [carryAt, hj1, hj2]

private theorem interCarryLoop_eq_self_of_fixed (n : Nat) (X : HybridNumber)
    (hfixed : ∀ i : Nat, 0 < i → i ≤ n → carryAt i X = X) :
    interCarryLoop n X = X := by
  induction n with
  | zero =>
      simp [interCarryLoop]
  | succ n ih =>
      have hfixedN : ∀ i : Nat, 0 < i → i ≤ n → carryAt i X = X := by
        intro i hi hile
        exact hfixed i hi (Nat.le_trans hile (Nat.le_succ n))
      calc
        interCarryLoop (n + 1) X
            = carryAt (n + 1) (interCarryLoop n X) := by simp [interCarryLoop]
        _ = carryAt (n + 1) X := by rw [ih hfixedN]
        _ = X := hfixed (n + 1) (Nat.succ_pos n) (Nat.le_refl (n + 1))

/-- One inter-level carry pass with proof-oriented fuel `eval X`.
This guarantees all positive levels up to that bound are carry-normal. -/
noncomputable def interCarry (X : HybridNumber) : HybridNumber :=
  interCarryLoop (eval X) X

theorem interCarry_preserves_eval (X : HybridNumber) :
    eval (interCarry X) = eval X := by
  simpa [interCarry] using interCarryLoop_preserves_eval (eval X) X

theorem interCarry_preserves_canonical (X : HybridNumber) :
    IsCanonical X → IsCanonical (interCarry X) := by
  intro hX
  simpa [interCarry] using interCarryLoop_preserves_canonical (eval X) X hX

theorem interCarry_idempotent_of_canonical (X : HybridNumber) (hX : IsCanonical X) :
    interCarry (interCarry X) = interCarry X := by
  let Y := interCarry X
  have hcanonY : IsCanonical Y := by
    simpa [Y] using interCarry_preserves_canonical X hX
  have hsmallY : ∀ i : Nat, 0 < i → i ≤ eval Y → levelEval (Y i) < weight i := by
    intro i hi hile
    have hile' : i ≤ eval X := by simpa [Y, interCarry_preserves_eval X] using hile
    simpa [Y] using interCarryLoop_small (eval X) X i hi hile'
  have hfixed : ∀ i : Nat, 0 < i → i ≤ eval Y → carryAt i Y = Y := by
    intro i hi hile
    exact carryAt_eq_self_of_small i Y hcanonY hi (hsmallY i hi hile)
  have hloop : interCarryLoop (eval Y) Y = Y :=
    interCarryLoop_eq_self_of_fixed (eval Y) Y hfixed
  simpa [interCarry, Y] using hloop

/-- Intra-normalization sends zero payload to zero payload. -/
@[simp] theorem intraNormalize_zero : intraNormalize (0 : LazyPayload) = 0 := by
  have hs : levelEval (intraNormalize (0 : LazyPayload)) = 0 := by
    simpa [lazyEvalFib] using intraNormalize_sound (0 : LazyPayload)
  have hc : List.IsZeckendorfRep (intraNormalize (0 : LazyPayload)) :=
    intraNormalize_canonical (0 : LazyPayload)
  have huniq :
      Nat.zeckendorf (levelEval (intraNormalize (0 : LazyPayload)))
        = intraNormalize (0 : LazyPayload) := by
    simpa [levelEval, lazyEvalFib] using Nat.zeckendorf_sum_fib hc
  have hzero :
      Nat.zeckendorf 0 = intraNormalize (0 : LazyPayload) := by
    simpa [hs] using huniq
  simpa [Nat.zeckendorf_zero] using hzero

/-- Apply intra-level normalization at every active level. -/
noncomputable def normalizeIntra (X : LazyHybridNumber) : HybridNumber :=
  X.mapRange intraNormalize (by simp)

theorem normalizeIntra_sound (X : LazyHybridNumber) :
    eval (normalizeIntra X) = lazyEval X := by
  classical
  simpa [normalizeIntra, eval, lazyEval, intraNormalize_sound] using
    (Finsupp.sum_mapRange_index
      (g := X)
      (f := intraNormalize)
      (hf := by simp)
      (h := fun i z => levelEval z * weight i)
      (h0 := by
        intro i
        have hlevel0 : levelEval (0 : ZeckPayload) = 0 := by
          change (List.map Nat.fib ([] : List Nat)).sum = 0
          simp
        calc
          levelEval (0 : ZeckPayload) * weight i = 0 * weight i := by
            rw [hlevel0]
          _ = 0 := Nat.zero_mul _))

theorem normalizeIntra_canonical (X : LazyHybridNumber) :
    IsCanonical (normalizeIntra X) := by
  intro i
  simpa [normalizeIntra] using intraNormalize_canonical (X i)

/-- Full lazy-to-canonical normalization. -/
noncomputable def normalize (X : LazyHybridNumber) : HybridNumber :=
  interCarry (normalizeIntra X)

theorem normalize_sound (X : LazyHybridNumber) :
    eval (normalize X) = lazyEval X := by
  simpa [normalize] using
    (interCarry_preserves_eval (normalizeIntra X)).trans (normalizeIntra_sound X)

theorem normalize_canonical (X : LazyHybridNumber) :
    IsCanonical (normalize X) := by
  have h0 : IsCanonical (normalizeIntra X) := normalizeIntra_canonical X
  simpa [normalize] using interCarry_preserves_canonical (normalizeIntra X) h0

/-- Termination witness for intra-level normalization. -/
theorem intraNormalize_terminates (z : LazyZeckendorf) :
    ∃ c : ZeckPayload, levelEval c = lazyEvalFib z ∧ List.IsZeckendorfRep c := by
  refine ⟨intraNormalize z, intraNormalize_sound z, intraNormalize_canonical z⟩

/-- Termination witness for full normalization. -/
theorem normalize_terminates (X : LazyHybridNumber) :
    ∃ Y : HybridNumber, eval Y = lazyEval X ∧ IsCanonical Y := by
  refine ⟨normalize X, normalize_sound X, normalize_canonical X⟩

end HeytingLean.Bridge.Veselov.HybridZeckendorf
