import Mathlib.Data.List.Basic

/-!
# Minimal surreal core

`SurrealCore` collects the lightweight, list-based `PreGame` structure
that the rest of the surreal pipeline relies on. It offers:

* a smart constructor (`PreGame.build`) that computes a consistent birthday,
* budgeted comparison operators (`leAt`/`le`/`lt`) and a legality predicate,
* structural Conway-style arithmetic on finite pre-games (`add`/`neg`/`mul`),
* legacy fuel-bounded approximations (`addApprox`/`negApprox`/`mulApprox`)
  retained for benchmarking and comparability.

This module is intentionally lightweight and is not presented as a full,
quotiented Conway theory of surreal numbers.
-/

namespace HeytingLean
namespace Numbers
namespace SurrealCore

/-- Minimal pre-game skeleton used by the surreal pipeline. -/
structure PreGame where
  L : List PreGame := []
  R : List PreGame := []
  birth : Nat := 0
deriving Repr

namespace PreGame

def maxBirth (xs : List PreGame) : Nat :=
  xs.foldl (fun acc g => Nat.max acc g.birth) 0

/-- Smart constructor that updates `birth` from child lists. -/
def build (L R : List PreGame) : PreGame :=
  { L := L
    R := R
    birth := Nat.succ (Nat.max (maxBirth L) (maxBirth R)) }

end PreGame

/-! ### Conway null cut and birthdays -/

/-- Conway-style null cut `{∅ ∣ ∅}` with birthday zero. -/
def nullCut : PreGame :=
  { L := [], R := [], birth := 0 }

def birthday (g : PreGame) : Nat := g.birth

def truncate (θ : Nat) (g : PreGame) : Option PreGame :=
  if birthday g ≤ θ then some g else none

/-- Finite-day comparison core (rank-indexed): `leAt k x y` computes `x ≤ y` up to budget `k`. -/
noncomputable def leAt : Nat → PreGame → PreGame → Prop
  | 0, _, _ => True
  | Nat.succ k, x, y =>
      (∀ l ∈ x.L, ¬ leAt k y l) ∧ (∀ r ∈ y.R, ¬ leAt k r x)

/-- Finite-day order: `x ≤ y` at budget `x.birth + y.birth`. -/
noncomputable def le (x y : PreGame) : Prop :=
  leAt (x.birth + y.birth) x y

/-- Strict order derived from `≤` by asymmetry. -/
noncomputable def lt (x y : PreGame) : Prop := ¬ le y x

/-- Legality via the classical cut condition. -/
noncomputable def legal (g : PreGame) : Prop :=
  ∀ l ∈ g.L, ∀ r ∈ g.R, lt l r

/-- Canonicalisation (identity). -/
def canonicalize (g : PreGame) : PreGame := g

/-- Surreal closure hook: canonicalise and assume legality is enforced upstream. -/
def close (g : PreGame) : PreGame := canonicalize g

theorem canonicalize_idem (g : PreGame) :
    canonicalize (canonicalize g) = canonicalize g := rfl

/-! ## Structural finite Conway arithmetic

For finite `PreGame` trees, these definitions compute Conway-style operations by
well-founded recursion on the game size, eliminating fuel artifacts.
-/

private theorem sizeOf_lt_sizeOf_pregame_mk_left
    (L R : List PreGame) (birth : Nat) {x : PreGame} (hx : x ∈ L) :
    sizeOf x < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
  have hx' : sizeOf x < sizeOf L := by
    induction L with
    | nil =>
        cases hx
    | cons h t ih =>
        cases hx with
        | head =>
            have hpos : 0 < 1 + sizeOf t := by
              have : 0 < sizeOf t + 1 := Nat.succ_pos _
              exact lt_of_lt_of_eq this (by simp [Nat.add_comm])
            have hlt : sizeOf x < sizeOf x + (1 + sizeOf t) :=
              Nat.lt_add_of_pos_right hpos
            refine lt_of_lt_of_eq hlt ?_
            rw [List.cons.sizeOf_spec]
            calc
              sizeOf x + (1 + sizeOf t) = 1 + (sizeOf x + sizeOf t) := by
                exact Nat.add_left_comm (sizeOf x) 1 (sizeOf t)
              _ = 1 + sizeOf x + sizeOf t := by
                exact (Eq.symm (Nat.add_assoc 1 (sizeOf x) (sizeOf t)))
        | tail _ hx1 =>
            have hlt : sizeOf x < sizeOf t := ih hx1
            have htpos : 0 < 1 + sizeOf h := by
              have : 0 < sizeOf h + 1 := Nat.succ_pos _
              exact lt_of_lt_of_eq this (by simp [Nat.add_comm])
            have ht_lt : sizeOf t < sizeOf t + (1 + sizeOf h) :=
              Nat.lt_add_of_pos_right htpos
            have ht_lt' : sizeOf t < sizeOf (h :: t) := by
              refine lt_of_lt_of_eq ht_lt ?_
              rw [List.cons.sizeOf_spec]
              calc
                sizeOf t + (1 + sizeOf h) = 1 + (sizeOf t + sizeOf h) := by
                  exact Nat.add_left_comm (sizeOf t) 1 (sizeOf h)
                _ = 1 + sizeOf t + sizeOf h := by
                  exact (Eq.symm (Nat.add_assoc 1 (sizeOf t) (sizeOf h)))
                _ = 1 + sizeOf h + sizeOf t := by
                  exact Nat.add_right_comm 1 (sizeOf t) (sizeOf h)
            exact Nat.lt_trans hlt ht_lt'
  have hpos : 0 < (1 + sizeOf R + sizeOf birth) := by
    refine lt_of_lt_of_eq (Nat.succ_pos (sizeOf R + sizeOf birth)) ?_
    simp [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]
  have hlt : sizeOf L < sizeOf L + (1 + sizeOf R + sizeOf birth) :=
    Nat.lt_add_of_pos_right hpos
  have hL : sizeOf L < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
    simpa [PreGame.mk.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
  exact Nat.lt_trans hx' hL

private theorem sizeOf_lt_sizeOf_pregame_mk_right
    (L R : List PreGame) (birth : Nat) {x : PreGame} (hx : x ∈ R) :
    sizeOf x < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
  have hx' : sizeOf x < sizeOf R := by
    induction R with
    | nil =>
        cases hx
    | cons h t ih =>
        cases hx with
        | head =>
            have hpos : 0 < 1 + sizeOf t := by
              have : 0 < sizeOf t + 1 := Nat.succ_pos _
              exact lt_of_lt_of_eq this (by simp [Nat.add_comm])
            have hlt : sizeOf x < sizeOf x + (1 + sizeOf t) :=
              Nat.lt_add_of_pos_right hpos
            refine lt_of_lt_of_eq hlt ?_
            rw [List.cons.sizeOf_spec]
            calc
              sizeOf x + (1 + sizeOf t) = 1 + (sizeOf x + sizeOf t) := by
                exact Nat.add_left_comm (sizeOf x) 1 (sizeOf t)
              _ = 1 + sizeOf x + sizeOf t := by
                exact (Eq.symm (Nat.add_assoc 1 (sizeOf x) (sizeOf t)))
        | tail _ hx1 =>
            have hlt : sizeOf x < sizeOf t := ih hx1
            have htpos : 0 < 1 + sizeOf h := by
              have : 0 < sizeOf h + 1 := Nat.succ_pos _
              exact lt_of_lt_of_eq this (by simp [Nat.add_comm])
            have ht_lt : sizeOf t < sizeOf t + (1 + sizeOf h) :=
              Nat.lt_add_of_pos_right htpos
            have ht_lt' : sizeOf t < sizeOf (h :: t) := by
              refine lt_of_lt_of_eq ht_lt ?_
              rw [List.cons.sizeOf_spec]
              calc
                sizeOf t + (1 + sizeOf h) = 1 + (sizeOf t + sizeOf h) := by
                  exact Nat.add_left_comm (sizeOf t) 1 (sizeOf h)
                _ = 1 + sizeOf t + sizeOf h := by
                  exact (Eq.symm (Nat.add_assoc 1 (sizeOf t) (sizeOf h)))
                _ = 1 + sizeOf h + sizeOf t := by
                  exact Nat.add_right_comm 1 (sizeOf t) (sizeOf h)
            exact Nat.lt_trans hlt ht_lt'
  have hpos : 0 < (1 + sizeOf L + sizeOf birth) := by
    refine lt_of_lt_of_eq (Nat.succ_pos (sizeOf L + sizeOf birth)) ?_
    simp [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]
  have hlt : sizeOf R < sizeOf R + (1 + sizeOf L + sizeOf birth) :=
    Nat.lt_add_of_pos_right hpos
  have hR : sizeOf R < sizeOf ({ L := L, R := R, birth := birth } : PreGame) := by
    simpa [PreGame.mk.sizeOf_spec, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
  exact Nat.lt_trans hx' hR

private theorem sizeOf_lt_sizeOf_left (g : PreGame) {x : PreGame} (hx : x ∈ g.L) :
    sizeOf x < sizeOf g := by
  cases g with
  | mk L R birth =>
      simpa using (sizeOf_lt_sizeOf_pregame_mk_left L R birth hx)

private theorem sizeOf_lt_sizeOf_right (g : PreGame) {x : PreGame} (hx : x ∈ g.R) :
    sizeOf x < sizeOf g := by
  cases g with
  | mk L R birth =>
      simpa using (sizeOf_lt_sizeOf_pregame_mk_right L R birth hx)

/-- Conway negation on finite pre-games: swap options recursively. -/
noncomputable def neg : PreGame → PreGame
  | { L := L, R := R, birth := _ } =>
      PreGame.build (R.map neg) (L.map neg)
termination_by g => sizeOf g
decreasing_by
  all_goals
    first
    | exact sizeOf_lt_sizeOf_pregame_mk_left _ _ _ (by assumption)
    | exact sizeOf_lt_sizeOf_pregame_mk_right _ _ _ (by assumption)

/-- Conway addition on finite pre-games by structural recursion. -/
noncomputable def add : PreGame → PreGame → PreGame
  | x, y =>
      let L :=
        (x.L.map (fun xl => add xl y)) ++
        (y.L.map (fun yl => add x yl))
      let R :=
        (x.R.map (fun xr => add xr y)) ++
        (y.R.map (fun yr => add x yr))
      PreGame.build L R
termination_by x y => (sizeOf x, sizeOf y)
decreasing_by
  all_goals
    first
    | exact Prod.Lex.left (b₁ := sizeOf y) (b₂ := sizeOf y)
        (sizeOf_lt_sizeOf_left (g := x) (by assumption))
    | exact Prod.Lex.right (a := sizeOf x)
        (sizeOf_lt_sizeOf_left (g := y) (by assumption))
    | exact Prod.Lex.left (b₁ := sizeOf y) (b₂ := sizeOf y)
        (sizeOf_lt_sizeOf_right (g := x) (by assumption))
    | exact Prod.Lex.right (a := sizeOf x)
        (sizeOf_lt_sizeOf_right (g := y) (by assumption))

private noncomputable def sub (x y : PreGame) : PreGame := add x (neg y)

private def listBind {α β : Type} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (fun x acc => f x ++ acc) []

/-- Detect the canonical null cut `{∅ | ∅}` with birthday `0`. -/
def isNullCut : PreGame → Bool
  | { L := [], R := [], birth := 0 } => true
  | _ => false

@[simp] theorem isNullCut_nullCut : isNullCut nullCut = true := by
  rfl

/-- Conway multiplication on finite pre-games via well-founded recursion
on pair-size (`sizeOf x + sizeOf y`). -/
noncomputable def mul : PreGame → PreGame → PreGame := by
  classical
  let mulPair : PreGame × PreGame → PreGame :=
    (measure (fun p : PreGame × PreGame => sizeOf p.1 + sizeOf p.2)).wf.fix
      (fun p ih =>
        let x := p.1
        let y := p.2
        let L₁ :=
          listBind x.L.attach (fun xl =>
            y.L.attach.map (fun (yl : { g // g ∈ y.L }) =>
              let hxl : sizeOf xl.1 < sizeOf x := sizeOf_lt_sizeOf_left (g := x) xl.2
              let hyl : sizeOf yl.1 < sizeOf y := sizeOf_lt_sizeOf_left (g := y) yl.2
              let m1 : sizeOf xl.1 + sizeOf y < sizeOf x + sizeOf y :=
                Nat.add_lt_add_right hxl (sizeOf y)
              let m2 : sizeOf x + sizeOf yl.1 < sizeOf x + sizeOf y :=
                Nat.add_lt_add_left hyl (sizeOf x)
              let m3a : sizeOf xl.1 + sizeOf yl.1 < sizeOf x + sizeOf yl.1 :=
                Nat.add_lt_add_right hxl (sizeOf yl.1)
              let m3b : sizeOf x + sizeOf yl.1 < sizeOf x + sizeOf y :=
                Nat.add_lt_add_left hyl (sizeOf x)
              sub
                (add (ih (xl.1, y) m1) (ih (x, yl.1) m2))
                (ih (xl.1, yl.1) (Nat.lt_trans m3a m3b))))
        let L₂ :=
          listBind x.R.attach (fun xr =>
            y.R.attach.map (fun (yr : { g // g ∈ y.R }) =>
              let hxr : sizeOf xr.1 < sizeOf x := sizeOf_lt_sizeOf_right (g := x) xr.2
              let hyr : sizeOf yr.1 < sizeOf y := sizeOf_lt_sizeOf_right (g := y) yr.2
              let m1 : sizeOf xr.1 + sizeOf y < sizeOf x + sizeOf y :=
                Nat.add_lt_add_right hxr (sizeOf y)
              let m2 : sizeOf x + sizeOf yr.1 < sizeOf x + sizeOf y :=
                Nat.add_lt_add_left hyr (sizeOf x)
              let m3a : sizeOf xr.1 + sizeOf yr.1 < sizeOf x + sizeOf yr.1 :=
                Nat.add_lt_add_right hxr (sizeOf yr.1)
              let m3b : sizeOf x + sizeOf yr.1 < sizeOf x + sizeOf y :=
                Nat.add_lt_add_left hyr (sizeOf x)
              sub
                (add (ih (xr.1, y) m1) (ih (x, yr.1) m2))
                (ih (xr.1, yr.1) (Nat.lt_trans m3a m3b))))
        let R₁ :=
          listBind x.L.attach (fun xl =>
            y.R.attach.map (fun (yr : { g // g ∈ y.R }) =>
              let hxl : sizeOf xl.1 < sizeOf x := sizeOf_lt_sizeOf_left (g := x) xl.2
              let hyr : sizeOf yr.1 < sizeOf y := sizeOf_lt_sizeOf_right (g := y) yr.2
              let m1 : sizeOf xl.1 + sizeOf y < sizeOf x + sizeOf y :=
                Nat.add_lt_add_right hxl (sizeOf y)
              let m2 : sizeOf x + sizeOf yr.1 < sizeOf x + sizeOf y :=
                Nat.add_lt_add_left hyr (sizeOf x)
              let m3a : sizeOf xl.1 + sizeOf yr.1 < sizeOf x + sizeOf yr.1 :=
                Nat.add_lt_add_right hxl (sizeOf yr.1)
              let m3b : sizeOf x + sizeOf yr.1 < sizeOf x + sizeOf y :=
                Nat.add_lt_add_left hyr (sizeOf x)
              sub
                (add (ih (xl.1, y) m1) (ih (x, yr.1) m2))
                (ih (xl.1, yr.1) (Nat.lt_trans m3a m3b))))
        let R₂ :=
          listBind x.R.attach (fun xr =>
            y.L.attach.map (fun (yl : { g // g ∈ y.L }) =>
              let hxr : sizeOf xr.1 < sizeOf x := sizeOf_lt_sizeOf_right (g := x) xr.2
              let hyl : sizeOf yl.1 < sizeOf y := sizeOf_lt_sizeOf_left (g := y) yl.2
              let m1 : sizeOf xr.1 + sizeOf y < sizeOf x + sizeOf y :=
                Nat.add_lt_add_right hxr (sizeOf y)
              let m2 : sizeOf x + sizeOf yl.1 < sizeOf x + sizeOf y :=
                Nat.add_lt_add_left hyl (sizeOf x)
              let m3a : sizeOf xr.1 + sizeOf yl.1 < sizeOf x + sizeOf yl.1 :=
                Nat.add_lt_add_right hxr (sizeOf yl.1)
              let m3b : sizeOf x + sizeOf yl.1 < sizeOf x + sizeOf y :=
                Nat.add_lt_add_left hyl (sizeOf x)
              sub
                (add (ih (xr.1, y) m1) (ih (x, yl.1) m2))
                (ih (xr.1, yl.1) (Nat.lt_trans m3a m3b))))
        PreGame.build (L₁ ++ L₂) (R₁ ++ R₂))
  exact fun x y =>
    if isNullCut x || isNullCut y then nullCut else mulPair (x, y)

@[simp] theorem mul_nullCut_left (x : PreGame) :
    mul nullCut x = nullCut := by
  simp [mul]

@[simp] theorem mul_nullCut_right (x : PreGame) :
    mul x nullCut = nullCut := by
  simp [mul]

/-! ## Fuel-bounded legacy variants

These are retained for benchmarking and historical comparability.
-/

private def addAt : Nat → PreGame → PreGame → PreGame
  | 0, _, _ => nullCut
  | Nat.succ k, x, y =>
      let xL := x.L.map (fun l => addAt k l y)
      let yL := y.L.map (fun l => addAt k x l)
      let xR := x.R.map (fun r => addAt k r y)
      let yR := y.R.map (fun r => addAt k x r)
      PreGame.build (xL ++ yL) (xR ++ yR)

def addApprox (x y : PreGame) : PreGame :=
  addAt (Nat.succ (x.birth + y.birth)) x y

private def negAt : Nat → PreGame → PreGame
  | 0, x => x
  | Nat.succ k, x => PreGame.build (x.R.map (fun r => negAt k r)) (x.L.map (fun l => negAt k l))

def negApprox (x : PreGame) : PreGame :=
  negAt (Nat.succ x.birth) x

private def subApprox (x y : PreGame) : PreGame := addApprox x (negApprox y)

private def mulAt : Nat → PreGame → PreGame → PreGame
  | 0, _, _ => nullCut
  | Nat.succ k, x, y =>
      let mulRec := fun a b => mulAt k a b
      let L₁ :=
        listBind x.L (fun xl =>
          y.L.map (fun yl =>
            subApprox (addApprox (mulRec xl y) (mulRec x yl)) (mulRec xl yl)))
      let L₂ :=
        listBind x.R (fun xr =>
          y.R.map (fun yr =>
            subApprox (addApprox (mulRec xr y) (mulRec x yr)) (mulRec xr yr)))
      let R₁ :=
        listBind x.L (fun xl =>
          y.R.map (fun yr =>
            subApprox (addApprox (mulRec xl y) (mulRec x yr)) (mulRec xl yr)))
      let R₂ :=
        listBind x.R (fun xr =>
          y.L.map (fun yl =>
            subApprox (addApprox (mulRec xr y) (mulRec x yl)) (mulRec xr yl)))
      PreGame.build (L₁ ++ L₂) (R₁ ++ R₂)

def mulApprox (x y : PreGame) : PreGame :=
  mulAt (Nat.succ (x.birth + y.birth)) x y

end SurrealCore
end Numbers
end HeytingLean
