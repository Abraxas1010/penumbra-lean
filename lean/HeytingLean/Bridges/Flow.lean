import Mathlib.Order.Nucleus
import HeytingLean.Metrics.Curvature
import Mathlib.Data.Set.Lattice

/-!
# Flow Lens scaffolding (library-only)

This module introduces lightweight flow types and an identity nucleus over
sets of trajectories as a simple baseline. Smoothing/normalization helpers are
provided as pure functions and can be swapped into the nucleus later when
an idempotent, inf-preserving closure is designed.
-/

namespace HeytingLean
namespace Bridges

abbrev FlowPoint := Array Float
abbrev FlowTraj  := Array FlowPoint

namespace Flow

/-- A trivial smoothing helper (keeps endpoints). -/
def smoothOnce (t : FlowTraj) : FlowTraj := Id.run do
  let n := t.size
  if n ≤ 2 then return t
  let mut out : FlowTraj := #[]
  out := out.push t[0]!
  for i in [0:n-2] do
    let a := t[i]!
    let b := t[i+1]!
    let m := min a.size b.size
    let mut mid : FlowPoint := #[]
    for j in [0:m] do
      mid := mid.push ((a[j]! + b[j]!) / 2.0)
    out := out.push mid
  out := out.push t[n-1]!
  return out

/-- Identity nucleus on `Set FlowTraj` (baseline). -/
def flowNucleusId : Nucleus (Set FlowTraj) where
  toInfHom :=
  { toFun := id
    map_inf' := by intro _ _; rfl }
  idempotent' := by intro _; rfl
  le_apply' := by intro _; rfl

/-- A simple nontrivial nucleus parameterized by a fixed set `U`.
    It closes any set `S` by union with `U`, which is an inflationary,
    idempotent, and `inf`-preserving operator on `Set`s. -/
def flowNucleusUnion (U : Set FlowTraj) : Nucleus (Set FlowTraj) where
  toInfHom :=
  { toFun := fun S => S ∪ U
    map_inf' := by
      intro S T
      -- (S ∩ T) ∪ U = (S ∪ U) ∩ (T ∪ U)
      ext x; constructor <;> intro hx
      · rcases hx with hx | hx
        · exact And.intro (Or.inl hx.1) (Or.inl hx.2)
        · exact And.intro (Or.inr hx) (Or.inr hx)
      · rcases hx with ⟨h1, h2⟩
        cases h1 with
        | inl hS =>
          cases h2 with
          | inl hT => exact Or.inl ⟨hS, hT⟩
          | inr hU => exact Or.inr hU
        | inr hU => exact Or.inr hU }
  idempotent' := by
    intro S; -- (S ∪ U) ∪ U ⊆ S ∪ U
    intro x hx; cases hx with
    | inl hxSU => cases hxSU with
      | inl hS => exact Or.inl hS
      | inr hU => exact Or.inr hU
    | inr hU => exact Or.inr hU
  le_apply' := by
    intro S; -- S ⊆ S ∪ U
    intro x hx; exact Or.inl hx

/-! ## Bounded‑curvature/velocity admissibility

We define a simple admissibility predicate: a trajectory is admissible if its
maximum Menger curvature and average velocity magnitude are bounded by given
thresholds. This produces a fixed set `U_{kTol,vTol}` and we build the nucleus
`S ↦ S ∪ U_{kTol,vTol}` from it. -/

open HeytingLean.Metrics

def pointNorm (p : FlowPoint) : Float := Id.run do
  let zero : FlowPoint := Array.replicate p.size 0.0
  return l2Dist p zero

def maxCurvature (t : FlowTraj) : Float := Id.run do
  let n := t.size
  if n < 3 then return 0.0
  let mut m : Float := 0.0
  for i in [0:n-2] do
    if i + 2 ≤ n then
      let k := mengerCurvature t[i]! t[i+1]! t[i+2]!
      if k > m then m := k else ()
  return m

def avgVelMag (t : FlowTraj) : Float := Id.run do
  let v := finiteDiff t
  let n := v.size
  if n = 0 then return 0.0
  let mut s : Float := 0.0
  for dv in v do s := s + pointNorm dv
  return s / (Float.ofNat n)

def isAdmissible (kTol vTol : Float) (t : FlowTraj) : Bool :=
  let k := maxCurvature t
  let v := avgVelMag t
  (k ≤ kTol) && (v ≤ vTol)

def admissibleSet (kTol vTol : Float) : Set FlowTraj :=
  { t | isAdmissible kTol vTol t = true }

def flowNucleusBounded (kTol vTol : Float) : Nucleus (Set FlowTraj) :=
  flowNucleusUnion (admissibleSet kTol vTol)

/-- Dot product of two points (arrays of equal/min length). -/
def dot (a b : FlowPoint) : Float := Id.run do
  let n := min a.size b.size
  let mut s := 0.0
  for i in [0:n] do s := s + a[i]! * b[i]!
  return s

/-- Cosine similarity; returns 1.0 if a or b is zero to avoid division by zero. -/
def cosSim (a b : FlowPoint) : Float :=
  let na := pointNorm a
  let nb := pointNorm b
  if na == 0.0 || nb == 0.0 then 1.0 else (dot a b) / (na * nb)

/-- Check if a trajectory forms a simple loop under position and direction thresholds.
    - `posTol`: max distance between first and last point.
    - `dirCosTol`: min cosine similarity between first and last segment directions. -/
def isLoop (posTol dirCosTol : Float) (t : FlowTraj) : Bool := Id.run do
  let n := t.size
  if n < 3 then return false
  let p0 := t[0]!
  let pN := t[n-1]!
  let close := (l2Dist p0 pN) ≤ posTol
  let v0 := Id.run do
    let a := t[0]!
    let b := t[1]!
    let m := min a.size b.size
    let mut d : FlowPoint := #[]
    for j in [0:m] do d := d.push (b[j]! - a[j]!)
    d
  let vN := Id.run do
    let a := t[n-2]!
    let b := t[n-1]!
    let m := min a.size b.size
    let mut d : FlowPoint := #[]
    for j in [0:m] do d := d.push (b[j]! - a[j]!)
    d
  let cos := cosSim v0 vN
  return close && (cos ≥ dirCosTol)

def loopSet (posTol dirCosTol : Float) : Set FlowTraj :=
  { t | isLoop posTol dirCosTol t = true }

def flowNucleusOsc (posTol dirCosTol : Float) : Nucleus (Set FlowTraj) :=
  flowNucleusUnion (loopSet posTol dirCosTol)

/-- Strict loop: basic loop plus minimum perimeter and area constraints (2D).
    `minPerim` and `minArea` are Float thresholds. -/
def isLoopStrict (posTol dirCosTol minPerim minArea : Float) (t : FlowTraj) : Bool := Id.run do
  if isLoop posTol dirCosTol t = false then return false
  let per := perimeter2D t
  let ar := area2D t
  return (per ≥ minPerim) && (ar ≥ minArea)

def loopSetStrict (posTol dirCosTol minPerim minArea : Float) : Set FlowTraj :=
  { t | isLoopStrict posTol dirCosTol minPerim minArea t = true }

def flowNucleusOscStrict (posTol dirCosTol minPerim minArea : Float) : Nucleus (Set FlowTraj) :=
  flowNucleusUnion (loopSetStrict posTol dirCosTol minPerim minArea)

end Flow

end Bridges
end HeytingLean
