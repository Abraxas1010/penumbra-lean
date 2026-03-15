/-!
# Curvature and simple flow metrics (library-only)

This module provides lightweight geometric helpers over arrays of `Float`:
- `mengerCurvature`: Menger curvature for three points in ℝ^d (as arrays of `Float`).
- `finiteDiff`: forward finite difference between consecutive points.

These functions are intended for tiny demos and compile-only tests; they avoid
heavy mathlib imports to keep strict builds fast.
-/

namespace HeytingLean
namespace Metrics

abbrev FlowPoint := Array Float

private def sq (x : Float) := x * x

def l2Dist (a b : FlowPoint) : Float := Id.run do
  let n := min a.size b.size
  let mut s : Float := 0.0
  for i in [0:n] do
    let d := a[i]! - b[i]!
    s := s + sq d
  return Float.sqrt s

/-- Menger curvature of a triple (a,b,c) in ℝ^d, using side lengths.
    Returns 0.0 when points are collinear or degenerate. -/
def mengerCurvature (a b c : FlowPoint) : Float :=
  let ab := l2Dist a b
  let bc := l2Dist b c
  let ca := l2Dist c a
  let p := (ab + bc + ca) / 2.0
  let area2 := p * (p - ab) * (p - bc) * (p - ca)
  if area2 ≤ 0.0 then 0.0
  else
    let area := Float.sqrt area2
    let denom := ab * bc * ca
    if denom == 0.0 then 0.0 else (4.0 * area) / denom

/-- Forward finite differences over a trajectory of points. -/
def finiteDiff (traj : Array FlowPoint) : Array FlowPoint := Id.run do
  let n := traj.size
  if n = 0 then return #[]
  if n = 1 then return #[]
  let mut out : Array FlowPoint := #[]
  for i in [0:n-1] do
    let x := traj[i]!
    let y := traj[i+1]!
    let m := min x.size y.size
    let mut d : FlowPoint := #[]
    for j in [0:m] do
      d := d.push (y[j]! - x[j]!)
    out := out.push d
  return out

/-! ## 2D polygon helpers (shoelace + perimeter)

We treat points as 2D by projecting to their first two coordinates (missing
coordinates default to 0). These are coarse helpers for small demos. -/

private def proj2 (p : FlowPoint) : Float × Float :=
  let x := if 0 < p.size then p[0]! else 0.0
  let y := if 1 < p.size then p[1]! else 0.0
  (x, y)

def perimeter2D (poly : Array FlowPoint) : Float := Id.run do
  let n := poly.size
  if n < 2 then return 0.0
  let mut s : Float := 0.0
  for i in [0:n-1] do
    let (x1, y1) := proj2 poly[i]!
    let (x2, y2) := proj2 poly[i+1]!
    let dx := x2 - x1; let dy := y2 - y1
    s := s + Float.sqrt (dx*dx + dy*dy)
  return s

def area2D (poly : Array FlowPoint) : Float := Id.run do
  let n := poly.size
  if n < 3 then return 0.0
  let mut acc : Float := 0.0
  for i in [0:n-1] do
    let (x1, y1) := proj2 poly[i]!
    let (x2, y2) := proj2 poly[i+1]!
    acc := acc + (x1 * y2 - x2 * y1)
  return Float.abs (acc / 2.0)

end Metrics
end HeytingLean
