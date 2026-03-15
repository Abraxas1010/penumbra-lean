import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Bridge.AlMayahi.TauEpoch.Stats

Statistics micro-library for τ-Epoch Discovery II:
- weighted mean / weighted chi-squared
- Birge ratio and Λ statistic
- Spearman correlation scaffold
- Binomial sign-test p-value scaffold
- Linear regression scaffold

Pure definitions are over `ℝ` for theorem statements; Float helpers are
provided only for reproducibility checks (`#eval`).
-/

namespace HeytingLean.Bridge.AlMayahi.TauEpoch

open scoped BigOperators

noncomputable section

variable {n : ℕ}

/-- Weight used in weighted-mean/χ² calculations: `wᵢ = 1/σᵢ²`. -/
noncomputable def wtWeight (σ : Fin n → ℝ) (i : Fin n) : ℝ :=
  1 / (σ i) ^ 2

/-- Weighted mean `μ = Σ(wᵢ xᵢ) / Σ(wᵢ)`. -/
noncomputable def wtMean (x σ : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, wtWeight σ i * x i) / (∑ i : Fin n, wtWeight σ i)

/-- Weighted chi-squared `χ² = Σ((xᵢ - μ)² / σᵢ²)`. -/
noncomputable def chi2Wt (x σ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ((x i - wtMean x σ) ^ 2) / (σ i) ^ 2

/-- Birge ratio `sqrt(χ²/ν)`. -/
noncomputable def birge (chi2 : ℝ) (dof : ℕ) : ℝ :=
  Real.sqrt (chi2 / (dof : ℝ))

/-- Parameter-free tension statistic `Λ = χ² / n - 1`. -/
noncomputable def lambdaStat (chi2 : ℝ) (n : ℕ) : ℝ :=
  chi2 / (n : ℝ) - 1

/-- No-tension condition encoded as `χ² = ν`. -/
def noTension (chi2 : ℝ) (dof : ℕ) : Prop :=
  chi2 = (dof : ℝ)

theorem birge_nonneg (chi2 : ℝ) (dof : ℕ) : 0 ≤ birge chi2 dof := by
  exact Real.sqrt_nonneg _

theorem lambda_eq_zero_iff (chi2 : ℝ) (n : ℕ) (hnn : (n : ℝ) ≠ 0) :
    lambdaStat chi2 n = 0 ↔ chi2 = (n : ℝ) := by
  constructor
  · intro h
    have hdiv : chi2 / (n : ℝ) = 1 := sub_eq_zero.mp h
    simpa using (div_eq_iff hnn).1 hdiv
  · intro hchi
    unfold lambdaStat
    rw [hchi]
    have hdiv : ((n : ℝ) / (n : ℝ)) = (1 : ℝ) := by
      field_simp [hnn]
    linarith [hdiv]

theorem birge_sq_eq (chi2 : ℝ) (dof : ℕ) (hchi : 0 ≤ chi2 / (dof : ℝ)) :
    birge chi2 dof ^ 2 = chi2 / (dof : ℝ) := by
  unfold birge
  simpa [pow_two] using Real.sq_sqrt hchi

theorem birge_eq_one_iff_no_tension
    (chi2 : ℝ) (dof : ℕ) (hdof : (dof : ℝ) ≠ 0) (hchi : 0 ≤ chi2 / (dof : ℝ)) :
    birge chi2 dof = 1 ↔ noTension chi2 dof := by
  constructor
  · intro h
    have hsq : birge chi2 dof ^ 2 = 1 := by
      nlinarith [h]
    have hratio : chi2 / (dof : ℝ) = 1 := by
      calc
        chi2 / (dof : ℝ) = birge chi2 dof ^ 2 := by
          symm
          exact birge_sq_eq chi2 dof hchi
        _ = 1 := hsq
    simpa [noTension] using (div_eq_iff hdof).1 hratio
  · intro hnt
    have hratio : chi2 / (dof : ℝ) = 1 := by
      rw [hnt]
      field_simp [hdof]
    calc
      birge chi2 dof = Real.sqrt (chi2 / (dof : ℝ)) := rfl
      _ = Real.sqrt 1 := by rw [hratio]
      _ = 1 := by simp

theorem birge_mono_lambda (chi2 : ℝ) (n : ℕ) (hchi : 0 ≤ chi2 / (n : ℝ)) :
    birge chi2 n ^ 2 = lambdaStat chi2 n + 1 := by
  calc
    birge chi2 n ^ 2 = chi2 / (n : ℝ) := birge_sq_eq chi2 n hchi
    _ = (chi2 / (n : ℝ) - 1) + 1 := by ring
    _ = lambdaStat chi2 n + 1 := by simp [lambdaStat]

/-- Arithmetic mean over finite indexed samples. -/
noncomputable def mean (x : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, x i) / (n : ℝ)

/-- Centered value at index `i`. -/
noncomputable def centered (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i - mean x

/-- Covariance-like finite sum (normalized by `n`). -/
noncomputable def covariance (x y : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, centered x i * centered y i) / (n : ℝ)

/-- Variance proxy from covariance. -/
noncomputable def variance (x : Fin n → ℝ) : ℝ :=
  covariance x x

/-- Raw Pearson ratio (unclamped). -/
noncomputable def pearsonRhoRaw (x y : Fin n → ℝ) : ℝ :=
  if _h : variance x = 0 ∨ variance y = 0 then
    0
  else
    covariance x y / Real.sqrt (variance x * variance y)

/-- Bounded Pearson ratio used by this scaffold (`[-1,1]` clamp). -/
noncomputable def pearsonRho (x y : Fin n → ℝ) : ℝ :=
  max (-1) (min 1 (pearsonRhoRaw x y))

/-- Rank surrogate: number of entries `≤ xᵢ`. -/
noncomputable def rank (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  ((Finset.univ.filter (fun j : Fin n => x j ≤ x i)).card : ℝ)

/-- Spearman correlation as Pearson-on-ranks (bounded via clamp). -/
noncomputable def spearmanRho (x y : Fin n → ℝ) : ℝ :=
  pearsonRho (fun i => rank x i) (fun i => rank y i)

theorem pearsonRho_bound (x y : Fin n → ℝ) :
    -1 ≤ pearsonRho x y ∧ pearsonRho x y ≤ 1 := by
  unfold pearsonRho
  constructor
  · exact le_max_left _ _
  · refine (max_le_iff).2 ?_
    constructor
    · norm_num
    · exact min_le_left _ _

theorem spearmanRho_bound (x y : Fin n → ℝ) :
    -1 ≤ spearmanRho x y ∧ spearmanRho x y ≤ 1 := by
  simpa [spearmanRho] using
    (pearsonRho_bound (x := fun i => rank x i) (y := fun i => rank y i))

/-- Raw upper-tail binomial sign-test probability:
`Σ_{i=positive..total} choose(total, i) / 2^total`. -/
noncomputable def binomialUpperTailRaw (positiveCount total : ℕ) : ℝ :=
  (Finset.sum (Finset.Icc positiveCount total) (fun i => (Nat.choose total i : ℝ))) /
    (2 : ℝ) ^ total

/-- Bounded sign-test p-value (`[0,1]` clamp). -/
noncomputable def binomialSignPValue (positiveCount total : ℕ) : ℝ :=
  max 0 (min 1 (binomialUpperTailRaw positiveCount total))

theorem binomialSignPValue_unit_interval (positiveCount total : ℕ) :
    0 ≤ binomialSignPValue positiveCount total ∧
      binomialSignPValue positiveCount total ≤ 1 := by
  unfold binomialSignPValue
  constructor
  · exact le_max_left _ _
  · refine (max_le_iff).2 ?_
    constructor
    · norm_num
    · exact min_le_left _ _

/-- Denominator term for simple linear regression slope. -/
noncomputable def regressionDenom (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (x i - mean x) ^ 2

/-- Slope `A` in `y = A x + B` (zero when denominator vanishes). -/
noncomputable def regressionSlope (x y : Fin n → ℝ) : ℝ :=
  if _h : regressionDenom x = 0 then
    0
  else
    (∑ i : Fin n, (x i - mean x) * (y i - mean y)) / regressionDenom x

/-- Intercept `B` in `y = A x + B`. -/
noncomputable def regressionIntercept (x y : Fin n → ℝ) : ℝ :=
  mean y - regressionSlope x y * mean x

/-- Regression prediction at sample index `i`. -/
noncomputable def regressionPredict (x y : Fin n → ℝ) (i : Fin n) : ℝ :=
  regressionSlope x y * x i + regressionIntercept x y

/-- Residual sum of squares. -/
noncomputable def residualSS (x y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (y i - regressionPredict x y i) ^ 2

/-- Total sum of squares. -/
noncomputable def totalSS (y : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, (y i - mean y) ^ 2

/-- Raw `R²` value (guarded when total variance is zero). -/
noncomputable def rSquaredRaw (x y : Fin n → ℝ) : ℝ :=
  if _h : totalSS y = 0 then
    1
  else
    1 - residualSS x y / totalSS y

/-- Regression triple `(A, B, R²)` with bounded `R²`. -/
noncomputable def linearRegression (x y : Fin n → ℝ) : ℝ × ℝ × ℝ :=
  (regressionSlope x y, regressionIntercept x y, max 0 (min 1 (rSquaredRaw x y)))

theorem linearRegression_r2_unit_interval (x y : Fin n → ℝ) :
    0 ≤ (linearRegression x y).2.2 ∧ (linearRegression x y).2.2 ≤ 1 := by
  unfold linearRegression
  constructor
  · exact le_max_left _ _
  · refine (max_le_iff).2 ?_
    constructor
    · norm_num
    · exact min_le_left _ _

theorem linearRegression_perfect (x y : Fin n → ℝ) (h : rSquaredRaw x y = 1) :
    (linearRegression x y).2.2 = 1 := by
  simp [linearRegression, h]

end

section FloatHelpers

/-- Float helper: list sum. -/
def floatSum (xs : List Float) : Float :=
  xs.foldl (fun acc x => acc + x) 0

/-- Float helper: arithmetic mean over a list. -/
def floatMean (xs : List Float) : Float :=
  match xs.length with
  | 0 => 0
  | n + 1 => floatSum xs / Float.ofNat (n + 1)

/-- Float helper for weighted mean using zipped `(x, σ)` pairs. -/
def floatWeightedMean (xs σs : List Float) : Float :=
  let pairs := List.zip xs σs
  let num := pairs.foldl
    (fun acc p =>
      let x := p.1
      let s := p.2
      acc + (1 / (s * s)) * x) 0
  let den := pairs.foldl
    (fun acc p =>
      let s := p.2
      acc + (1 / (s * s))) 0
  if den == 0 then 0 else num / den

/-- Float helper for weighted χ² with weighted-mean center. -/
def floatChi2Wt (xs σs : List Float) : Float :=
  let μ := floatWeightedMean xs σs
  (List.zip xs σs).foldl
    (fun acc p =>
      let x := p.1
      let s := p.2
      acc + ((x - μ) * (x - μ)) / (s * s)) 0

/-- Float helper: sample mid-rank (SciPy-style tie handling). -/
def floatRanks (xs : List Float) : List Float :=
  xs.map (fun x =>
    let ltCount := xs.foldl (fun acc y => if y < x then acc + 1 else acc) 0
    let eqCount := xs.foldl (fun acc y => if y == x then acc + 1 else acc) 0
    Float.ofNat ltCount + Float.ofNat (eqCount + 1) / 2.0)

/-- Float helper: covariance over zipped lists. -/
def floatCovariance (xs ys : List Float) : Float :=
  let pairs := List.zip xs ys
  let mx := floatMean xs
  let my := floatMean ys
  let num := pairs.foldl
    (fun acc p =>
      let x := p.1
      let y := p.2
      acc + (x - mx) * (y - my)) 0
  match pairs.length with
  | 0 => 0
  | n + 1 => num / Float.ofNat (n + 1)

/-- Float helper: variance over list. -/
def floatVariance (xs : List Float) : Float :=
  floatCovariance xs xs

/-- Float helper: bounded clamp to `[0,1]`. -/
def floatClampUnit (x : Float) : Float :=
  max 0 (min 1 x)

/-- Float helper: bounded Pearson ratio over lists. -/
def floatPearson (xs ys : List Float) : Float :=
  let vx := floatVariance xs
  let vy := floatVariance ys
  let sx := Float.sqrt vx
  let sy := Float.sqrt vy
  let raw := if sx == 0 || sy == 0 then 0 else floatCovariance xs ys / (sx * sy)
  max (-1) (min 1 raw)

/-- Float helper: Spearman as Pearson-on-ranks. -/
def floatSpearman (xs ys : List Float) : Float :=
  floatPearson (floatRanks xs) (floatRanks ys)

/-- Float helper: exact one-sided permutation p-value for Pearson `r`.
`positive = true` computes `P(r_perm >= r_obs)`, otherwise `P(r_perm <= r_obs)`.

Uses a tiny epsilon in the boundary comparison to stabilize tie cases that can
drift by one ulp across equivalent permutations. -/
def floatPearsonOneSidedPValue (xs ys : List Float) (positive : Bool) : Float :=
  let rObs := floatPearson xs ys
  let eps : Float := 1e-12
  let perms := ys.permutations
  let total := perms.length
  if total = 0 then
    1
  else
    let extreme := perms.foldl
      (fun acc yp =>
        let r := floatPearson xs yp
        if (if positive then rObs - eps <= r else r <= rObs + eps) then acc + 1 else acc) 0
    Float.ofNat extreme / Float.ofNat total

/-- Float helper: binomial upper-tail p-value. -/
def floatBinomialUpperTail (positiveCount total : Nat) : Float :=
  let idx := (List.range (total + 1)).filter (fun i => positiveCount ≤ i)
  let num : Nat := idx.foldl (fun acc i => acc + Nat.choose total i) 0
  Float.ofNat num / Float.ofNat (2 ^ total)

/-- Float helper: bounded binomial p-value in `[0,1]`. -/
def floatBinomialSignPValue (positiveCount total : Nat) : Float :=
  floatClampUnit (floatBinomialUpperTail positiveCount total)

/-- Float helper: all entries are strictly positive. -/
def floatAllPositive (xs : List Float) : Bool :=
  xs.all (fun x => 0 < x)

/-- Float helper: slope for simple linear regression. -/
def floatRegressionSlope (xs ys : List Float) : Float :=
  let mx := floatMean xs
  let my := floatMean ys
  let pairs := List.zip xs ys
  let num := pairs.foldl
    (fun acc p =>
      let x := p.1
      let y := p.2
      acc + (x - mx) * (y - my)) 0
  let den := pairs.foldl
    (fun acc p =>
      let x := p.1
      acc + (x - mx) * (x - mx)) 0
  if den == 0 then 0 else num / den

/-- Float helper: intercept for simple linear regression. -/
def floatRegressionIntercept (xs ys : List Float) : Float :=
  floatMean ys - floatRegressionSlope xs ys * floatMean xs

/-- Float helper: prediction for a single x value. -/
def floatRegressionPredict (xs ys : List Float) (x : Float) : Float :=
  floatRegressionSlope xs ys * x + floatRegressionIntercept xs ys

/-- Float helper: bounded regression tuple `(A, B, R²)`. -/
def floatLinearRegression (xs ys : List Float) : Float × Float × Float :=
  let slope := floatRegressionSlope xs ys
  let intercept := floatRegressionIntercept xs ys
  let pairs := List.zip xs ys
  let yMean := floatMean ys
  let rss := pairs.foldl
    (fun acc p =>
      let x := p.1
      let y := p.2
      let yhat := floatRegressionPredict xs ys x
      acc + (y - yhat) * (y - yhat)) 0
  let tss := ys.foldl (fun acc y => acc + (y - yMean) * (y - yMean)) 0
  let r2Raw := if tss == 0 then 1 else 1 - rss / tss
  (slope, intercept, floatClampUnit r2Raw)

end FloatHelpers

end HeytingLean.Bridge.AlMayahi.TauEpoch
