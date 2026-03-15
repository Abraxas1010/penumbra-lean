import Mathlib.Data.Fin.Basic
import Mathlib.Data.Multiset.ZeroCons
import HeytingLean.WPP.Wolfram.CausalGraph
import HeytingLean.WPP.Wolfram.ConfluenceTheory

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# Confluence vs causal invariance (independence)

We formalize the **terminating** notions used in the Wolfram Physics / SetReplace
discussion (Piskunov 2020):

- **Confluence** (terminating / unique-normal-form): any two reachable normal forms are
  isomorphic as hypergraphs (vertex relabeling).
- **Causal invariance** (terminating): any two singleway evolutions reaching normal forms
  have isomorphic causal graphs.

Then we implement two concrete SetReplace-style counterexamples showing **independence**:
neither property implies the other.
-/

universe u v

namespace Properties

variable {V : Type u} {P : Type v}
variable (sys : System V P) [DecidableEq V]

/-- Confluence for terminating systems: reachable normal forms are unique up to vertex relabeling. -/
def ConfluentNF : Prop :=
  ∀ ⦃s₁ s₂ : HGraph V⦄,
    sys.Reachable s₁ → sys.NormalForm s₁ →
    sys.Reachable s₂ → sys.NormalForm s₂ →
    HGraph.Iso s₁ s₂

/-- Causal invariance for terminating systems: causal graphs of (maximal) evolutions are isomorphic. -/
def CausalInvariant : Prop :=
  ∀ ⦃es₁ es₂ : List sys.Event⦄ ⦃t₁ t₂ : HGraph V⦄,
    sys.Evolves sys.init es₁ t₁ → sys.NormalForm t₁ →
    sys.Evolves sys.init es₂ t₂ → sys.NormalForm t₂ →
    CausalGraph.Iso (sys.causalGraphOf es₁) (sys.causalGraphOf es₂)

end Properties

namespace Counterexamples

/-! ## Helpers -/

section Helpers

variable {V : Type u}

/-- The canonical `Fin 2 → V` substitution determined by a pair `(a,b)`. -/
def sigma2 (a b : V) : Fin 2 → V :=
  Fin.cases a (fun _ : Fin 1 => b)

@[simp] lemma sigma2_zero (a b : V) : sigma2 (V := V) a b 0 = a := by
  simp [sigma2]

@[simp] lemma sigma2_one (a b : V) : sigma2 (V := V) a b 1 = b := by
  -- `1 : Fin 2` is `succ 0`.
  simpa [sigma2] using
    (Fin.cases_succ (motive := fun _ : Fin 2 => V)
      (zero := a) (succ := fun _ : Fin 1 => b) (0 : Fin 1))

lemma inj_sigma2 {a b : V} (h : a ≠ b) : Function.Injective (sigma2 (V := V) a b) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
          have : a = b := by simpa [sigma2] using hij
          exact (h this).elim
  | succ i =>
      cases j using Fin.cases with
      | zero =>
          have : b = a := by simpa [sigma2] using hij
          exact (h this.symm).elim
      | succ j =>
          have hi : i = 0 := Fin.eq_zero i
          have hj : j = 0 := Fin.eq_zero j
          subst hi; subst hj
          rfl

end Helpers

/-! ## CE1: confluent but not causally invariant -/

namespace CE1

abbrev P : Type := Fin 2
abbrev V : Type := Fin 3

def rule : Rule P where
  lhs := ([([0] : Expr P), [0, 1]] : List (Expr P))
  rhs := ([[0, 1], ([1] : Expr P)] : List (Expr P))

def init : HGraph V :=
  ([[0], [0, 1], [1, 2], [0, 2]] : List (Expr V))

def sys : System V P where
  rules := [rule]
  init := init

local instance : DecidableEq V := inferInstance

def e12 : sys.Event :=
  { idx := ⟨0, by decide⟩
    σ := sigma2 (V := V) 0 1 }

def e13 : sys.Event :=
  { idx := ⟨0, by decide⟩
    σ := sigma2 (V := V) 0 2 }

def e23 : sys.Event :=
  { idx := ⟨0, by decide⟩
    σ := sigma2 (V := V) 1 2 }

def s0 : HGraph V := sys.init
def s1 : HGraph V := ([[1], [0, 1], [1, 2], [0, 2]] : List (Expr V))
def s2 : HGraph V := ([[2], [0, 1], [1, 2], [0, 2]] : List (Expr V))

private lemma pair_le {a b : Expr V} {s : HGraph V} (hab : a ≠ b) (ha : a ∈ s) (hb : b ∈ s) :
    (([a, b] : List (Expr V)) : HGraph V) ≤ s := by
  have hnot : a ∉ ({b} : HGraph V) := by
    simpa using hab
  have hb_le : ({b} : HGraph V) ≤ s :=
    (Multiset.singleton_le.2 hb)
  -- `([a,b] : List _)` coerces to `a ::ₘ {b}`.
  have : (a ::ₘ ({b} : HGraph V)) ≤ s :=
    (Multiset.cons_le_of_notMem hnot).2 ⟨ha, hb_le⟩
  simpa using this

lemma e12_app_s0 : e12.Applicable (sys := sys) s0 := by
  dsimp [System.Event.Applicable, s0, sys]
  -- simplify `e12.input`
  -- goal: instantiated LHS ≤ init
  have ha : ([0] : Expr V) ∈ init := by simp [init]
  have hb : ([0, 1] : Expr V) ∈ init := by simp [init]
  have hab : ([0] : Expr V) ≠ ([0, 1] : Expr V) := by decide
  -- `simp` computes the instantiated LHS as `[[0],[0,1]]`.
  simpa [System.Event.input, Rule.instLhs, Rule.inst, HGraph.rename, Expr.rename, e12, sys, rule]
    using (pair_le (a := ([0] : Expr V)) (b := ([0, 1] : Expr V)) hab ha hb)

lemma e13_app_s0 : e13.Applicable (sys := sys) s0 := by
  dsimp [System.Event.Applicable, s0, sys]
  have ha : ([0] : Expr V) ∈ init := by simp [init]
  have hb : ([0, 2] : Expr V) ∈ init := by simp [init]
  have hab : ([0] : Expr V) ≠ ([0, 2] : Expr V) := by decide
  simpa [System.Event.input, Rule.instLhs, Rule.inst, HGraph.rename, Expr.rename, e13, sys, rule]
    using (pair_le (a := ([0] : Expr V)) (b := ([0, 2] : Expr V)) hab ha hb)

lemma e23_app_s1 : e23.Applicable (sys := sys) s1 := by
  dsimp [System.Event.Applicable, s1, sys]
  have ha : ([1] : Expr V) ∈ s1 := by simp [s1]
  have hb : ([1, 2] : Expr V) ∈ s1 := by simp [s1]
  have hab : ([1] : Expr V) ≠ ([1, 2] : Expr V) := by decide
  simpa [System.Event.input, Rule.instLhs, Rule.inst, HGraph.rename, Expr.rename, e23, sys, rule]
    using (pair_le (a := ([1] : Expr V)) (b := ([1, 2] : Expr V)) hab ha hb)

lemma e12_apply_s0 : e12.apply (sys := sys) s0 = s1 := by
  decide

lemma e13_apply_s0 : e13.apply (sys := sys) s0 = s2 := by
  decide

lemma e23_apply_s1 : e23.apply (sys := sys) s1 = s2 := by
  decide

private lemma idx_eq_zero (e : sys.Event) : e.idx = ⟨0, by decide⟩ := by
  apply Fin.ext
  have : e.idx.1 < 1 := by
    have h : e.idx.1 < sys.rules.length := e.idx.isLt
    dsimp [sys] at h
    exact h
  exact Nat.lt_one_iff.mp this

private lemma mem_input_singleton (e : sys.Event) : ([e.σ 0] : Expr V) ∈ e.input (sys := sys) := by
  have hidx : e.idx = ⟨0, by decide⟩ := idx_eq_zero (e := e)
  simp [System.Event.input, sys, rule, hidx, Rule.instLhs, Rule.inst, HGraph.rename, Expr.rename]

private lemma mem_input_pair (e : sys.Event) : ([e.σ 0, e.σ 1] : Expr V) ∈ e.input (sys := sys) := by
  have hidx : e.idx = ⟨0, by decide⟩ := idx_eq_zero (e := e)
  simp [System.Event.input, sys, rule, hidx, Rule.instLhs, Rule.inst, HGraph.rename, Expr.rename]

lemma s2_normalForm : sys.NormalForm s2 := by
  intro e happ
  have hmem0' : ([e.σ 0] : Expr V) ∈ s2 :=
    Multiset.mem_of_le happ (mem_input_singleton (e := e))
  have hσ0 : e.σ 0 = (2 : V) := by
    -- the only singleton in `s2` is `[2]`
    simpa [s2] using hmem0'
  have hmem01' : ([e.σ 0, e.σ 1] : Expr V) ∈ s2 :=
    Multiset.mem_of_le happ (mem_input_pair (e := e))
  have hmem21 : ([2, e.σ 1] : Expr V) ∈ s2 := by
    simpa [hσ0] using hmem01'
  -- Now `e.σ 1` ranges over `0,1,2`; none yields an edge starting with `2` in `s2`.
  cases hσ1 : e.σ 1 using Fin.cases with
  | zero =>
      have : ([2, (0 : V)] : Expr V) ∈ s2 := by
        simpa [hσ1] using hmem21
      simp [s2] at this
  | succ x =>
      cases hx : x using Fin.cases with
      | zero =>
          have : ([2, (1 : V)] : Expr V) ∈ s2 := by
            -- `e.σ 1 = succ 0 = 1`
            simpa [hσ1, hx] using hmem21
          simp [s2] at this
      | succ y =>
          have hy : y = 0 := Fin.eq_zero y
          subst hy
          have : ([2, (2 : V)] : Expr V) ∈ s2 := by
            -- `e.σ 1 = succ (succ 0) = 2`
            simpa [hσ1, hx] using hmem21
          simp [s2] at this

lemma s0_not_normalForm : ¬ sys.NormalForm s0 := by
  intro hn
  exact hn e13 e13_app_s0

lemma s1_not_normalForm : ¬ sys.NormalForm s1 := by
  intro hn
  exact hn e23 e23_app_s1

private lemma apply_eq_of_sigma_eq {e e' : sys.Event} (hσ : e.σ = e'.σ) (s : HGraph V) :
    e.apply (sys := sys) s = e'.apply (sys := sys) s := by
  have hidxe : e.idx = ⟨0, by decide⟩ := idx_eq_zero (e := e)
  have hidxe' : e'.idx = ⟨0, by decide⟩ := idx_eq_zero (e := e')
  simp [System.Event.apply, System.Event.input, System.Event.output, hσ, hidxe, hidxe', sys, rule]

private lemma sigma0_eq_of_app_s0 {e : sys.Event} (happ : e.Applicable (sys := sys) s0) :
    e.σ 0 = (0 : V) := by
  have hmem0' : ([e.σ 0] : Expr V) ∈ s0 :=
    Multiset.mem_of_le happ (mem_input_singleton (e := e))
  simpa [s0, init, sys] using hmem0'

private lemma sigma1_eq_one_or_two_of_app_s0 {e : sys.Event} (happ : e.Applicable (sys := sys) s0) :
    e.σ 1 = (1 : V) ∨ e.σ 1 = (2 : V) := by
  have hσ0 : e.σ 0 = (0 : V) := sigma0_eq_of_app_s0 (e := e) happ
  have hmem01' : ([e.σ 0, e.σ 1] : Expr V) ∈ s0 :=
    Multiset.mem_of_le happ (mem_input_pair (e := e))
  have hmem0x : ([0, e.σ 1] : Expr V) ∈ s0 := by
    simpa [hσ0] using hmem01'
  -- `e.σ 1` cannot be `0` since `[0,0] ∉ s0`; thus it is `1` or `2`.
  cases hσ1 : e.σ 1 using Fin.cases with
  | zero =>
      have : ([0, (0 : V)] : Expr V) ∈ s0 := by
        simpa [hσ1] using hmem0x
      have : False := by
        simp [s0, init, sys] at this
      exact this.elim
  | succ x =>
      cases hx : x using Fin.cases with
      | zero => left; rfl
      | succ y =>
          right
          have hy : y = 0 := Fin.eq_zero y
          subst hy
          rfl

private lemma sigma_eq_e12_of_app_s0 {e : sys.Event} (happ : e.Applicable (sys := sys) s0)
    (hσ1 : e.σ 1 = (1 : V)) : e.σ = e12.σ := by
  have hσ0 : e.σ 0 = (0 : V) := sigma0_eq_of_app_s0 (e := e) happ
  funext i
  cases i using Fin.cases with
  | zero => simp [e12, hσ0]
  | succ j =>
      have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp [e12, hσ1]

private lemma sigma_eq_e13_of_app_s0 {e : sys.Event} (happ : e.Applicable (sys := sys) s0)
    (hσ1 : e.σ 1 = (2 : V)) : e.σ = e13.σ := by
  have hσ0 : e.σ 0 = (0 : V) := sigma0_eq_of_app_s0 (e := e) happ
  funext i
  cases i using Fin.cases with
  | zero => simp [e13, hσ0]
  | succ j =>
      have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp [e13, hσ1]

private lemma sigma0_eq_of_app_s1 {e : sys.Event} (happ : e.Applicable (sys := sys) s1) :
    e.σ 0 = (1 : V) := by
  have hmem0' : ([e.σ 0] : Expr V) ∈ s1 :=
    Multiset.mem_of_le happ (mem_input_singleton (e := e))
  simpa [s1] using hmem0'

private lemma sigma1_eq_two_of_app_s1 {e : sys.Event} (happ : e.Applicable (sys := sys) s1) :
    e.σ 1 = (2 : V) := by
  have hσ0 : e.σ 0 = (1 : V) := sigma0_eq_of_app_s1 (e := e) happ
  have hmem01' : ([e.σ 0, e.σ 1] : Expr V) ∈ s1 :=
    Multiset.mem_of_le happ (mem_input_pair (e := e))
  have hmem1x : ([1, e.σ 1] : Expr V) ∈ s1 := by
    simpa [hσ0] using hmem01'
  -- The only length-2 edge in `s1` starting with `1` is `[1,2]`.
  simpa [s1] using hmem1x

private lemma sigma_eq_e23_of_app_s1 {e : sys.Event} (happ : e.Applicable (sys := sys) s1) :
    e.σ = e23.σ := by
  have hσ0 : e.σ 0 = (1 : V) := sigma0_eq_of_app_s1 (e := e) happ
  have hσ1 : e.σ 1 = (2 : V) := sigma1_eq_two_of_app_s1 (e := e) happ
  funext i
  cases i using Fin.cases with
  | zero => simp [e23, hσ0]
  | succ j =>
      have hj : j = 0 := Fin.eq_zero j
      subst hj
      simp [e23, hσ1]

private lemma final_nf_eq_s2 {es : List sys.Event} {t : HGraph V} :
    sys.Evolves s0 es t → sys.NormalForm t → t = s2 := by
  intro hev hnf
  cases hev with
  | nil =>
      exact (s0_not_normalForm hnf).elim
  | cons e happ hrest =>
      have hσ1' : e.σ 1 = (1 : V) ∨ e.σ 1 = (2 : V) :=
        sigma1_eq_one_or_two_of_app_s0 (e := e) happ
      cases hσ1' with
      | inl hσ1 =>
          have hσ : e.σ = e12.σ := sigma_eq_e12_of_app_s0 (e := e) happ hσ1
          have hmid : e.apply (sys := sys) s0 = s1 := by
            have := apply_eq_of_sigma_eq (e := e) (e' := e12) hσ s0
            simpa [e12_apply_s0] using this
          cases hrest with
          | nil _ =>
              exact (s1_not_normalForm (by simpa [hmid] using hnf)).elim
          | cons e' happ' hrest' =>
              have happ' : e'.Applicable (sys := sys) s1 := by
                -- rewrite applicability along `e.apply s0 = s1`
                simpa [hmid] using happ'
              have hσ' : e'.σ = e23.σ := sigma_eq_e23_of_app_s1 (e := e') happ'
              have hmid' : e'.apply (sys := sys) s1 = s2 := by
                have := apply_eq_of_sigma_eq (e := e') (e' := e23) hσ' s1
                simpa [e23_apply_s1] using this
              have hn2 : sys.NormalForm s2 := s2_normalForm
              cases hrest' with
              | nil _ =>
                  -- `t = e'.apply (e.apply s0) = e'.apply s1 = s2`
                  simp [hmid, hmid']
              | cons e'' happ'' _ =>
                  have happ'' : e''.Applicable (sys := sys) s2 := by
                    -- rewrite applicability along `e.apply s0 = s1` and `e'.apply s1 = s2`
                    simpa [hmid, hmid'] using happ''
                  exact False.elim (hn2 e'' happ'')
      | inr hσ1 =>
          have hσ : e.σ = e13.σ := sigma_eq_e13_of_app_s0 (e := e) happ hσ1
          have hmid : e.apply (sys := sys) s0 = s2 := by
            have := apply_eq_of_sigma_eq (e := e) (e' := e13) hσ s0
            simpa [e13_apply_s0] using this
          have hn2 : sys.NormalForm s2 := s2_normalForm
          cases hrest with
          | nil _ =>
              simp [hmid]
          | cons e'' happ'' _ =>
              have happ'' : e''.Applicable (sys := sys) s2 := by
                simpa [hmid] using happ''
              exact False.elim (hn2 e'' happ'')

theorem terminatingFrom_init : System.TerminatingFrom (sys := sys) s0 := by
  refine ⟨2, ?_⟩
  intro es t hev
  cases hev with
  | nil =>
      simp
  | cons e happ hrest =>
      rename_i esTail
      -- From `s0`, any applicable event must map `σ 1` to `1` or `2`.
      have hσ1 : e.σ 1 = (1 : V) ∨ e.σ 1 = (2 : V) :=
        sigma1_eq_one_or_two_of_app_s0 (e := e) happ
      cases hσ1 with
      | inl hσ1 =>
          -- First step is `e12`, hence `e.apply s0 = s1`.
          have hσ : e.σ = e12.σ := sigma_eq_e12_of_app_s0 (e := e) happ hσ1
          have hmid : e.apply (sys := sys) s0 = s1 := by
            have := apply_eq_of_sigma_eq (e := e) (e' := e12) hσ s0
            simpa [e12_apply_s0] using this
          have hrest' : sys.Evolves s1 esTail t := by
            simpa [hmid] using hrest
          cases hrest' with
          | nil =>
              -- `es = []`, so the total length is `1`.
              simp
          | cons e' happ' hrest'' =>
              -- Second step must be `e23`, hence `e'.apply s1 = s2`, and then we must stop.
              have hσ' : e'.σ = e23.σ := sigma_eq_e23_of_app_s1 (e := e') happ'
              have hmid' : e'.apply (sys := sys) s1 = s2 := by
                have := apply_eq_of_sigma_eq (e := e') (e' := e23) hσ' s1
                simpa [e23_apply_s1] using this
              have hn2 : sys.NormalForm s2 := s2_normalForm
              -- The tail after reaching `s2` must be empty (since `s2` is a normal form).
              cases hrest'' with
              | nil =>
                  simp
              | cons e'' happ'' _ =>
                  have happ'' : e''.Applicable (sys := sys) s2 := by
                    simpa [hmid'] using happ''
                  exact False.elim (hn2 e'' happ'')
      | inr hσ1 =>
          -- First step is `e13`, hence `e.apply s0 = s2`, and then we must stop.
          have hσ : e.σ = e13.σ := sigma_eq_e13_of_app_s0 (e := e) happ hσ1
          have hmid : e.apply (sys := sys) s0 = s2 := by
            have := apply_eq_of_sigma_eq (e := e) (e' := e13) hσ s0
            simpa [e13_apply_s0] using this
          have hn2 : sys.NormalForm s2 := s2_normalForm
          cases hrest with
          | nil =>
              simp
          | cons e' happ' _ =>
              have happ' : e'.Applicable (sys := sys) s2 := by
                simpa [hmid] using happ'
              exact False.elim (hn2 e' happ')

theorem confluentNF : Properties.ConfluentNF (sys := sys) := by
  intro s₁ s₂ hr₁ hn₁ hr₂ hn₂
  rcases hr₁ with ⟨es₁, hev₁⟩
  rcases hr₂ with ⟨es₂, hev₂⟩
  have hs₁ : s₁ = s2 := final_nf_eq_s2 (es := es₁) (t := s₁) hev₁ hn₁
  have hs₂ : s₂ = s2 := final_nf_eq_s2 (es := es₂) (t := s₂) hev₂ hn₂
  subst hs₁; subst hs₂
  exact HGraph.Iso.refl s2

theorem not_causalInvariant : ¬ Properties.CausalInvariant (sys := sys) := by
  intro hci
  -- Two terminating evolutions to the same normal form `s2`:
  --   short: `[e13]`  (length 1)
  --   long:  `[e12, e23]` (length 2)
  have hn2 : sys.NormalForm s2 := s2_normalForm
  have hev_short : sys.Evolves s0 [e13] s2 := by
    refine System.Evolves.cons (sys := sys) (s := s0) (es := []) (t := s2) e13 ?_ ?_
    · exact e13_app_s0
    · simpa [e13_apply_s0] using (System.Evolves.nil (sys := sys) s2)
  have hev_long : sys.Evolves s0 [e12, e23] s2 := by
    refine System.Evolves.cons (sys := sys) (s := s0) (es := [e23]) (t := s2) e12 ?_ ?_
    · exact e12_app_s0
    · have : sys.Evolves (e12.apply (sys := sys) s0) [e23] s2 := by
        refine System.Evolves.cons (sys := sys) (s := e12.apply (sys := sys) s0) (es := []) (t := s2) e23 ?_ ?_
        · simpa [e12_apply_s0] using e23_app_s1
        · simpa [e23_apply_s1, e12_apply_s0] using (System.Evolves.nil (sys := sys) s2)
      simpa using this
  have hiso : CausalGraph.Iso (sys.causalGraphOf [e13]) (sys.causalGraphOf [e12, e23]) :=
    hci hev_short hn2 hev_long hn2
  have hne : (sys.causalGraphOf [e13]).n ≠ (sys.causalGraphOf [e12, e23]).n := by
    simp [System.causalGraphOf]
  exact hne (CausalGraph.Iso.n_eq hiso)

end CE1

/-! ## CE2: causally invariant but not confluent -/

namespace CE2

abbrev P : Type := Fin 2
abbrev V : Type := Fin 2

def rule : Rule P where
  lhs := ([[0, 1], [1, 0]] : List (Expr P))
  rhs := ([([0] : Expr P)] : List (Expr P))

def init : HGraph V :=
  ([[0, 1], [1, 0], ([0] : Expr V)] : List (Expr V))

def sys : System V P where
  rules := [rule]
  init := init

local instance : DecidableEq V := inferInstance

def e_id : sys.Event :=
  { idx := ⟨0, by decide⟩
    σ := sigma2 (V := V) 0 1 }

def e_swap : sys.Event :=
  { idx := ⟨0, by decide⟩
    σ := sigma2 (V := V) 1 0 }

def s0 : HGraph V := sys.init
def nf1 : HGraph V := ([[0], [0]] : List (Expr V))
def nf2 : HGraph V := ([[0], [1]] : List (Expr V))

private lemma sigma_eq_e_id_or_swap (e : sys.Event) (happ : e.Applicable (sys := sys) s0) :
    e.σ = e_id.σ ∨ e.σ = e_swap.σ := by
  -- Use applicability: the instantiated LHS contains the edge `[σ 0, σ 1]`, and `s0`
  -- has only two length-2 edges (`[0,1]` and `[1,0]`), so `σ` must be either identity or swap.
  have hmem01 : ([e.σ 0, e.σ 1] : Expr V) ∈ s0 := by
    have hidx : e.idx = ⟨0, by decide⟩ := by
      -- `sys.rules.length = 1`, so any event must have `idx = 0`.
      simpa [sys] using (Fin.eq_zero e.idx)
    have hmemIn : ([e.σ 0, e.σ 1] : Expr V) ∈ e.input (sys := sys) := by
      simp [System.Event.input, sys, rule, hidx, Rule.instLhs, Rule.inst, HGraph.rename, Expr.rename]
    exact Multiset.mem_of_le happ hmemIn
  cases hσ0 : e.σ 0 using Fin.cases with
  | zero =>
      have hσ1 : e.σ 1 = (1 : V) := by
        cases hσ1 : e.σ 1 using Fin.cases with
        | zero =>
            have h00 : ([0, (0 : V)] : Expr V) ∈ s0 := by
              simpa [hσ0, hσ1] using hmem01
            have : False := by
              simp [s0, sys, init] at h00
            exact this.elim
        | succ j =>
            have hj : j = 0 := Fin.eq_zero j
            subst hj
            simp
      left
      funext i
      cases i using Fin.cases with
      | zero => simp [e_id, hσ0]
      | succ j =>
          have hj : j = 0 := Fin.eq_zero j
          subst hj
          simp [e_id, hσ1]
  | succ j =>
      have hj : j = 0 := Fin.eq_zero j
      subst hj
      have hσ1 : e.σ 1 = (0 : V) := by
        cases hσ1 : e.σ 1 using Fin.cases with
        | zero => simp
        | succ k =>
            have hk : k = 0 := Fin.eq_zero k
            subst hk
            have h11 : ([1, (1 : V)] : Expr V) ∈ s0 := by
              simpa [hσ0, hσ1] using hmem01
            have : False := by
              simp [s0, sys, init] at h11
            exact this.elim
      right
      funext i
      cases i using Fin.cases with
      | zero => simp [e_swap, hσ0]
      | succ j =>
          have hj : j = 0 := Fin.eq_zero j
          subst hj
          simp [e_swap, hσ1]

lemma e_id_app : e_id.Applicable (sys := sys) s0 := by
  dsimp [System.Event.Applicable, s0, sys]
  -- LHS has two distinct length-2 edges which are both present in `init`.
  have ha : ([0, 1] : Expr V) ∈ init := by simp [init]
  have hb : ([1, 0] : Expr V) ∈ init := by simp [init]
  have hab : ([0, 1] : Expr V) ≠ ([1, 0] : Expr V) := by decide
  have hle : (([[0, 1], [1, 0]] : List (Expr V)) : HGraph V) ≤ init := by
    -- use the CE1 helper `pair_le` pattern directly
    have hnot : ([0, 1] : Expr V) ∉ ({[1, 0]} : HGraph V) := by simp [hab]
    have hb_le : ({[1, 0]} : HGraph V) ≤ init := (Multiset.singleton_le.2 hb)
    have : ([0, 1] : Expr V) ::ₘ ({[1, 0]} : HGraph V) ≤ init :=
      (Multiset.cons_le_of_notMem hnot).2 ⟨ha, hb_le⟩
    simpa using this
  simpa [System.Event.input, Rule.instLhs, Rule.inst, HGraph.rename, Expr.rename, e_id, rule]
    using hle

lemma e_swap_app : e_swap.Applicable (sys := sys) s0 := by
  dsimp [System.Event.Applicable, s0, sys]
  have ha : ([1, 0] : Expr V) ∈ init := by simp [init]
  have hb : ([0, 1] : Expr V) ∈ init := by simp [init]
  have hab : ([1, 0] : Expr V) ≠ ([0, 1] : Expr V) := by decide
  have hle : (([[1, 0], [0, 1]] : List (Expr V)) : HGraph V) ≤ init := by
    have hnot : ([1, 0] : Expr V) ∉ ({[0, 1]} : HGraph V) := by simp [hab]
    have hb_le : ({[0, 1]} : HGraph V) ≤ init := (Multiset.singleton_le.2 hb)
    have : ([1, 0] : Expr V) ::ₘ ({[0, 1]} : HGraph V) ≤ init :=
      (Multiset.cons_le_of_notMem hnot).2 ⟨ha, hb_le⟩
    simpa using this
  simpa [System.Event.input, Rule.instLhs, Rule.inst, HGraph.rename, Expr.rename, e_swap, rule]
    using hle

lemma e_id_apply : e_id.apply (sys := sys) s0 = nf1 := by
  decide

lemma e_swap_apply : e_swap.apply (sys := sys) s0 = nf2 := by
  decide

private lemma idx_eq_zero (e : sys.Event) : e.idx = ⟨0, by decide⟩ := by
  apply Fin.ext
  have : e.idx.1 < 1 := by
    have h : e.idx.1 < sys.rules.length := e.idx.isLt
    dsimp [sys] at h
    exact h
  exact Nat.lt_one_iff.mp this

private lemma apply_eq_of_sigma_eq {e e' : sys.Event} (hσ : e.σ = e'.σ) (s : HGraph V) :
    e.apply (sys := sys) s = e'.apply (sys := sys) s := by
  have hidxe : e.idx = ⟨0, by decide⟩ := idx_eq_zero (e := e)
  have hidxe' : e'.idx = ⟨0, by decide⟩ := idx_eq_zero (e := e')
  simp [System.Event.apply, System.Event.input, System.Event.output, hσ, hidxe, hidxe', sys, rule]

lemma nf1_normalForm : sys.NormalForm nf1 := by
  intro e happ
  -- LHS requires length-2 expressions; `nf1` has only length-1 expressions.
  have hmem : ([e.σ 0, e.σ 1] : Expr V) ∈ nf1 :=
    Multiset.mem_of_le happ (by
      have hidx : e.idx = ⟨0, by decide⟩ := idx_eq_zero (e := e)
      simp [System.Event.input, sys, rule, hidx, Rule.instLhs, Rule.inst, HGraph.rename, Expr.rename])
  simp [nf1] at hmem

lemma nf2_normalForm : sys.NormalForm nf2 := by
  intro e happ
  have hmem : ([e.σ 0, e.σ 1] : Expr V) ∈ nf2 :=
    Multiset.mem_of_le happ (by
      have hidx : e.idx = ⟨0, by decide⟩ := idx_eq_zero (e := e)
      simp [System.Event.input, sys, rule, hidx, Rule.instLhs, Rule.inst, HGraph.rename, Expr.rename])
  simp [nf2] at hmem

private lemma length_eq_one_of_nf {es : List sys.Event} {t : HGraph V} :
    sys.Evolves s0 es t → sys.NormalForm t → es.length = 1 := by
  intro hev hnf
  -- `s0` is not a normal form because `e_id` is applicable.
  have hs0 : ¬ sys.NormalForm s0 := by
    intro hn
    exact hn e_id e_id_app
  cases hev with
  | nil =>
      exact (hs0 hnf).elim
  | cons e happ hrest =>
      -- Any single step from `s0` yields `nf1` or `nf2`, both normal forms.
      have hn_mid : sys.NormalForm (e.apply (sys := sys) s0) := by
        have hσ : e.σ = e_id.σ ∨ e.σ = e_swap.σ := sigma_eq_e_id_or_swap (e := e) happ
        cases hσ with
        | inl hσ =>
            have happly : e.apply (sys := sys) s0 = nf1 := by
              calc
                e.apply (sys := sys) s0 = e_id.apply (sys := sys) s0 := by
                  simpa using (apply_eq_of_sigma_eq (e := e) (e' := e_id) hσ s0)
                _ = nf1 := e_id_apply
            simp [happly, nf1_normalForm]
        | inr hσ =>
            have happly : e.apply (sys := sys) s0 = nf2 := by
              calc
                e.apply (sys := sys) s0 = e_swap.apply (sys := sys) s0 := by
                  simpa using (apply_eq_of_sigma_eq (e := e) (e' := e_swap) hσ s0)
                _ = nf2 := e_swap_apply
            simp [happly, nf2_normalForm]
      -- Therefore the tail must be empty.
      cases hrest with
      | nil => simp
      | cons e' happ' _ =>
          exact (hn_mid e' happ').elim

private lemma edge_iff_false_of_len_eq_one (es : List sys.Event) (hlen : es.length = 1)
    (i j : Fin (sys.causalGraphOf es).n) : (sys.causalGraphOf es).edge i j ↔ False := by
  constructor
  · intro h
    have hi_lt : i.1 < 1 := by
      have : i.1 < es.length := i.isLt
      simpa [hlen] using this
    have hi0 : i.1 = 0 := Nat.lt_one_iff.mp hi_lt
    have hj_lt : j.1 < 1 := by
      have : j.1 < es.length := j.isLt
      simpa [hlen] using this
    have hj0 : j.1 = 0 := Nat.lt_one_iff.mp hj_lt
    have hlt : i.1 < j.1 := h.1
    simp [hi0, hj0] at hlt
  · intro hf
    exact False.elim hf

theorem terminatingFrom_init : System.TerminatingFrom (sys := sys) s0 := by
  refine ⟨1, ?_⟩
  intro es t hev
  cases hev with
  | nil =>
      simp
  | cons e happ hrest =>
      -- Any applicable event from `s0` must be either `e_id` or `e_swap`.
      have hσ : e.σ = e_id.σ ∨ e.σ = e_swap.σ := sigma_eq_e_id_or_swap (e := e) happ
      -- After one step we are in a normal form (`nf1` or `nf2`), so the tail must be empty.
      have hn_mid : sys.NormalForm (e.apply (sys := sys) s0) := by
        cases hσ with
        | inl hσ =>
            have happly : e.apply (sys := sys) s0 = nf1 := by
              have := apply_eq_of_sigma_eq (e := e) (e' := e_id) hσ s0
              simpa [e_id_apply] using this
            simpa [happly] using nf1_normalForm
        | inr hσ =>
            have happly : e.apply (sys := sys) s0 = nf2 := by
              have := apply_eq_of_sigma_eq (e := e) (e' := e_swap) hσ s0
              simpa [e_swap_apply] using this
            simpa [happly] using nf2_normalForm
      cases hrest with
      | nil =>
          simp
      | cons e' happ' _ =>
          exact False.elim (hn_mid e' happ')

theorem causalInvariant : Properties.CausalInvariant (sys := sys) := by
  intro es₁ es₂ t₁ t₂ hev₁ hn₁ hev₂ hn₂
  have hlen1 : es₁.length = 1 := length_eq_one_of_nf (es := es₁) (t := t₁) hev₁ hn₁
  have hlen2 : es₂.length = 1 := length_eq_one_of_nf (es := es₂) (t := t₂) hev₂ hn₂
  have hlen : (sys.causalGraphOf es₁).n = (sys.causalGraphOf es₂).n := by
    simp [System.causalGraphOf, hlen1, hlen2]
  refine ⟨Equiv.cast (congrArg Fin hlen), ?_⟩
  intro i j
  have hfalse1 : (sys.causalGraphOf es₁).edge i j ↔ False :=
    edge_iff_false_of_len_eq_one (es := es₁) hlen1 i j
  have hfalse2 :
      (sys.causalGraphOf es₂).edge (Equiv.cast (congrArg Fin hlen) i) (Equiv.cast (congrArg Fin hlen) j) ↔ False :=
    edge_iff_false_of_len_eq_one (es := es₂) hlen2 _ _
  constructor
  · intro h
    exact (False.elim ((hfalse1.mp h)))
  · intro h
    exact (False.elim ((hfalse2.mp h)))

theorem not_confluentNF : ¬ Properties.ConfluentNF (sys := sys) := by
  intro hconf
  have hr1 : sys.Reachable nf1 := by
    refine ⟨[e_id], ?_⟩
    refine System.Evolves.cons (sys := sys) (s := s0) (es := []) (t := nf1) e_id e_id_app ?_
    simpa [e_id_apply] using (System.Evolves.nil (sys := sys) nf1)
  have hr2 : sys.Reachable nf2 := by
    refine ⟨[e_swap], ?_⟩
    refine System.Evolves.cons (sys := sys) (s := s0) (es := []) (t := nf2) e_swap e_swap_app ?_
    simpa [e_swap_apply] using (System.Evolves.nil (sys := sys) nf2)
  have hn1 : sys.NormalForm nf1 := nf1_normalForm
  have hn2 : sys.NormalForm nf2 := nf2_normalForm
  have hiso : HGraph.Iso nf1 nf2 := hconf hr1 hn1 hr2 hn2
  -- show no permutation of `Fin 2` maps `nf1` to `nf2`
  rcases hiso with ⟨e, he⟩
  have h0 : e 0 = (0 : V) ∨ e 0 = (1 : V) := by
    cases e 0 using Fin.cases with
    | zero => exact Or.inl rfl
    | succ j =>
        have hj : j = 0 := Fin.eq_zero j
        subst hj
        exact Or.inr rfl
  cases h0 with
  | inl he0 =>
      -- `e = id`
      have he1 : e 1 = (1 : V) := by
        -- injectivity forces `e 1 ≠ e 0 = 0`, hence `e 1 = 1`
        have hne : e 1 ≠ (0 : V) := by
          intro h
          have : (1 : V) = 0 := e.injective (by simpa [he0] using h)
          exact (by decide : (1 : V) ≠ 0) this
        cases he1' : e 1 using Fin.cases with
        | zero => exact (hne he1').elim
        | succ j =>
            have hj : j = 0 := Fin.eq_zero j
            subst hj
            simp
      have hid : e = Equiv.refl V := by
        ext i
        cases i using Fin.cases with
        | zero => simp [he0]
        | succ j =>
            have hj : j = 0 := Fin.eq_zero j
            subst hj
            simp [he1]
      subst hid
      have : nf1 = nf2 := by
        simpa [HGraph.rename, HGraph.rename_id] using he
      exact (by decide : (nf1 : HGraph V) ≠ nf2) this
  | inr he0 =>
      -- `e = swap`
      have hswap : e = Equiv.swap (0 : V) 1 := by
        ext i
        cases i using Fin.cases with
        | zero => simp [he0, Equiv.swap_apply_left]
        | succ j =>
            have hj : j = 0 := Fin.eq_zero j
            subst hj
            -- injectivity forces `e 1 = 0`
            have hne : e 1 ≠ (1 : V) := by
              intro h
              have : (1 : V) = 0 := e.injective (by simpa [he0] using h)
              exact (by decide : (1 : V) ≠ 0) this
            cases he1' : e 1 using Fin.cases with
            | zero => simp [he1', Equiv.swap_apply_right]
            | succ k =>
                have hk : k = 0 := Fin.eq_zero k
                subst hk
                have : e 1 = (1 : V) := by simp [he1']
                exact (hne this).elim
      subst hswap
      -- compute rename under the swap: `nf1` becomes `[[1],[1]]`, not `nf2`.
      have : HGraph.rename (Equiv.swap (0 : V) 1) nf1 = nf2 := by simpa [HGraph.rename] using he
      have : (([[1], [1]] : List (Expr V)) : HGraph V) = nf2 := by
        simpa [nf1, nf2] using this
      exact (by decide : ((([[1], [1]] : List (Expr V)) : HGraph V) : HGraph V) ≠ nf2) this

end CE2

/-! ## Independence theorem -/

theorem confluence_causal_invariance_independent :
    (¬ (∀ {V P : Type} (sys : System V P) [DecidableEq V],
        Properties.ConfluentNF (sys := sys) → Properties.CausalInvariant (sys := sys))) ∧
    (¬ (∀ {V P : Type} (sys : System V P) [DecidableEq V],
        Properties.CausalInvariant (sys := sys) → Properties.ConfluentNF (sys := sys))) := by
  constructor
  · intro h
    have : Properties.CausalInvariant (sys := CE1.sys) := h (sys := CE1.sys) CE1.confluentNF
    exact CE1.not_causalInvariant this
  · intro h
    have : Properties.ConfluentNF (sys := CE2.sys) := h (sys := CE2.sys) CE2.causalInvariant
    exact CE2.not_confluentNF this

end Counterexamples

end Wolfram
end WPP
end HeytingLean
