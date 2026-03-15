import HeytingLean.WPP.Wolfram.ConfluenceCausalInvariance
import HeytingLean.WPP.Wolfram.CausalGraphGC

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# CE1 under observable-event causal graphs

In `ConfluenceCausalInvariance`, CE1 is confluent (unique normal form) but **not** causally
invariant under the SetReplace-style causal graph, since the two maximal evolutions to the normal
form have different lengths.

Here we show that the same two evolutions *do* have isomorphic causal graphs under the
observable-event ("GC") abstraction from `CausalGraphGC`.
-/

namespace Counterexamples.CE1

open Counterexamples.CE1

local instance : DecidableEq V := inferInstance

private lemma e13_observableB : System.Event.observableB (sys := sys) e13 s2 = true := by
  decide

private lemma e23_observableB : System.Event.observableB (sys := sys) e23 s2 = true := by
  decide

private lemma e12_observableB : System.Event.observableB (sys := sys) e12 s2 = false := by
  decide

private lemma idxs_short : sys.observableIdxs [e13] s2 = [⟨0, by decide⟩] := by
  decide

private lemma idxs_long : sys.observableIdxs [e12, e23] s2 = [⟨1, by decide⟩] := by
  decide

private lemma gc_n_short : (sys.causalGraphGCOf [e13] s2).n = 1 := by
  simp (config := { zeta := true }) [System.causalGraphGCOf, idxs_short]

private lemma gc_n_long : (sys.causalGraphGCOf [e12, e23] s2).n = 1 := by
  simp (config := { zeta := true }) [System.causalGraphGCOf, idxs_long]

private lemma gc_edge_false_short (i j : Fin (sys.causalGraphGCOf [e13] s2).n) :
    (sys.causalGraphGCOf [e13] s2).edge i j ↔ False := by
  simp (config := { zeta := true }) [System.causalGraphGCOf, idxs_short]

private lemma gc_edge_false_long (i j : Fin (sys.causalGraphGCOf [e12, e23] s2).n) :
    (sys.causalGraphGCOf [e12, e23] s2).edge i j ↔ False := by
  simp (config := { zeta := true }) [System.causalGraphGCOf, idxs_long]

/-- In CE1, the *short* evolution `[e13]` and the *long* evolution `[e12, e23]` have isomorphic
observable-event causal graphs. -/
theorem causalGraphGC_iso_short_long :
    CausalGraph.Iso (sys.causalGraphGCOf [e13] s2) (sys.causalGraphGCOf [e12, e23] s2) := by
  have hn : (sys.causalGraphGCOf [e13] s2).n = (sys.causalGraphGCOf [e12, e23] s2).n := by
    simp [gc_n_short, gc_n_long]
  refine ⟨Equiv.cast (congrArg Fin hn), ?_⟩
  intro i j
  have hfalse1 : (sys.causalGraphGCOf [e13] s2).edge i j ↔ False :=
    gc_edge_false_short (i := i) (j := j)
  have hfalse2 :
      (sys.causalGraphGCOf [e12, e23] s2).edge (Equiv.cast (congrArg Fin hn) i)
        (Equiv.cast (congrArg Fin hn) j) ↔ False :=
    gc_edge_false_long (i := (Equiv.cast (congrArg Fin hn) i)) (j := (Equiv.cast (congrArg Fin hn) j))
  constructor <;> intro h
  · exact False.elim (hfalse1.mp h)
  · exact False.elim (hfalse2.mp h)

end Counterexamples.CE1

namespace Counterexamples.CE2

open Counterexamples.CE2

local instance : DecidableEq V := inferInstance

private lemma s0_not_normalForm : ¬ sys.NormalForm s0 := by
  intro hn
  exact hn e_id e_id_app

private lemma sigma_eq_e_id_or_swap (e : sys.Event) (happ : e.Applicable (sys := sys) s0) :
    e.σ = e_id.σ ∨ e.σ = e_swap.σ := by
  have hmem01 : ([e.σ 0, e.σ 1] : Expr V) ∈ s0 := by
    have hidx : e.idx = ⟨0, by decide⟩ := by
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
        | zero => rfl
        | succ j =>
            have hj : j = 0 := Fin.eq_zero j
            subst hj
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

private lemma apply_eq_of_sigma_eq {e e' : sys.Event} (hσ : e.σ = e'.σ) (s : HGraph V) :
    e.apply (sys := sys) s = e'.apply (sys := sys) s := by
  have hidxe : e.idx = ⟨0, by decide⟩ := by
    simpa [sys] using (Fin.eq_zero e.idx)
  have hidxe' : e'.idx = ⟨0, by decide⟩ := by
    simpa [sys] using (Fin.eq_zero e'.idx)
  simp [System.Event.apply, System.Event.input, System.Event.output, hσ, hidxe, hidxe', sys, rule]

private lemma normalForm_apply_s0_of_app {e : sys.Event} (happ : e.Applicable (sys := sys) s0) :
    sys.NormalForm (e.apply (sys := sys) s0) := by
  have hσ : e.σ = e_id.σ ∨ e.σ = e_swap.σ := sigma_eq_e_id_or_swap (e := e) happ
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

private lemma length_eq_one_of_nf {es : List sys.Event} {t : HGraph V} :
    sys.Evolves s0 es t → sys.NormalForm t → es.length = 1 := by
  intro hev hnf
  cases hev with
  | nil =>
      exact (s0_not_normalForm (by simpa using hnf)).elim
  | cons e happ hrest =>
      have hn_mid : sys.NormalForm (e.apply (sys := sys) s0) :=
        normalForm_apply_s0_of_app (e := e) happ
      cases hrest with
      | nil =>
          simp
      | cons e' happ' _ =>
          exact False.elim (hn_mid e' happ')

private lemma e_observableB_of_evolves_singleton {e : sys.Event} {t : HGraph V}
    (hev : sys.Evolves s0 [e] t) : System.Event.observableB (sys := sys) e t = true := by
  cases hev with
  | cons e' _happ hrest =>
      cases hrest with
      | nil =>
          -- In this branch, `t = e.apply s0`.
          set t' := e.apply (sys := sys) s0
          -- The RHS always creates the singleton edge `[σ 0]`, which is not in the LHS.
          have hout : ([e.σ 0] : Expr V) ∈ e.output (sys := sys) := by
            simp [System.Event.output, Rule.instRhs, Rule.inst, HGraph.rename, Expr.rename, sys, rule]
          have hnot : ([e.σ 0] : Expr V) ∉ e.input (sys := sys) := by
            intro hx
            simp [System.Event.input, Rule.instLhs, Rule.inst, HGraph.rename, Expr.rename, sys, rule] at hx
          have ht : ([e.σ 0] : Expr V) ∈ t' := by
            have : ([e.σ 0] : Expr V) ∈ e.output (sys := sys) := hout
            -- `t = e.apply s0 = (s0 - input) + output`, so any output edge is in `t`.
            simpa [t', System.Event.apply, System.Event.output] using (Multiset.mem_add.mpr (Or.inr this))
          -- `observableB` is an `||`-fold over outputs; since a created output is in `t`, it is `true`.
          dsimp [System.Event.observableB]
          have hmemTrue :
              true ∈
                ((e.output (sys := sys)).map (fun x => decide (x ∉ e.input (sys := sys) ∧ x ∈ t'))) := by
            refine Multiset.mem_map.2 ?_
            refine ⟨([e.σ 0] : Expr V), hout, ?_⟩
            exact decide_eq_true ⟨hnot, ht⟩
          exact System.Multiset.fold_or_eq_true_of_mem_true hmemTrue

/-- CE2 remains causally invariant under the observable-event (GC) causal graph. -/
theorem causalInvariantGC : Properties.GCausalInvariant (sys := sys) := by
  intro es₁ es₂ t₁ t₂ hev₁ hn₁ hev₂ hn₂
  have hlen1 : es₁.length = 1 := length_eq_one_of_nf (es := es₁) (t := t₁) hev₁ hn₁
  have hlen2 : es₂.length = 1 := length_eq_one_of_nf (es := es₂) (t := t₂) hev₂ hn₂
  cases es₁ with
  | nil => cases hlen1
  | cons e1 tail1 =>
      cases tail1 with
      | nil =>
          cases es₂ with
          | nil => cases hlen2
          | cons e2 tail2 =>
              cases tail2 with
              | nil =>
                  have hob1 : System.Event.observableB (sys := sys) e1 t₁ = true :=
                    e_observableB_of_evolves_singleton (e := e1) (t := t₁) (by simpa using hev₁)
                  have hob2 : System.Event.observableB (sys := sys) e2 t₂ = true :=
                    e_observableB_of_evolves_singleton (e := e2) (t := t₂) (by simpa using hev₂)
                  have idxs1 : sys.observableIdxs [e1] t₁ = [⟨0, by simp⟩] := by
                    simp [System.observableIdxs, hob1]
                    decide
                  have idxs2 : sys.observableIdxs [e2] t₂ = [⟨0, by simp⟩] := by
                    simp [System.observableIdxs, hob2]
                    decide
                  have hn1 : (sys.causalGraphGCOf [e1] t₁).n = 1 := by
                    have hlen : (sys.observableIdxs [e1] t₁).length = 1 := by
                      simp [idxs1]
                    simpa (config := { zeta := true }) [System.causalGraphGCOf] using hlen
                  have hn2 : (sys.causalGraphGCOf [e2] t₂).n = 1 := by
                    have hlen : (sys.observableIdxs [e2] t₂).length = 1 := by
                      simp [idxs2]
                    simpa (config := { zeta := true }) [System.causalGraphGCOf] using hlen
                  have hn : (sys.causalGraphGCOf [e1] t₁).n = (sys.causalGraphGCOf [e2] t₂).n := by
                    simp [hn1, hn2]
                  refine ⟨Equiv.cast (congrArg Fin hn), ?_⟩
                  intro i j
                  have hfalse1 : (sys.causalGraphGCOf [e1] t₁).edge i j ↔ False := by
                    simp (config := { zeta := true }) [System.causalGraphGCOf, idxs1]
                  have hfalse2 :
                      (sys.causalGraphGCOf [e2] t₂).edge (Equiv.cast (congrArg Fin hn) i)
                        (Equiv.cast (congrArg Fin hn) j) ↔ False := by
                    simp (config := { zeta := true }) [System.causalGraphGCOf, idxs2]
                  constructor <;> intro h
                  · exact False.elim (hfalse1.mp h)
                  · exact False.elim (hfalse2.mp h)
              | cons _ _ => cases hlen2
      | cons _ _ => cases hlen1

end Counterexamples.CE2

end Wolfram
end WPP
end HeytingLean
