import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.MapFold

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# Wolfram hypergraphs (SetReplace-style)

This is a minimal, SetReplace-aligned encoding:
- An **expression** is an ordered list of vertices (duplicates allowed).
- A **hypergraph state** is a multiset of expressions (duplicates allowed).

We also define vertex-renaming and a basic isomorphism notion for states.
-/

universe u v

/-- An expression / spatial hyperedge: ordered, duplicate-aware. -/
abbrev Expr (V : Type u) : Type u := List V

/-- A hypergraph state: multiset of expressions (edge multiplicity matters). -/
abbrev HGraph (V : Type u) : Type u := Multiset (Expr V)

namespace Expr

/-- Rename vertices in an expression. -/
@[simp] def rename {V : Type u} {W : Type v} (f : V → W) : Expr V → Expr W :=
  List.map f

@[simp] lemma rename_id {V : Type u} (e : Expr V) :
    rename (fun x => x) e = e := by
  simp [rename]

@[simp] lemma rename_comp {U : Type u} {V : Type v} {W : Type _}
    (f : U → V) (g : V → W) (e : Expr U) :
    rename (fun x => g (f x)) e = rename g (rename f e) := by
  simp [rename, List.map_map]

end Expr

namespace HGraph

/-- Rename vertices in a hypergraph state. -/
@[simp] def rename {V : Type u} {W : Type v} (f : V → W) : HGraph V → HGraph W :=
  Multiset.map (Expr.rename f)

@[simp] lemma rename_id {V : Type u} (g : HGraph V) :
    rename (fun x => x) g = g := by
  simp [rename]

@[simp] lemma rename_comp {U : Type u} {V : Type v} {W : Type _}
    (f : U → V) (g : V → W) (h : HGraph U) :
    rename (fun x => g (f x)) h = rename g (rename f h) := by
  -- Step 1: rewrite the LHS map-function pointwise to the composed function.
  have hfun :
      Multiset.map (Expr.rename (fun x => g (f x))) h =
        Multiset.map ((Expr.rename g) ∘ (Expr.rename f)) h := by
    refine Multiset.map_congr rfl ?_
    intro e _he
    simp [Expr.rename, Function.comp, List.map_map]
  -- Step 2: use `Multiset.map_map` to expand composition on the multiset side.
  calc
    rename (fun x => g (f x)) h
        = Multiset.map (Expr.rename (fun x => g (f x))) h := rfl
    _ = Multiset.map ((Expr.rename g) ∘ (Expr.rename f)) h := hfun
    _ = Multiset.map (Expr.rename g) (Multiset.map (Expr.rename f) h) := by
          exact (Multiset.map_map (Expr.rename g) (Expr.rename f) h).symm
    _ = rename g (rename f h) := rfl

/-- Hypergraph isomorphism (vertex relabeling). -/
def Iso {V : Type u} (g₁ g₂ : HGraph V) : Prop :=
  ∃ e : Equiv.Perm V, rename e g₁ = g₂

@[refl] lemma Iso.refl {V : Type u} (g : HGraph V) : Iso g g := by
  refine ⟨Equiv.refl V, ?_⟩
  simp [rename]

@[symm] lemma Iso.symm {V : Type u} {g₁ g₂ : HGraph V} : Iso g₁ g₂ → Iso g₂ g₁ := by
  intro h
  rcases h with ⟨e, he⟩
  refine ⟨e.symm, ?_⟩
  -- Apply `rename` with `e.symm` to the equality `rename e g₁ = g₂`.
  have := congrArg (rename e.symm) he
  -- Normalize `rename (e.symm) (rename e g₁)` to `g₁`.
  simpa [rename_comp, rename_id] using this.symm

@[trans] lemma Iso.trans {V : Type u} {g₁ g₂ g₃ : HGraph V} : Iso g₁ g₂ → Iso g₂ g₃ → Iso g₁ g₃ := by
  intro h12 h23
  rcases h12 with ⟨e12, he12⟩
  rcases h23 with ⟨e23, he23⟩
  -- `Equiv.trans e12 e23` is composition `e23 ∘ e12`.
  refine ⟨e12.trans e23, ?_⟩
  have h1 : rename e23 (rename e12 g₁) = rename e23 g₂ := by
    simpa [he12] using congrArg (rename e23) he12
  have h2 : rename e23 g₂ = g₃ := he23
  have : rename e23 (rename e12 g₁) = g₃ := h1.trans h2
  simpa [rename_comp, Function.comp] using this

end HGraph

namespace HGraph

variable {V : Type u}

/-- Fold-step for collecting vertices from expressions. -/
def vertsStep [DecidableEq V] : Finset V → Expr V → Finset V :=
  fun acc e => acc ∪ e.toFinset

instance instRightCommutative_vertsStep [DecidableEq V] :
    RightCommutative (vertsStep (V := V)) := by
  refine ⟨?_⟩
  intro a b c
  simp [vertsStep, Finset.union_left_comm, Finset.union_comm]

/-- A `Finset` of vertices occurring in a hypergraph state (computable via a commutative fold). -/
def verts [DecidableEq V] (g : HGraph V) : Finset V :=
  Multiset.foldl (vertsStep (V := V)) ∅ g

private lemma mem_foldl_of_mem_acc [DecidableEq V] {v : V} {b : Finset V} {g : HGraph V}
    (hv : v ∈ b) : v ∈ Multiset.foldl (vertsStep (V := V)) b g := by
  classical
  induction g using Multiset.induction_on generalizing b with
  | empty =>
      simpa using hv
  | cons a g ih =>
      -- `foldl` is monotone for `∪`: membership in the accumulator is preserved.
      have hv' : v ∈ b ∪ a.toFinset := Finset.mem_union.mpr (Or.inl hv)
      simpa [vertsStep, Multiset.foldl_cons] using ih (b := b ∪ a.toFinset) (hv := hv')

private lemma foldl_mono [DecidableEq V] {b b' : Finset V} {g : HGraph V} (hb : b ⊆ b') :
    Multiset.foldl (vertsStep (V := V)) b g ⊆ Multiset.foldl (vertsStep (V := V)) b' g := by
  classical
  induction g using Multiset.induction_on generalizing b b' with
  | empty =>
      simpa using hb
  | cons a g ih =>
      -- unfold one `cons` step and use monotonicity of `∪`
      simpa [Multiset.foldl_cons, vertsStep] using
        ih (b := b ∪ a.toFinset) (b' := b' ∪ a.toFinset) (hb := by
          intro x hx
          rcases Finset.mem_union.mp hx with hx | hx
          · exact Finset.mem_union.mpr (Or.inl (hb hx))
          · exact Finset.mem_union.mpr (Or.inr hx))

lemma mem_verts_of_mem {v : V} [DecidableEq V] {e : Expr V} {g : HGraph V}
    (he : e ∈ g) (hv : v ∈ e) : v ∈ verts (V := V) g := by
  classical
  -- Induct on the multiset of expressions.
  induction g using Multiset.induction_on generalizing e with
  | empty =>
      cases he
  | cons a g ih =>
      have hmem : e = a ∨ e ∈ g := by
        simpa [Multiset.mem_cons] using he
      cases hmem with
      | inl hEq =>
          subst hEq
          have hvA : v ∈ List.toFinset e := by
            simpa [List.mem_toFinset] using hv
          -- `verts (a ::ₘ g) = foldl step ∅ (a ::ₘ g) = foldl step a.toFinset g`
          have : v ∈ Multiset.foldl (vertsStep (V := V)) (List.toFinset e) g :=
            mem_foldl_of_mem_acc (V := V) (b := List.toFinset e) (g := g) (v := v) (hv := hvA)
          simpa [verts, Multiset.foldl_cons, vertsStep] using this
      | inr hEg =>
          have hvTail : v ∈ verts (V := V) g := ih (e := e) hEg hv
          -- Monotonicity in the initial accumulator: `∅ ⊆ a.toFinset`.
          have hsub :
              Multiset.foldl (vertsStep (V := V)) ∅ g ⊆
                Multiset.foldl (vertsStep (V := V)) (List.toFinset a) g :=
            foldl_mono (V := V) (g := g) (b := ∅) (b' := List.toFinset a) (hb := by
              intro x hx
              exact False.elim ((Finset.notMem_empty x) hx))
          have : v ∈ Multiset.foldl (vertsStep (V := V)) (List.toFinset a) g := hsub hvTail
          simpa [verts, Multiset.foldl_cons, vertsStep] using this

end HGraph

end Wolfram
end WPP
end HeytingLean
