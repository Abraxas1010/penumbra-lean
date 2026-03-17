import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Penumbra.MonotoneCouplingObstruction

Phase 4 tests whether the rotational energy functional
`E(n) = k / (f n * δ n)` can be rescued by a monotone increasing modulation
`f`. The key identity is exact: the `2/3` energy ratio is controlled by the
growth factor `f 3 / f 2`. If the required growth factor is below `1`, then no
monotone increasing modulation can realise it.
-/

namespace Penumbra

noncomputable section

def modulatedEnergy (k : ℝ) (f δ : ℕ → ℝ) (n : ℕ) : ℝ :=
  k / (f n * δ n)

theorem modulated_energy_ratio_two_three
    {k : ℝ} {f δ : ℕ → ℝ}
    (hk : k ≠ 0)
    (hf2 : f 2 ≠ 0) (hf3 : f 3 ≠ 0)
    (hδ2 : δ 2 ≠ 0) (hδ3 : δ 3 ≠ 0) :
    modulatedEnergy k f δ 2 / modulatedEnergy k f δ 3 =
      (f 3 * δ 3) / (f 2 * δ 2) := by
  unfold modulatedEnergy
  field_simp [hk, hf2, hf3, hδ2, hδ3]

theorem required_growth_factor
    {k target : ℝ} {f δ : ℕ → ℝ}
    (hk : k ≠ 0)
    (hf2 : f 2 ≠ 0) (hf3 : f 3 ≠ 0)
    (hδ2 : δ 2 ≠ 0) (hδ3 : δ 3 ≠ 0)
    (hratio : modulatedEnergy k f δ 2 / modulatedEnergy k f δ 3 = target) :
    f 3 / f 2 = target * (δ 2 / δ 3) := by
  have hratio' := modulated_energy_ratio_two_three hk hf2 hf3 hδ2 hδ3
  rw [hratio] at hratio'
  have hδ3' : δ 3 ≠ 0 := hδ3
  have hf2' : f 2 ≠ 0 := hf2
  field_simp [hf2', hδ3'] at hratio' ⊢
  ring_nf at hratio' ⊢
  linarith

theorem monotone_growth_ratio_ge_one
    {f : ℕ → ℝ}
    (hmono : Monotone f)
    (hf2 : 0 < f 2) :
    1 ≤ f 3 / f 2 := by
  have h23 : f 2 ≤ f 3 := hmono (by decide : 2 ≤ 3)
  have hf2' : 0 ≤ f 2 := le_of_lt hf2
  have hdiv : f 2 / f 2 ≤ f 3 / f 2 := by
    exact (div_le_div_of_nonneg_right h23 hf2')
  simpa [hf2.ne'] using hdiv

theorem monotone_coupling_obstruction
    {k target : ℝ} {f δ : ℕ → ℝ}
    (hk : k ≠ 0)
    (hmono : Monotone f)
    (hf2 : 0 < f 2) (hf3 : 0 < f 3)
    (hδ2 : 0 < δ 2) (hδ3 : 0 < δ 3)
    (hratio : modulatedEnergy k f δ 2 / modulatedEnergy k f δ 3 = target)
    (htarget : target * (δ 2 / δ 3) < 1) :
    False := by
  have hreq := required_growth_factor hk hf2.ne' hf3.ne' hδ2.ne' hδ3.ne' hratio
  have hge : 1 ≤ f 3 / f 2 := monotone_growth_ratio_ge_one hmono hf2
  rw [hreq] at hge
  linarith

end

end Penumbra
