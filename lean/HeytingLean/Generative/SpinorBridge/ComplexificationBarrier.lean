import HeytingLean.Generative.SpinorBridge.DimensionalityFromSU2
import HeytingLean.Generative.FourDBarrier

namespace HeytingLean.Generative.SpinorBridge

open HeytingLean.Generative

/-- Real SU(2) directions versus their imaginary companions after complexification. -/
inductive GeneratorFlavor
  | real
  | imaginary
  deriving DecidableEq, Fintype, Repr

/-- A real SL(2,ℂ) generator is a Pauli direction plus a real/imaginary tag. -/
abbrev SL2CGenerator := SU2Generator × GeneratorFlavor

theorem generatorFlavor_count :
    Fintype.card GeneratorFlavor = 2 := by
  decide

/-- The algebraic image of a complexified generator. -/
def complexifiedGeneratorMatrix : SL2CGenerator → Mat2
  | (g, .real) => generatorMatrix g
  | (g, .imaginary) => (Complex.I : ℂ) • generatorMatrix g

theorem sl2c_generator_count :
    Fintype.card SL2CGenerator = 6 := by
  simp [generator_count_via_equiv, generatorFlavor_count]

theorem complexification_doubles_generators :
    Fintype.card SL2CGenerator = 2 * Fintype.card SU2Generator := by
  simp [generator_count_via_equiv, generatorFlavor_count]

/-- Classify the SU(2) to SL(2,ℂ) extension by its generator count and barrier status. -/
structure GroupExtension where
  dimCurrent : ℕ
  dimExtended : ℕ
  nNewGenerators : ℕ
  dim_eq : dimExtended = dimCurrent + nNewGenerators
  status : EmergenceStatus

def su2_to_sl2c : GroupExtension where
  dimCurrent := Fintype.card SU2Generator
  dimExtended := Fintype.card SL2CGenerator
  nNewGenerators := Fintype.card SU2Generator
  dim_eq := by
    simp [generator_count_via_equiv, generatorFlavor_count]
  status := emergenceStatus 2

theorem complexification_is_barrier :
    su2_to_sl2c.status = .barrier ∧ emergenceStatus 2 = .barrier := by
  exact ⟨by simp [su2_to_sl2c, level2_barrier], level2_barrier⟩

theorem time_is_complexification_not_dimension :
    Fintype.card SU2Generator = 3 ∧
      Fintype.card SL2CGenerator = 2 * Fintype.card SU2Generator := by
  exact ⟨generator_count_via_equiv, complexification_doubles_generators⟩

theorem barrier_is_complexification_choice :
    residualFreedom level2 = 0 ∧
      emergenceStatus 2 = .barrier ∧
      su2_to_sl2c.status = .barrier ∧
      su2_to_sl2c.dimExtended = 2 * su2_to_sl2c.dimCurrent := by
  refine ⟨residual_freedom_zero level2, level2_barrier, ?_, ?_⟩
  · simp [su2_to_sl2c, level2_barrier]
  · simpa [su2_to_sl2c] using complexification_doubles_generators

end HeytingLean.Generative.SpinorBridge
