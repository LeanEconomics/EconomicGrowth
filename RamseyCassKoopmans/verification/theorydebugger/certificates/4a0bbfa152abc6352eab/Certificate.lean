import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"r": "v0", "s": "v1"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), (((((1 : ℝ) / 10) * v1) * ((((9 : ℝ) / 2) * (v0 ^ 3)) - ((2 : ℝ) * (v0 ^ 8)))) = (((2 : ℝ) * ((((1 : ℝ) / 10) * v1) * (((6 : ℝ) * (v0 ^ 3)) - (v0 ^ 8)))) - ((((((1 : ℝ) / 2) * v1) * v0) * ((3 : ℝ) / 2)) * (v0 ^ 2))))

theorem feasible : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), True := by
  refine ⟨(1 : ℝ), (1 : ℝ), ?_⟩
  norm_num

theorem satisfying : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), (True ∧ (((((1 : ℝ) / 10) * _v1) * ((((9 : ℝ) / 2) * (_v0 ^ 3)) - ((2 : ℝ) * (_v0 ^ 8)))) = (((2 : ℝ) * ((((1 : ℝ) / 10) * _v1) * (((6 : ℝ) * (_v0 ^ 3)) - (_v0 ^ 8)))) - ((((((1 : ℝ) / 2) * _v1) * _v0) * ((3 : ℝ) / 2)) * (_v0 ^ 2))))) := by
  refine ⟨(1 : ℝ), (1 : ℝ), ?_⟩
  norm_num

#check feasible
#print axioms feasible
#check satisfying
#print axioms satisfying
end TheoryDebugger.Generated
