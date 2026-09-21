import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"x": "v0"}
def original : Prop :=
  ∀ (v0 : ℝ), ((((3 : ℝ) * (v0 ^ 2)) + (((2 : ℝ) * v0) - ((3 : ℝ) * (v0 ^ 2)))) = ((2 : ℝ) * v0))

theorem feasible : ∃ (_v0 : ℝ), True := by
  refine ⟨((1 : ℝ) / 2), ?_⟩
  norm_num

theorem satisfying : ∃ (_v0 : ℝ), (True ∧ ((((3 : ℝ) * (_v0 ^ 2)) + (((2 : ℝ) * _v0) - ((3 : ℝ) * (_v0 ^ 2)))) = ((2 : ℝ) * _v0))) := by
  refine ⟨((1 : ℝ) / 2), ?_⟩
  norm_num

#check feasible
#print axioms feasible
#check satisfying
#print axioms satisfying
end TheoryDebugger.Generated
