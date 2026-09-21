import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"r": "v0"}
def original : Prop :=
  ∀ (v0 : ℝ), (((((5 : ℝ) * v0) - ((6 : ℝ) * (v0 ^ 3))) + (v0 ^ 8)) = ((v0 * ((1 : ℝ) - v0)) * (((5 : ℝ) + ((5 : ℝ) * v0)) - (((((v0 ^ 2) + (v0 ^ 3)) + (v0 ^ 4)) + (v0 ^ 5)) + (v0 ^ 6)))))

theorem feasible : ∃ (_v0 : ℝ), True := by
  refine ⟨(1 : ℝ), ?_⟩
  norm_num

theorem satisfying : ∃ (_v0 : ℝ), (True ∧ (((((5 : ℝ) * _v0) - ((6 : ℝ) * (_v0 ^ 3))) + (_v0 ^ 8)) = ((_v0 * ((1 : ℝ) - _v0)) * (((5 : ℝ) + ((5 : ℝ) * _v0)) - (((((_v0 ^ 2) + (_v0 ^ 3)) + (_v0 ^ 4)) + (_v0 ^ 5)) + (_v0 ^ 6)))))) := by
  refine ⟨(1 : ℝ), ?_⟩
  norm_num

#check feasible
#print axioms feasible
#check satisfying
#print axioms satisfying
end TheoryDebugger.Generated
