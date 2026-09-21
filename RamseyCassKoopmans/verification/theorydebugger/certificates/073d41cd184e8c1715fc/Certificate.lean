import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"F": "v1", "K": "v3", "V": "v0", "Z": "v2", "fprime": "v4", "m": "v7", "q": "v6", "u": "v5"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), ∀ (v4 : ℝ), ∀ (v5 : ℝ), ∀ (v6 : ℝ), ∀ (v7 : ℝ), (v0 = ((((v0 - (v5 * (v1 - v2))) + (v5 * (v1 - (v4 * v3)))) + ((v6 - v5) * v2)) - ((((v7 * v6) - (v5 * v4)) * v3) + (v6 * (v2 - (v7 * v3))))))

theorem feasible : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), ∃ (_v5 : ℝ), ∃ (_v6 : ℝ), ∃ (_v7 : ℝ), True := by
  refine ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), ?_⟩
  norm_num

theorem satisfying : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), ∃ (_v5 : ℝ), ∃ (_v6 : ℝ), ∃ (_v7 : ℝ), (True ∧ (_v0 = ((((_v0 - (_v5 * (_v1 - _v2))) + (_v5 * (_v1 - (_v4 * _v3)))) + ((_v6 - _v5) * _v2)) - ((((_v7 * _v6) - (_v5 * _v4)) * _v3) + (_v6 * (_v2 - (_v7 * _v3))))))) := by
  refine ⟨(1 : ℝ), (2 : ℝ), (0 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), ?_⟩
  norm_num

#check feasible
#print axioms feasible
#check satisfying
#print axioms satisfying
end TheoryDebugger.Generated
