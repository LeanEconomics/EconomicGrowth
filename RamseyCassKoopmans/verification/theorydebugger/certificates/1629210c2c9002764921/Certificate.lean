import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"U": "v2", "c": "v5", "d": "v1", "g": "v4", "q": "v3", "w": "v0"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), ∀ (v4 : ℝ), ∀ (v5 : ℝ), ((((((-1 : ℝ) * v1) * v0) * (v2 + (v3 * (v4 - v5)))) + (((v0 * v1) * v3) * (v4 - v5))) = ((((-1 : ℝ) * v1) * v0) * v2))

theorem feasible : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), ∃ (_v5 : ℝ), True := by
  refine ⟨(1 : ℝ), (1 : ℝ), ((8 : ℝ) / 3), ((10 : ℝ) / 9), (3 : ℝ), (3 : ℝ), ?_⟩
  norm_num

theorem satisfying : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), ∃ (_v5 : ℝ), (True ∧ ((((((-1 : ℝ) * _v1) * _v0) * (_v2 + (_v3 * (_v4 - _v5)))) + (((_v0 * _v1) * _v3) * (_v4 - _v5))) = ((((-1 : ℝ) * _v1) * _v0) * _v2))) := by
  refine ⟨(1 : ℝ), (1 : ℝ), ((8 : ℝ) / 3), ((10 : ℝ) / 9), (3 : ℝ), (3 : ℝ), ?_⟩
  norm_num

#check feasible
#print axioms feasible
#check satisfying
#print axioms satisfying
end TheoryDebugger.Generated
