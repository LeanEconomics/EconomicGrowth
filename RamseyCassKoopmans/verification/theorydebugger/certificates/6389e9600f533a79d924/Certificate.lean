import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"K": "v5", "Z": "v6", "fprime": "v4", "m": "v1", "p": "v0", "u": "v3", "w": "v2"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), ∀ (v4 : ℝ), ∀ (v5 : ℝ), ∀ (v6 : ℝ), (((((v1 * v0) - ((v2 * v3) * v4)) * v5) + (v0 * (v6 - (v1 * v5)))) = ((v0 * v6) - (((v2 * v3) * v4) * v5)))

theorem feasible : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), ∃ (_v5 : ℝ), ∃ (_v6 : ℝ), True := by
  refine ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), (0 : ℝ), ?_⟩
  norm_num

theorem satisfying : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), ∃ (_v5 : ℝ), ∃ (_v6 : ℝ), (True ∧ (((((_v1 * _v0) - ((_v2 * _v3) * _v4)) * _v5) + (_v0 * (_v6 - (_v1 * _v5)))) = ((_v0 * _v6) - (((_v2 * _v3) * _v4) * _v5)))) := by
  refine ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), (1 : ℝ), (0 : ℝ), ?_⟩
  norm_num

#check feasible
#print axioms feasible
#check satisfying
#print axioms satisfying
end TheoryDebugger.Generated
