import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"d": "v1", "fprime": "v5", "m": "v2", "q": "v3", "qdot": "v0", "u": "v4"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), ∀ (v4 : ℝ), ∀ (v5 : ℝ), (v0 = (((v1 + v2) * v3) - (v4 * v5))) → ((v0 - (v1 * v3)) = ((v2 * v3) - (v4 * v5)))

theorem sample_h0 : ((0 : ℝ) = ((((1 : ℝ) + (1 : ℝ)) * (1 : ℝ)) - ((1 : ℝ) * (2 : ℝ)))) := by
  norm_num

theorem feasible : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), ∃ (_v5 : ℝ), ((_v0 = (((_v1 + _v2) * _v3) - (_v4 * _v5)))) := by
  refine ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), ?_⟩
  norm_num

theorem satisfying : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), ∃ (_v5 : ℝ), (((_v0 = (((_v1 + _v2) * _v3) - (_v4 * _v5)))) ∧ ((_v0 - (_v1 * _v3)) = ((_v2 * _v3) - (_v4 * _v5)))) := by
  refine ⟨(0 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), (1 : ℝ), (2 : ℝ), ?_⟩
  norm_num

#check sample_h0
#print axioms sample_h0
#check feasible
#print axioms feasible
#check satisfying
#print axioms satisfying
end TheoryDebugger.Generated
