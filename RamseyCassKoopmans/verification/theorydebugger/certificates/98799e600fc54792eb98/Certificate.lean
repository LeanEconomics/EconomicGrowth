import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"c": "v4", "cd": "v1", "d": "v6", "g": "v3", "gp": "v5", "q": "v0", "qdot": "v2"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), ∀ (v4 : ℝ), ∀ (v5 : ℝ), ∀ (v6 : ℝ), (v2 = ((v6 - v5) * v0)) → ((((v0 * v1) + (v2 * (v3 - v4))) + (v0 * ((v5 * (v3 - v4)) - v1))) = ((v6 * v0) * (v3 - v4)))

theorem sample_h0 : ((1 : ℝ) = (((1 : ℝ) - (0 : ℝ)) * (1 : ℝ))) := by
  norm_num

theorem feasible : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), ∃ (_v5 : ℝ), ∃ (_v6 : ℝ), ((_v2 = ((_v6 - _v5) * _v0))) := by
  refine ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (3 : ℝ), (3 : ℝ), (0 : ℝ), (1 : ℝ), ?_⟩
  norm_num

theorem satisfying : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), ∃ (_v5 : ℝ), ∃ (_v6 : ℝ), (((_v2 = ((_v6 - _v5) * _v0))) ∧ ((((_v0 * _v1) + (_v2 * (_v3 - _v4))) + (_v0 * ((_v5 * (_v3 - _v4)) - _v1))) = ((_v6 * _v0) * (_v3 - _v4)))) := by
  refine ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), (3 : ℝ), (3 : ℝ), (0 : ℝ), (1 : ℝ), ?_⟩
  norm_num

#check sample_h0
#print axioms sample_h0
#check feasible
#print axioms feasible
#check satisfying
#print axioms satisfying
end TheoryDebugger.Generated
