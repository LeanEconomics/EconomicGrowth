import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"c": "v0", "r": "v1"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), (v0 > (0 : ℝ)) → (v1 > (0 : ℝ)) → ((v0 * v1) = (1 : ℝ)) → (((v0 - v1) - (((1 : ℝ) + (v1 * v1)) * v0)) = ((-2 : ℝ) * v1))

theorem sample_h0 : ((3 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem sample_h1 : (((1 : ℝ) / 3) > (0 : ℝ)) := by
  norm_num

theorem sample_h2 : (((3 : ℝ) * ((1 : ℝ) / 3)) = (1 : ℝ)) := by
  norm_num

theorem feasible : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ((_v0 > (0 : ℝ)) ∧ (_v1 > (0 : ℝ)) ∧ ((_v0 * _v1) = (1 : ℝ))) := by
  refine ⟨(3 : ℝ), ((1 : ℝ) / 3), ?_⟩
  norm_num

theorem satisfying : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), (((_v0 > (0 : ℝ)) ∧ (_v1 > (0 : ℝ)) ∧ ((_v0 * _v1) = (1 : ℝ))) ∧ (((_v0 - _v1) - (((1 : ℝ) + (_v1 * _v1)) * _v0)) = ((-2 : ℝ) * _v1))) := by
  refine ⟨(3 : ℝ), ((1 : ℝ) / 3), ?_⟩
  norm_num

#check sample_h0
#print axioms sample_h0
#check sample_h1
#print axioms sample_h1
#check sample_h2
#print axioms sample_h2
#check feasible
#print axioms feasible
#check satisfying
#print axioms satisfying
end TheoryDebugger.Generated
