import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"x": "v0"}
def original : Prop :=
  ∀ (v0 : ℝ), (v0 > ((2 : ℝ) / 3)) → ((((2 : ℝ) * v0) - ((3 : ℝ) * (v0 ^ 2))) ≥ (0 : ℝ))

theorem sample_h0 : ((1 : ℝ) > ((2 : ℝ) / 3)) := by
  norm_num

theorem feasible : ∃ (_v0 : ℝ), ((_v0 > ((2 : ℝ) / 3))) := by
  refine ⟨(1 : ℝ), ?_⟩
  norm_num

theorem refuting : ∃ (_v0 : ℝ), (((_v0 > ((2 : ℝ) / 3))) ∧ ¬ ((((2 : ℝ) * _v0) - ((3 : ℝ) * (_v0 ^ 2))) ≥ (0 : ℝ))) := by
  refine ⟨(1 : ℝ), ?_⟩
  norm_num

theorem sample_not_goal : ¬ ((((2 : ℝ) * (1 : ℝ)) - ((3 : ℝ) * ((1 : ℝ) ^ 2))) ≥ (0 : ℝ)) := by
  norm_num

theorem refutation : ¬ original := by
  intro h
  unfold original at h
  exact sample_not_goal (h (1 : ℝ) sample_h0)

#check sample_h0
#print axioms sample_h0
#check feasible
#print axioms feasible
#check refuting
#print axioms refuting
#check sample_not_goal
#print axioms sample_not_goal
#check refutation
#print axioms refutation
end TheoryDebugger.Generated
