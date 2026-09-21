import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"r": "v0"}
def original : Prop :=
  ∀ (v0 : ℝ), (v0 > (0 : ℝ)) → (v0 ≤ (1 : ℝ)) → (((-1 : ℝ) / 2) = (((3 : ℝ) * (v0 ^ 2)) - (4 : ℝ)))

theorem sample_h0 : ((1 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem sample_h1 : ((1 : ℝ) ≤ (1 : ℝ)) := by
  norm_num

theorem feasible : ∃ (_v0 : ℝ), ((_v0 > (0 : ℝ)) ∧ (_v0 ≤ (1 : ℝ))) := by
  refine ⟨(1 : ℝ), ?_⟩
  norm_num

theorem refuting : ∃ (_v0 : ℝ), (((_v0 > (0 : ℝ)) ∧ (_v0 ≤ (1 : ℝ))) ∧ ¬ (((-1 : ℝ) / 2) = (((3 : ℝ) * (_v0 ^ 2)) - (4 : ℝ)))) := by
  refine ⟨(1 : ℝ), ?_⟩
  norm_num

theorem sample_not_goal : ¬ (((-1 : ℝ) / 2) = (((3 : ℝ) * ((1 : ℝ) ^ 2)) - (4 : ℝ))) := by
  norm_num

theorem refutation : ¬ original := by
  intro h
  unfold original at h
  exact sample_not_goal (h (1 : ℝ) sample_h0 sample_h1)

#check sample_h0
#print axioms sample_h0
#check sample_h1
#print axioms sample_h1
#check feasible
#print axioms feasible
#check refuting
#print axioms refuting
#check sample_not_goal
#print axioms sample_not_goal
#check refutation
#print axioms refutation
end TheoryDebugger.Generated
