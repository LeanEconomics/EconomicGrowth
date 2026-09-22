import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"D": "v0", "k": "v1", "response": "v2"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), (v0 > (0 : ℝ)) → (v1 > (0 : ℝ)) → ((v0 * v2) = ((-1 : ℝ) * v1)) → (v2 > (0 : ℝ))

theorem sample_h0 : ((1 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem sample_h1 : ((2 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem sample_h2 : (((1 : ℝ) * (-2 : ℝ)) = ((-1 : ℝ) * (2 : ℝ))) := by
  norm_num

theorem feasible : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ((_v0 > (0 : ℝ)) ∧ (_v1 > (0 : ℝ)) ∧ ((_v0 * _v2) = ((-1 : ℝ) * _v1))) := by
  refine ⟨(1 : ℝ), (2 : ℝ), (-2 : ℝ), ?_⟩
  norm_num

theorem refuting : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), (((_v0 > (0 : ℝ)) ∧ (_v1 > (0 : ℝ)) ∧ ((_v0 * _v2) = ((-1 : ℝ) * _v1))) ∧ ¬ (_v2 > (0 : ℝ))) := by
  refine ⟨(1 : ℝ), (2 : ℝ), (-2 : ℝ), ?_⟩
  norm_num

theorem sample_not_goal : ¬ ((-2 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem refutation : ¬ original := by
  intro h
  unfold original at h
  exact sample_not_goal (h (1 : ℝ) (2 : ℝ) (-2 : ℝ) sample_h0 sample_h1 sample_h2)

#check sample_h0
#print axioms sample_h0
#check sample_h1
#print axioms sample_h1
#check sample_h2
#print axioms sample_h2
#check feasible
#print axioms feasible
#check refuting
#print axioms refuting
#check sample_not_goal
#print axioms sample_not_goal
#check refutation
#print axioms refutation
end TheoryDebugger.Generated
