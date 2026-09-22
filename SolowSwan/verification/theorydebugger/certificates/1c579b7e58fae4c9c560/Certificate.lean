import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"k": "v2", "m": "v1", "mp": "v4", "s": "v0", "y": "v3"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), ∀ (v4 : ℝ), (v0 > (0 : ℝ)) → (v2 > (0 : ℝ)) → ((v0 * v3) = (v1 * v2)) → ((v4 * v2) ≤ v3) → ((v0 * v4) < v1)

theorem sample_h0 : (((1 : ℝ) / 2) > (0 : ℝ)) := by
  norm_num

theorem sample_h1 : ((1 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem sample_h2 : ((((1 : ℝ) / 2) * (2 : ℝ)) = ((1 : ℝ) * (1 : ℝ))) := by
  norm_num

theorem sample_h3 : (((2 : ℝ) * (1 : ℝ)) ≤ (2 : ℝ)) := by
  norm_num

theorem feasible : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), ((_v0 > (0 : ℝ)) ∧ (_v2 > (0 : ℝ)) ∧ ((_v0 * _v3) = (_v1 * _v2)) ∧ ((_v4 * _v2) ≤ _v3)) := by
  refine ⟨((1 : ℝ) / 2), (1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), ?_⟩
  norm_num

theorem refuting : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), (((_v0 > (0 : ℝ)) ∧ (_v2 > (0 : ℝ)) ∧ ((_v0 * _v3) = (_v1 * _v2)) ∧ ((_v4 * _v2) ≤ _v3)) ∧ ¬ ((_v0 * _v4) < _v1)) := by
  refine ⟨((1 : ℝ) / 2), (1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), ?_⟩
  norm_num

theorem sample_not_goal : ¬ ((((1 : ℝ) / 2) * (2 : ℝ)) < (1 : ℝ)) := by
  norm_num

theorem refutation : ¬ original := by
  intro h
  unfold original at h
  exact sample_not_goal (h ((1 : ℝ) / 2) (1 : ℝ) (1 : ℝ) (2 : ℝ) (2 : ℝ) sample_h0 sample_h1 sample_h2 sample_h3)

#check sample_h0
#print axioms sample_h0
#check sample_h1
#print axioms sample_h1
#check sample_h2
#print axioms sample_h2
#check sample_h3
#print axioms sample_h3
#check feasible
#print axioms feasible
#check refuting
#print axioms refuting
#check sample_not_goal
#print axioms sample_not_goal
#check refutation
#print axioms refutation
end TheoryDebugger.Generated
