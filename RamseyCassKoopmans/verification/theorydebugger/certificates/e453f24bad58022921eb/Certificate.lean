import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"c": "v0", "r": "v1"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), (v0 > (0 : ℝ)) → (v1 > (0 : ℝ)) → ((v0 * v1) = (1 : ℝ)) → (((v0 - v1) - (((1 : ℝ) + (v1 * v1)) * v0)) ≥ (0 : ℝ))

theorem no_satisfying : ∀ (v0 : ℝ), ∀ (v1 : ℝ), (v0 > (0 : ℝ)) → (v1 > (0 : ℝ)) → ((v0 * v1) = (1 : ℝ)) → ¬ (((v0 - v1) - (((1 : ℝ) + (v1 * v1)) * v0)) ≥ (0 : ℝ)) := by
  intro v0 v1 h0 h1 h2
  have square_0 : 0 ≤ v0 ^ 2 := sq_nonneg v0
  have square_1 : 0 ≤ v1 ^ 2 := sq_nonneg v1
  intro h_goal
  first | (solve | norm_num at *) | positivity | (solve | (subst_vars; ring)) | nlinarith

#check no_satisfying
#print axioms no_satisfying
end TheoryDebugger.Generated
