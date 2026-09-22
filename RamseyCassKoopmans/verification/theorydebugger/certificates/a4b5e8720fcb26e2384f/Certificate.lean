import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"B": "v1", "r": "v0"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), (v0 ≥ (0 : ℝ)) → (v0 ≤ (1 : ℝ)) → (v1 ≥ (0 : ℝ)) → (((v0 * ((1 : ℝ) - v0)) * v1) ≥ (0 : ℝ))

theorem claim : original := by
  unfold original
  intro v0 v1 h0 h1 h2
  have square_0 : 0 ≤ v0 ^ 2 := sq_nonneg v0
  have square_1 : 0 ≤ v1 ^ 2 := sq_nonneg v1
  first | (solve | norm_num at *) | positivity | (solve | (subst_vars; ring)) | nlinarith

#check claim
#print axioms claim
end TheoryDebugger.Generated
