import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"x": "v0"}
def original : Prop :=
  ∀ (v0 : ℝ), (v0 > (0 : ℝ)) → (v0 ≤ ((2 : ℝ) / 3)) → ((((2 : ℝ) * v0) - ((3 : ℝ) * (v0 ^ 2))) ≥ (0 : ℝ))

theorem claim : original := by
  unfold original
  intro v0 h0 h1
  have square_0 : 0 ≤ v0 ^ 2 := sq_nonneg v0
  have positive_square_0 : 0 < v0 ^ 2 := by positivity
  first | (solve | norm_num at *) | positivity | (solve | (subst_vars; ring)) | nlinarith

#check claim
#print axioms claim
end TheoryDebugger.Generated
