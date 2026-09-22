import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"r": "v0"}
def original : Prop :=
  ∀ (v0 : ℝ), (((((5 : ℝ) * v0) - ((6 : ℝ) * (v0 ^ 3))) + (v0 ^ 8)) = ((v0 * ((1 : ℝ) - v0)) * (((5 : ℝ) + ((5 : ℝ) * v0)) - (((((v0 ^ 2) + (v0 ^ 3)) + (v0 ^ 4)) + (v0 ^ 5)) + (v0 ^ 6)))))

theorem claim : original := by
  unfold original
  intro v0
  have square_0 : 0 ≤ v0 ^ 2 := sq_nonneg v0
  first | (solve | norm_num at *) | positivity | (solve | (subst_vars; ring)) | nlinarith

#check claim
#print axioms claim
end TheoryDebugger.Generated
