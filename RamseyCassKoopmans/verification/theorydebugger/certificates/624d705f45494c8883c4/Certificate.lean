import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"x": "v0"}
def original : Prop :=
  ∀ (v0 : ℝ), ((((2 : ℝ) * v0) * ((1 : ℝ) - ((2 : ℝ) * v0))) = ((((2 : ℝ) * v0) - ((3 : ℝ) * (v0 ^ 2))) - (v0 ^ 2)))

theorem claim : original := by
  unfold original
  intro v0
  have square_0 : 0 ≤ v0 ^ 2 := sq_nonneg v0
  first | (solve | norm_num at *) | positivity | (solve | (subst_vars; ring)) | nlinarith

#check claim
#print axioms claim
end TheoryDebugger.Generated
