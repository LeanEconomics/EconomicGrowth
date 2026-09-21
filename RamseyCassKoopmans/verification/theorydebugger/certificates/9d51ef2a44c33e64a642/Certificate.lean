import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"r": "v0", "s": "v1"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), (((((1 : ℝ) / 10) * v1) * ((((9 : ℝ) / 2) * (v0 ^ 3)) - ((2 : ℝ) * (v0 ^ 8)))) = (((2 : ℝ) * ((((1 : ℝ) / 10) * v1) * (((6 : ℝ) * (v0 ^ 3)) - (v0 ^ 8)))) - ((((((1 : ℝ) / 2) * v1) * v0) * ((3 : ℝ) / 2)) * (v0 ^ 2))))

theorem claim : original := by
  unfold original
  intro v0 v1
  have square_0 : 0 ≤ v0 ^ 2 := sq_nonneg v0
  have square_1 : 0 ≤ v1 ^ 2 := sq_nonneg v1
  first | (solve | norm_num at *) | positivity | (solve | (subst_vars; ring)) | nlinarith

#check claim
#print axioms claim
end TheoryDebugger.Generated
