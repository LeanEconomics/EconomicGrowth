import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"K": "v5", "Z": "v6", "fprime": "v4", "m": "v1", "p": "v0", "u": "v3", "w": "v2"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), ∀ (v4 : ℝ), ∀ (v5 : ℝ), ∀ (v6 : ℝ), (((((v1 * v0) - ((v2 * v3) * v4)) * v5) + (v0 * (v6 - (v1 * v5)))) = ((v0 * v6) - (((v2 * v3) * v4) * v5)))

theorem claim : original := by
  unfold original
  intro v0 v1 v2 v3 v4 v5 v6
  have square_0 : 0 ≤ v0 ^ 2 := sq_nonneg v0
  have square_1 : 0 ≤ v1 ^ 2 := sq_nonneg v1
  have square_2 : 0 ≤ v2 ^ 2 := sq_nonneg v2
  have square_3 : 0 ≤ v3 ^ 2 := sq_nonneg v3
  have square_4 : 0 ≤ v4 ^ 2 := sq_nonneg v4
  have square_5 : 0 ≤ v5 ^ 2 := sq_nonneg v5
  have square_6 : 0 ≤ v6 ^ 2 := sq_nonneg v6
  first | (solve | norm_num at *) | positivity | (solve | (subst_vars; ring)) | nlinarith

#check claim
#print axioms claim
end TheoryDebugger.Generated
