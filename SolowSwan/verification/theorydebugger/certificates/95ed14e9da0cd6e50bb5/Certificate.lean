import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"k": "v2", "m": "v1", "s": "v0", "y": "v3"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), ((v0 * v3) = (v1 * v2)) → ((((1 : ℝ) - v0) * v3) = (v3 - (v1 * v2)))

theorem claim : original := by
  unfold original
  intro v0 v1 v2 v3 h0
  have square_0 : 0 ≤ v0 ^ 2 := sq_nonneg v0
  have square_1 : 0 ≤ v1 ^ 2 := sq_nonneg v1
  have square_2 : 0 ≤ v2 ^ 2 := sq_nonneg v2
  have square_3 : 0 ≤ v3 ^ 2 := sq_nonneg v3
  have equality_product_0_0 := congrArg (fun x : ℝ => x * v0) h0
  have equality_product_0_1 := congrArg (fun x : ℝ => x * v1) h0
  have equality_product_0_2 := congrArg (fun x : ℝ => x * v2) h0
  have equality_product_0_3 := congrArg (fun x : ℝ => x * v3) h0
  first | (solve | norm_num at *) | positivity | (solve | (subst_vars; ring)) | nlinarith

#check claim
#print axioms claim
end TheoryDebugger.Generated
