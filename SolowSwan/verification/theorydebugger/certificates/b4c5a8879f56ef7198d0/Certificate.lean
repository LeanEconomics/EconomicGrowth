import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"k": "v2", "m": "v1", "mp": "v4", "s": "v0", "y": "v3"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), ∀ (v4 : ℝ), (v0 > (0 : ℝ)) → (v2 > (0 : ℝ)) → ((v0 * v3) = (v1 * v2)) → ((v4 * v2) < v3) → ((v0 * v4) < v1)

theorem claim : original := by
  unfold original
  intro v0 v1 v2 v3 v4 h0 h1 h2 h3
  have square_0 : 0 ≤ v0 ^ 2 := sq_nonneg v0
  have square_1 : 0 ≤ v1 ^ 2 := sq_nonneg v1
  have square_2 : 0 ≤ v2 ^ 2 := sq_nonneg v2
  have square_3 : 0 ≤ v3 ^ 2 := sq_nonneg v3
  have square_4 : 0 ≤ v4 ^ 2 := sq_nonneg v4
  have positive_square_0 : 0 < v0 ^ 2 := by positivity
  have positive_square_1 : 0 < v2 ^ 2 := by positivity
  have equality_product_2_0 := congrArg (fun x : ℝ => x * v0) h2
  have equality_product_2_1 := congrArg (fun x : ℝ => x * v1) h2
  have equality_product_2_2 := congrArg (fun x : ℝ => x * v2) h2
  have equality_product_2_3 := congrArg (fun x : ℝ => x * v3) h2
  have equality_product_2_4 := congrArg (fun x : ℝ => x * v4) h2
  first | (solve | norm_num at *) | positivity | (solve | (subst_vars; ring)) | nlinarith

#check claim
#print axioms claim
end TheoryDebugger.Generated
