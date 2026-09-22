import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"d": "v0", "depreciation": "v4", "m": "v1", "n": "v3", "rho": "v2"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), ∀ (v4 : ℝ), (v0 > (0 : ℝ)) → (v3 > (0 : ℝ)) → (v4 > (0 : ℝ)) → (v0 = (v2 - v3)) → (v1 = (v3 + v4)) → ((v0 + v1) = (v2 + v4))

theorem claim : original := by
  unfold original
  intro v0 v1 v2 v3 v4 h0 h1 h2 h3 h4
  have square_0 : 0 ≤ v0 ^ 2 := sq_nonneg v0
  have square_1 : 0 ≤ v1 ^ 2 := sq_nonneg v1
  have square_2 : 0 ≤ v2 ^ 2 := sq_nonneg v2
  have square_3 : 0 ≤ v3 ^ 2 := sq_nonneg v3
  have square_4 : 0 ≤ v4 ^ 2 := sq_nonneg v4
  have positive_square_0 : 0 < v0 ^ 2 := by positivity
  have positive_square_1 : 0 < v3 ^ 2 := by positivity
  have positive_square_2 : 0 < v4 ^ 2 := by positivity
  have equality_product_3_0 := congrArg (fun x : ℝ => x * v0) h3
  have equality_product_3_1 := congrArg (fun x : ℝ => x * v1) h3
  have equality_product_3_2 := congrArg (fun x : ℝ => x * v2) h3
  have equality_product_3_3 := congrArg (fun x : ℝ => x * v3) h3
  have equality_product_3_4 := congrArg (fun x : ℝ => x * v4) h3
  have equality_product_4_0 := congrArg (fun x : ℝ => x * v0) h4
  have equality_product_4_1 := congrArg (fun x : ℝ => x * v1) h4
  have equality_product_4_2 := congrArg (fun x : ℝ => x * v2) h4
  have equality_product_4_3 := congrArg (fun x : ℝ => x * v3) h4
  have equality_product_4_4 := congrArg (fun x : ℝ => x * v4) h4
  first | (solve | norm_num at *) | positivity | (solve | (subst_vars; ring)) | nlinarith

#check claim
#print axioms claim
end TheoryDebugger.Generated
