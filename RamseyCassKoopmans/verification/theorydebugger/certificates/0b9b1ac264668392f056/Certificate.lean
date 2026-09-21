import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"c": "v4", "cd": "v1", "d": "v6", "g": "v3", "gp": "v5", "q": "v0", "qdot": "v2"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), ∀ (v4 : ℝ), ∀ (v5 : ℝ), ∀ (v6 : ℝ), (v2 = ((v6 - v5) * v0)) → ((((v0 * v1) + (v2 * (v3 - v4))) + (v0 * ((v5 * (v3 - v4)) - v1))) = ((v6 * v0) * (v3 - v4)))

theorem claim : original := by
  unfold original
  intro v0 v1 v2 v3 v4 v5 v6 h0
  have square_0 : 0 ≤ v0 ^ 2 := sq_nonneg v0
  have square_1 : 0 ≤ v1 ^ 2 := sq_nonneg v1
  have square_2 : 0 ≤ v2 ^ 2 := sq_nonneg v2
  have square_3 : 0 ≤ v3 ^ 2 := sq_nonneg v3
  have square_4 : 0 ≤ v4 ^ 2 := sq_nonneg v4
  have square_5 : 0 ≤ v5 ^ 2 := sq_nonneg v5
  have square_6 : 0 ≤ v6 ^ 2 := sq_nonneg v6
  have equality_product_0_0 := congrArg (fun x : ℝ => x * v0) h0
  have equality_product_0_1 := congrArg (fun x : ℝ => x * v1) h0
  have equality_product_0_2 := congrArg (fun x : ℝ => x * v2) h0
  have equality_product_0_3 := congrArg (fun x : ℝ => x * v3) h0
  have equality_product_0_4 := congrArg (fun x : ℝ => x * v4) h0
  have equality_product_0_5 := congrArg (fun x : ℝ => x * v5) h0
  have equality_product_0_6 := congrArg (fun x : ℝ => x * v6) h0
  first | (solve | norm_num at *) | positivity | (solve | (subst_vars; ring)) | nlinarith

#check claim
#print axioms claim
end TheoryDebugger.Generated
