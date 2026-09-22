import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"otherz": "v3", "q": "v1", "u": "v0", "z": "v2"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), (v0 > (0 : ℝ)) → (v1 > (0 : ℝ)) → (v2 ≥ (0 : ℝ)) → (v1 ≤ v0) → (((v1 - v0) * v2) = (0 : ℝ)) → (v3 ≥ (0 : ℝ)) → (((v1 - v0) * (v2 - v3)) ≥ (0 : ℝ))

theorem claim : original := by
  unfold original
  intro v0 v1 v2 v3 h0 h1 h2 h3 h4 h5
  have square_0 : 0 ≤ v0 ^ 2 := sq_nonneg v0
  have square_1 : 0 ≤ v1 ^ 2 := sq_nonneg v1
  have square_2 : 0 ≤ v2 ^ 2 := sq_nonneg v2
  have square_3 : 0 ≤ v3 ^ 2 := sq_nonneg v3
  have positive_square_0 : 0 < v0 ^ 2 := by positivity
  have positive_square_1 : 0 < v1 ^ 2 := by positivity
  have equality_product_4_0 := congrArg (fun x : ℝ => x * v0) h4
  have equality_product_4_1 := congrArg (fun x : ℝ => x * v1) h4
  have equality_product_4_2 := congrArg (fun x : ℝ => x * v2) h4
  have equality_product_4_3 := congrArg (fun x : ℝ => x * v3) h4
  first | (solve | norm_num at *) | positivity | (solve | (subst_vars; ring)) | nlinarith

#check claim
#print axioms claim
end TheoryDebugger.Generated
