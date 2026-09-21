import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"x": "v0"}
def original : Prop :=
  ∀ (v0 : ℝ), (v0 = ((2 : ℝ) / 3)) → ((((2 : ℝ) * v0) * ((1 : ℝ) - ((2 : ℝ) * v0))) = ((-1 : ℝ) * (v0 ^ 2)))

theorem claim : original := by
  unfold original
  intro v0 h0
  have square_0 : 0 ≤ v0 ^ 2 := sq_nonneg v0
  have equality_product_0_0 := congrArg (fun x : ℝ => x * v0) h0
  first | (solve | norm_num at *) | positivity | (solve | (subst_vars; ring)) | nlinarith

#check claim
#print axioms claim
end TheoryDebugger.Generated
