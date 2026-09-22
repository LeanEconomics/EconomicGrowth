import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"d": "v0", "m": "v1", "mp": "v2"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), (v0 ≥ (0 : ℝ)) → (v1 > (0 : ℝ)) → (v2 = (v0 + v1)) → (v2 > v1)

theorem sample_h0 : ((1 : ℝ) ≥ (0 : ℝ)) := by
  norm_num

theorem sample_h1 : ((1 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem sample_h2 : ((2 : ℝ) = ((1 : ℝ) + (1 : ℝ))) := by
  norm_num

theorem feasible : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ((_v0 ≥ (0 : ℝ)) ∧ (_v1 > (0 : ℝ)) ∧ (_v2 = (_v0 + _v1))) := by
  refine ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), ?_⟩
  norm_num

theorem satisfying : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), (((_v0 ≥ (0 : ℝ)) ∧ (_v1 > (0 : ℝ)) ∧ (_v2 = (_v0 + _v1))) ∧ (_v2 > _v1)) := by
  refine ⟨(1 : ℝ), (1 : ℝ), (2 : ℝ), ?_⟩
  norm_num

#check sample_h0
#print axioms sample_h0
#check sample_h1
#print axioms sample_h1
#check sample_h2
#print axioms sample_h2
#check feasible
#print axioms feasible
#check satisfying
#print axioms satisfying
end TheoryDebugger.Generated
