import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"k": "v2", "m": "v1", "sg": "v0", "y": "v3"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), (v1 > (0 : ℝ)) → (v2 > (0 : ℝ)) → (v3 > (0 : ℝ)) → ((v1 * v2) < v3) → ((v0 * v3) = (v1 * v2)) → (v0 < (1 : ℝ))

theorem sample_h0 : ((1 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem sample_h1 : ((1 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem sample_h2 : ((2 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem sample_h3 : (((1 : ℝ) * (1 : ℝ)) < (2 : ℝ)) := by
  norm_num

theorem sample_h4 : ((((1 : ℝ) / 2) * (2 : ℝ)) = ((1 : ℝ) * (1 : ℝ))) := by
  norm_num

theorem feasible : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ((_v1 > (0 : ℝ)) ∧ (_v2 > (0 : ℝ)) ∧ (_v3 > (0 : ℝ)) ∧ ((_v1 * _v2) < _v3) ∧ ((_v0 * _v3) = (_v1 * _v2))) := by
  refine ⟨((1 : ℝ) / 2), (1 : ℝ), (1 : ℝ), (2 : ℝ), ?_⟩
  norm_num

theorem satisfying : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), (((_v1 > (0 : ℝ)) ∧ (_v2 > (0 : ℝ)) ∧ (_v3 > (0 : ℝ)) ∧ ((_v1 * _v2) < _v3) ∧ ((_v0 * _v3) = (_v1 * _v2))) ∧ (_v0 < (1 : ℝ))) := by
  refine ⟨((1 : ℝ) / 2), (1 : ℝ), (1 : ℝ), (2 : ℝ), ?_⟩
  norm_num

#check sample_h0
#print axioms sample_h0
#check sample_h1
#print axioms sample_h1
#check sample_h2
#print axioms sample_h2
#check sample_h3
#print axioms sample_h3
#check sample_h4
#print axioms sample_h4
#check feasible
#print axioms feasible
#check satisfying
#print axioms satisfying
end TheoryDebugger.Generated
