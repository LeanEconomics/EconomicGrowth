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

theorem sample_h0 : ((1 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem sample_h1 : ((1 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem sample_h2 : ((1 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem sample_h3 : ((1 : ℝ) = ((2 : ℝ) - (1 : ℝ))) := by
  norm_num

theorem sample_h4 : ((2 : ℝ) = ((1 : ℝ) + (1 : ℝ))) := by
  norm_num

theorem feasible : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), ((_v0 > (0 : ℝ)) ∧ (_v3 > (0 : ℝ)) ∧ (_v4 > (0 : ℝ)) ∧ (_v0 = (_v2 - _v3)) ∧ (_v1 = (_v3 + _v4))) := by
  refine ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), ?_⟩
  norm_num

theorem satisfying : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ∃ (_v4 : ℝ), (((_v0 > (0 : ℝ)) ∧ (_v3 > (0 : ℝ)) ∧ (_v4 > (0 : ℝ)) ∧ (_v0 = (_v2 - _v3)) ∧ (_v1 = (_v3 + _v4))) ∧ ((_v0 + _v1) = (_v2 + _v4))) := by
  refine ⟨(1 : ℝ), (2 : ℝ), (2 : ℝ), (1 : ℝ), (1 : ℝ), ?_⟩
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
