import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 400000
namespace TheoryDebugger.Generated

-- Variable dictionary: {"A": "v0", "k0": "v2", "k1": "v3", "p": "v1"}
def original : Prop :=
  ∀ (v0 : ℝ), ∀ (v1 : ℝ), ∀ (v2 : ℝ), ∀ (v3 : ℝ), (v1 > (0 : ℝ)) → (v0 ≤ (((-1 : ℝ) * v1) * (v3 - v2))) → (v0 ≤ (v1 * (v3 - v2)))

theorem sample_h0 : ((1 : ℝ) > (0 : ℝ)) := by
  norm_num

theorem sample_h1 : ((0 : ℝ) ≤ (((-1 : ℝ) * (1 : ℝ)) * ((0 : ℝ) - (0 : ℝ)))) := by
  norm_num

theorem feasible : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), ((_v1 > (0 : ℝ)) ∧ (_v0 ≤ (((-1 : ℝ) * _v1) * (_v3 - _v2)))) := by
  refine ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), ?_⟩
  norm_num

theorem satisfying : ∃ (_v0 : ℝ), ∃ (_v1 : ℝ), ∃ (_v2 : ℝ), ∃ (_v3 : ℝ), (((_v1 > (0 : ℝ)) ∧ (_v0 ≤ (((-1 : ℝ) * _v1) * (_v3 - _v2)))) ∧ (_v0 ≤ (_v1 * (_v3 - _v2)))) := by
  refine ⟨(0 : ℝ), (1 : ℝ), (0 : ℝ), (0 : ℝ), ?_⟩
  norm_num

#check sample_h0
#print axioms sample_h0
#check sample_h1
#print axioms sample_h1
#check feasible
#print axioms feasible
#check satisfying
#print axioms satisfying
end TheoryDebugger.Generated
