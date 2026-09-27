/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import DiscreteTime.GeneralSolow
import Solow1956.Growth.GeneralSolowExamples

/-! # Concrete discrete-time economies and boundary checks

The technology examples of `Solow1956.Growth.GeneralSolowExamples` are time-free
and are reused. The checks below concern the map itself, including why the
restrictions in `Params` cannot be dropped.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime

open Solow1956.Neoclassical

/-- Sample parameters for a concrete non-Cobb–Douglas economy satisfy `Params`. -/
theorem example_params : Params (1 / 4) (1 / 2) 1 := ⟨by norm_num, by norm_num, by norm_num,
  by norm_num⟩

/-- A sum of powers has a unique positive fixed point of the discrete map. -/
theorem mixed_power_fixed_exists :
    ∃! k : ℝ, 0 < k ∧
      next (fun k : ℝ => k ^ (1 / 2 : ℝ) + k ^ (1 / 3 : ℝ)) (1 / 4) (1 / 2) 1 k = k :=
  existsUnique_steadyState mixed_power_technology example_params

/-- Every positive path of that economy converges monotonically to its steady state. -/
theorem mixed_power_converges {k₀ : ℝ} (hk₀ : 0 < k₀) :
    Tendsto (path (fun k : ℝ => k ^ (1 / 2 : ℝ) + k ^ (1 / 3 : ℝ)) (1 / 4) (1 / 2) 1 k₀) atTop
      (𝓝 (steady mixed_power_technology (1 / 4) (1 / 2) 1)) :=
  (isPath_path hk₀).tendsto mixed_power_technology example_params

/-- Without positive effective dilution capital grows every period: there is no
positive steady state. -/
theorem no_positive_fixed_without_dilution {f : ℝ → ℝ} (h : Technology f)
    {s δ γ k : ℝ} (hs : 0 < s) (hγ : 0 < γ) (hm : γ - 1 + δ ≤ 0) (hk : 0 < k) :
    k < next f s δ γ k := by
  have := no_positive_steady_without_dilution h hs hm hk
  have hd := next_sub_self (f := f) (s := s) (δ := δ) hγ k
  have := div_pos this hγ
  linarith

/-- Depreciation above one breaks positivity of the map, so `δ ≤ 1` cannot be dropped:
with `f = √k`, `s = 1`, `δ = 3`, `γ = 1`, the stock `4` is sent to `-6`. -/
theorem depreciation_above_one_breaks_positivity :
    next (fun k : ℝ => k ^ (1 / 2 : ℝ)) 1 3 1 4 = -6 := by
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  simp only [next, h4]
  norm_num

/-- Linear technology can have more than one positive fixed point. -/
theorem linear_technology_multiple_fixed :
    next (fun k : ℝ => 2 * k) (1 / 2) 1 1 1 = 1 ∧
      next (fun k : ℝ => 2 * k) (1 / 2) 1 1 2 = 2 ∧ (1 : ℝ) ≠ 2 := by
  norm_num [next]

end Solow1956.DiscreteTime
