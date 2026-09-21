/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/
import Solow1956.Growth.GeneralSolow
import Solow1956.Growth.SolowGoldenRule
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Concrete technologies and boundary checks for the general theorem -/

open Set Filter Topology

namespace Solow1956.Neoclassical

theorem technology_rpow {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Technology (fun k : ℝ => k ^ α) := by
  have hd (k : ℝ) (hk : 0 < k) : HasDerivAt (fun k : ℝ => k ^ α)
      (α * k ^ (α - 1)) k := Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hk))
  have hdc : ContinuousOn (fun k : ℝ => α * k ^ (α - 1)) (Ioi 0) := by
    intro k hk
    have hh := Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl (ne_of_gt hk))
    exact (hh.continuousAt.const_mul α).continuousWithinAt
  refine ⟨(Real.continuous_rpow_const hα.le).continuousOn,
    Real.zero_rpow (ne_of_gt hα), fun k hk => (hd k hk).differentiableAt,
    hdc.congr (fun k hk => (hd k hk).deriv), Real.strictConcaveOn_rpow hα hα1,
    ?_, ?_, ?_⟩
  · intro k hk
    rw [(hd k hk).deriv]
    exact mul_pos hα (Real.rpow_pos_of_pos hk _)
  · apply (Tendsto.const_mul_atTop hα (tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr hα1))).congr'
    filter_upwards [self_mem_nhdsWithin] with k hk
    exact (hd k hk).deriv.symm
  · have hl : Tendsto (fun k : ℝ => α * k ^ (α - 1)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (sub_pos.mpr hα1)).const_mul α
      simpa only [neg_sub, mul_zero] using this
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
    exact (hd k hk).deriv.symm

theorem Technology.add {f g : ℝ → ℝ} (hf : Technology f) (hg : Technology g) :
    Technology (fun k => f k + g k) := by
  have hd (k : ℝ) (hk : 0 < k) :
      HasDerivAt (fun k => f k + g k) (deriv f k + deriv g k) k :=
    (hf.differentiable k hk).hasDerivAt.add (hg.differentiable k hk).hasDerivAt
  refine ⟨hf.continuous.add hg.continuous, by rw [hf.zero, hg.zero]; ring,
    fun k hk => (hd k hk).differentiableAt,
    (hf.derivative_continuous.add hg.derivative_continuous).congr (fun k hk => (hd k hk).deriv),
    hf.concave.add hg.concave, ?_, ?_, ?_⟩
  · intro k hk
    rw [(hd k hk).deriv]
    exact add_pos (hf.marginal_positive k hk) (hg.marginal_positive k hk)
  · apply (Filter.Tendsto.atTop_add_atTop hf.inada_zero hg.inada_zero).congr'
    filter_upwards [self_mem_nhdsWithin] with k hk
    exact (hd k hk).deriv.symm
  · have hh : Tendsto (fun k => deriv f k + deriv g k) atTop (𝓝 (0 : ℝ)) := by
      simpa only [add_zero] using hf.inada_top.add hg.inada_top
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
    exact (hd k hk).deriv.symm

/-- A sum of powers is covered without solving the trajectory in closed form. -/
theorem mixed_power_technology : Technology (fun k : ℝ => k ^ (1 / 2 : ℝ) + k ^ (1 / 3 : ℝ)) :=
  (technology_rpow (by norm_num) (by norm_num)).add
    (technology_rpow (by norm_num) (by norm_num))

/-- A concrete non-Cobb–Douglas economy has a positive unique steady state. -/
theorem mixed_power_steady_exists :
    ∃! k : ℝ, 0 < k ∧ rate (fun k : ℝ => k ^ (1 / 2 : ℝ) + k ^ (1 / 3 : ℝ))
      (1 / 4) 1 k = 0 :=
  existsUnique_steadyState mixed_power_technology (by norm_num) (by norm_num)

/-- Without positive effective dilution, there is no positive stationary stock
under the maintained production and positive-saving assumptions. -/
theorem no_positive_steady_without_dilution {f : ℝ → ℝ} (h : Technology f)
    {s m k : ℝ} (hs : 0 < s) (hm : m ≤ 0) (hk : 0 < k) : 0 < rate f s m k := by
  have hsave := mul_pos hs (h.output_pos hk)
  have hdil := mul_nonpos_of_nonpos_of_nonneg hm hk.le
  dsimp [rate]
  linarith

/-- Linear technology can have more than one positive steady stock. It lacks
the strict-concavity/Inada assumptions of the general theorem. -/
theorem linear_technology_multiple_steady :
    rate (fun k : ℝ => 2 * k) (1 / 2) 1 1 = 0 ∧
    rate (fun k : ℝ => 2 * k) (1 / 2) 1 2 = 0 ∧ (1 : ℝ) ≠ 2 := by
  norm_num [rate]

end Solow1956.Neoclassical
