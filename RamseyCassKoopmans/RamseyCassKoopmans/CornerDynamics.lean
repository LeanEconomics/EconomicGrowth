import RamseyCassKoopmans.ClosedFormDynamics
import RamseyCassKoopmans.PathGluing

/-!
# The zero-investment regime in the solvable CRRA model

Large initial stocks require zero gross investment before the interior branch.
The switching time is a parameter here; it will be selected from initial capital.
The state and costate joins are proved differentiable, not assumed smooth.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans.ClosedForm.Corner

noncomputable def r (τ t : ℝ) : ℝ := Real.exp ((t - τ) / 4)
noncomputable def inverseFactor (τ t : ℝ) : ℝ := Real.exp ((τ - t) / 4)
noncomputable def preCapital (τ t : ℝ) : ℝ := (4 / 9) * inverseFactor τ t ^ 4
noncomputable def preConsumption (τ t : ℝ) : ℝ := (4 / 3) * inverseFactor τ t ^ 2
noncomputable def preShadow (τ t : ℝ) : ℝ := Real.sqrt 3 / 10 * (6 * r τ t ^ 3 - r τ t ^ 8)
noncomputable def preMu (τ t : ℝ) : ℝ := Real.sqrt 3 / 2 * r τ t
noncomputable def preMp (τ t : ℝ) : ℝ := 3 / 2 * r τ t ^ 2

theorem r_pos (τ t : ℝ) : 0 < r τ t := Real.exp_pos _
theorem inverseFactor_pos (τ t : ℝ) : 0 < inverseFactor τ t := Real.exp_pos _
theorem r_switch (τ : ℝ) : r τ τ = 1 := by simp [r]
theorem inverseFactor_switch (τ : ℝ) : inverseFactor τ τ = 1 := by simp [inverseFactor]

theorem r_eq_inv_inverseFactor (τ t : ℝ) : r τ t = (inverseFactor τ t)⁻¹ := by
  rw [r, inverseFactor, ← Real.exp_neg]
  congr 1
  ring

theorem hasDerivAt_r (τ t : ℝ) : HasDerivAt (r τ) (r τ t / 4) t := by
  convert (((hasDerivAt_id t).sub_const τ).div_const 4).exp using 1
  · rfl
  · simp [r, div_eq_mul_inv]

theorem hasDerivAt_inverseFactor (τ t : ℝ) :
    HasDerivAt (inverseFactor τ) (-inverseFactor τ t / 4) t := by
  convert (((hasDerivAt_id t).const_sub τ).div_const 4).exp using 1
  · rfl
  · simp [inverseFactor]
    ring

theorem r_continuous (τ : ℝ) : Continuous (r τ) := by unfold r; fun_prop
theorem inverseFactor_continuous (τ : ℝ) : Continuous (inverseFactor τ) := by
  unfold inverseFactor
  fun_prop

theorem hasDerivAt_preCapital (τ t : ℝ) :
    HasDerivAt (preCapital τ) (-preCapital τ t) t := by
  convert ((hasDerivAt_inverseFactor τ t).pow 4).const_mul (4 / 9) using 1
  · rfl
  · dsimp [preCapital]
    ring

theorem hasDerivAt_preConsumption (τ t : ℝ) :
    HasDerivAt (preConsumption τ) (-preConsumption τ t / 2) t := by
  convert ((hasDerivAt_inverseFactor τ t).pow 2).const_mul (4 / 3) using 1
  · rfl
  · dsimp [preConsumption]
    ring

theorem hasDerivAt_preShadow (τ t : ℝ) :
    HasDerivAt (preShadow τ) (2 * preShadow τ t - preMu τ t * preMp τ t) t := by
  convert (((hasDerivAt_r τ t).pow 3).const_mul 6 |>.sub
    ((hasDerivAt_r τ t).pow 8)).const_mul (Real.sqrt 3 / 10) using 1
  · rfl
  · dsimp [preShadow, preMu, preMp]
    ring

theorem preCapital_pos (τ t : ℝ) : 0 < preCapital τ t := by
  exact mul_pos (by norm_num) (pow_pos (inverseFactor_pos τ t) 4)

theorem preConsumption_pos (τ t : ℝ) : 0 < preConsumption τ t := by
  exact mul_pos (by norm_num) (sq_pos_of_pos (inverseFactor_pos τ t))

theorem sqrt_preCapital (τ t : ℝ) :
    Real.sqrt (preCapital τ t) = (2 / 3) * inverseFactor τ t ^ 2 := by
  apply (Real.sqrt_eq_iff_eq_sq (preCapital_pos τ t).le (by positivity)).2
  dsimp [preCapital]
  ring

theorem sqrt_preConsumption (τ t : ℝ) :
    Real.sqrt (preConsumption τ t) = (2 / Real.sqrt 3) * inverseFactor τ t := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  apply (Real.sqrt_eq_iff_eq_sq (preConsumption_pos τ t).le
    (mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg 3)) (inverseFactor_pos τ t).le)).2
  dsimp [preConsumption]
  field_simp
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

theorem pre_resource (τ t : ℝ) : preConsumption τ t = Examples.production (preCapital τ t) := by
  rw [Examples.production, sqrt_preCapital]
  dsimp [preConsumption]
  ring

theorem pre_utility_derivative (τ t : ℝ) :
    HasDerivAt utility (preMu τ t) (preConsumption τ t) := by
  convert hasDerivAt_utility (preConsumption_pos τ t) using 1
  rw [sqrt_preConsumption, preMu, r_eq_inv_inverseFactor]
  field_simp

theorem pre_production_derivative (τ t : ℝ) :
    HasDerivAt Examples.production (preMp τ t) (preCapital τ t) := by
  change HasDerivAt utility (preMp τ t) (preCapital τ t)
  convert hasDerivAt_utility (preCapital_pos τ t) using 1
  rw [sqrt_preCapital, preMp, r_eq_inv_inverseFactor]
  field_simp

theorem preShadow_pos {τ t : ℝ} (ht : t ≤ τ) : 0 < preShadow τ t := by
  have hr := r_pos τ t
  have hr1 : r τ t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpow : r τ t ^ 8 ≤ r τ t ^ 3 := pow_le_pow_of_le_one hr.le hr1 (by norm_num)
  have hdiff : 0 < 6 * r τ t ^ 3 - r τ t ^ 8 := by nlinarith [pow_pos hr 3]
  exact mul_pos (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)) hdiff

/-- The investment wedge is nonpositive before the switch. The inequality is
polynomial after scaling by positive marginal utility. -/
theorem preShadow_le_preMu {τ t : ℝ} (ht : t ≤ τ) : preShadow τ t ≤ preMu τ t := by
  have hr := (r_pos τ t).le
  have hr1 : r τ t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : r τ t ^ 2 ≤ r τ t := by simpa using pow_le_pow_of_le_one hr hr1 (show 1 ≤ 2 by norm_num)
  have h3 : r τ t ^ 3 ≤ r τ t := by simpa using pow_le_pow_of_le_one hr hr1 (show 1 ≤ 3 by norm_num)
  have h4 : r τ t ^ 4 ≤ r τ t := by simpa using pow_le_pow_of_le_one hr hr1 (show 1 ≤ 4 by norm_num)
  have h5 : r τ t ^ 5 ≤ r τ t := by simpa using pow_le_pow_of_le_one hr hr1 (show 1 ≤ 5 by norm_num)
  have h6 : r τ t ^ 6 ≤ r τ t := by simpa using pow_le_pow_of_le_one hr hr1 (show 1 ≤ 6 by norm_num)
  have hinner :
      0 ≤ 5 + 5 * r τ t - r τ t ^ 2 - r τ t ^ 3 - r τ t ^ 4 - r τ t ^ 5 - r τ t ^ 6 := by
    linarith
  have hprod := mul_nonneg (mul_nonneg hr (sub_nonneg.mpr hr1)) hinner
  have hpoly : 6 * r τ t ^ 3 - r τ t ^ 8 ≤ 5 * r τ t := by nlinarith only [hprod]
  have hmul := mul_le_mul_of_nonneg_left hpoly (Real.sqrt_nonneg 3)
  dsimp [preShadow, preMu]
  nlinarith

end RamseyCassKoopmans.ClosedForm.Corner
