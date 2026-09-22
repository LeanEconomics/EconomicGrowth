import RamseyCassKoopmans.StationaryOptimality
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# A concrete square-root technology and logarithmic-utility economy

Take `f(k) = 2√k`, `U(c) = log c`, effective depreciation/dilution `m = 1`
and effective utility discounting `d = 1`. The stationary capital stock is
`k* = 1/4`, consumption is `c* = 3/4`, and replacement investment is `1/4`.

This file constructs the constant path, proves its finite lifetime welfare is
`log (3/4)`, and proves that no admissible competitor from the same initial stock
with finite limiting welfare achieves a larger objective. Competitors may
disinvest, so the comparison also covers the Cass subclass. This is an actual
economy instantiating the verification theorem, not another conditional claim
about unspecified utility or production functions. No nonstationary trajectory
from a different initial stock is constructed here.
-/

open Set

namespace RamseyCassKoopmans.Examples

noncomputable def production (k : ℝ) : ℝ := 2 * Real.sqrt k

theorem sqrt_quarter : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
  norm_num

theorem production_quarter : production (1 / 4) = 1 := by
  rw [production, sqrt_quarter]
  norm_num

theorem production_concave : ConcaveOn ℝ (Ici 0) production := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := Real.strictConcaveOn_sqrt.concaveOn.2 hx hy ha hb hab
  simp only [production, smul_eq_mul] at *
  nlinarith

theorem production_hasDerivAt_quarter : HasDerivAt production 2 (1 / 4) := by
  have h := (Real.hasDerivAt_sqrt (x := (1 / 4 : ℝ)) (by norm_num)).const_mul 2
  rw [sqrt_quarter] at h
  norm_num at h
  exact h

/-- Four units of capital suffice as a global resource-based capacity bound. -/
theorem production_capacity (x : ℝ) (hx : 4 ≤ x) : production x ≤ 1 * x := by
  have hx0 : 0 ≤ x := by linarith
  have hs : 2 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
      norm_num
    rwa [h4] at h
  calc
    production x = 2 * Real.sqrt x := rfl
    _ ≤ Real.sqrt x * Real.sqrt x :=
      mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg x)
    _ = x := Real.mul_self_sqrt hx0
    _ = 1 * x := by ring

theorem log_continuous_positive : ContinuousOn Real.log (Ioi 0) := by
  intro c hc
  exact (Real.continuousAt_log (ne_of_gt hc)).continuousWithinAt

theorem log_hasDerivAt_three_quarters :
    HasDerivAt Real.log (4 / 3 : ℝ) (3 / 4) := by
  convert Real.hasDerivAt_log (x := (3 / 4 : ℝ)) (by norm_num) using 1
  norm_num

/-- The concrete optimal candidate, including its actual resource and capital laws. -/
noncomputable def logSqrtPath : FeasiblePath production 1 :=
  stationaryPath production 1 (1 / 4) (3 / 4) (by norm_num) (by norm_num)
    (by rw [production_quarter]; norm_num)

theorem logSqrtPath_values (t : ℝ) :
    logSqrtPath.capital t = 1 / 4 ∧ logSqrtPath.consumption t = 3 / 4 ∧
      logSqrtPath.investment t = 1 / 4 := by
  norm_num [logSqrtPath, stationaryPath]

theorem logSqrtPath_nonnegativeInvestment : logSqrtPath.NonnegativeInvestment := by
  intro t _
  norm_num [logSqrtPath, stationaryPath]

theorem logSqrtPath_hasWelfare :
    HasWelfare Real.log (discount 1) logSqrtPath.consumption (Real.log (3 / 4)) := by
  simpa only [logSqrtPath, div_one] using
    (stationaryPath_hasWelfare production Real.log 1 (1 / 4) (3 / 4) 1
      (by norm_num) (by norm_num) (by rw [production_quarter]; norm_num) (by norm_num))

/-- Global welfare comparison for this explicit economy and stationary initial
stock, including every positive-consumption competitor with finite limiting welfare. -/
theorem logSqrtPath_optimal (b : FeasiblePath production 1) (J : ℝ)
    (hinit : b.capital 0 = 1 / 4)
    (hJ : HasWelfare Real.log (discount 1) b.consumption J) :
    J ≤ Real.log (3 / 4) := by
  have h := stationaryPath_optimality production Real.log 1 (1 / 4) (3 / 4) 1 4
    (by norm_num) (by norm_num) (by rw [production_quarter]; norm_num)
    production_concave strictConcaveOn_log_Ioi.concaveOn log_continuous_positive
    production_hasDerivAt_quarter.differentiableAt
    log_hasDerivAt_three_quarters.differentiableAt
    (by rw [log_hasDerivAt_three_quarters.deriv]; norm_num)
    (by rw [production_hasDerivAt_quarter.deriv]; norm_num)
    (by norm_num) (by norm_num) production_capacity b J hinit hJ
  simpa only [div_one] using h

end RamseyCassKoopmans.Examples
