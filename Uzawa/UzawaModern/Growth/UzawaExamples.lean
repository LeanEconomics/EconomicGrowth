/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/
import UzawaModern.Growth.Uzawa
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum

/-!
# A nonvacuous Cobb–Douglas instance of Uzawa's theorem

`K(t)=exp(2t)`, `L(t)=1`, `Y(t)=4 exp(2t)`, `C(t)=I(t)=2 exp(2t)`, and `δ=0`,
with `F(K,L,t)=4 exp(t) sqrt(K L)`. All economic levels are strictly positive.
The final proof applies the general theorem after checking its actual premises.
Positive and diminishing marginal products and Inada limits of this familiar
Cobb–Douglas technology are not asserted as additional formal results here.
-/

namespace UzawaModern.Uzawa.Examples

def growingEconomy : BalancedGrowthData where
  start := 0
  outputInitial := 4
  consumptionInitial := 2
  investmentInitial := 2
  capitalInitial := 1
  laborInitial := 1
  outputGrowth := 2
  consumptionGrowth := 2
  investmentGrowth := 2
  capitalGrowth := 2
  laborGrowth := 0
  depreciation := 0

noncomputable def production (K L t : ℝ) : ℝ :=
  4 * Real.exp t * Real.sqrt (K * L)

theorem resource (t : ℝ) : growingEconomy.output t =
    growingEconomy.consumption t + growingEconomy.investment t := by
  simp only [BalancedGrowthData.output, BalancedGrowthData.consumption,
    BalancedGrowthData.investment, growingEconomy, trajectory]
  ring

theorem accumulation (t : ℝ) : HasDerivAt growingEconomy.capital
    (growingEconomy.investment t - growingEconomy.depreciation * growingEconomy.capital t) t := by
  convert! hasDerivAt_trajectory 1 2 0 t using 1
  simp [BalancedGrowthData.investment, BalancedGrowthData.capital, growingEconomy, trajectory]

theorem production_on_path (t : ℝ) : growingEconomy.output t =
    production (growingEconomy.capital t) (growingEconomy.labor t) t := by
  have hsqrt : Real.sqrt (Real.exp (2 * t)) = Real.exp t := by
    have he : Real.exp (2 * t) = (Real.exp t) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he, Real.sqrt_sq (Real.exp_pos _).le]
  simp only [BalancedGrowthData.output, BalancedGrowthData.capital,
    BalancedGrowthData.labor, growingEconomy, trajectory, sub_zero, zero_mul,
    Real.exp_zero, one_mul, mul_one, production]
  rw [hsqrt]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem constant_returns (K L : ℝ) {a : ℝ} (ha : 0 < a) :
    production (a * K) (a * L) 0 = a * production K L 0 := by
  have h : (a * K) * (a * L) = a ^ 2 * (K * L) := by ring
  simp only [production, Real.exp_zero, mul_one, h,
    Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  ring

/-- All the substantive hypotheses of the general theorem are realized here. -/
theorem labor_augmenting (t : ℝ) (ht : 0 ≤ t) :
    growingEconomy.output t = production (growingEconomy.capital t)
      (growingEconomy.technology t * growingEconomy.labor t) 0 := by
  exact growingEconomy.labor_augmenting_representation (by norm_num [growingEconomy])
    (by norm_num [growingEconomy]) (by norm_num [growingEconomy])
    (by norm_num [growingEconomy]) (fun u _ => resource u)
    (fun u _ => accumulation u) (fun u _ => production_on_path u)
    (fun K L _ _ _ ha => constant_returns K L ha) t ht

theorem levels_positive (t : ℝ) : 0 < growingEconomy.output t ∧
    0 < growingEconomy.consumption t ∧ 0 < growingEconomy.investment t ∧
    0 < growingEconomy.capital t ∧ 0 < growingEconomy.labor t := by
  repeat' constructor
  all_goals apply trajectory_pos; norm_num [growingEconomy]

end UzawaModern.Uzawa.Examples
