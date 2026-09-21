/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Uzawa's steady-state growth theorem, Jones–Scrimgeour / Schlicht version

Jones and Scrimgeour (2008), *A New Proof of Uzawa's Steady-State Growth
Theorem*, Review of Economics and Statistics 90(1), 180–182, Theorem 2.1.
The published argument is credited to Schlicht (2006). It differs from the
elasticity/inverse-function argument in the 2004 NBER working paper 10921.

Positive investment and nonnegative consumption force output, investment,
and capital to grow at the same rate. Constant returns then gives the
labor-augmenting representation using the original production function at
the starting date. The representation is asserted along the given path,
not for all counterfactual capital/labor inputs at every date.

We encode constant-rate paths explicitly with exponentials. Only the resource,
production, and accumulation equations on/after `start` are assumed. Their
extension before `start` is immaterial. To identify the growth rates, we use
the resource equation at three dates and a weighted-square identity; this
avoids the paper's second differentiation while proving the same implication.

Only constant returns is needed of production. Consequently the theorem also
applies to the paper's smaller class of neoclassical production functions;
their other properties are retained by reusing the same function at `start`.
-/

namespace UzawaModern.Uzawa

/-- A level at date `start` growing at a constant exponential rate. -/
noncomputable def trajectory (initial rate start t : ℝ) : ℝ :=
  initial * Real.exp (rate * (t - start))

@[simp] theorem trajectory_start (initial rate start : ℝ) :
    trajectory initial rate start start = initial := by simp [trajectory]

theorem trajectory_pos {initial : ℝ} (h : 0 < initial) (rate start t : ℝ) :
    0 < trajectory initial rate start t := mul_pos h (Real.exp_pos _)

theorem hasDerivAt_trajectory (initial rate start t : ℝ) :
    HasDerivAt (trajectory initial rate start)
      (rate * trajectory initial rate start t) t := by
  have h := (((hasDerivAt_id t).sub_const start).const_mul rate).exp.const_mul initial
  convert! h using 1
  dsimp [trajectory]
  ring

theorem trajectory_one (initial rate start : ℝ) :
    trajectory initial rate start (start + 1) = initial * Real.exp rate := by
  simp [trajectory]

theorem trajectory_two (initial rate start : ℝ) :
    trajectory initial rate start (start + 2) = initial * (Real.exp rate) ^ 2 := by
  simp only [trajectory, add_sub_cancel_left]
  rw [show rate * 2 = rate + rate by ring, Real.exp_add, pow_two]

/-- If an aggregate and its two nonnegative components have matching first
and second moments, a positive component has the aggregate's rate. -/
theorem rate_eq_of_weighted_moments {Y C I a b d : ℝ}
    (hC : 0 ≤ C) (hI : 0 < I) (h₀ : Y = C + I)
    (h₁ : Y * a = C * b + I * d)
    (h₂ : Y * a ^ 2 = C * b ^ 2 + I * d ^ 2) : a = d := by
  have hvariance : C * (b - a) ^ 2 + I * (d - a) ^ 2 = 0 := by
    calc
      _ = (C * b ^ 2 + I * d ^ 2) - 2 * a * (C * b + I * d) +
          a ^ 2 * (C + I) := by ring
      _ = 0 := by rw [← h₀, ← h₁, ← h₂]; ring
  have hCvar := mul_nonneg hC (sq_nonneg (b - a))
  have hIvar : I * (d - a) ^ 2 = 0 :=
    le_antisymm (by linarith) (mul_nonneg hI.le (sq_nonneg _))
  have hsq : (d - a) ^ 2 = 0 := (mul_eq_zero.mp hIvar).resolve_left (ne_of_gt hI)
  nlinarith [sq_nonneg (d - a)]

/-- The resource identity on a balanced path makes investment and output
grow at the same rate. Consumption may be identically zero. -/
theorem outputGrowth_eq_investmentGrowth {Y C I gY gC gI start : ℝ}
    (hC : 0 ≤ C) (hI : 0 < I)
    (hresource : ∀ t, start ≤ t → trajectory Y gY start t =
      trajectory C gC start t + trajectory I gI start t) : gY = gI := by
  have h₀ := hresource start le_rfl
  have h₁ := hresource (start + 1) (by linarith)
  have h₂ := hresource (start + 2) (by linarith)
  simp only [trajectory_start] at h₀
  simp only [trajectory_one] at h₁
  simp only [trajectory_two] at h₂
  exact Real.exp_injective (rate_eq_of_weighted_moments hC hI h₀ h₁ h₂)

/-- The accumulation equation identifies investment's rate with capital's.
The positive-investment assumption prevents cancellation of a zero level. -/
theorem investmentGrowth_eq_capitalGrowth {I K gI gK δ start : ℝ}
    (hI : 0 < I)
    (haccum : ∀ t, start ≤ t → HasDerivAt (trajectory K gK start)
      (trajectory I gI start t - δ * trajectory K gK start t) t) : gI = gK := by
  have hlevels (t : ℝ) (ht : start ≤ t) :
      trajectory I gI start t = (gK + δ) * trajectory K gK start t := by
    have h := (hasDerivAt_trajectory K gK start t).unique (haccum t ht)
    linarith
  have h₀ := hlevels start le_rfl
  have h₁ := hlevels (start + 1) (by linarith)
  simp only [trajectory_start] at h₀
  simp only [trajectory_one] at h₁
  have hprod : I * Real.exp gI = I * Real.exp gK := by
    calc
      _ = (gK + δ) * (K * Real.exp gK) := h₁
      _ = ((gK + δ) * K) * Real.exp gK := by ring
      _ = _ := by rw [← h₀]
  exact Real.exp_injective (mul_left_cancel₀ (ne_of_gt hI) hprod)

/-- Initial levels and growth rates of the five quantities in Definition 2.2.
Sign and equilibrium restrictions are explicit hypotheses of the theorem. -/
structure BalancedGrowthData where
  start : ℝ
  outputInitial : ℝ
  consumptionInitial : ℝ
  investmentInitial : ℝ
  capitalInitial : ℝ
  laborInitial : ℝ
  outputGrowth : ℝ
  consumptionGrowth : ℝ
  investmentGrowth : ℝ
  capitalGrowth : ℝ
  laborGrowth : ℝ
  depreciation : ℝ

namespace BalancedGrowthData

noncomputable def output (p : BalancedGrowthData) : ℝ → ℝ :=
  trajectory p.outputInitial p.outputGrowth p.start
noncomputable def consumption (p : BalancedGrowthData) : ℝ → ℝ :=
  trajectory p.consumptionInitial p.consumptionGrowth p.start
noncomputable def investment (p : BalancedGrowthData) : ℝ → ℝ :=
  trajectory p.investmentInitial p.investmentGrowth p.start
noncomputable def capital (p : BalancedGrowthData) : ℝ → ℝ :=
  trajectory p.capitalInitial p.capitalGrowth p.start
noncomputable def labor (p : BalancedGrowthData) : ℝ → ℝ :=
  trajectory p.laborInitial p.laborGrowth p.start

/-- The labor-augmenting index, normalized to one at the starting date. -/
noncomputable def technology (p : BalancedGrowthData) (t : ℝ) : ℝ :=
  Real.exp ((p.outputGrowth - p.laborGrowth) * (t - p.start))

theorem technology_pos (p : BalancedGrowthData) (t : ℝ) : 0 < p.technology t :=
  Real.exp_pos _

@[simp] theorem technology_start (p : BalancedGrowthData) : p.technology p.start = 1 := by
  simp [technology]

theorem hasDerivAt_technology (p : BalancedGrowthData) (t : ℝ) :
    HasDerivAt p.technology
      ((p.outputGrowth - p.laborGrowth) * p.technology t) t := by
  have h := (((hasDerivAt_id t).sub_const p.start).const_mul
    (p.outputGrowth - p.laborGrowth)).exp
  convert! h using 1
  dsimp [technology]
  ring

theorem technology_growthRate (p : BalancedGrowthData) (t : ℝ) :
    deriv p.technology t / p.technology t = p.outputGrowth - p.laborGrowth := by
  rw [(p.hasDerivAt_technology t).deriv]
  exact mul_div_cancel_right₀ _ (ne_of_gt (p.technology_pos t))

/-- Effective labor and output share the same exponential factor. -/
theorem technology_mul_labor (p : BalancedGrowthData) (t : ℝ) :
    p.technology t * p.labor t =
      Real.exp (p.outputGrowth * (t - p.start)) * p.laborInitial := by
  unfold technology labor trajectory
  calc
    _ = (Real.exp ((p.outputGrowth - p.laborGrowth) * (t - p.start)) *
        Real.exp (p.laborGrowth * (t - p.start))) * p.laborInitial := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

theorem output_per_worker (p : BalancedGrowthData) (t : ℝ) :
    p.output t / p.labor t =
      trajectory (p.outputInitial / p.laborInitial)
        (p.outputGrowth - p.laborGrowth) p.start t := by
  unfold output labor trajectory
  rw [mul_div_mul_comm, ← Real.exp_sub]
  congr 2
  ring

/-- No equality of growth rates is built into the definition of balanced growth:
it follows from resource feasibility and accumulation with positive investment. -/
theorem outputGrowth_eq_capitalGrowth (p : BalancedGrowthData)
    (hC : 0 ≤ p.consumptionInitial) (hI : 0 < p.investmentInitial)
    (hresource : ∀ t, p.start ≤ t → p.output t = p.consumption t + p.investment t)
    (haccum : ∀ t, p.start ≤ t → HasDerivAt p.capital
      (p.investment t - p.depreciation * p.capital t) t) :
    p.outputGrowth = p.capitalGrowth :=
  (Uzawa.outputGrowth_eq_investmentGrowth hC hI hresource).trans
    (investmentGrowth_eq_capitalGrowth hI haccum)

/-- **Uzawa's on-path labor-augmenting representation.** This is the production
identity of Jones–Scrimgeour (2008), equation (5), proved by Schlicht's scaling
argument. Positive marginal products, concavity, nonnegative depreciation, and
nonnegative labor growth are unnecessary for this identity and are not assumed.
`technology_growthRate` supplies its stated rate `g = gY - n`. -/
theorem labor_augmenting_representation (p : BalancedGrowthData) {F : ℝ → ℝ → ℝ → ℝ}
    (hK : 0 < p.capitalInitial) (hL : 0 < p.laborInitial)
    (hC : 0 ≤ p.consumptionInitial) (hI : 0 < p.investmentInitial)
    (hresource : ∀ t, p.start ≤ t → p.output t = p.consumption t + p.investment t)
    (haccum : ∀ t, p.start ≤ t → HasDerivAt p.capital
      (p.investment t - p.depreciation * p.capital t) t)
    (hproduction : ∀ t, p.start ≤ t → p.output t = F (p.capital t) (p.labor t) t)
    (hCRS : ∀ K L a, 0 < K → 0 < L → 0 < a →
      F (a * K) (a * L) p.start = a * F K L p.start) :
    ∀ t, p.start ≤ t → p.output t = F (p.capital t) (p.technology t * p.labor t) p.start := by
  have hrates := p.outputGrowth_eq_capitalGrowth hC hI hresource haccum
  have h₀ := hproduction p.start le_rfl
  simp only [output, capital, labor, trajectory_start] at h₀
  intro t _
  rw [p.technology_mul_labor]
  change p.outputInitial * Real.exp (p.outputGrowth * (t - p.start)) =
    F (p.capitalInitial * Real.exp (p.capitalGrowth * (t - p.start)))
      (Real.exp (p.outputGrowth * (t - p.start)) * p.laborInitial) p.start
  rw [← hrates, mul_comm p.capitalInitial, hCRS _ _ _ hK hL (Real.exp_pos _), ← h₀]
  ring

end BalancedGrowthData
end UzawaModern.Uzawa
