import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/

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

/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/

/-!
# The elasticity identity in Jones–Scrimgeour (2004)

NBER working paper 10921, equation (4) and footnotes 4–5, printed pp. 5–6.
For output per worker `f(k)`, capital/output is `h(k) = k/f(k)` and the capital
share is `α = f'(k) k / f(k)`. This file proves `h' = (1-α)/f(k)` and derives
the output-versus-capital/output elasticity `α/(1-α)` along a differentiable
local inverse parameterization. Its existence is an explicit hypothesis;
we do not assume that pointwise nonzero derivatives prove global surjectivity.

These are local calculus statements from the 2004 argument. They are not a
proof of its later separation-of-variables step. The independent `Uzawa`
module proves the published 2008 on-path theorem via the Schlicht argument.
-/

namespace UzawaModern.UzawaElasticity

open Filter
open scoped Topology

/-- Differentiate the capital/output ratio without assuming an inverse exists. -/
theorem hasDerivAt_capitalOutputRatio {f : ℝ → ℝ} {k m : ℝ}
    (hf : HasDerivAt f m k) (hy : f k ≠ 0) :
    HasDerivAt (fun u => u / f u) ((1 - m * k / f k) / f k) k := by
  have h := (hasDerivAt_id k).fun_div hf hy
  convert! h using 1
  dsimp
  field_simp

/-- A positive labor share makes the capital/output derivative strictly positive. -/
theorem capitalOutputRatio_derivative_pos {f : ℝ → ℝ} {k m : ℝ}
    (hy : 0 < f k) (hshare : m * k / f k < 1) :
    0 < (1 - m * k / f k) / f k :=
  div_pos (sub_pos.mpr hshare) hy

/-- Equation (4): the output elasticity with respect to capital/output is
the capital share divided by the labor share. The identity `k(x)=x f(k(x))`
is required in a neighborhood, so it can legitimately be differentiated. -/
theorem output_capitalOutput_elasticity {f k : ℝ → ℝ} {x m k' : ℝ}
    (hk : HasDerivAt k k' x) (hf : HasDerivAt f m (k x))
    (hy : 0 < f (k x))
    (hshare : m * k x / f (k x) < 1)
    (hidentity : ∀ᶠ u in 𝓝 x, k u = u * f (k u)) :
    (m * k') * x / f (k x) =
      (m * k x / f (k x)) / (1 - m * k x / f (k x)) := by
  have hid : k x = x * f (k x) :=
    Filter.EventuallyEq.eq_of_nhds (show k =ᶠ[𝓝 x] (fun u => u * f (k u)) from hidentity)
  have hcomp := hf.comp x hk
  have hproduct := (hasDerivAt_id x).mul hcomp
  have hder : k' = f (k x) + x * (m * k') := by
    simpa using hk.unique (hproduct.congr_of_eventuallyEq hidentity)
  have halpha : m * k x / f (k x) = m * x := by
    calc
      _ = m * (x * f (k x)) / f (k x) := congrArg (fun v => m * v / f (k x)) hid
      _ = _ := by field_simp
  have hden : 1 - m * x ≠ 0 := by rw [halpha] at hshare; linarith
  have hkprime : k' = f (k x) / (1 - m * x) := by
    apply (eq_div_iff hden).mpr
    nlinarith [hder]
  rw [halpha, hkprime]
  field_simp

end UzawaModern.UzawaElasticity

/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/

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

/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/

/-!
# A repaired capital/output-coordinate proof of Uzawa representation

This is a strengthened, domain-wide theorem motivated by Jones-Scrimgeour
(2004), not a claim to prove that paper's literal assumptions. We assume
the capital/output map has the whole positive half-line as its range, and
later impose share invariance at every positive capital/output ratio.
We construct its inverse, prove continuity and differentiability, derive
the elasticity identity, and prove separation by the mean value theorem.
-/

namespace UzawaModern.UzawaSeparation

open Set Filter
open scoped Topology

/-- Intensive technologies with an explicitly specified global ratio range.
No inverse, inverse derivative, or separation identity is assumed. -/
structure Technology where
  output : ℝ → ℝ → ℝ
  marginal : ℝ → ℝ → ℝ
  output_pos : ∀ t k, 0 < k → 0 < output t k
  hasDerivAt_output : ∀ t k, 0 < k → HasDerivAt (output t) (marginal t k) k
  share_lt_one : ∀ t k, 0 < k → marginal t k * k / output t k < 1
  ratio_surjective : ∀ t x, 0 < x → ∃ k, 0 < k ∧ k / output t k = x

namespace Technology

noncomputable def ratio (T : Technology) (t k : ℝ) : ℝ := k / T.output t k

noncomputable def share (T : Technology) (t k : ℝ) : ℝ :=
  T.marginal t k * k / T.output t k

theorem ratio_pos (T : Technology) (t : ℝ) {k : ℝ} (hk : 0 < k) :
    0 < T.ratio t k := div_pos hk (T.output_pos t k hk)

theorem hasDerivAt_ratio (T : Technology) (t : ℝ) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (T.ratio t) ((1 - T.share t k) / T.output t k) k :=
  UzawaElasticity.hasDerivAt_capitalOutputRatio (T.hasDerivAt_output t k hk)
    (ne_of_gt (T.output_pos t k hk))

theorem ratio_derivative_pos (T : Technology) (t : ℝ) {k : ℝ} (hk : 0 < k) :
    0 < (1 - T.share t k) / T.output t k :=
  div_pos (sub_pos.mpr (T.share_lt_one t k hk)) (T.output_pos t k hk)

theorem ratio_strictMonoOn (T : Technology) (t : ℝ) :
    StrictMonoOn (T.ratio t) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro k hk
    exact (T.hasDerivAt_ratio t hk).continuousAt.continuousWithinAt
  · intro k hk
    have hk' : 0 < k := by simpa only [interior_Ioi, mem_Ioi] using hk
    rw [(T.hasDerivAt_ratio t hk').deriv]
    exact T.ratio_derivative_pos t hk'

/-- Choose a positive preimage; all subsequent inverse properties are proved. -/
noncomputable def capital (T : Technology) (t x : ℝ) : ℝ :=
  if hx : 0 < x then Classical.choose (T.ratio_surjective t x hx) else 0

theorem capital_pos (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < T.capital t x := by
  simp only [capital, dite_eq_left hx]
  exact (Classical.choose_spec (T.ratio_surjective t x hx)).1

theorem ratio_capital (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    T.ratio t (T.capital t x) = x := by
  simp only [capital, dite_eq_left hx, ratio]
  exact (Classical.choose_spec (T.ratio_surjective t x hx)).2

theorem capital_ratio (T : Technology) (t : ℝ) {k : ℝ} (hk : 0 < k) :
    T.capital t (T.ratio t k) = k := by
  apply (T.ratio_strictMonoOn t).injOn (T.capital_pos t (T.ratio_pos t hk)) hk
  exact T.ratio_capital t (T.ratio_pos t hk)

theorem capital_strictMonoOn (T : Technology) (t : ℝ) :
    StrictMonoOn (T.capital t) (Ioi 0) := by
  intro x hx y hy hxy
  apply lt_of_not_ge
  intro hle
  have h := (T.ratio_strictMonoOn t).monotoneOn
    (T.capital_pos t hy) (T.capital_pos t hx) hle
  rw [T.ratio_capital t hy, T.ratio_capital t hx] at h
  exact (not_le_of_gt hxy) h

theorem capital_image (T : Technology) (t : ℝ) : T.capital t '' Ioi 0 = Ioi 0 := by
  apply Subset.antisymm
  · rintro k ⟨x, hx, rfl⟩
    exact T.capital_pos t hx
  · intro k hk
    exact ⟨T.ratio t k, T.ratio_pos t hk, T.capital_ratio t hk⟩

theorem continuousAt_capital (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (T.capital t) x := by
  apply (T.capital_strictMonoOn t).continuousAt_of_image_mem_nhds
    (isOpen_Ioi.mem_nhds hx)
  rw [T.capital_image t]
  exact isOpen_Ioi.mem_nhds (T.capital_pos t hx)

theorem hasDerivAt_capital (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (T.capital t)
      (((1 - T.share t (T.capital t x)) / T.output t (T.capital t x))⁻¹) x := by
  apply HasDerivAt.of_local_left_inverse (T.continuousAt_capital t hx)
    (T.hasDerivAt_ratio t (T.capital_pos t hx))
    (ne_of_gt (T.ratio_derivative_pos t (T.capital_pos t hx)))
  filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
  exact T.ratio_capital t hu

noncomputable def phi (T : Technology) (t x : ℝ) : ℝ := T.output t (T.capital t x)

noncomputable def phiDerivative (T : Technology) (t x : ℝ) : ℝ :=
  T.marginal t (T.capital t x) *
    (((1 - T.share t (T.capital t x)) / T.output t (T.capital t x))⁻¹)

theorem phi_pos (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < T.phi t x := T.output_pos t _ (T.capital_pos t hx)

theorem hasDerivAt_phi (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (T.phi t) (T.phiDerivative t x) x :=
  (T.hasDerivAt_output t _ (T.capital_pos t hx)).comp x (T.hasDerivAt_capital t hx)

theorem capital_eq_ratio_mul_phi (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    T.capital t x = x * T.phi t x :=
  (div_eq_iff (ne_of_gt (T.phi_pos t hx))).mp (T.ratio_capital t hx)

/-- The 2004 elasticity equation, now with the inverse actually constructed. -/
theorem elasticity (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    T.phiDerivative t x * x / T.phi t x =
      T.share t (T.capital t x) / (1 - T.share t (T.capital t x)) := by
  apply UzawaElasticity.output_capitalOutput_elasticity (T.hasDerivAt_capital t hx)
    (T.hasDerivAt_output t _ (T.capital_pos t hx))
    (T.phi_pos t hx) (T.share_lt_one t _ (T.capital_pos t hx))
  filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
  exact T.capital_eq_ratio_mul_phi t hu

/-- The added quantifier: shares agree at every positive capital/output
coordinate, across dates. Constancy on one path is insufficient. -/
def SharesInvariant (T : Technology) (reference : ℝ) : Prop :=
  ∀ t x, 0 < x → T.share t (T.capital t x) =
    T.share reference (T.capital reference x)

/-- The separation factor is defined from the technologies, not from a path. -/
noncomputable def technology (T : Technology) (reference t : ℝ) : ℝ :=
  T.phi t 1 / T.phi reference 1

theorem technology_pos (T : Technology) (reference t : ℝ) :
    0 < T.technology reference t :=
  div_pos (T.phi_pos t zero_lt_one) (T.phi_pos reference zero_lt_one)

@[simp] theorem technology_reference (T : Technology) (reference : ℝ) :
    T.technology reference reference = 1 :=
  div_self (ne_of_gt (T.phi_pos reference zero_lt_one))

/-- Equal shares imply that the ratio of the two coordinate technologies
has derivative zero throughout the positive half-line. -/
theorem hasDerivAt_phi_ratio_zero (T : Technology) (reference : ℝ)
    (hinvariant : T.SharesInvariant reference) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u => T.phi t u / T.phi reference u) 0 x := by
  have ht := ne_of_gt (T.phi_pos t hx)
  have hr := ne_of_gt (T.phi_pos reference hx)
  have heq : T.phiDerivative t x * x / T.phi t x =
      T.phiDerivative reference x * x / T.phi reference x := by
    rw [T.elasticity t hx, T.elasticity reference hx, hinvariant t x hx]
  have hcross : T.phiDerivative t x * T.phi reference x =
      T.phi t x * T.phiDerivative reference x := by
    apply mul_right_cancel₀ (ne_of_gt hx)
    nlinarith [(div_eq_div_iff ht hr).mp heq]
  convert! (T.hasDerivAt_phi t hx).fun_div (T.hasDerivAt_phi reference hx) hr using 1
  rw [hcross]
  simp

/-- The mean value theorem performs the separation step on a connected domain.
No integration constant or domain-wide identity is silently assumed. -/
theorem separation (T : Technology) (reference : ℝ)
    (hinvariant : T.SharesInvariant reference) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    T.phi t x = T.technology reference t * T.phi reference x := by
  have hd (u : ℝ) (hu : 0 < u) :
      HasDerivAt (fun v => T.phi t v / T.phi reference v) 0 u :=
    T.hasDerivAt_phi_ratio_zero reference hinvariant t hu
  have heq : T.phi t x / T.phi reference x = T.phi t 1 / T.phi reference 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
      (fun u hu => (hd u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hd u hu).deriv) hx (by norm_num)
  exact (div_eq_iff (ne_of_gt (T.phi_pos reference hx))).mp heq

/-- Reconstruct the original intensive production function from separation.
This holds for every positive capital input, not only an observed path. -/
theorem intensive_representation (T : Technology) (reference : ℝ)
    (hinvariant : T.SharesInvariant reference) (t : ℝ) {k : ℝ} (hk : 0 < k) :
    T.output t k = T.technology reference t *
      T.output reference (k / T.technology reference t) := by
  let x := T.ratio t k
  have hx : 0 < x := T.ratio_pos t hk
  have hinv : T.capital t x = k := T.capital_ratio t hk
  have hsep := T.separation reference hinvariant t hx
  have hscaled : k / T.technology reference t = T.capital reference x := by
    apply (div_eq_iff (ne_of_gt (T.technology_pos reference t))).mpr
    calc
      k = T.capital t x := hinv.symm
      _ = x * T.phi t x := T.capital_eq_ratio_mul_phi t hx
      _ = T.capital reference x * T.technology reference t := by
        rw [hsep, T.capital_eq_ratio_mul_phi reference hx]
        ring
  calc
    T.output t k = T.phi t x := by simp only [phi, hinv]
    _ = T.technology reference t * T.phi reference x := hsep
    _ = _ := by rw [hscaled]; rfl

/-- The CRS technology associated with the intensive production function. -/
noncomputable def production (T : Technology) (t K L : ℝ) : ℝ :=
  L * T.output t (K / L)

/-- The homogenized intensive technology really is the original F whenever
F has constant returns and its labor-one slice is `T.output`. -/
theorem production_eq_original (T : Technology) {F : ℝ → ℝ → ℝ → ℝ}
    (t : ℝ) {K L : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hslice : ∀ k, 0 < k → T.output t k = F k 1 t)
    (hCRS : ∀ k l a, 0 < k → 0 < l → 0 < a →
      F (a * k) (a * l) t = a * F k l t) :
    T.production t K L = F K L t := by
  have h := hCRS (K / L) 1 L (div_pos hK hL) zero_lt_one hL
  have hdiv : L * (K / L) = K := by field_simp
  rw [hdiv, mul_one] at h
  rw [production, hslice _ (div_pos hK hL)]
  exact h.symm

/-- The repaired domain-wide representation obtained through the elasticity
proof. The reference function is the original technology at `reference`. -/
theorem production_representation (T : Technology) (reference : ℝ)
    (hinvariant : T.SharesInvariant reference) (t : ℝ) {K L : ℝ}
    (hK : 0 < K) (hL : 0 < L) :
    T.production t K L =
      T.production reference K (T.technology reference t * L) := by
  unfold production
  rw [T.intensive_representation reference hinvariant t (div_pos hK hL)]
  have harg : K / L / T.technology reference t = K / (T.technology reference t * L) := by
    rw [div_div, mul_comm L]
  rw [harg]
  ring

/-- Transfer the domain-wide representation back to the original CRS F.
The reference-date function is unchanged, preserving any additional
neoclassical properties of that function without inferring them from a path. -/
theorem original_production_representation (T : Technology) (reference : ℝ)
    (hinvariant : T.SharesInvariant reference) {F : ℝ → ℝ → ℝ → ℝ}
    (hslice : ∀ t k, 0 < k → T.output t k = F k 1 t)
    (hCRS : ∀ t k l a, 0 < k → 0 < l → 0 < a →
      F (a * k) (a * l) t = a * F k l t)
    (t : ℝ) {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    F K L t = F K (T.technology reference t * L) reference := by
  calc
    F K L t = T.production t K L :=
      (T.production_eq_original t hK hL (hslice t) (hCRS t)).symm
    _ = T.production reference K (T.technology reference t * L) :=
      T.production_representation reference hinvariant t hK hL
    _ = _ := T.production_eq_original reference hK
      (mul_pos (T.technology_pos reference t) hL) (hslice reference) (hCRS reference)

/-- Separation identifies the same technology factor at any positive ratio. -/
theorem technology_eq_phi_ratio (T : Technology) (reference : ℝ)
    (hinvariant : T.SharesInvariant reference) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    T.technology reference t = T.phi t x / T.phi reference x := by
  apply (eq_div_iff (ne_of_gt (T.phi_pos reference hx))).mpr
  exact (T.separation reference hinvariant t hx).symm

/-- Translate observed production into the capital/output coordinates. -/
theorem phi_of_production (T : Technology) (t : ℝ) {K L Y : ℝ}
    (hK : 0 < K) (hL : 0 < L) (hY : 0 < Y)
    (hproduction : Y = T.production t K L) :
    T.phi t (K / Y) = Y / L := by
  have hf : T.output t (K / L) = Y / L := by
    rw [hproduction, production]
    field_simp
  have hx : T.ratio t (K / L) = K / Y := by
    unfold ratio
    rw [hf]
    field_simp
  rw [← hx]
  simp only [phi, T.capital_ratio t (div_pos hK hL), hf]

/-- Accounting calibrates the factor derived by separation to the exponential
index. Only the rate-equality lemma is shared with the Schlicht proof;
its representation theorem is not used. -/
theorem technology_eq_balanced_growth (T : Technology) (p : Uzawa.BalancedGrowthData)
    (hinvariant : T.SharesInvariant p.start)
    (hK : 0 < p.capitalInitial) (hL : 0 < p.laborInitial)
    (hC : 0 ≤ p.consumptionInitial) (hI : 0 < p.investmentInitial)
    (hresource : ∀ t, p.start ≤ t → p.output t = p.consumption t + p.investment t)
    (haccum : ∀ t, p.start ≤ t → HasDerivAt p.capital
      (p.investment t - p.depreciation * p.capital t) t)
    (hproduction : ∀ t, p.start ≤ t →
      p.output t = T.production t (p.capital t) (p.labor t)) :
    ∀ t, p.start ≤ t → T.technology p.start t = p.technology t := by
  have hy0 : 0 < p.outputInitial := by
    have h := hresource p.start le_rfl
    simp only [Uzawa.BalancedGrowthData.output, Uzawa.BalancedGrowthData.consumption,
      Uzawa.BalancedGrowthData.investment, Uzawa.trajectory_start] at h
    linarith
  have hrates := p.outputGrowth_eq_capitalGrowth hC hI hresource haccum
  have hratio (t : ℝ) : p.capital t / p.output t = p.capitalInitial / p.outputInitial := by
    simp only [Uzawa.BalancedGrowthData.capital, Uzawa.BalancedGrowthData.output,
      Uzawa.trajectory]
    rw [← hrates]
    field_simp
  have hphi (t : ℝ) (ht : p.start ≤ t) :
      T.phi t (p.capitalInitial / p.outputInitial) = p.output t / p.labor t := by
    have h := T.phi_of_production t (Uzawa.trajectory_pos hK _ _ _)
      (Uzawa.trajectory_pos hL _ _ _) (Uzawa.trajectory_pos hy0 _ _ _) (hproduction t ht)
    change T.phi t (p.capital t / p.output t) = p.output t / p.labor t at h
    rwa [hratio t] at h
  intro t ht
  rw [T.technology_eq_phi_ratio p.start hinvariant t (div_pos hK hy0),
    hphi t ht, hphi p.start le_rfl, p.output_per_worker t, p.output_per_worker p.start,
    Uzawa.trajectory_start]
  unfold Uzawa.trajectory Uzawa.BalancedGrowthData.technology
  field_simp

/-- The repaired 2004-style theorem: separation supplies the representation;
positive-investment accounting supplies the index's specified growth rate. -/
theorem repaired_labor_augmenting_representation
    (T : Technology) (p : Uzawa.BalancedGrowthData)
    (hinvariant : T.SharesInvariant p.start)
    (hK : 0 < p.capitalInitial) (hL : 0 < p.laborInitial)
    (hC : 0 ≤ p.consumptionInitial) (hI : 0 < p.investmentInitial)
    (hresource : ∀ t, p.start ≤ t → p.output t = p.consumption t + p.investment t)
    (haccum : ∀ t, p.start ≤ t → HasDerivAt p.capital
      (p.investment t - p.depreciation * p.capital t) t)
    (hproduction : ∀ t, p.start ≤ t →
      p.output t = T.production t (p.capital t) (p.labor t)) :
    ∀ t, p.start ≤ t → p.output t =
      T.production p.start (p.capital t) (p.technology t * p.labor t) := by
  intro t ht
  have hk : 0 < p.capital t := Uzawa.trajectory_pos hK _ _ _
  have hl : 0 < p.labor t := Uzawa.trajectory_pos hL _ _ _
  rw [hproduction t ht,
    T.production_representation p.start hinvariant t hk hl,
    T.technology_eq_balanced_growth p hinvariant hK hL hC hI hresource haccum hproduction t ht]

/-- At the initial date use a within-domain derivative; no assumptions about
the technology path before the start date are needed for calibration. -/
theorem hasDerivWithinAt_technology_of_balanced_growth
    (T : Technology) (p : Uzawa.BalancedGrowthData)
    (heq : ∀ t, p.start ≤ t → T.technology p.start t = p.technology t)
    {t : ℝ} (ht : p.start ≤ t) :
    HasDerivWithinAt (T.technology p.start)
      ((p.outputGrowth - p.laborGrowth) * T.technology p.start t) (Ici p.start) t := by
  rw [heq t ht]
  apply (p.hasDerivAt_technology t).hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact heq u hu
  · exact heq t ht

end Technology
end UzawaModern.UzawaSeparation

/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/

/-! # Nonvacuity and an economic application of the repaired elasticity proof -/

namespace UzawaModern.UzawaSeparation.Examples

open Technology

theorem sqrt_share {b k : ℝ} (hb : 0 < b) (hk : 0 < k) :
    (b / (2 * Real.sqrt k)) * k / (b * Real.sqrt k) = 1 / 2 := by
  have hs := Real.sqrt_pos.mpr hk
  have hsq := Real.sq_sqrt hk.le
  field_simp
  nlinarith

theorem sqrt_ratio_square {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    (b * x) ^ 2 / (b * Real.sqrt ((b * x) ^ 2)) = x := by
  rw [Real.sqrt_sq (mul_pos hb hx).le]
  field_simp

/-- Every positive multiplier path supplies the full coordinate structure,
including surjectivity onto all positive capital/output ratios. -/
noncomputable def sqrtTechnology (b : ℝ → ℝ) (hb : ∀ t, 0 < b t) : Technology where
  output t k := b t * Real.sqrt k
  marginal t k := b t / (2 * Real.sqrt k)
  output_pos t k hk := mul_pos (hb t) (Real.sqrt_pos.mpr hk)
  hasDerivAt_output t k hk := by
    convert! (Real.hasDerivAt_sqrt (ne_of_gt hk)).const_mul (b t) using 1
    ring
  share_lt_one t k hk := by rw [sqrt_share (hb t) hk]; norm_num
  ratio_surjective t x hx :=
    ⟨(b t * x) ^ 2, sq_pos_of_pos (mul_pos (hb t) hx), sqrt_ratio_square (hb t) hx⟩

theorem sqrt_capital (b : ℝ → ℝ) (hb : ∀ t, 0 < b t) (t : ℝ)
    {x : ℝ} (hx : 0 < x) :
    (sqrtTechnology b hb).capital t x = (b t * x) ^ 2 := by
  have hk := sq_pos_of_pos (mul_pos (hb t) hx)
  have h := (sqrtTechnology b hb).capital_ratio t hk
  have hr : (sqrtTechnology b hb).ratio t ((b t * x) ^ 2) = x :=
    sqrt_ratio_square (hb t) hx
  rwa [hr] at h

theorem sqrt_phi (b : ℝ → ℝ) (hb : ∀ t, 0 < b t) (t : ℝ)
    {x : ℝ} (hx : 0 < x) : (sqrtTechnology b hb).phi t x = (b t) ^ 2 * x := by
  unfold Technology.phi
  rw [sqrt_capital b hb t hx]
  change b t * Real.sqrt ((b t * x) ^ 2) = _
  rw [Real.sqrt_sq (mul_pos (hb t) hx).le]
  ring

theorem sqrt_shares_invariant (b : ℝ → ℝ) (hb : ∀ t, 0 < b t) (reference : ℝ) :
    (sqrtTechnology b hb).SharesInvariant reference := by
  intro t x hx
  change b t / (2 * Real.sqrt _) * _ / (b t * Real.sqrt _) =
    b reference / (2 * Real.sqrt _) * _ / (b reference * Real.sqrt _)
  rw [sqrt_share (hb t) ((sqrtTechnology b hb).capital_pos t hx),
    sqrt_share (hb reference) ((sqrtTechnology b hb).capital_pos reference hx)]

theorem sqrt_technology (b : ℝ → ℝ) (hb : ∀ t, 0 < b t) (reference t : ℝ) :
    (sqrtTechnology b hb).technology reference t = (b t) ^ 2 / (b reference) ^ 2 := by
  simp only [Technology.technology, sqrt_phi b hb _ zero_lt_one, mul_one]

/-- The same positive-investment economy used for the Schlicht proof. -/
noncomputable def growingTechnology : Technology :=
  sqrtTechnology (fun t => 4 * Real.exp t) (fun t => mul_pos (by norm_num) (Real.exp_pos t))

theorem growing_shares_invariant : growingTechnology.SharesInvariant 0 :=
  sqrt_shares_invariant _ _ 0

theorem growing_production (t : ℝ) : Uzawa.Examples.growingEconomy.output t =
    growingTechnology.production t (Uzawa.Examples.growingEconomy.capital t)
      (Uzawa.Examples.growingEconomy.labor t) := by
  have h := Uzawa.Examples.production_on_path t
  simpa only [Technology.production, growingTechnology, sqrtTechnology,
    Uzawa.Examples.production, Uzawa.BalancedGrowthData.labor,
    Uzawa.Examples.growingEconomy, Uzawa.trajectory, zero_mul,
    Real.exp_zero, mul_one, one_mul, div_one] using h

/-- All premises of the repaired proof are checked, including the global
inverse range and share quantifier. The final theorem uses separation. -/
theorem growing_labor_augmenting (t : ℝ) (ht : 0 ≤ t) :
    Uzawa.Examples.growingEconomy.output t = growingTechnology.production 0
      (Uzawa.Examples.growingEconomy.capital t)
      (Uzawa.Examples.growingEconomy.technology t * Uzawa.Examples.growingEconomy.labor t) := by
  exact growingTechnology.repaired_labor_augmenting_representation
    Uzawa.Examples.growingEconomy growing_shares_invariant
    (by norm_num [Uzawa.Examples.growingEconomy])
    (by norm_num [Uzawa.Examples.growingEconomy])
    (by norm_num [Uzawa.Examples.growingEconomy])
    (by norm_num [Uzawa.Examples.growingEconomy])
    (fun u _ => Uzawa.Examples.resource u)
    (fun u _ => Uzawa.Examples.accumulation u)
    (fun u _ => growing_production u) t ht

/-- The inferred technology factor has rate 2, matching output per worker. -/
theorem growing_technology (t : ℝ) (ht : 0 ≤ t) :
    growingTechnology.technology 0 t = Real.exp (2 * t) := by
  have h := growingTechnology.technology_eq_balanced_growth
    Uzawa.Examples.growingEconomy growing_shares_invariant
    (by norm_num [Uzawa.Examples.growingEconomy])
    (by norm_num [Uzawa.Examples.growingEconomy])
    (by norm_num [Uzawa.Examples.growingEconomy])
    (by norm_num [Uzawa.Examples.growingEconomy])
    (fun u _ => Uzawa.Examples.resource u)
    (fun u _ => Uzawa.Examples.accumulation u)
    (fun u _ => growing_production u) t ht
  simpa [Uzawa.BalancedGrowthData.technology, Uzawa.Examples.growingEconomy] using h

end UzawaModern.UzawaSeparation.Examples

/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/

/-!
Independent checks prompted by comparing Jones-Scrimgeour (2004, 2008)
and Schlicht (2006). These are research audit lemmas, not a completed
formalization of the 2004 paper's neoclassical model or its proof.
-/

namespace UzawaModern.VersionAudit

/-- Zero investment can coexist with positive capital: the coefficient
`gK + depreciation` can be zero. This is the omitted branch in Schlicht. -/
theorem zero_investment_positive_capital :
    (0 + (0 : ℝ)) * 1 = 0 ∧ (0 : ℝ) < 1 := by norm_num

/-- Two observations with fixed capital and proportional effective labor/output
are incompatible with CRS and strict increase in capital. This rules out ANY
such G, rather than only the frozen original production function. -/
theorem no_strict_capital_representation {G : ℝ → ℝ → ℝ} {A b : ℝ}
    (hA : 0 < A) (hb : 1 < b)
    (hCRS : ∀ K L s, 0 < K → 0 < L → 0 < s →
      G (s * K) (s * L) = s * G K L)
    (hinc : StrictMonoOn (fun K => G K A) (Set.Ioi 0))
    (hbase : G 1 A = 1) (hlater : G 1 (b * A) = b) : False := by
  have hbpos : 0 < b := lt_trans zero_lt_one hb
  have hbne : b ≠ 0 := ne_of_gt hbpos
  have hscaled : (1 / b) * (b * A) = A := by field_simp
  have hvalue : G (1 / b) A = 1 := by
    have h := hCRS 1 (b * A) (1 / b) zero_lt_one
      (mul_pos hbpos hA) (one_div_pos.mpr hbpos)
    simpa only [mul_one, hscaled, hlater, one_div_mul_cancel hbne] using h
  have hless : 1 / b < (1 : ℝ) := (div_lt_one hbpos).mpr hb
  have h := hinc (one_div_pos.mpr hbpos) (by norm_num) hless
  change G (1 / b) A < G 1 A at h
  rw [hvalue, hbase] at h
  exact lt_irrefl _ h

/-- Apply the two-point obstruction to A(t)=a*exp(t), Y(t)=exp(t), K(t)=1.
Every positive normalization a is covered. Exponential path assumptions
are explicit; the production model's curvature/Inada properties are not
asserted to have been formalized by this lemma. -/
theorem zero_investment_no_neoclassical_representation
    {G : ℝ → ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hCRS : ∀ K L s, 0 < K → 0 < L → 0 < s →
      G (s * K) (s * L) = s * G K L)
    (hinc : StrictMonoOn (fun K => G K a) (Set.Ioi 0))
    (hpath : ∀ t, 0 ≤ t → G 1 (a * Real.exp t) = Real.exp t) : False := by
  apply no_strict_capital_representation ha
    (Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)) hCRS hinc
  · simpa using hpath 0 le_rfl
  · simpa [mul_comm] using hpath 1 (by norm_num)


end UzawaModern.VersionAudit

#print axioms UzawaModern.Uzawa.trajectory_start
#print axioms UzawaModern.Uzawa.trajectory_pos
#print axioms UzawaModern.Uzawa.hasDerivAt_trajectory
#print axioms UzawaModern.Uzawa.trajectory_one
#print axioms UzawaModern.Uzawa.trajectory_two
#print axioms UzawaModern.Uzawa.rate_eq_of_weighted_moments
#print axioms UzawaModern.Uzawa.outputGrowth_eq_investmentGrowth
#print axioms UzawaModern.Uzawa.investmentGrowth_eq_capitalGrowth
#print axioms UzawaModern.Uzawa.BalancedGrowthData.technology_pos
#print axioms UzawaModern.Uzawa.BalancedGrowthData.technology_start
#print axioms UzawaModern.Uzawa.BalancedGrowthData.hasDerivAt_technology
#print axioms UzawaModern.Uzawa.BalancedGrowthData.technology_growthRate
#print axioms UzawaModern.Uzawa.BalancedGrowthData.technology_mul_labor
#print axioms UzawaModern.Uzawa.BalancedGrowthData.output_per_worker
#print axioms UzawaModern.Uzawa.BalancedGrowthData.outputGrowth_eq_capitalGrowth
#print axioms UzawaModern.Uzawa.BalancedGrowthData.labor_augmenting_representation
#print axioms UzawaModern.UzawaElasticity.hasDerivAt_capitalOutputRatio
#print axioms UzawaModern.UzawaElasticity.capitalOutputRatio_derivative_pos
#print axioms UzawaModern.UzawaElasticity.output_capitalOutput_elasticity
#print axioms UzawaModern.Uzawa.Examples.resource
#print axioms UzawaModern.Uzawa.Examples.accumulation
#print axioms UzawaModern.Uzawa.Examples.production_on_path
#print axioms UzawaModern.Uzawa.Examples.constant_returns
#print axioms UzawaModern.Uzawa.Examples.labor_augmenting
#print axioms UzawaModern.Uzawa.Examples.levels_positive
#print axioms UzawaModern.UzawaSeparation.Technology.ratio_pos
#print axioms UzawaModern.UzawaSeparation.Technology.hasDerivAt_ratio
#print axioms UzawaModern.UzawaSeparation.Technology.ratio_derivative_pos
#print axioms UzawaModern.UzawaSeparation.Technology.ratio_strictMonoOn
#print axioms UzawaModern.UzawaSeparation.Technology.capital_pos
#print axioms UzawaModern.UzawaSeparation.Technology.ratio_capital
#print axioms UzawaModern.UzawaSeparation.Technology.capital_ratio
#print axioms UzawaModern.UzawaSeparation.Technology.capital_strictMonoOn
#print axioms UzawaModern.UzawaSeparation.Technology.capital_image
#print axioms UzawaModern.UzawaSeparation.Technology.continuousAt_capital
#print axioms UzawaModern.UzawaSeparation.Technology.hasDerivAt_capital
#print axioms UzawaModern.UzawaSeparation.Technology.phi_pos
#print axioms UzawaModern.UzawaSeparation.Technology.hasDerivAt_phi
#print axioms UzawaModern.UzawaSeparation.Technology.capital_eq_ratio_mul_phi
#print axioms UzawaModern.UzawaSeparation.Technology.elasticity
#print axioms UzawaModern.UzawaSeparation.Technology.technology_pos
#print axioms UzawaModern.UzawaSeparation.Technology.technology_reference
#print axioms UzawaModern.UzawaSeparation.Technology.hasDerivAt_phi_ratio_zero
#print axioms UzawaModern.UzawaSeparation.Technology.separation
#print axioms UzawaModern.UzawaSeparation.Technology.intensive_representation
#print axioms UzawaModern.UzawaSeparation.Technology.production_eq_original
#print axioms UzawaModern.UzawaSeparation.Technology.production_representation
#print axioms UzawaModern.UzawaSeparation.Technology.original_production_representation
#print axioms UzawaModern.UzawaSeparation.Technology.technology_eq_phi_ratio
#print axioms UzawaModern.UzawaSeparation.Technology.phi_of_production
#print axioms UzawaModern.UzawaSeparation.Technology.technology_eq_balanced_growth
#print axioms UzawaModern.UzawaSeparation.Technology.repaired_labor_augmenting_representation
#print axioms UzawaModern.UzawaSeparation.Technology.hasDerivWithinAt_technology_of_balanced_growth
#print axioms UzawaModern.UzawaSeparation.Examples.sqrt_share
#print axioms UzawaModern.UzawaSeparation.Examples.sqrt_ratio_square
#print axioms UzawaModern.UzawaSeparation.Examples.sqrt_capital
#print axioms UzawaModern.UzawaSeparation.Examples.sqrt_phi
#print axioms UzawaModern.UzawaSeparation.Examples.sqrt_shares_invariant
#print axioms UzawaModern.UzawaSeparation.Examples.sqrt_technology
#print axioms UzawaModern.UzawaSeparation.Examples.growing_shares_invariant
#print axioms UzawaModern.UzawaSeparation.Examples.growing_production
#print axioms UzawaModern.UzawaSeparation.Examples.growing_labor_augmenting
#print axioms UzawaModern.UzawaSeparation.Examples.growing_technology
#print axioms UzawaModern.VersionAudit.zero_investment_positive_capital
#print axioms UzawaModern.VersionAudit.no_strict_capital_representation
#print axioms UzawaModern.VersionAudit.zero_investment_no_neoclassical_representation
