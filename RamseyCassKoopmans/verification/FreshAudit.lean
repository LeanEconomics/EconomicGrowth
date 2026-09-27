import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
set_option autoImplicit false


/-!
# Growth paths and finite welfare

Original work released under the Unlicense. A path is defined on real time,
but feasibility is imposed only for nonnegative time. Controls are continuous
and capital satisfies the resource equation classically. This is an explicit
regularity restriction, not a formalization of every measurable control.

Investment may be negative in `FeasiblePath` (Koopmans's resource convention).
Cass's additional nonnegative-investment restriction is `NonnegativeInvestment`.
Neither convergence nor optimality is part of feasibility.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

structure FeasiblePath (f : ℝ → ℝ) (m : ℝ) where
  capital : ℝ → ℝ
  consumption : ℝ → ℝ
  investment : ℝ → ℝ
  capital_nonneg : ∀ t, 0 ≤ t → 0 ≤ capital t
  consumption_pos : ∀ t, 0 ≤ t → 0 < consumption t
  consumption_continuous : ContinuousOn consumption (Ici 0)
  investment_continuous : ContinuousOn investment (Ici 0)
  resource : ∀ t, 0 ≤ t → consumption t + investment t = f (capital t)
  dynamics : ∀ t, 0 ≤ t →
    HasDerivAt capital (investment t - m * capital t) t

def FeasiblePath.NonnegativeInvestment {f : ℝ → ℝ} {m : ℝ}
    (a : FeasiblePath f m) : Prop := ∀ t, 0 ≤ t → 0 ≤ a.investment t

theorem FeasiblePath.capital_continuous {f : ℝ → ℝ} {m : ℝ}
    (a : FeasiblePath f m) : ContinuousOn a.capital (Ici 0) := by
  intro t ht
  exact (a.dynamics t ht).continuousAt.continuousWithinAt

noncomputable def discount (d t : ℝ) : ℝ := Real.exp (-d * t)

theorem discount_pos (d t : ℝ) : 0 < discount d t := Real.exp_pos _

theorem discount_continuous (d : ℝ) : Continuous (discount d) := by
  unfold discount
  fun_prop

theorem hasDerivAt_discount (d t : ℝ) :
    HasDerivAt (discount d) (-d * discount d t) t := by
  change HasDerivAt (fun s : ℝ => Real.exp (-d * s)) (-d * Real.exp (-d * t)) t
  simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id t).const_mul (-d)).exp

/-- Finite-horizon welfare is always a finite-interval integral. Infinite welfare
is specified using a limit, so a divergent Bochner integral is never mistaken for zero. -/
noncomputable def welfare (U w c : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, w t * U (c t)

def HasWelfare (U w c : ℝ → ℝ) (J : ℝ) : Prop :=
  Tendsto (welfare U w c) atTop (𝓝 J)

def boundary (p ka kb : ℝ → ℝ) (t : ℝ) : ℝ := p t * (ka t - kb t)

/-- Conversion from Cass's current-value costate to its present-value price. -/
theorem hasDerivAt_discounted_costate {q : ℝ → ℝ} {d m mu mp t : ℝ}
    (hq : HasDerivAt q ((d + m) * q t - mu * mp) t) :
    HasDerivAt (fun s => discount d s * q s)
      (m * (discount d t * q t) - discount d t * mu * mp) t := by
  convert (hasDerivAt_discount d t).mul hq using 1
  ring

end RamseyCassKoopmans


/-!
# Checked polynomial identities for Ramsey–Cass–Koopmans verification

The correspondingly named TheoryDebugger cases are stored under
`verification/theorydebugger/inputs`. Their generated certificates independently
check the exact polynomial abstractions with Lean. This module provides reusable
named lemmas, without importing the generated certificates' shared namespace.

None of these algebra lemmas alone asserts existence or optimality of a path.
-/

namespace RamseyCassKoopmans

/-- Discounting cancels the pure-discount term in the current-value costate law. -/
theorem discounted_costate_normalization (qdot d m q u fprime : ℝ)
    (h : qdot = (d + m) * q - u * fprime) :
    qdot - d * q = m * q - u * fprime := by
  rw [h]
  ring

/-- Normalized boundary derivative after the two capital laws and the costate
law are substituted. `K` and `Z` are candidate-minus-competitor gaps. -/
theorem present_value_boundary_derivative (p m w u fprime K Z : ℝ) :
    (m * p - w * u * fprime) * K + p * (Z - m * K) =
      p * Z - w * u * fprime * K := by
  ring

/-- Pointwise counterpart of the finite-horizon welfare identity. `bdot` is the
derivative of the discounted capital-value gap divided by the discount factor.
The named feasibility and costate equations are explicit; the TheoryDebugger
case `cass_pointwise_welfare_identity` substitutes these same equations first
and uses candidate-minus-competitor gap variables. -/
theorem cass_pointwise_welfare_identity
    (U0 U1 f0 f1 c0 c1 z0 z1 k0 k1 fprime u q m d qdot k0dot k1dot : ℝ)
    (hresource0 : c0 + z0 = f0) (hresource1 : c1 + z1 = f1)
    (hcapital0 : k0dot = z0 - m * k0) (hcapital1 : k1dot = z1 - m * k1)
    (hcostate : qdot = (d + m) * q - u * fprime) :
    U0 - U1 =
      (U0 - U1 - u * (c0 - c1)) +
      u * (f0 - f1 - fprime * (k0 - k1)) +
      (q - u) * (z0 - z1) -
      ((qdot - d * q) * (k0 - k1) + q * (k0dot - k1dot)) := by
  rw [← hresource0, ← hresource1, hcapital0, hcapital1, hcostate]
  ring

/-- Present-value formulation of the same decomposition. This matches
TheoryDebugger's `present_value_welfare_identity` after feasibility substitution
and the separately checked `present_value_boundary_derivative` identity. -/
theorem present_value_welfare_identity
    (Ua Ub fa fb ca cb za zb ka kb mp mu p m w pd : ℝ)
    (hresourceA : ca + za = fa) (hresourceB : cb + zb = fb)
    (hcostate : pd = m * p - w * mu * mp) :
    w * (Ua - Ub) +
      (pd * (ka - kb) + p * ((za - m * ka) - (zb - m * kb))) =
      w * (Ua - Ub - mu * (ca - cb)) +
      w * mu * (fa - fb - mp * (ka - kb)) +
      (p - w * mu) * (za - zb) := by
  rw [← hresourceA, ← hresourceB, hcostate]
  ring

/-- Supporting inequalities, nonnegative welfare weight and allocation
complementarity give the pointwise comparison used by the analytic theorem. -/
theorem present_value_comparison_nonneg
    (Ua Ub fa fb ca cb za zb ka kb mp mu p m w pd : ℝ)
    (hresourceA : ca + za = fa) (hresourceB : cb + zb = fb)
    (hutility : 0 ≤ Ua - Ub - mu * (ca - cb))
    (htechnology : 0 ≤ fa - fb - mp * (ka - kb))
    (hw : 0 ≤ w) (hmu : 0 ≤ mu)
    (hallocation : 0 ≤ (p - w * mu) * (za - zb))
    (hcostate : pd = m * p - w * mu * mp) :
    0 ≤ w * (Ua - Ub) +
      (pd * (ka - kb) + p * ((za - m * ka) - (zb - m * kb))) := by
  rw [present_value_welfare_identity Ua Ub fa fb ca cb za zb ka kb mp mu p m w pd
    hresourceA hresourceB hcostate]
  exact add_nonneg (add_nonneg (mul_nonneg hw hutility)
    (mul_nonneg (mul_nonneg hw hmu) htechnology)) hallocation

/-- Complementarity permits a strict costate gap at zero investment. -/
theorem corner_does_not_imply_euler_equality :
    ¬ (∀ (u q z : ℝ), 0 < u → 0 < q → 0 ≤ z → q ≤ u →
      (q - u) * z = 0 → q = u) := by
  intro h
  have hx := h 2 1 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at hx

/-- Strictly positive investment repairs the Euler-equality inference. -/
theorem interior_implies_euler_equality (u q z : ℝ)
    (hcomplementarity : (q - u) * z = 0) (hz : 0 < z) : q = u := by
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcomplementarity).resolve_right (ne_of_gt hz))

/-- The candidate's complementarity conditions make the investment gap term
nonnegative for every competitor with nonnegative investment. -/
theorem complementarity_welfare_term (u q z otherz : ℝ)
    (hgap : q ≤ u) (hcomplementarity : (q - u) * z = 0)
    (hother : 0 ≤ otherz) : 0 ≤ (q - u) * (z - otherz) := by
  have hprod : (q - u) * otherz ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hgap) hother
  nlinarith

/-- Concavity remainders and the complementarity remainder add nonnegatively. -/
theorem nonnegative_welfare_remainders (RU RF Rz u : ℝ)
    (hRU : 0 ≤ RU) (hRF : 0 ≤ RF) (hRz : 0 ≤ Rz) (hu : 0 ≤ u) :
    0 ≤ RU + u * RF + Rz := by
  positivity

/-- The competitor-minus-candidate welfare bound uses candidate-minus-competitor
terminal capital. This is an algebraic implication, not an integration theorem. -/
theorem correct_terminal_bound (A p k0 k1 : ℝ)
    (h : A ≤ -1 * p * (k1 - k0)) : A ≤ p * (k0 - k1) := by
  nlinarith

/-- Reversing that terminal-capital sign is invalid even for positive prices
and positive terminal capital in both paths. -/
theorem reversed_terminal_bound_is_invalid :
    ¬ (∀ (A p k0 k1 : ℝ), 0 < p → A ≤ -1 * p * (k1 - k0) →
      A ≤ p * (k1 - k0)) := by
  intro h
  have hx := h 1 1 2 1 (by norm_num) (by norm_num)
  norm_num at hx

/-- Population weighting cancels population growth from the stationary rate. -/
theorem population_weighted_stationary_rate (d m rho n depreciation : ℝ)
    (hd : d = rho - n) (hm : m = n + depreciation) :
    d + m = rho + depreciation := by
  linarith

end RamseyCassKoopmans


/-!
# Supporting inequalities from actual concave functions

These results connect utility and production concavity to the tangent bounds
used in the welfare verification theorem. They include competitors on either
side of the candidate, and do not assume the desired supporting inequality.
Only the derivative at the candidate point is required.
-/

namespace RamseyCassKoopmans

open Set

/-- A differentiable concave function lies below its tangent at the candidate.
The competitor may be on either side, or equal to the candidate. -/
theorem concave_support {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
    (hconc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hderiv : HasDerivAt f f' x) :
    f y - f x ≤ f' * (y - x) := by
  rcases lt_trichotomy y x with hlt | heq | hgt
  · have hs := hconc.le_slope_of_hasDerivAt hy hx hlt hderiv
    rw [slope_def_field] at hs
    have hmul := (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    nlinarith
  · subst y
    simp
  · have hs := hconc.slope_le_of_hasDerivAt hx hy hgt hderiv
    rw [slope_def_field] at hs
    exact (div_le_iff₀ (sub_pos.mpr hgt)).mp hs

/-- Strict concavity makes the tangent inequality strict at every distinct
competitor, including admissible endpoints of the domain. -/
theorem strict_concave_support {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
    (hconc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hderiv : HasDerivAt f f' x) (hne : y ≠ x) :
    f y - f x < f' * (y - x) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs := hconc.lt_slope_of_hasDerivAt hy hx hlt hderiv
    rw [slope_def_field] at hs
    have hmul := (lt_div_iff₀ (sub_pos.mpr hlt)).mp hs
    nlinarith
  · have hs := hconc.slope_lt_of_hasDerivAt hx hy hgt hderiv
    rw [slope_def_field] at hs
    exact (div_lt_iff₀ (sub_pos.mpr hgt)).mp hs

/-- The source welfare comparison's concavity remainder is nonnegative. -/
theorem concavity_remainder_nonneg {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
    (hconc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hderiv : HasDerivAt f f' x) :
    0 ≤ f x - f y - f' * (x - y) := by
  have h := concave_support hconc hx hy hderiv
  nlinarith

/-- A distinct competitor gives a strictly positive concavity remainder. -/
theorem concavity_remainder_pos {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
    (hconc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hderiv : HasDerivAt f f' x) (hne : y ≠ x) :
    0 < f x - f y - f' * (x - y) := by
  have h := strict_concave_support hconc hx hy hderiv hne
  nlinarith

/-- Under strict concavity the remainder vanishes precisely at the candidate.
This pointwise fact alone is not an integrated uniqueness theorem. -/
theorem concavity_remainder_eq_zero_iff {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
    (hconc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hderiv : HasDerivAt f f' x) :
    f x - f y - f' * (x - y) = 0 ↔ y = x := by
  constructor
  · intro hzero
    by_contra hne
    have hpos := concavity_remainder_pos hconc hx hy hderiv hne
    linarith
  · intro heq
    subst y
    simp

end RamseyCassKoopmans


/-!
# Vanishing terminal capital terms

The welfare comparison retains the terminal term `p t * (k₀ t - k₁ t)`.
This file proves its disappearance from explicit economic hypotheses. In particular,
convergence of consumption to a positive level and continuity of marginal utility there
yield a finite marginal-utility limit; positive discounting then makes prices vanish.
No Euler equation alone is asserted to imply either convergence or optimality.
-/

open Filter Set
open scoped Topology

namespace RamseyCassKoopmans.Terminal

/-- Bounded nonnegative capital paths have a vanishing terminal difference whenever
the present-value price tends to zero. The hypotheses concern nonnegative times only. -/
theorem terminal_tendsto_zero_of_bounded_capital
    {p k₀ k₁ : ℝ → ℝ} {K : ℝ}
    (hp : Tendsto p atTop (𝓝 0))
    (h₀ : ∀ t, 0 ≤ t → 0 ≤ k₀ t ∧ k₀ t ≤ K)
    (h₁ : ∀ t, 0 ≤ t → 0 ≤ k₁ t ∧ k₁ t ≤ K) :
    Tendsto (fun t => p t * (k₀ t - k₁ t)) atTop (𝓝 0) := by
  apply hp.zero_mul_isBoundedUnder_le
  apply isBoundedUnder_of_eventually_le (a := K)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  change ‖k₀ t - k₁ t‖ ≤ K
  rw [Real.norm_eq_abs, abs_le]
  have hzero := h₀ t ht
  have hone := h₁ t ht
  constructor <;> linarith

/-- A positive constant discount rate makes the discount factor vanish. -/
theorem discount_factor_tendsto_zero {d : ℝ} (hd : 0 < d) :
    Tendsto (fun t : ℝ => Real.exp (-d * t)) atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hd))

/-- Positive discounting and a finite marginal-utility limit imply vanishing
present-value prices. No sign assumption on marginal utility is needed for this limit. -/
theorem discounted_price_tendsto_zero
    {d μ : ℝ} {mu : ℝ → ℝ} (hd : 0 < d)
    (hmu : Tendsto mu atTop (𝓝 μ)) :
    Tendsto (fun t => Real.exp (-d * t) * mu t) atTop (𝓝 0) := by
  simpa only [zero_mul] using (discount_factor_tendsto_zero hd).mul hmu

/-- Discounted marginal utility times a bounded capital difference tends to zero. -/
theorem discounted_terminal_tendsto_zero
    {d μ K : ℝ} {mu k₀ k₁ : ℝ → ℝ} (hd : 0 < d)
    (hmu : Tendsto mu atTop (𝓝 μ))
    (h₀ : ∀ t, 0 ≤ t → 0 ≤ k₀ t ∧ k₀ t ≤ K)
    (h₁ : ∀ t, 0 ≤ t → 0 ≤ k₁ t ∧ k₁ t ≤ K) :
    Tendsto (fun t => (Real.exp (-d * t) * mu t) * (k₀ t - k₁ t))
      atTop (𝓝 0) :=
  terminal_tendsto_zero_of_bounded_capital (discounted_price_tendsto_zero hd hmu) h₀ h₁

/-- Consumption convergence plus continuity of marginal utility at the limit gives
the price-decay hypothesis used in the infinite-horizon comparison. A positive
consumption limit is economically natural but continuity is the exact analytic premise. -/
theorem discounted_price_tendsto_zero_of_consumption_limit
    {d cstar : ℝ} {c marginalUtility : ℝ → ℝ} (hd : 0 < d)
    (hc : Tendsto c atTop (𝓝 cstar))
    (hmu : ContinuousAt marginalUtility cstar) :
    Tendsto (fun t => Real.exp (-d * t) * marginalUtility (c t)) atTop (𝓝 0) :=
  discounted_price_tendsto_zero hd (hmu.tendsto.comp hc)

/-- A feasible capital path cannot cross above a capacity `K` at which net output
is nonpositive, provided net output remains nonpositive above that capacity.
The proof uses a strictly increasing comparison barrier and then lets its slope vanish.
Right derivatives suffice, matching the piecewise smooth admissibility in Koopmans. -/
theorem capital_le_capacity
    {k c f : ℝ → ℝ} {m K : ℝ}
    (hk : ContinuousOn k (Ici 0))
    (hd : ∀ t, 0 ≤ t →
      HasDerivWithinAt k (f (k t) - c t - m * k t) (Ici t) t)
    (hc : ∀ t, 0 ≤ t → 0 ≤ c t)
    (hK : ∀ x, K ≤ x → f x ≤ m * x)
    (hinit : k 0 ≤ K) :
    ∀ t, 0 ≤ t → k t ≤ K := by
  intro T hT
  apply le_of_forall_pos_le_add
  intro ε hε
  let a : ℝ := ε / (T + 1)
  have ha : 0 < a := div_pos hε (by linarith)
  have hbarrier : ∀ ⦃t⦄, t ∈ Icc 0 T → k t ≤ K + a * (t + 1) := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (b := T) (B := fun t => K + a * (t + 1))
      (hf' := fun t ht => hd t ht.1)
      (B' := fun _ => a)
    · exact hk.mono (fun _ hx => hx.1)
    · linarith
    · intro t
      convert ((hasDerivAt_id t).add_const 1).const_mul a |>.const_add K using 1 <;> simp
    · intro t ht heq
      have htk : K ≤ k t := by
        rw [heq]
        have := mul_nonneg (le_of_lt ha) (show 0 ≤ t + 1 by linarith [ht.1])
        linarith
      have hn := hK (k t) htk
      have hct := hc t ht.1
      linarith
  have hfinal := hbarrier ⟨hT, le_rfl⟩
  have haT : a * (T + 1) = ε := by
    dsimp [a]
    exact div_mul_cancel₀ ε (by linarith)
  rwa [haT] at hfinal

/-- The terminal condition follows from explicit production and feasibility bounds,
positive discounting, and convergence of marginal utility. Capital bounds are proved
from the resource equations instead of supplied as assumptions. -/
theorem discounted_terminal_tendsto_zero_of_feasible_paths
    {k₀ k₁ c₀ c₁ f mu : ℝ → ℝ} {d μ m K : ℝ}
    (hd : 0 < d) (hmu : Tendsto mu atTop (𝓝 μ))
    (hK : ∀ x, K ≤ x → f x ≤ m * x)
    (hk₀ : ContinuousOn k₀ (Ici 0))
    (hk₁ : ContinuousOn k₁ (Ici 0))
    (hresource₀ : ∀ t, 0 ≤ t →
      HasDerivWithinAt k₀ (f (k₀ t) - c₀ t - m * k₀ t) (Ici t) t)
    (hresource₁ : ∀ t, 0 ≤ t →
      HasDerivWithinAt k₁ (f (k₁ t) - c₁ t - m * k₁ t) (Ici t) t)
    (hc₀ : ∀ t, 0 ≤ t → 0 ≤ c₀ t)
    (hc₁ : ∀ t, 0 ≤ t → 0 ≤ c₁ t)
    (hcapital₀ : ∀ t, 0 ≤ t → 0 ≤ k₀ t)
    (hcapital₁ : ∀ t, 0 ≤ t → 0 ≤ k₁ t)
    (hinit₀ : k₀ 0 ≤ K) (hinit₁ : k₁ 0 ≤ K) :
    Tendsto (fun t => (Real.exp (-d * t) * mu t) * (k₀ t - k₁ t))
      atTop (𝓝 0) := by
  apply discounted_terminal_tendsto_zero hd hmu
  · exact fun t ht => ⟨hcapital₀ t ht,
      capital_le_capacity hk₀ hresource₀ hc₀ hK hinit₀ t ht⟩
  · exact fun t ht => ⟨hcapital₁ t ht,
      capital_le_capacity hk₁ hresource₁ hc₁ hK hinit₁ t ht⟩

end RamseyCassKoopmans.Terminal


/-!
# Stationary capital in the positive-discount growth model

Cass (1965), p. 236, and Koopmans (1965), pp. 247–248, identify stationary
capital by `f'(k) = d + m`. Here `d` is effective utility discounting and `m`
is depreciation plus population dilution. This file proves stationary existence,
uniqueness, positive consumption and the comparison with the golden-rule stock.

Existence is first proved from **explicit finite brackets**. A separate theorem
derives those brackets from the Inada limits. The brackets are inequalities at
ordinary positive capital stocks; they do not assume existence of a stationary
stock. Uniqueness holds on the entire positive half-line. The strict-concavity
versions derive decreasing marginal product and the positive supporting-line gap
from actual functions.

These are stationary results, not existence or convergence of a nonstationary
optimal trajectory.
-/

namespace RamseyCassKoopmans

open Set
open Filter
open scoped Topology

/-- A continuous, strictly decreasing marginal product crosses a bracketed
target exactly once on positive capital. Uniqueness is not limited to the bracket. -/
theorem existsUnique_positive_root_of_bracket
    (mp : ℝ → ℝ) (target a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (hcont : ContinuousOn mp (Icc a b))
    (hanti : StrictAntiOn mp (Ioi 0))
    (hlower : mp b ≤ target) (hupper : target ≤ mp a) :
    ∃! k : ℝ, 0 < k ∧ mp k = target := by
  obtain ⟨k, hk, heq⟩ := intermediate_value_Icc' hab hcont ⟨hlower, hupper⟩
  have hkpos : 0 < k := lt_of_lt_of_le ha hk.1
  refine ⟨k, ⟨hkpos, heq⟩, ?_⟩
  intro y hy
  exact hanti.injOn hy.1 hkpos (hy.2.trans heq.symm)

/-- The two marginal-product Inada limits provide finite positive brackets for
every positive target. This explicitly connects boundary limits to the IVT. -/
theorem exists_positive_bracket_of_inada
    (mp : ℝ → ℝ) (target : ℝ) (htarget : 0 < target)
    (hatZero : Tendsto mp (𝓝[>] (0 : ℝ)) atTop)
    (hatTop : Tendsto mp atTop (𝓝 (0 : ℝ))) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ mp b < target ∧ target < mp a := by
  have haevent : ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  obtain ⟨a, ha, hma⟩ := (haevent.and (hatZero.eventually_gt_atTop target)).exists
  have hbevent : ∀ᶠ b : ℝ in atTop, mp b < target :=
    hatTop.eventually (gt_mem_nhds htarget)
  obtain ⟨b, hab, hmb⟩ := ((eventually_gt_atTop a).and hbevent).exists
  exact ⟨a, b, ha, hab, hmb, hma⟩

/-- A full Inada-based root result, with continuity and strict antitonicity on
positive capital. There is no assumed stationary root or finite bracket. -/
theorem existsUnique_positive_root_of_inada
    (mp : ℝ → ℝ) (target : ℝ) (htarget : 0 < target)
    (hcont : ContinuousOn mp (Ioi 0))
    (hanti : StrictAntiOn mp (Ioi 0))
    (hatZero : Tendsto mp (𝓝[>] (0 : ℝ)) atTop)
    (hatTop : Tendsto mp atTop (𝓝 (0 : ℝ))) :
    ∃! k : ℝ, 0 < k ∧ mp k = target := by
  obtain ⟨a, b, ha, hab, hmb, hma⟩ :=
    exists_positive_bracket_of_inada mp target htarget hatZero hatTop
  exact existsUnique_positive_root_of_bracket mp target a b ha hab.le
    (hcont.mono (fun _ hk => lt_of_lt_of_le ha hk.1)) hanti hmb.le hma.le

/-- For a strictly concave technology, its derivative is strictly decreasing
on positive capital. Differentiability at zero is deliberately not required. -/
theorem production_deriv_strictAnti
    (f : ℝ → ℝ)
    (hconc : StrictConcaveOn ℝ (Ici 0) f)
    (hdiff : ∀ k : ℝ, 0 < k → DifferentiableAt ℝ f k) :
    StrictAntiOn (deriv f) (Ioi 0) := by
  have hsub : Ioi (0 : ℝ) ⊆ Ici (0 : ℝ) := by
    intro k hk
    change 0 < k at hk
    change 0 ≤ k
    exact hk.le
  apply (hconc.subset hsub (convex_Ioi (0 : ℝ))).strictAntiOn_deriv
  exact hdiff

/-- The source stationary condition has a unique positive solution under
strict concavity, differentiability and a finite bracket for marginal product. -/
theorem existsUnique_stationary_capital_of_bracket
    (f : ℝ → ℝ) (d m a b : ℝ)
    (hconc : StrictConcaveOn ℝ (Ici 0) f)
    (hdiff : ∀ k : ℝ, 0 < k → DifferentiableAt ℝ f k)
    (ha : 0 < a) (hab : a ≤ b)
    (hcont : ContinuousOn (deriv f) (Icc a b))
    (hlower : deriv f b ≤ d + m) (hupper : d + m ≤ deriv f a) :
    ∃! k : ℝ, 0 < k ∧ deriv f k = d + m :=
  existsUnique_positive_root_of_bracket (deriv f) (d + m) a b ha hab hcont
    (production_deriv_strictAnti f hconc hdiff) hlower hupper

/-- Cass's stationary-capital root from strict concavity and the two
marginal-product Inada limits. The derivative need only be continuous on the
positive half-line; it need not exist at zero. -/
theorem existsUnique_stationary_capital_of_inada
    (f : ℝ → ℝ) (d m : ℝ) (hpositive : 0 < d + m)
    (hconc : StrictConcaveOn ℝ (Ici 0) f)
    (hdiff : ∀ k : ℝ, 0 < k → DifferentiableAt ℝ f k)
    (hcont : ContinuousOn (deriv f) (Ioi 0))
    (hatZero : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop)
    (hatTop : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))) :
    ∃! k : ℝ, 0 < k ∧ deriv f k = d + m :=
  existsUnique_positive_root_of_inada (deriv f) (d + m) hpositive hcont
    (production_deriv_strictAnti f hconc hdiff) hatZero hatTop

/-- Strict concavity and zero production at zero imply a strict gap between
output and capital valued at marginal product. This is a proved supporting-line
inequality, including the endpoint zero without differentiability there. -/
theorem marginal_product_times_capital_lt_output
    (f : ℝ → ℝ) (k : ℝ)
    (hconc : StrictConcaveOn ℝ (Ici 0) f)
    (hzero : f 0 = 0) (hk : 0 < k)
    (hdiff : DifferentiableAt ℝ f k) :
    deriv f k * k < f k := by
  have h := hconc.deriv_lt_slope (show (0 : ℝ) ∈ Ici 0 by simp)
    (le_of_lt hk) hk hdiff
  rw [slope_def_field, hzero, sub_zero, sub_zero] at h
  exact (lt_div_iff₀ hk).mp h

/-- Stationary consumption is positive, even at zero discount, when the
stationary marginal-product condition and strict concavity hold. -/
theorem stationary_consumption_pos
    (f : ℝ → ℝ) (k d m : ℝ)
    (hconc : StrictConcaveOn ℝ (Ici 0) f)
    (hzero : f 0 = 0) (hk : 0 < k)
    (hdiff : DifferentiableAt ℝ f k)
    (hd : 0 ≤ d) (hstationary : deriv f k = d + m) :
    0 < f k - m * k := by
  have hgap := marginal_product_times_capital_lt_output f k hconc hzero hk hdiff
  rw [hstationary] at hgap
  have hdk : 0 ≤ d * k := mul_nonneg hd (le_of_lt hk)
  nlinarith

/-- Existence and uniqueness of the stationary capital/consumption pair. The
positivity of consumption is derived, not included in the bracket hypothesis. -/
theorem existsUnique_positive_stationary_pair_of_bracket
    (f : ℝ → ℝ) (d m a b : ℝ)
    (hconc : StrictConcaveOn ℝ (Ici 0) f) (hzero : f 0 = 0)
    (hdiff : ∀ k : ℝ, 0 < k → DifferentiableAt ℝ f k)
    (hd : 0 ≤ d) (ha : 0 < a) (hab : a ≤ b)
    (hcont : ContinuousOn (deriv f) (Icc a b))
    (hlower : deriv f b ≤ d + m) (hupper : d + m ≤ deriv f a) :
    ∃! kc : ℝ × ℝ, 0 < kc.1 ∧ 0 < kc.2 ∧
      deriv f kc.1 = d + m ∧ kc.2 = f kc.1 - m * kc.1 := by
  obtain ⟨k, hk, hunique⟩ := existsUnique_stationary_capital_of_bracket
    f d m a b hconc hdiff ha hab hcont hlower hupper
  refine ⟨(k, f k - m * k), ⟨hk.1, ?_, hk.2, rfl⟩, ?_⟩
  · exact stationary_consumption_pos f k d m hconc hzero hk.1 (hdiff k hk.1) hd hk.2
  · intro kc hkc
    have heq : kc.1 = k := hunique kc.1 ⟨hkc.1, hkc.2.2.1⟩
    apply Prod.ext heq
    simpa only [heq] using hkc.2.2.2

/-- The positive stationary pair exists uniquely under the marginal-product
Inada limits. The output normalization `f 0 = 0` is explicit, as in Koopmans's
appendix and as a strengthened boundary assumption for Cass. -/
theorem existsUnique_positive_stationary_pair_of_inada
    (f : ℝ → ℝ) (d m : ℝ) (hd : 0 ≤ d) (hm : 0 < m)
    (hconc : StrictConcaveOn ℝ (Ici 0) f) (hzero : f 0 = 0)
    (hdiff : ∀ k : ℝ, 0 < k → DifferentiableAt ℝ f k)
    (hcont : ContinuousOn (deriv f) (Ioi 0))
    (hatZero : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop)
    (hatTop : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))) :
    ∃! kc : ℝ × ℝ, 0 < kc.1 ∧ 0 < kc.2 ∧
      deriv f kc.1 = d + m ∧ kc.2 = f kc.1 - m * kc.1 := by
  have htarget : 0 < d + m := add_pos_of_nonneg_of_pos hd hm
  obtain ⟨a, b, ha, hab, hmb, hma⟩ :=
    exists_positive_bracket_of_inada (deriv f) (d + m) htarget hatZero hatTop
  exact existsUnique_positive_stationary_pair_of_bracket f d m a b hconc hzero
    hdiff hd ha hab.le (hcont.mono (fun _ hk => lt_of_lt_of_le ha hk.1)) hmb.le hma.le

/-- A capital stock with marginal product `m` strictly maximizes sustainable
stationary consumption over every other nonnegative capital stock. Thus the
term "golden rule" has its economic maximizing meaning, not just a name for
an equation. -/
theorem golden_rule_strictly_maximizes_consumption
    (f : ℝ → ℝ) (kGR k m : ℝ)
    (hconc : StrictConcaveOn ℝ (Ici 0) f)
    (hkGR : 0 < kGR) (hk : 0 ≤ k) (hne : k ≠ kGR)
    (hdiff : DifferentiableAt ℝ f kGR) (hGR : deriv f kGR = m) :
    f k - m * k < f kGR - m * kGR := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs := hconc.deriv_lt_slope hk hkGR.le hlt hdiff
    rw [hGR, slope_def_field] at hs
    have hden : 0 < kGR - k := sub_pos.mpr hlt
    have hmul := (lt_div_iff₀ hden).mp hs
    nlinarith
  · have hs := hconc.slope_lt_deriv hkGR.le hk hgt hdiff
    rw [hGR, slope_def_field] at hs
    have hden : 0 < k - kGR := sub_pos.mpr hgt
    have hmul := (div_lt_iff₀ hden).mp hs
    nlinarith

/-- Positive discount lowers stationary capital below its golden-rule value.
No dynamic convergence assertion is used in this comparison. -/
theorem stationary_capital_lt_golden_rule
    (mp : ℝ → ℝ) (kstar kGR d m : ℝ)
    (hanti : StrictAntiOn mp (Ioi 0))
    (hkstar : 0 < kstar) (hkGR : 0 < kGR) (hd : 0 < d)
    (hstar : mp kstar = d + m) (hGR : mp kGR = m) :
    kstar < kGR := by
  by_contra h
  have hkorder : kGR ≤ kstar := le_of_not_gt h
  have hmp : mp kstar ≤ mp kGR := hanti.antitoneOn hkGR hkstar hkorder
  rw [hstar, hGR] at hmp
  linarith

/-- The golden-rule comparison for an actual differentiable strictly concave
production function. -/
theorem stationary_capital_lt_golden_rule_of_strictConcave
    (f : ℝ → ℝ) (kstar kGR d m : ℝ)
    (hconc : StrictConcaveOn ℝ (Ici 0) f)
    (hdiff : ∀ k : ℝ, 0 < k → DifferentiableAt ℝ f k)
    (hkstar : 0 < kstar) (hkGR : 0 < kGR) (hd : 0 < d)
    (hstar : deriv f kstar = d + m) (hGR : deriv f kGR = m) :
    kstar < kGR :=
  stationary_capital_lt_golden_rule (deriv f) kstar kGR d m
    (production_deriv_strictAnti f hconc hdiff) hkstar hkGR hd hstar hGR

/-- Stationary gross investment is positive when dilution/depreciation and
capital are positive, so this state is interior to Cass's investment constraint. -/
theorem stationary_investment_pos (m k : ℝ) (hm : 0 < m) (hk : 0 < k) :
    0 < m * k := mul_pos hm hk

/-- The stationary pair satisfies the resource and capital equations. -/
theorem stationary_resource_and_capital (f : ℝ → ℝ) (k m : ℝ) :
    (f k - m * k) + m * k = f k ∧ m * k - m * k = 0 := by
  constructor <;> ring

/-- With nonzero intertemporal-substitution coefficient, stationarity of the
interior Euler equation is equivalent to the source marginal-product condition.
This is a characterization of its zero, not a derivation of the Euler ODE. -/
theorem interior_euler_stationary_iff
    (mp coefficient d m : ℝ) (hcoefficient : coefficient ≠ 0) :
    coefficient * (mp - d - m) = 0 ↔ mp = d + m := by
  rw [mul_eq_zero, or_iff_right hcoefficient]
  constructor <;> intro h <;> linarith

end RamseyCassKoopmans


/-!
# Stationary feasible paths and their objective values

A resource-balanced pair of constant capital and positive consumption determines an
actual feasible path. With positive effective discounting, its welfare is finite.
Stationarity and feasibility alone do not assert optimality; supporting prices and
an appropriate comparison theorem are needed for that conclusion.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

/-- Constant capital and consumption, with replacement investment `m * k`. -/
def stationaryPath (f : ℝ → ℝ) (m k c : ℝ)
    (hk : 0 ≤ k) (hc : 0 < c) (hresource : c + m * k = f k) :
    FeasiblePath f m where
  capital := fun _ => k
  consumption := fun _ => c
  investment := fun _ => m * k
  capital_nonneg := fun _ _ => hk
  consumption_pos := fun _ _ => hc
  consumption_continuous := continuousOn_const
  investment_continuous := continuousOn_const
  resource := fun _ _ => hresource
  dynamics := fun t _ => by simpa using hasDerivAt_const t k

/-- Nonnegative effective depreciation makes stationary replacement investment
nonnegative, so this path also satisfies Cass's investment restriction. -/
theorem stationaryPath_nonnegativeInvestment
    (f : ℝ → ℝ) (m k c : ℝ) (hk : 0 ≤ k) (hc : 0 < c)
    (hresource : c + m * k = f k) (hm : 0 ≤ m) :
    (stationaryPath f m k c hk hc hresource).NonnegativeInvestment :=
  fun _ _ => mul_nonneg hm hk

/-- Exact finite-horizon welfare of constant consumption. This holds for every
real horizon; no integrability hypothesis on utility away from `c` is required. -/
theorem welfare_constant_consumption
    (U : ℝ → ℝ) (c d T : ℝ) (hd : 0 < d) :
    welfare U (discount d) (fun _ => c) T = U c * (1 - discount d T) / d := by
  have hprimitive : ∀ t : ℝ,
      HasDerivAt (fun s => U c * (1 - discount d s) / d)
        (discount d t * U c) t := by
    intro t
    convert ((hasDerivAt_discount d t).const_sub 1).const_mul (U c) |>.div_const d
      using 1
    field_simp [ne_of_gt hd]
  have hintegrable : IntervalIntegrable (fun t => discount d t * U c) volume 0 T :=
    ((discount_continuous d).mul continuous_const).intervalIntegrable 0 T
  unfold welfare
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hprimitive t) hintegrable]
  simp [discount]

/-- Constant positive-discount welfare converges to utility divided by discounting. -/
theorem hasWelfare_constant_consumption
    (U : ℝ → ℝ) (c d : ℝ) (hd : 0 < d) :
    HasWelfare U (discount d) (fun _ => c) (U c / d) := by
  unfold HasWelfare
  have hdiscount : Tendsto (discount d) atTop (𝓝 0) :=
    Terminal.discount_factor_tendsto_zero hd
  have hlimit := (hdiscount.const_sub 1).const_mul (U c) |>.div_const d
  simp only [sub_zero, mul_one] at hlimit
  exact hlimit.congr (fun T => (welfare_constant_consumption U c d T hd).symm)

/-- Every stationary feasible path has the explicit discounted objective `U c / d`. -/
theorem stationaryPath_hasWelfare
    (f U : ℝ → ℝ) (m k c d : ℝ) (hk : 0 ≤ k) (hc : 0 < c)
    (hresource : c + m * k = f k) (hd : 0 < d) :
    HasWelfare U (discount d)
      (stationaryPath f m k c hk hc hresource).consumption (U c / d) :=
  hasWelfare_constant_consumption U c d hd

end RamseyCassKoopmans


/-!
# Optimality verification

The finite-horizon comparison retains terminal capital. Optimality is then
proved for finite limiting welfare values, with the boundary limit explicit.
The hypotheses certify a supplied candidate; they do not assert that one exists.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

/-- Supporting prices and tangent bounds along a candidate path. The supporting
bounds can be derived from concavity and differentiability. Time regularity is
explicit. The price is in present value, so the discount weight occurs in the
costate equation. -/
structure SupportingPrices (f U w : ℝ → ℝ) (m : ℝ) (a : FeasiblePath f m) where
  price : ℝ → ℝ
  marginalUtility : ℝ → ℝ
  marginalProduct : ℝ → ℝ
  weight_nonneg : ∀ t, 0 ≤ t → 0 ≤ w t
  weight_continuous : ContinuousOn w (Ici 0)
  utility_continuous : ContinuousOn U (Ioi 0)
  marginalUtility_continuous : ContinuousOn marginalUtility (Ici 0)
  marginalProduct_continuous : ContinuousOn marginalProduct (Ici 0)
  marginalUtility_nonneg : ∀ t, 0 ≤ t → 0 ≤ marginalUtility t
  utility_support : ∀ t, 0 ≤ t → ∀ c, 0 < c →
    U c - U (a.consumption t) ≤ marginalUtility t * (c - a.consumption t)
  production_support : ∀ t, 0 ≤ t → ∀ k, 0 ≤ k →
    f k - f (a.capital t) ≤ marginalProduct t * (k - a.capital t)
  costate : ∀ t, 0 ≤ t → HasDerivAt price
    (m * price t - w t * marginalUtility t * marginalProduct t) t

theorem SupportingPrices.price_continuous {f U w : ℝ → ℝ} {m : ℝ}
    {a : FeasiblePath f m} (v : SupportingPrices f U w m a) :
    ContinuousOn v.price (Ici 0) := by
  intro t ht
  exact (v.costate t ht).continuousAt.continuousWithinAt

/-- The allocation comparison holds for Cass by complementary slackness, and
for Koopmans's interior allocation because the price wedge is zero. -/
def AllocationComparison {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m) : Prop :=
  ∀ t, 0 ≤ t →
    0 ≤ (v.price t - w t * v.marginalUtility t) * (a.investment t - b.investment t)

theorem allocation_of_cass {f U w : ℝ → ℝ} {m : ℝ} {a b : FeasiblePath f m}
    (v : SupportingPrices f U w m a)
    (hwedge : ∀ t, 0 ≤ t → v.price t ≤ w t * v.marginalUtility t)
    (hslack : ∀ t, 0 ≤ t →
      (v.price t - w t * v.marginalUtility t) * a.investment t = 0)
    (hb : b.NonnegativeInvestment) : AllocationComparison v b := by
  intro t ht
  exact complementarity_welfare_term (w t * v.marginalUtility t) (v.price t)
    (a.investment t) (b.investment t) (hwedge t ht) (hslack t ht) (hb t ht)

theorem allocation_of_interior {f U w : ℝ → ℝ} {m : ℝ} {a b : FeasiblePath f m}
    (v : SupportingPrices f U w m a)
    (hprice : ∀ t, 0 ≤ t → v.price t = w t * v.marginalUtility t) :
    AllocationComparison v b := by
  intro t ht
  simp [hprice t ht]

def boundaryRate {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m) (t : ℝ) : ℝ :=
  (m * v.price t - w t * v.marginalUtility t * v.marginalProduct t) *
      (a.capital t - b.capital t) +
    v.price t * ((a.investment t - m * a.capital t) -
      (b.investment t - m * b.capital t))

theorem hasDerivAt_boundary {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (boundary v.price a.capital b.capital) (boundaryRate v b t) t := by
  exact (v.costate t ht).mul ((a.dynamics t ht).sub (b.dynamics t ht))

theorem boundaryRate_continuous {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m) :
    ContinuousOn (boundaryRate v b) (Ici 0) := by
  exact (((continuousOn_const.mul v.price_continuous).sub
    ((v.weight_continuous.mul v.marginalUtility_continuous).mul
      v.marginalProduct_continuous)).mul
        (a.capital_continuous.sub b.capital_continuous)).add
    (v.price_continuous.mul ((a.investment_continuous.sub
      (continuousOn_const.mul a.capital_continuous)).sub
        (b.investment_continuous.sub (continuousOn_const.mul b.capital_continuous))))

theorem welfare_integrand_continuous {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m) :
    ContinuousOn (fun t => w t * U (b.consumption t)) (Ici 0) := by
  exact v.weight_continuous.mul (v.utility_continuous.comp b.consumption_continuous
    (fun t ht => b.consumption_pos t ht))

/-- The algebraic comparison is applied to the actual resource and price laws. -/
theorem pointwise_comparison {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ w t * (U (a.consumption t) - U (b.consumption t)) + boundaryRate v b t := by
  apply present_value_comparison_nonneg
    (U (a.consumption t)) (U (b.consumption t))
    (f (a.capital t)) (f (b.capital t))
    (a.consumption t) (b.consumption t) (a.investment t) (b.investment t)
    (a.capital t) (b.capital t) (v.marginalProduct t) (v.marginalUtility t)
    (v.price t) m (w t)
    (m * v.price t - w t * v.marginalUtility t * v.marginalProduct t)
    (a.resource t ht) (b.resource t ht)
  · nlinarith [v.utility_support t ht (b.consumption t) (b.consumption_pos t ht)]
  · nlinarith [v.production_support t ht (b.capital t) (b.capital_nonneg t ht)]
  · exact v.weight_nonneg t ht
  · exact v.marginalUtility_nonneg t ht
  · exact halloc t ht
  · rfl

/-- Finite-horizon comparison, with the economically correct boundary sign:
competitor minus candidate welfare is at most price times candidate minus
competitor terminal capital. No terminal condition is used here. -/
theorem finite_horizon_comparison {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    {T : ℝ} (hT : 0 ≤ T) :
    welfare U w b.consumption T - welfare U w a.consumption T ≤
      boundary v.price a.capital b.capital T := by
  have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
  have haint :=
    ((welfare_integrand_continuous v a).mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
  have hbint :=
    ((welfare_integrand_continuous v b).mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
  have hBint := ((boundaryRate_continuous v b).mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
  have hFTC : (∫ t in (0 : ℝ)..T, boundaryRate v b t) =
      boundary v.price a.capital b.capital T - boundary v.price a.capital b.capital 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hBint
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact hasDerivAt_boundary v b ht.1
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..T,
      (w t * U (a.consumption t) - w t * U (b.consumption t)) + boundaryRate v b t := by
    apply intervalIntegral.integral_nonneg hT
    intro t ht
    simpa only [mul_sub] using pointwise_comparison v b halloc ht.1
  rw [intervalIntegral.integral_add (haint.sub hbint) hBint,
    intervalIntegral.integral_sub haint hbint, hFTC] at hnonneg
  have hB0 : boundary v.price a.capital b.capital 0 = 0 := by simp [boundary, hinit]
  rw [hB0] at hnonneg
  change welfare U w a.consumption T - welfare U w b.consumption T +
    (boundary v.price a.capital b.capital T - 0) ≥ 0 at hnonneg
  linarith

/-- Infinite-horizon verification for competitors with finite limiting welfare.
The candidate is not assumed optimal; the conclusion follows from the proved
finite comparison and the explicit terminal limit. -/
theorem infinite_horizon_optimality {f U w : ℝ → ℝ} {m Ja Jb : ℝ}
    {a : FeasiblePath f m} (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0)) :
    Jb ≤ Ja := by
  have hle : Jb - Ja ≤ 0 := le_of_tendsto_of_tendsto (hb.sub ha) hterminal
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact finite_horizon_comparison v b halloc hinit hT)
  linarith

/-- Price decay and bounded feasible capital discharge the terminal premise. -/
theorem infinite_horizon_optimality_of_bounded_capital
    {f U w : ℝ → ℝ} {m Ja Jb K : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hp : Tendsto v.price atTop (𝓝 0))
    (hka : ∀ t, 0 ≤ t → a.capital t ≤ K)
    (hkb : ∀ t, 0 ≤ t → b.capital t ≤ K) : Jb ≤ Ja := by
  exact infinite_horizon_optimality v b halloc hinit ha hb
    (Terminal.terminal_tendsto_zero_of_bounded_capital hp
      (fun t ht => ⟨a.capital_nonneg t ht, hka t ht⟩)
      (fun t ht => ⟨b.capital_nonneg t ht, hkb t ht⟩))

end RamseyCassKoopmans


/-!
# Cass's current-value certificate

This connects actual derivatives of concave utility and production to the
verification theorem. It includes nonnegative investment and complementary
slackness. It does not replace complementary slackness by an everywhere-interior
Euler equation. Positive consumption and continuous controls are explicit
regularity restrictions. Finite welfare is expressed as a limit of finite integrals.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

/-- Supporting prices derived from concavity, differentiability, and the actual
current-value costate equation, rather than postulated tangent inequalities. -/
noncomputable def cassSupportingPrices
    (f U q : ℝ → ℝ) (d m : ℝ) (a : FeasiblePath f m)
    (hfconc : ConcaveOn ℝ (Ici 0) f) (hUconc : ConcaveOn ℝ (Ioi 0) U)
    (hUcont : ContinuousOn U (Ioi 0))
    (hfderiv : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hUderiv : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hak : ∀ t, 0 ≤ t → 0 < a.capital t)
    (hmu : ∀ t, 0 ≤ t → 0 ≤ deriv U (a.consumption t))
    (hq : ∀ t, 0 ≤ t → HasDerivAt q
      ((d + m) * q t - deriv U (a.consumption t) * deriv f (a.capital t)) t) :
    SupportingPrices f U (discount d) m a where
  price := fun t => discount d t * q t
  marginalUtility := fun t => deriv U (a.consumption t)
  marginalProduct := fun t => deriv f (a.capital t)
  weight_nonneg := fun t _ => (discount_pos d t).le
  weight_continuous := (discount_continuous d).continuousOn
  utility_continuous := hUcont
  marginalUtility_continuous := hUprime.comp a.consumption_continuous a.consumption_pos
  marginalProduct_continuous := hfprime.comp a.capital_continuous hak
  marginalUtility_nonneg := hmu
  utility_support := fun t ht _c hc => concave_support hUconc
    (a.consumption_pos t ht) hc (hUderiv _ (a.consumption_pos t ht)).hasDerivAt
  production_support := fun t ht _k hk => concave_support hfconc
    (a.capital_nonneg t ht) hk (hfderiv _ (hak t ht)).hasDerivAt
  costate := fun t ht => hasDerivAt_discounted_costate (hq t ht)

/-- The source resource equation supplies the right derivative needed by the
capital comparison lemma. -/
theorem FeasiblePath.resource_derivative {f : ℝ → ℝ} {m : ℝ}
    (a : FeasiblePath f m) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt a.capital
      (f (a.capital t) - a.consumption t - m * a.capital t) (Ici t) t := by
  convert (a.dynamics t ht).hasDerivWithinAt using 1
  linarith [a.resource t ht]

/-- A capacity assumption and feasibility imply the capital bound used in
transversality. Consumption is positive in this library's admissible class. -/
theorem FeasiblePath.capital_le_capacity {f : ℝ → ℝ} {m K : ℝ}
    (a : FeasiblePath f m) (hK : ∀ k, K ≤ k → f k ≤ m * k)
    (hinit : a.capital 0 ≤ K) : ∀ t, 0 ≤ t → a.capital t ≤ K :=
  Terminal.capital_le_capacity a.capital_continuous
    (fun _ ht => a.resource_derivative ht)
    (fun t ht => (a.consumption_pos t ht).le) hK hinit

/-- Cass verification for continuous positive-consumption paths. The theorem
uses the current-value costate equation, the investment corner, and a genuine
terminal price condition; capital bounds are proved from feasibility. It is a
sufficiency theorem for a supplied candidate, not an existence theorem. -/
theorem cass_candidate_dominates
    (f U q : ℝ → ℝ) (d m K Ja Jb : ℝ) (a b : FeasiblePath f m)
    (hfconc : ConcaveOn ℝ (Ici 0) f) (hUconc : ConcaveOn ℝ (Ioi 0) U)
    (hUcont : ContinuousOn U (Ioi 0))
    (hfderiv : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hUderiv : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hak : ∀ t, 0 ≤ t → 0 < a.capital t)
    (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hq : ∀ t, 0 ≤ t → HasDerivAt q
      ((d + m) * q t - deriv U (a.consumption t) * deriv f (a.capital t)) t)
    (hwedge : ∀ t, 0 ≤ t → q t ≤ deriv U (a.consumption t))
    (hslack : ∀ t, 0 ≤ t → (q t - deriv U (a.consumption t)) * a.investment t = 0)
    (hbinvest : b.NonnegativeInvestment)
    (hinit : a.capital 0 = b.capital 0)
    (hcapacity : ∀ k, K ≤ k → f k ≤ m * k) (ha0 : a.capital 0 ≤ K)
    (ha : HasWelfare U (discount d) a.consumption Ja)
    (hb : HasWelfare U (discount d) b.consumption Jb)
    (htrans : Tendsto (fun t => discount d t * q t) atTop (𝓝 0)) : Jb ≤ Ja := by
  let v := cassSupportingPrices f U q d m a hfconc hUconc hUcont hfderiv hUderiv
    hfprime hUprime hak (fun t ht => (hqn t ht).trans (hwedge t ht)) hq
  have halloc : AllocationComparison v b := by
    apply allocation_of_cass v
    · intro t ht
      exact mul_le_mul_of_nonneg_left (hwedge t ht) (discount_pos d t).le
    · intro t ht
      change (discount d t * q t - discount d t * deriv U (a.consumption t)) *
        a.investment t = 0
      calc
        _ = discount d t * ((q t - deriv U (a.consumption t)) * a.investment t) := by ring
        _ = 0 := by rw [hslack t ht, mul_zero]
    · exact hbinvest
  exact infinite_horizon_optimality_of_bounded_capital v b halloc hinit ha hb htrans
    (a.capital_le_capacity hcapacity ha0)
    (b.capital_le_capacity hcapacity (hinit ▸ ha0))

/-- Optimality within this library's continuous-control, positive-consumption,
finite-welfare version of Cass's feasible class. Candidate membership is explicit. -/
def IsCassOptimal {f : ℝ → ℝ} {m : ℝ} (U : ℝ → ℝ) (d : ℝ)
    (a : FeasiblePath f m) (Ja : ℝ) : Prop :=
  a.NonnegativeInvestment ∧ HasWelfare U (discount d) a.consumption Ja ∧
    ∀ (b : FeasiblePath f m), b.NonnegativeInvestment → a.capital 0 = b.capital 0 →
      ∀ Jb, HasWelfare U (discount d) b.consumption Jb → Jb ≤ Ja

/-- A feasible Cass candidate satisfying the certificate really is optimal in
the stated admissible class, including its own nonnegative investment. -/
theorem cass_certificate_is_optimal
    (f U q : ℝ → ℝ) (d m K Ja : ℝ) (a : FeasiblePath f m)
    (hfconc : ConcaveOn ℝ (Ici 0) f) (hUconc : ConcaveOn ℝ (Ioi 0) U)
    (hUcont : ContinuousOn U (Ioi 0))
    (hfderiv : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hUderiv : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hak : ∀ t, 0 ≤ t → 0 < a.capital t)
    (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hq : ∀ t, 0 ≤ t → HasDerivAt q
      ((d + m) * q t - deriv U (a.consumption t) * deriv f (a.capital t)) t)
    (hwedge : ∀ t, 0 ≤ t → q t ≤ deriv U (a.consumption t))
    (hslack : ∀ t, 0 ≤ t → (q t - deriv U (a.consumption t)) * a.investment t = 0)
    (hainvest : a.NonnegativeInvestment)
    (hcapacity : ∀ k, K ≤ k → f k ≤ m * k) (ha0 : a.capital 0 ≤ K)
    (ha : HasWelfare U (discount d) a.consumption Ja)
    (htrans : Tendsto (fun t => discount d t * q t) atTop (𝓝 0)) :
    IsCassOptimal U d a Ja := by
  refine ⟨hainvest, ha, ?_⟩
  intro b hbinvest hinit Jb hb
  exact cass_candidate_dominates f U q d m K Ja Jb a b hfconc hUconc hUcont
    hfderiv hUderiv hfprime hUprime hak hqn hq hwedge hslack hbinvest hinit
    hcapacity ha0 ha hb htrans

end RamseyCassKoopmans


/-!
# Constructed stationary optimal paths

This file constructs supporting prices for the stationary capital/consumption pair
and proves its optimality against every admissible competitor with the same initial
capital and a finite limiting objective. The terminal condition follows from a
proved resource-based capital bound and positive discounting. This is an optimal
path construction at the stationary initial stock, not an existence assertion for
arbitrary initial capital.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

/-- The modified golden-rule equation supplies the costate equation for an actual
stationary path. The tangent inequalities follow from concavity of the functions. -/
noncomputable def stationarySupportingPrices
    (f U : ℝ → ℝ) (m k c d : ℝ)
    (hk : 0 ≤ k) (hc : 0 < c) (hresource : c + m * k = f k)
    (hf : ConcaveOn ℝ (Ici 0) f) (hU : ConcaveOn ℝ (Ioi 0) U)
    (hUcont : ContinuousOn U (Ioi 0))
    (hfderiv : DifferentiableAt ℝ f k) (hUderiv : DifferentiableAt ℝ U c)
    (hmu : 0 ≤ deriv U c) (hstationary : deriv f k = d + m) :
    SupportingPrices f U (discount d) m (stationaryPath f m k c hk hc hresource) where
  price := fun t => discount d t * deriv U c
  marginalUtility := fun _ => deriv U c
  marginalProduct := fun _ => deriv f k
  weight_nonneg := fun t _ => (discount_pos d t).le
  weight_continuous := (discount_continuous d).continuousOn
  utility_continuous := hUcont
  marginalUtility_continuous := continuousOn_const
  marginalProduct_continuous := continuousOn_const
  marginalUtility_nonneg := fun _ _ => hmu
  utility_support := fun _ _ y hy => concave_support hU hc hy hUderiv.hasDerivAt
  production_support := fun _ _ y hy => concave_support hf hk hy hfderiv.hasDerivAt
  costate := fun t _ => by
    convert (hasDerivAt_discount d t).mul_const (deriv U c) using 1
    rw [hstationary]
    ring

/-- A stationary feasible pair satisfying the modified golden rule is optimal
among all feasible paths from its initial stock with finite limiting welfare.
Investment may be negative for competitors. Their capital bound is derived from
their resource equations and the technology's capacity bound. -/
theorem stationaryPath_optimality
    (f U : ℝ → ℝ) (m k c d K : ℝ)
    (hk : 0 ≤ k) (hc : 0 < c) (hresource : c + m * k = f k)
    (hf : ConcaveOn ℝ (Ici 0) f) (hU : ConcaveOn ℝ (Ioi 0) U)
    (hUcont : ContinuousOn U (Ioi 0))
    (hfderiv : DifferentiableAt ℝ f k) (hUderiv : DifferentiableAt ℝ U c)
    (hmu : 0 ≤ deriv U c) (hstationary : deriv f k = d + m)
    (hd : 0 < d) (hkK : k ≤ K)
    (hcapacity : ∀ x, K ≤ x → f x ≤ m * x)
    (b : FeasiblePath f m) (J : ℝ)
    (hinit : b.capital 0 = k) (hJ : HasWelfare U (discount d) b.consumption J) :
    J ≤ U c / d := by
  let v := stationarySupportingPrices f U m k c d hk hc hresource
    hf hU hUcont hfderiv hUderiv hmu hstationary
  have hbound : ∀ t, 0 ≤ t → b.capital t ≤ K := by
    apply Terminal.capital_le_capacity (f := f) (c := b.consumption) (m := m)
      b.capital_continuous
    · intro t ht
      convert (b.dynamics t ht).hasDerivWithinAt (s := Ici t) using 1
      linarith [b.resource t ht]
    · exact fun t ht => (b.consumption_pos t ht).le
    · exact hcapacity
    · simpa only [hinit] using hkK
  apply infinite_horizon_optimality_of_bounded_capital v b
      (allocation_of_interior v (fun _ _ => rfl))
      (show (stationaryPath f m k c hk hc hresource).capital 0 = b.capital 0 from hinit.symm)
      (stationaryPath_hasWelfare f U m k c d hk hc hresource hd) hJ
  · exact Terminal.discounted_price_tendsto_zero hd tendsto_const_nhds
  · exact fun _ _ => hkK
  · exact hbound

/-- A concave production function whose marginal product vanishes at infinity
eventually produces no more than replacement requirements. Thus a capacity bound
is derived from the Inada limit, not assumed separately. -/
theorem exists_capacity_of_marginal_product_tendsto_zero
    (f : ℝ → ℝ) (m : ℝ) (hm : 0 < m)
    (hf : ConcaveOn ℝ (Ici 0) f)
    (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hftop : Tendsto (deriv f) atTop (𝓝 0)) :
    ∃ K : ℝ, 0 < K ∧ ∀ x, K ≤ x → f x ≤ m * x := by
  have hevent : ∀ᶠ a : ℝ in atTop, deriv f a < m :=
    hftop.eventually (gt_mem_nhds hm)
  obtain ⟨a, ha, hma⟩ := ((eventually_gt_atTop (0 : ℝ)).and hevent).exists
  let C : ℝ := f a - deriv f a * a
  let K : ℝ := max a (C / (m - deriv f a))
  have hapos : a ≤ K := le_max_left _ _
  have hKpos : 0 < K := ha.trans_le hapos
  refine ⟨K, hKpos, ?_⟩
  intro x hx
  have hs := concave_support hf ha.le (hKpos.le.trans hx) (hfdiff a ha).hasDerivAt
  have hquot : C / (m - deriv f a) ≤ x := (le_max_right _ _).trans hx
  have hmul := (div_le_iff₀ (sub_pos.mpr hma)).mp hquot
  dsimp [C] at hmul
  nlinarith

/-- An actual stationary optimal path exists under strict concavity, the
marginal-product Inada limits, positive discounting and positive dilution.
The initial stock is the derived stationary stock. The conclusion includes its
finite objective and compares against every finite-welfare feasible competitor,
including competitors which disinvest. It does not construct a path from an
arbitrary prescribed initial stock. -/
theorem exists_stationary_optimal_path_of_inada
    (f U : ℝ → ℝ) (d m : ℝ) (hd : 0 < d) (hm : 0 < m)
    (hf : StrictConcaveOn ℝ (Ici 0) f) (hfzero : f 0 = 0)
    (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hfcont : ContinuousOn (deriv f) (Ioi 0))
    (hfatZero : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop)
    (hfatTop : Tendsto (deriv f) atTop (𝓝 0))
    (hU : ConcaveOn ℝ (Ioi 0) U) (hUcont : ContinuousOn U (Ioi 0))
    (hUdiff : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hmu : ∀ c, 0 < c → 0 ≤ deriv U c) :
    ∃ (a : FeasiblePath f m) (k c : ℝ),
      0 < k ∧ 0 < c ∧ deriv f k = d + m ∧
      (∀ t, a.capital t = k ∧ a.consumption t = c) ∧
      a.NonnegativeInvestment ∧
      HasWelfare U (discount d) a.consumption (U c / d) ∧
      ∀ (b : FeasiblePath f m) (J : ℝ), b.capital 0 = a.capital 0 →
        HasWelfare U (discount d) b.consumption J → J ≤ U c / d := by
  obtain ⟨⟨k, c⟩, hk, hc, hstationary, hconsumption⟩ :=
    (existsUnique_positive_stationary_pair_of_inada f d m hd.le hm hf hfzero
      hfdiff hfcont hfatZero hfatTop).exists
  have hresource : c + m * k = f k := by linarith
  obtain ⟨K, _, hcapacity⟩ :=
    exists_capacity_of_marginal_product_tendsto_zero f m hm hf.concaveOn hfdiff hfatTop
  have hkK : k ≤ K := by
    by_contra h
    have hcap := hcapacity k (le_of_lt (lt_of_not_ge h))
    linarith
  let a := stationaryPath f m k c hk.le hc hresource
  refine ⟨a, k, c, hk, hc, hstationary, fun _ => ⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · exact stationaryPath_nonnegativeInvestment f m k c hk.le hc hresource hm.le
  · exact stationaryPath_hasWelfare f U m k c d hk.le hc hresource hd
  · intro b J hinit hJ
    exact stationaryPath_optimality f U m k c d K hk.le hc hresource
      hf.concaveOn hU hUcont (hfdiff k hk) (hUdiff c hc) (hmu c hc)
      hstationary hd hkK hcapacity b J hinit hJ

end RamseyCassKoopmans


/-!
# Verification of convergent interior Euler candidates

Koopmans's published characterization supplements the Euler equation with an
asymptotic condition. Here convergence of consumption to a positive level is an
explicit hypothesis: it is used to derive price decay and eliminate the terminal
capital term. The costate is constructed from actual marginal utility by the chain
rule. No investment sign restriction is imposed, in keeping with the disinvestment
allowed by this feasible-path convention.

This is the sufficient-direction verification for a supplied regular candidate,
with finite limiting welfare values. It does not construct a nonstationary Euler
path, prove its convergence, or establish the complete necessity-and-sufficiency
statement in Koopmans's Proposition I.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

/-- The consumption Euler equation is exactly the current-value costate equation
for `q = U' ∘ c`, once the derivative is justified by the chain rule. This form
avoids dividing by `U''` and therefore requires no hidden nonvanishing premise. -/
theorem euler_implies_current_value_costate
    {U c : ℝ → ℝ} {cd d m mp t : ℝ}
    (hc : HasDerivAt c cd t)
    (hU2 : HasDerivAt (deriv U) (deriv (deriv U) (c t)) (c t))
    (heuler : deriv (deriv U) (c t) * cd = deriv U (c t) * (d + m - mp)) :
    HasDerivAt (fun s => deriv U (c s))
      ((d + m) * deriv U (c t) - deriv U (c t) * mp) t := by
  convert hU2.comp t hc using 1
  · rfl
  · rw [heuler]
    ring

/-- A convergent Euler candidate is optimal among the stated feasible paths with
the same initial capital and finite welfare. Consumption convergence is assumed,
not deduced from the Euler equation. All capital and terminal bounds are proved
from the resource law, production assumptions, and this positive-limit premise. -/
theorem convergent_euler_candidate_optimal
    (f U cd : ℝ → ℝ) (d m cstar Ja Jb : ℝ) (a b : FeasiblePath f m)
    (hd : 0 < d) (hm : 0 < m)
    (hfconc : ConcaveOn ℝ (Ici 0) f) (hUconc : ConcaveOn ℝ (Ioi 0) U)
    (hUcont : ContinuousOn U (Ioi 0))
    (hfderiv : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hUderiv : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hfprime_top : Tendsto (deriv f) atTop (𝓝 0))
    (hak : ∀ t, 0 ≤ t → 0 < a.capital t)
    (hmu : ∀ t, 0 ≤ t → 0 ≤ deriv U (a.consumption t))
    (hcd : ∀ t, 0 ≤ t → HasDerivAt a.consumption (cd t) t)
    (hU2 : ∀ c, 0 < c → HasDerivAt (deriv U) (deriv (deriv U) c) c)
    (heuler : ∀ t, 0 ≤ t →
      deriv (deriv U) (a.consumption t) * cd t =
        deriv U (a.consumption t) * (d + m - deriv f (a.capital t)))
    (hcstar : 0 < cstar) (hconvergence : Tendsto a.consumption atTop (𝓝 cstar))
    (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U (discount d) a.consumption Ja)
    (hb : HasWelfare U (discount d) b.consumption Jb) : Jb ≤ Ja := by
  have hq : ∀ t, 0 ≤ t → HasDerivAt (fun s => deriv U (a.consumption s))
      ((d + m) * deriv U (a.consumption t) -
        deriv U (a.consumption t) * deriv f (a.capital t)) t := by
    intro t ht
    exact euler_implies_current_value_costate (hcd t ht)
      (hU2 _ (a.consumption_pos t ht)) (heuler t ht)
  let v := cassSupportingPrices f U (fun t => deriv U (a.consumption t)) d m a
    hfconc hUconc hUcont hfderiv hUderiv hfprime hUprime hak hmu hq
  obtain ⟨K, _, hcapacity⟩ :=
    exists_capacity_of_marginal_product_tendsto_zero f m hm hfconc hfderiv hfprime_top
  let K' := max K (a.capital 0)
  have hcapacity' : ∀ x, K' ≤ x → f x ≤ m * x :=
    fun x hx => hcapacity x ((le_max_left _ _).trans hx)
  have ha0 : a.capital 0 ≤ K' := le_max_right _ _
  have hb0 : b.capital 0 ≤ K' := hinit ▸ ha0
  have hmucont : ContinuousAt (deriv U) cstar :=
    hUprime.continuousAt (isOpen_Ioi.mem_nhds hcstar)
  have hprice : Tendsto v.price atTop (𝓝 0) :=
    Terminal.discounted_price_tendsto_zero_of_consumption_limit hd hconvergence hmucont
  exact infinite_horizon_optimality_of_bounded_capital v b
    (allocation_of_interior v (fun _ _ => rfl)) hinit ha hb hprice
    (a.capital_le_capacity hcapacity' ha0) (b.capital_le_capacity hcapacity' hb0)

end RamseyCassKoopmans


/-!
# Strict welfare separation and consumption uniqueness

With strictly concave utility and positive welfare weights, a feasible competitor
whose consumption differs at even one nonnegative time has strictly lower finite
limiting welfare than a supplied certified candidate. Continuity of controls is
essential here: it turns a strict pointwise gap into a positive integral.

This is uniqueness conditional on a supplied candidate and the stated terminal
comparison; it does not construct an optimal trajectory.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

/-- A continuous nonnegative function that is positive at one nonnegative time
has a strictly positive limiting cumulative integral, whenever that limit exists.
The proof uses a positive finite integral and monotonicity thereafter. -/
theorem positive_limit_of_integral_nonneg_of_pos
    {F : ℝ → ℝ} {L t₀ : ℝ}
    (hcont : ContinuousOn F (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ F t)
    (ht₀ : 0 ≤ t₀) (hpos : 0 < F t₀)
    (hlim : Tendsto (fun T => ∫ t in (0 : ℝ)..T, F t) atTop (𝓝 L)) :
    0 < L := by
  have hT₀ : 0 < t₀ + 1 := by linarith
  have hpositive : 0 < ∫ t in (0 : ℝ)..(t₀ + 1), F t := by
    apply intervalIntegral.integral_pos hT₀
      (hcont.mono (fun _ ht => ht.1))
    · intro t ht
      exact hnonneg t ht.1.le
    · exact ⟨t₀, ⟨ht₀, by linarith⟩, hpos⟩
  have hle : (∫ t in (0 : ℝ)..(t₀ + 1), F t) ≤ L := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [eventually_ge_atTop (t₀ + 1)] with T hT
    have hTpos : 0 ≤ T := hT₀.le.trans hT
    apply intervalIntegral.integral_mono_interval le_rfl hT₀.le hT
    · exact (ae_restrict_mem measurableSet_Ioc).mono (fun t ht => hnonneg t ht.1.le)
    · exact (hcont.mono (fun _ ht => ht.1)).intervalIntegrable_of_Icc hTpos
  exact hpositive.trans_le hle

/-- The nonnegative instantaneous comparison surplus: weighted utility
advantage plus the derivative of the terminal-capital value gap. -/
noncomputable def comparisonSurplus {f U w : ℝ → ℝ} {m : ℝ}
    {a : FeasiblePath f m} (v : SupportingPrices f U w m a)
    (b : FeasiblePath f m) (t : ℝ) : ℝ :=
    w t * (U (a.consumption t) - U (b.consumption t)) + boundaryRate v b t

theorem comparisonSurplus_continuous {f U w : ℝ → ℝ} {m : ℝ}
    {a : FeasiblePath f m} (v : SupportingPrices f U w m a)
    (b : FeasiblePath f m) : ContinuousOn (comparisonSurplus v b) (Ici 0) := by
  exact (v.weight_continuous.mul
    ((v.utility_continuous.comp a.consumption_continuous
      (fun t ht => a.consumption_pos t ht)).sub
        (v.utility_continuous.comp b.consumption_continuous
          (fun t ht => b.consumption_pos t ht)))).add (boundaryRate_continuous v b)

/-- Strict utility concavity contributes a strict surplus whenever candidate
and competitor consumption differ. Production and allocation terms remain
nonnegative, including Cass's zero-investment corner. -/
theorem comparisonSurplus_pos_of_consumption_ne
    {f U w : ℝ → ℝ} {m t : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (ht : 0 ≤ t)
    (hstrict : StrictConcaveOn ℝ (Ioi 0) U)
    (hderiv : HasDerivAt U (v.marginalUtility t) (a.consumption t))
    (hw : 0 < w t) (hne : b.consumption t ≠ a.consumption t) :
    0 < comparisonSurplus v b t := by
  have hu := concavity_remainder_pos hstrict
    (a.consumption_pos t ht) (b.consumption_pos t ht) hderiv hne
  have hf : 0 ≤ f (a.capital t) - f (b.capital t) -
      v.marginalProduct t * (a.capital t - b.capital t) := by
    nlinarith [v.production_support t ht (b.capital t) (b.capital_nonneg t ht)]
  unfold comparisonSurplus boundaryRate
  rw [present_value_welfare_identity
    (U (a.consumption t)) (U (b.consumption t))
    (f (a.capital t)) (f (b.capital t))
    (a.consumption t) (b.consumption t) (a.investment t) (b.investment t)
    (a.capital t) (b.capital t) (v.marginalProduct t) (v.marginalUtility t)
    (v.price t) m (w t)
    (m * v.price t - w t * v.marginalUtility t * v.marginalProduct t)
    (a.resource t ht) (b.resource t ht) rfl]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (mul_pos hw hu)
      (mul_nonneg (mul_nonneg hw.le (v.marginalUtility_nonneg t ht)) hf)) (halloc t ht)

/-- Fundamental theorem of calculus gives an exact finite-horizon surplus
identity. In particular, the terminal value is retained with its correct sign. -/
theorem integral_comparisonSurplus
    {f U w : ℝ → ℝ} {m T : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (hinit : a.capital 0 = b.capital 0) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, comparisonSurplus v b t) =
      welfare U w a.consumption T - welfare U w b.consumption T +
        boundary v.price a.capital b.capital T := by
  have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
  have haint := ((welfare_integrand_continuous v a).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hT
  have hbint := ((welfare_integrand_continuous v b).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hT
  have hBint := ((boundaryRate_continuous v b).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hT
  have hFTC : (∫ t in (0 : ℝ)..T, boundaryRate v b t) =
      boundary v.price a.capital b.capital T - boundary v.price a.capital b.capital 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hBint
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact hasDerivAt_boundary v b ht.1
  simp only [comparisonSurplus, mul_sub]
  rw [intervalIntegral.integral_add (haint.sub hbint) hBint,
    intervalIntegral.integral_sub haint hbint, hFTC]
  simp [welfare, boundary, hinit]

/-- Convergence of finite welfare and the terminal gap implies convergence of
the cumulative comparison surplus to the candidate's welfare advantage. -/
theorem tendsto_integral_comparisonSurplus
    {f U w : ℝ → ℝ} {m Ja Jb : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0)) :
    Tendsto (fun T => ∫ t in (0 : ℝ)..T, comparisonSurplus v b t)
      atTop (𝓝 (Ja - Jb)) := by
  have hlim := (ha.sub hb).add hterminal
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (integral_comparisonSurplus v b hinit hT).symm

/-- A feasible competitor whose consumption differs at any nonnegative time
has strictly lower finite limiting welfare than the certified candidate. -/
theorem strict_welfare_separation
    {f U w : ℝ → ℝ} {m Ja Jb t₀ : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0))
    (hstrict : StrictConcaveOn ℝ (Ioi 0) U)
    (ht₀ : 0 ≤ t₀)
    (hderiv : HasDerivAt U (v.marginalUtility t₀) (a.consumption t₀))
    (hw : 0 < w t₀) (hne : b.consumption t₀ ≠ a.consumption t₀) :
    Jb < Ja := by
  have hpos : 0 < Ja - Jb := positive_limit_of_integral_nonneg_of_pos
    (comparisonSurplus_continuous v b)
    (fun t ht => pointwise_comparison v b halloc ht) ht₀
    (comparisonSurplus_pos_of_consumption_ne v b halloc ht₀ hstrict hderiv hw hne)
    (tendsto_integral_comparisonSurplus v b hinit ha hb hterminal)
  linarith

/-- Equal finite welfare forces equality of consumption at every nonnegative
time. Continuous controls make pointwise equality appropriate, rather than
merely equality almost everywhere. -/
theorem consumption_eq_of_welfare_eq
    {f U w : ℝ → ℝ} {m Ja Jb : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0))
    (hstrict : StrictConcaveOn ℝ (Ioi 0) U)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt U (v.marginalUtility t) (a.consumption t))
    (hw : ∀ t, 0 ≤ t → 0 < w t) (heq : Jb = Ja) :
    ∀ t, 0 ≤ t → b.consumption t = a.consumption t := by
  intro t ht
  by_contra hne
  have hlt := strict_welfare_separation v b halloc hinit ha hb hterminal hstrict ht
    (hderiv t ht) (hw t ht) hne
  linarith

/-- Strictly concave production gives a strictly positive surplus at a capital
discrepancy, provided the utility marginal value and welfare weight are positive. -/
theorem comparisonSurplus_pos_of_capital_ne
    {f U w : ℝ → ℝ} {m t : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (ht : 0 ≤ t)
    (hstrict : StrictConcaveOn ℝ (Ici 0) f)
    (hderiv : HasDerivAt f (v.marginalProduct t) (a.capital t))
    (hw : 0 < w t) (hmu : 0 < v.marginalUtility t)
    (hne : b.capital t ≠ a.capital t) : 0 < comparisonSurplus v b t := by
  have hf := concavity_remainder_pos hstrict
    (a.capital_nonneg t ht) (b.capital_nonneg t ht) hderiv hne
  have hu : 0 ≤ U (a.consumption t) - U (b.consumption t) -
      v.marginalUtility t * (a.consumption t - b.consumption t) := by
    nlinarith [v.utility_support t ht (b.consumption t) (b.consumption_pos t ht)]
  unfold comparisonSurplus boundaryRate
  rw [present_value_welfare_identity
    (U (a.consumption t)) (U (b.consumption t))
    (f (a.capital t)) (f (b.capital t))
    (a.consumption t) (b.consumption t) (a.investment t) (b.investment t)
    (a.capital t) (b.capital t) (v.marginalProduct t) (v.marginalUtility t)
    (v.price t) m (w t)
    (m * v.price t - w t * v.marginalUtility t * v.marginalProduct t)
    (a.resource t ht) (b.resource t ht) rfl]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_nonneg_of_pos (mul_nonneg hw.le hu) (mul_pos (mul_pos hw hmu) hf))
      (halloc t ht)

/-- A capital discrepancy likewise forces strictly lower competitor welfare
when production is strictly concave and marginal utility is strictly positive. -/
theorem strict_welfare_separation_of_capital_ne
    {f U w : ℝ → ℝ} {m Ja Jb t₀ : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0))
    (hstrict : StrictConcaveOn ℝ (Ici 0) f)
    (ht₀ : 0 ≤ t₀)
    (hderiv : HasDerivAt f (v.marginalProduct t₀) (a.capital t₀))
    (hw : 0 < w t₀) (hmu : 0 < v.marginalUtility t₀)
    (hne : b.capital t₀ ≠ a.capital t₀) : Jb < Ja := by
  have hpos : 0 < Ja - Jb := positive_limit_of_integral_nonneg_of_pos
    (comparisonSurplus_continuous v b)
    (fun t ht => pointwise_comparison v b halloc ht) ht₀
    (comparisonSurplus_pos_of_capital_ne v b halloc ht₀ hstrict hderiv hw hmu hne)
    (tendsto_integral_comparisonSurplus v b hinit ha hb hterminal)
  linarith

/-- Equal welfare forces capital equality under strict technology concavity,
actual marginal-product prices and positive marginal utility. -/
theorem capital_eq_of_welfare_eq
    {f U w : ℝ → ℝ} {m Ja Jb : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0))
    (hstrict : StrictConcaveOn ℝ (Ici 0) f)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt f (v.marginalProduct t) (a.capital t))
    (hw : ∀ t, 0 ≤ t → 0 < w t)
    (hmu : ∀ t, 0 ≤ t → 0 < v.marginalUtility t) (heq : Jb = Ja) :
    ∀ t, 0 ≤ t → b.capital t = a.capital t := by
  intro t ht
  by_contra hne
  have hlt := strict_welfare_separation_of_capital_ne v b halloc hinit ha hb hterminal
    hstrict ht (hderiv t ht) (hw t ht) (hmu t ht) hne
  linarith

/-- Under strict utility and technology concavity, equal finite welfare implies
equality of capital, consumption and investment on the economic time domain.
The proof includes the investment identity via feasibility; no uniqueness of an
unconstructed ODE solution is assumed. -/
theorem path_eq_of_welfare_eq
    {f U w : ℝ → ℝ} {m Ja Jb : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0))
    (hstrictU : StrictConcaveOn ℝ (Ioi 0) U)
    (hstrictF : StrictConcaveOn ℝ (Ici 0) f)
    (hderivU : ∀ t, 0 ≤ t → HasDerivAt U (v.marginalUtility t) (a.consumption t))
    (hderivF : ∀ t, 0 ≤ t → HasDerivAt f (v.marginalProduct t) (a.capital t))
    (hw : ∀ t, 0 ≤ t → 0 < w t)
    (hmu : ∀ t, 0 ≤ t → 0 < v.marginalUtility t) (heq : Jb = Ja) :
    ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
      b.consumption t = a.consumption t ∧ b.investment t = a.investment t := by
  intro t ht
  have hk := capital_eq_of_welfare_eq v b halloc hinit ha hb hterminal
    hstrictF hderivF hw hmu heq t ht
  have hc := consumption_eq_of_welfare_eq v b halloc hinit ha hb hterminal
    hstrictU hderivU hw heq t ht
  refine ⟨hk, hc, ?_⟩
  have hresourceA := a.resource t ht
  have hresourceB := b.resource t ht
  rw [hk, hc] at hresourceB
  linarith

end RamseyCassKoopmans


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


/-!
# A solvable nonstationary growth economy

Here both production and utility are `2 * sqrt`, with effective discount and
depreciation/dilution equal to one. The utility differs from the logarithmic
stationary example. This is the CRRA elasticity 1/2 specialization, not the
general Cass theorem. The transformed state `x = sqrt k` solves `x' = 1 - 2x`
on the interior optimal branch. No optimal path or convergence is postulated.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans.ClosedForm

noncomputable def utility (c : ℝ) : ℝ := 2 * Real.sqrt c
noncomputable def state (x₀ t : ℝ) : ℝ := 1 / 2 + (x₀ - 1 / 2) * discount 2 t
noncomputable def capital (x₀ t : ℝ) : ℝ := state x₀ t ^ 2
noncomputable def consumption (x₀ t : ℝ) : ℝ := 3 * state x₀ t ^ 2
noncomputable def investment (x₀ t : ℝ) : ℝ :=
  2 * state x₀ t - 3 * state x₀ t ^ 2

theorem state_zero (x₀ : ℝ) : state x₀ 0 = x₀ := by simp [state, discount]

theorem discount_le_one {d t : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ t) : discount d t ≤ 1 := by
  unfold discount
  exact Real.exp_le_one_iff.mpr (by nlinarith)

theorem state_pos {x₀ t : ℝ} (hx : 0 < x₀) (ht : 0 ≤ t) : 0 < state x₀ t := by
  have he := discount_pos 2 t
  have hle := discount_le_one (d := 2) (by norm_num) ht
  have hprod : 0 < x₀ * discount 2 t := mul_pos hx he
  unfold state
  nlinarith

theorem state_le_max {x₀ t : ℝ} (ht : 0 ≤ t) : state x₀ t ≤ max x₀ (1 / 2) := by
  have he := (discount_pos 2 t).le
  have hle := discount_le_one (d := 2) (by norm_num) ht
  rcases le_total x₀ (1 / 2) with hx | hx
  · rw [max_eq_right hx]
    have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) he
    dsimp [state]
    linarith
  · rw [max_eq_left hx]
    have := mul_le_mul_of_nonneg_left hle (sub_nonneg.mpr hx)
    dsimp [state]
    linarith

theorem hasDerivAt_state (x₀ t : ℝ) :
    HasDerivAt (state x₀) (1 - 2 * state x₀ t) t := by
  convert ((hasDerivAt_discount 2 t).const_mul (x₀ - 1 / 2)).const_add (1 / 2) using 1
  · rfl
  · dsimp [state]
    ring

theorem state_continuous (x₀ : ℝ) : Continuous (state x₀) := by
  exact ((discount_continuous 2).const_mul (x₀ - 1 / 2)).const_add (1 / 2)

theorem state_tendsto (x₀ : ℝ) : Tendsto (state x₀) atTop (𝓝 (1 / 2)) := by
  have h := ((Terminal.discount_factor_tendsto_zero (d := 2) (by norm_num)).const_mul
    (x₀ - 1 / 2)).const_add (1 / 2)
  change Tendsto (fun t => 1 / 2 + (x₀ - 1 / 2) * Real.exp (-2 * t)) _ _
  simpa only [mul_zero, add_zero] using h

theorem hasDerivAt_capital (x₀ t : ℝ) :
    HasDerivAt (capital x₀) (investment x₀ t - capital x₀ t) t := by
  convert (hasDerivAt_state x₀ t).pow 2 using 1
  · rfl
  · dsimp [capital, investment]
    ring

theorem capital_tendsto (x₀ : ℝ) : Tendsto (capital x₀) atTop (𝓝 (1 / 4)) := by
  convert (state_tendsto x₀).pow 2 using 1
  · rfl
  · norm_num

theorem consumption_tendsto (x₀ : ℝ) :
    Tendsto (consumption x₀) atTop (𝓝 (3 / 4)) := by
  convert (capital_tendsto x₀).const_mul 3 using 1
  · rfl
  · norm_num

theorem sqrt_capital {x₀ t : ℝ} (hx : 0 < x₀) (ht : 0 ≤ t) :
    Real.sqrt (capital x₀ t) = state x₀ t := by
  exact Real.sqrt_sq (state_pos hx ht).le

theorem sqrt_consumption {x₀ t : ℝ} (hx : 0 < x₀) (ht : 0 ≤ t) :
    Real.sqrt (consumption x₀ t) = Real.sqrt 3 * state x₀ t := by
  rw [consumption, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3),
    Real.sqrt_sq (state_pos hx ht).le]

/-- An explicit globally feasible path for every positive transformed initial
state, allowing disinvestment as in the Koopmans resource convention. -/
noncomputable def path (x₀ : ℝ) (hx : 0 < x₀) : FeasiblePath Examples.production 1 where
  capital := capital x₀
  consumption := consumption x₀
  investment := investment x₀
  capital_nonneg := fun _ _ => sq_nonneg _
  consumption_pos := fun t ht => mul_pos (by norm_num) (sq_pos_of_pos (state_pos hx ht))
  consumption_continuous := by
    exact (continuous_const.mul ((state_continuous x₀).pow 2)).continuousOn
  investment_continuous := by
    exact (((state_continuous x₀).const_mul 2).sub
      (continuous_const.mul ((state_continuous x₀).pow 2))).continuousOn
  resource := fun t ht => by
    dsimp [Examples.production]
    rw [sqrt_capital hx ht]
    dsimp [consumption, investment]
    ring
  dynamics := fun t _ => by simpa only [one_mul] using hasDerivAt_capital x₀ t

theorem path_initial (x₀ : ℝ) (hx : 0 < x₀) : (path x₀ hx).capital 0 = x₀ ^ 2 := by
  change state x₀ 0 ^ 2 = x₀ ^ 2
  rw [state_zero]

/-- The interior branch satisfies Cass's investment constraint when the initial
transformed state does not exceed 2/3. Larger stocks require the corner branch. -/
theorem path_nonnegativeInvestment (x₀ : ℝ) (hx : 0 < x₀) (hupper : x₀ ≤ 2 / 3) :
    (path x₀ hx).NonnegativeInvestment := by
  intro t ht
  have hpos := (state_pos hx ht).le
  have hbound : state x₀ t ≤ 2 / 3 :=
    (state_le_max ht).trans (max_le hupper (by norm_num))
  change 0 ≤ 2 * state x₀ t - 3 * state x₀ t ^ 2
  nlinarith [mul_nonneg hpos (show 0 ≤ 2 - 3 * state x₀ t by linarith)]

theorem utility_continuous : Continuous utility :=
  continuous_const.mul Real.continuous_sqrt

theorem utility_strictConcave : StrictConcaveOn ℝ (Ici 0) utility := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have h := Real.strictConcaveOn_sqrt.2 hx hy hxy ha hb hab
  simp only [utility, smul_eq_mul] at *
  nlinarith

theorem hasDerivAt_utility {c : ℝ} (hc : 0 < c) :
    HasDerivAt utility (Real.sqrt c)⁻¹ c := by
  have hs : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  convert (Real.hasDerivAt_sqrt (ne_of_gt hc)).const_mul 2 using 1
  · rfl
  · field_simp

theorem hasDerivAt_utility_consumption {x₀ t : ℝ} (hx : 0 < x₀) (ht : 0 ≤ t) :
    HasDerivAt utility (Real.sqrt 3 * state x₀ t)⁻¹ (consumption x₀ t) := by
  have hc : 0 < consumption x₀ t := (path x₀ hx).consumption_pos t ht
  simpa only [sqrt_consumption hx ht] using hasDerivAt_utility hc

theorem hasDerivAt_production_capital {x₀ t : ℝ} (hx : 0 < x₀) (ht : 0 ≤ t) :
    HasDerivAt Examples.production (state x₀ t)⁻¹ (capital x₀ t) := by
  have hk : 0 < capital x₀ t := sq_pos_of_pos (state_pos hx ht)
  change HasDerivAt utility (state x₀ t)⁻¹ (capital x₀ t)
  simpa only [sqrt_capital hx ht] using hasDerivAt_utility hk

noncomputable def shadow (x₀ t : ℝ) : ℝ := (Real.sqrt 3 * state x₀ t)⁻¹

theorem shadow_continuousOn (x₀ : ℝ) (hx : 0 < x₀) :
    ContinuousOn (shadow x₀) (Ici 0) := by
  apply (continuousOn_const.mul (state_continuous x₀).continuousOn).inv₀
  intro t ht
  exact ne_of_gt (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (state_pos hx ht))

theorem hasDerivAt_shadow {x₀ t : ℝ} (hx : 0 < x₀) (ht : 0 ≤ t) :
    HasDerivAt (shadow x₀) (2 * shadow x₀ t - shadow x₀ t * (state x₀ t)⁻¹) t := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hx' : state x₀ t ≠ 0 := ne_of_gt (state_pos hx ht)
  convert ((hasDerivAt_state x₀ t).const_mul (Real.sqrt 3)).inv (mul_ne_zero hs hx') using 1
  · rfl
  · dsimp [shadow]
    field_simp
    ring

noncomputable def supportingPrices (x₀ : ℝ) (hx : 0 < x₀) :
    SupportingPrices Examples.production utility (discount 1) 1 (path x₀ hx) where
  price := fun t => discount 1 t * shadow x₀ t
  marginalUtility := shadow x₀
  marginalProduct := fun t => (state x₀ t)⁻¹
  weight_nonneg := fun t _ => (discount_pos 1 t).le
  weight_continuous := (discount_continuous 1).continuousOn
  utility_continuous := utility_continuous.continuousOn
  marginalUtility_continuous := shadow_continuousOn x₀ hx
  marginalProduct_continuous := (state_continuous x₀).continuousOn.inv₀
    (fun _ ht => ne_of_gt (state_pos hx ht))
  marginalUtility_nonneg := fun t ht => inv_nonneg.mpr
    (mul_nonneg (Real.sqrt_nonneg 3) (state_pos hx ht).le)
  utility_support := fun t ht _c hc => concave_support
    (utility_strictConcave.concaveOn) ((path x₀ hx).consumption_pos t ht).le hc.le
    (hasDerivAt_utility_consumption hx ht)
  production_support := fun t ht _k hk => concave_support Examples.production_concave
    ((path x₀ hx).capital_nonneg t ht) hk (hasDerivAt_production_capital hx ht)
  costate := fun t ht => by
    apply hasDerivAt_discounted_costate (d := 1) (m := 1)
    simpa only [one_add_one_eq_two] using hasDerivAt_shadow hx ht

theorem shadow_tendsto (x₀ : ℝ) :
    Tendsto (shadow x₀) atTop (𝓝 (Real.sqrt 3 * (1 / 2))⁻¹) := by
  exact ((state_tendsto x₀).const_mul (Real.sqrt 3)).inv₀
    (mul_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))) (by norm_num))

theorem welfare_integrand {x₀ t : ℝ} (hx : 0 < x₀) (ht : 0 ≤ t) :
    discount 1 t * utility (consumption x₀ t) =
      Real.sqrt 3 * discount 1 t +
        2 * Real.sqrt 3 * (x₀ - 1 / 2) * discount 3 t := by
  have he : discount 1 t * discount 2 t = discount 3 t := by
    rw [discount, discount, ← Real.exp_add]
    congr 1
    ring
  rw [utility, sqrt_consumption hx ht, state]
  calc
    _ = Real.sqrt 3 * discount 1 t +
        2 * Real.sqrt 3 * (x₀ - 1 / 2) * (discount 1 t * discount 2 t) := by ring
    _ = _ := by rw [he]

theorem integral_discount (d T : ℝ) (hd : 0 < d) :
    (∫ t in (0 : ℝ)..T, discount d t) = (1 - discount d T) / d := by
  simpa only [welfare, mul_one, one_mul] using
    welfare_constant_consumption (fun _ => (1 : ℝ)) 1 d T hd

theorem welfare_path (x₀ : ℝ) (hx : 0 < x₀) {T : ℝ} (hT : 0 ≤ T) :
    welfare utility (discount 1) (path x₀ hx).consumption T =
      Real.sqrt 3 * (1 - discount 1 T) +
        (2 * Real.sqrt 3 * (x₀ - 1 / 2)) * ((1 - discount 3 T) / 3) := by
  unfold welfare
  change (∫ t in (0 : ℝ)..T, discount 1 t * utility (consumption x₀ t)) = _
  have heq : (∫ t in (0 : ℝ)..T, discount 1 t * utility (consumption x₀ t)) =
      ∫ t in (0 : ℝ)..T, (Real.sqrt 3 * discount 1 t +
        2 * Real.sqrt 3 * (x₀ - 1 / 2) * discount 3 t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact welfare_integrand hx ht.1
  rw [heq, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_discount 1 T (by norm_num), integral_discount 3 T (by norm_num)]
    simp only [div_one]
  · exact (continuous_const.mul (discount_continuous 1)).intervalIntegrable 0 T
  · exact (continuous_const.mul (discount_continuous 3)).intervalIntegrable 0 T

theorem path_hasWelfare (x₀ : ℝ) (hx : 0 < x₀) :
    HasWelfare utility (discount 1) (path x₀ hx).consumption
      (2 * Real.sqrt 3 * (1 + x₀) / 3) := by
  unfold HasWelfare
  have h1 := Terminal.discount_factor_tendsto_zero (d := 1) (by norm_num)
  have h3 := Terminal.discount_factor_tendsto_zero (d := 3) (by norm_num)
  have hlim := ((h1.const_sub 1).const_mul (Real.sqrt 3)).add
    (((h3.const_sub 1).div_const 3).const_mul (2 * Real.sqrt 3 * (x₀ - 1 / 2)))
  convert hlim.congr' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact (welfare_path x₀ hx hT).symm) using 1
  simp only [sub_zero, mul_one]
  congr 1
  ring

theorem state_strictMono {x₀ : ℝ} (hx : x₀ < 1 / 2) : StrictMono (state x₀) := by
  intro s t hst
  have he : discount 2 t < discount 2 s := Real.exp_lt_exp.mpr (by linarith)
  have hprod := mul_lt_mul_of_neg_left he (sub_neg.mpr hx)
  dsimp [state]
  linarith

theorem state_strictAnti {x₀ : ℝ} (hx : 1 / 2 < x₀) : StrictAnti (state x₀) := by
  intro s t hst
  have he : discount 2 t < discount 2 s := Real.exp_lt_exp.mpr (by linarith)
  have hprod := mul_lt_mul_of_pos_left he (sub_pos.mpr hx)
  dsimp [state]
  linarith

theorem capital_strictMonoOn {x₀ : ℝ} (hx : 0 < x₀) (hstar : x₀ < 1 / 2) :
    StrictMonoOn (capital x₀) (Ici 0) := by
  intro s hs t ht hst
  have h := state_strictMono hstar hst
  have hspos := state_pos hx hs
  have htpos := state_pos hx ht
  dsimp [capital]
  nlinarith

theorem capital_strictAntiOn {x₀ : ℝ} (hx : 0 < x₀) (hstar : 1 / 2 < x₀) :
    StrictAntiOn (capital x₀) (Ici 0) := by
  intro s hs t ht hst
  have h := state_strictAnti hstar hst
  have hspos := state_pos hx hs
  have htpos := state_pos hx ht
  dsimp [capital]
  nlinarith

theorem consumption_strictMonoOn {x₀ : ℝ} (hx : 0 < x₀) (hstar : x₀ < 1 / 2) :
    StrictMonoOn (consumption x₀) (Ici 0) := by
  intro s hs t ht hst
  exact mul_lt_mul_of_pos_left (capital_strictMonoOn hx hstar hs ht hst) (by norm_num)

theorem consumption_strictAntiOn {x₀ : ℝ} (hx : 0 < x₀) (hstar : 1 / 2 < x₀) :
    StrictAntiOn (consumption x₀) (Ici 0) := by
  intro s hs t ht hst
  exact mul_lt_mul_of_pos_left (capital_strictAntiOn hx hstar hs ht hst) (by norm_num)

/-- Global optimality of the constructed nonstationary path. The only hypotheses
on the candidate are the positive initial stock; feasibility, welfare, prices,
and their limits have all been constructed and proved. -/
theorem path_optimal (x₀ : ℝ) (hx : 0 < x₀)
    (b : FeasiblePath Examples.production 1) (J : ℝ)
    (hinit : b.capital 0 = x₀ ^ 2)
    (hb : HasWelfare utility (discount 1) b.consumption J) :
    J ≤ 2 * Real.sqrt 3 * (1 + x₀) / 3 := by
  let v := supportingPrices x₀ hx
  let K := max 4 (x₀ ^ 2)
  have hcap : ∀ k, K ≤ k → Examples.production k ≤ 1 * k :=
    fun k hk => Examples.production_capacity k ((le_max_left _ _).trans hk)
  have ha0 : (path x₀ hx).capital 0 ≤ K := by
    rw [path_initial]
    exact le_max_right _ _
  have hb0 : b.capital 0 ≤ K := by rw [hinit]; exact le_max_right _ _
  exact infinite_horizon_optimality_of_bounded_capital v b
    (allocation_of_interior v (fun _ _ => rfl))
    ((path_initial x₀ hx).trans hinit.symm) (path_hasWelfare x₀ hx) hb
    (Terminal.discounted_price_tendsto_zero (d := 1) (by norm_num) (shadow_tendsto x₀))
    ((path x₀ hx).capital_le_capacity hcap ha0) (b.capital_le_capacity hcap hb0)

/-- For every positive initial capital there is a globally feasible optimal
path converging to the modified-golden-rule capital and consumption. This is
the square-root utility/technology specialization with disinvestment allowed. -/
theorem exists_optimal_convergent_path (k₀ : ℝ) (hk : 0 < k₀) :
    ∃ a : FeasiblePath Examples.production 1,
      a.capital 0 = k₀ ∧
      HasWelfare utility (discount 1) a.consumption (2 * Real.sqrt 3 * (1 + Real.sqrt k₀) / 3) ∧
      Tendsto a.capital atTop (𝓝 (1 / 4)) ∧ Tendsto a.consumption atTop (𝓝 (3 / 4)) ∧
      ∀ b : FeasiblePath Examples.production 1, b.capital 0 = k₀ →
        ∀ J, HasWelfare utility (discount 1) b.consumption J →
          J ≤ 2 * Real.sqrt 3 * (1 + Real.sqrt k₀) / 3 := by
  have hx := Real.sqrt_pos.mpr hk
  refine ⟨path (Real.sqrt k₀) hx, ?_, path_hasWelfare _ hx,
    capital_tendsto _, consumption_tendsto _, ?_⟩
  · rw [path_initial, Real.sq_sqrt hk.le]
  · intro b hb J hJ
    apply path_optimal _ hx b J _ hJ
    simpa only [Real.sq_sqrt hk.le] using hb

/-- Below the corner threshold this same constructed path is a Cass optimum. -/
theorem path_isCassOptimal (x₀ : ℝ) (hx : 0 < x₀) (hupper : x₀ ≤ 2 / 3) :
    IsCassOptimal utility 1 (path x₀ hx) (2 * Real.sqrt 3 * (1 + x₀) / 3) := by
  refine ⟨path_nonnegativeInvestment x₀ hx hupper, path_hasWelfare x₀ hx, ?_⟩
  intro b _ hb J hJ
  exact path_optimal x₀ hx b J (hb.symm.trans (path_initial x₀ hx)) hJ

end RamseyCassKoopmans.ClosedForm


/-! # Joining economic regimes at a switching time
Original work under the Unlicense. Values and derivatives must agree at the
switch; the result does not silently assume differentiability of a branch join.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

noncomputable def joinAt (τ : ℝ) (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ τ then f t else g t

theorem joinAt_left {τ t : ℝ} (f g : ℝ → ℝ) (ht : t ≤ τ) :
    joinAt τ f g t = f t := ite_eq_left ht

theorem joinAt_right {τ t : ℝ} (f g : ℝ → ℝ) (ht : τ < t) :
    joinAt τ f g t = g t := ite_eq_right (not_le.mpr ht)

theorem continuous_joinAt {τ : ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hmatch : f τ = g τ) :
    Continuous (joinAt τ f g) := by
  apply hf.if_le hg continuous_id continuous_const
  intro t ht
  change t = τ at ht
  subst t
  exact hmatch

theorem hasDerivAt_joinAt_switch {τ v : ℝ} {f g : ℝ → ℝ}
    (hf : HasDerivAt f v τ) (hg : HasDerivAt g v τ) (hmatch : f τ = g τ) :
    HasDerivAt (joinAt τ f g) v τ := by
  have hleft : HasDerivWithinAt (joinAt τ f g) v (Iic τ) τ :=
    hf.hasDerivWithinAt.congr (fun t ht => ite_eq_left ht) (ite_eq_left le_rfl)
  have hright : HasDerivWithinAt (joinAt τ f g) v (Ici τ) τ := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      rcases eq_or_lt_of_le (show τ ≤ t from ht) with heq | hlt
      · subst t
        exact (ite_eq_left le_rfl).trans hmatch
      · exact ite_eq_right (not_le.mpr hlt)
    · exact (ite_eq_left le_rfl).trans hmatch
  have h := hleft.union hright
  rw [Iic_union_Ici] at h
  exact h.hasDerivAt Filter.univ_mem

theorem hasDerivAt_joinAt {τ t vf vg : ℝ} {f g : ℝ → ℝ}
    (hf : HasDerivAt f vf t) (hg : HasDerivAt g vg t)
    (hmatch : f τ = g τ) (hderiv : t = τ → vf = vg) :
    HasDerivAt (joinAt τ f g) (if t ≤ τ then vf else vg) t := by
  rcases lt_trichotomy t τ with hlt | heq | hgt
  · rw [ite_eq_left hlt.le]
    apply hf.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hlt] with s hs
    exact ite_eq_left hs.le
  · subst t
    rw [ite_eq_left le_rfl]
    exact hasDerivAt_joinAt_switch hf (hg.congr_deriv (hderiv rfl).symm) hmatch
  · rw [ite_eq_right (not_le.mpr hgt)]
    apply hg.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hgt] with s hs
    exact ite_eq_right (not_le.mpr hs)

theorem strictAnti_joinAt {τ : ℝ} {f g : ℝ → ℝ}
    (hf : StrictAnti f) (hg : StrictAnti g) (hmatch : f τ = g τ) :
    StrictAnti (joinAt τ f g) := by
  intro s t hst
  by_cases ht : t ≤ τ
  · rw [joinAt_left f g ht, joinAt_left f g (hst.le.trans ht)]
    exact hf hst
  · rw [joinAt_right f g (lt_of_not_ge ht)]
    by_cases hs : s ≤ τ
    · rw [joinAt_left f g hs]
      calc
        g t < g τ := hg (lt_of_not_ge ht)
        _ = f τ := hmatch.symm
        _ ≤ f s := hf.antitone hs
    · rw [joinAt_right f g (lt_of_not_ge hs)]
      exact hg hst

theorem tendsto_joinAt_atTop {τ L : ℝ} {f g : ℝ → ℝ}
    (hg : Tendsto g atTop (𝓝 L)) : Tendsto (joinAt τ f g) atTop (𝓝 L) := by
  apply hg.congr'
  filter_upwards [eventually_gt_atTop τ] with t ht
  exact (joinAt_right f g ht).symm

end RamseyCassKoopmans


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


/-! # A global Cass path with an initial zero-investment segment -/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans.ClosedForm.Corner

noncomputable def joinedCapital (τ : ℝ) : ℝ → ℝ :=
  joinAt τ (preCapital τ) (fun t => capital (2 / 3) (t - τ))
noncomputable def joinedConsumption (τ : ℝ) : ℝ → ℝ :=
  joinAt τ (preConsumption τ) (fun t => consumption (2 / 3) (t - τ))
noncomputable def joinedInvestment (τ : ℝ) : ℝ → ℝ :=
  joinAt τ (fun _ => 0) (fun t => investment (2 / 3) (t - τ))
noncomputable def joinedShadow (τ : ℝ) : ℝ → ℝ :=
  joinAt τ (preShadow τ) (fun t => shadow (2 / 3) (t - τ))
noncomputable def joinedMu (τ : ℝ) : ℝ → ℝ :=
  joinAt τ (preMu τ) (fun t => shadow (2 / 3) (t - τ))
noncomputable def joinedMp (τ : ℝ) : ℝ → ℝ :=
  joinAt τ (preMp τ) (fun t => (state (2 / 3) (t - τ))⁻¹)

theorem tail_state_pos (t : ℝ) : 0 < state (2 / 3) t := by
  have := discount_pos 2 t
  dsimp [state]
  nlinarith

theorem tail_shadow_hasDerivAt (t : ℝ) :
    HasDerivAt (shadow (2 / 3))
      (2 * shadow (2 / 3) t - shadow (2 / 3) t * (state (2 / 3) t)⁻¹) t := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hx : state (2 / 3) t ≠ 0 := ne_of_gt (tail_state_pos t)
  convert ((hasDerivAt_state (2 / 3) t).const_mul (Real.sqrt 3)).inv (mul_ne_zero hs hx) using 1
  · rfl
  · dsimp [shadow]
    field_simp
    ring

theorem tail_shadow_continuous : Continuous (shadow (2 / 3)) :=
  continuous_iff_continuousAt.mpr (fun t => (tail_shadow_hasDerivAt t).continuousAt)

theorem capital_match (τ : ℝ) : preCapital τ τ = capital (2 / 3) (τ - τ) := by
  norm_num [preCapital, inverseFactor, capital, state, discount]

theorem consumption_match (τ : ℝ) : preConsumption τ τ = consumption (2 / 3) (τ - τ) := by
  norm_num [preConsumption, inverseFactor, consumption, state, discount]

theorem investment_match (τ : ℝ) : (0 : ℝ) = investment (2 / 3) (τ - τ) := by
  norm_num [investment, state, discount]

theorem shadow_match (τ : ℝ) : preShadow τ τ = shadow (2 / 3) (τ - τ) := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  simp only [preShadow, r_switch, sub_self, shadow, state_zero]
  field_simp
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

theorem mu_match (τ : ℝ) : preMu τ τ = shadow (2 / 3) (τ - τ) := by
  rw [← shadow_match]
  norm_num [preMu, preShadow, r_switch]
  ring

theorem mp_match (τ : ℝ) : preMp τ τ = (state (2 / 3) (τ - τ))⁻¹ := by
  norm_num [preMp, r_switch, state_zero]

theorem hasDerivAt_joinedCapital (τ t : ℝ) :
    HasDerivAt (joinedCapital τ) (joinedInvestment τ t - joinedCapital τ t) t := by
  have htail : HasDerivAt (fun s => capital (2 / 3) (s - τ))
      (investment (2 / 3) (t - τ) - capital (2 / 3) (t - τ)) t := by
    convert (hasDerivAt_capital (2 / 3) (t - τ)).comp t ((hasDerivAt_id t).sub_const τ) using 1
    · rfl
    · simp
  have h := hasDerivAt_joinAt (hasDerivAt_preCapital τ t) htail (capital_match τ) (by
    intro heq
    subst t
    rw [← investment_match, capital_match]
    ring)
  convert h using 1
  · rfl
  · by_cases ht : t ≤ τ <;> simp [joinedCapital, joinedInvestment, joinAt, ht]

theorem hasDerivAt_joinedShadow (τ t : ℝ) :
    HasDerivAt (joinedShadow τ)
      (2 * joinedShadow τ t - joinedMu τ t * joinedMp τ t) t := by
  have htail : HasDerivAt (fun s => shadow (2 / 3) (s - τ))
      (2 * shadow (2 / 3) (t - τ) -
        shadow (2 / 3) (t - τ) * (state (2 / 3) (t - τ))⁻¹) t := by
    convert (tail_shadow_hasDerivAt (t - τ)).comp t ((hasDerivAt_id t).sub_const τ) using 1
    · rfl
    · simp
  have h := hasDerivAt_joinAt (hasDerivAt_preShadow τ t) htail (shadow_match τ) (by
    intro heq
    subst t
    rw [shadow_match, mu_match, mp_match])
  convert h using 1
  · rfl
  · by_cases ht : t ≤ τ <;> simp [joinedShadow, joinedMu, joinedMp, joinAt, ht]

theorem joinedConsumption_continuous (τ : ℝ) : Continuous (joinedConsumption τ) := by
  apply continuous_joinAt _ _ (consumption_match τ)
  · exact continuous_const.mul ((inverseFactor_continuous τ).pow 2)
  · exact (continuous_const.mul ((state_continuous (2 / 3)).pow 2)).comp
      (continuous_id.sub continuous_const)

theorem joinedInvestment_continuous (τ : ℝ) : Continuous (joinedInvestment τ) := by
  apply continuous_joinAt (τ := τ) (f := fun _ => 0)
    (g := fun t => investment (2 / 3) (t - τ)) continuous_const _ (investment_match τ)
  exact (((state_continuous (2 / 3)).const_mul 2).sub
    (continuous_const.mul ((state_continuous (2 / 3)).pow 2))).comp
      (continuous_id.sub continuous_const)

theorem joinedMu_continuous (τ : ℝ) : Continuous (joinedMu τ) := by
  exact continuous_joinAt (continuous_const.mul (r_continuous τ))
    (tail_shadow_continuous.comp (continuous_id.sub continuous_const)) (mu_match τ)

theorem joinedMp_continuous (τ : ℝ) : Continuous (joinedMp τ) := by
  apply continuous_joinAt (τ := τ) (f := preMp τ)
    (g := fun t => (state (2 / 3) (t - τ))⁻¹) _ _ (mp_match τ)
  · exact continuous_const.mul ((r_continuous τ).pow 2)
  · exact ((state_continuous (2 / 3)).inv₀ (fun s => ne_of_gt (tail_state_pos s))).comp
      (continuous_id.sub continuous_const)

noncomputable def cornerPath (τ : ℝ) : FeasiblePath Examples.production 1 where
  capital := joinedCapital τ
  consumption := joinedConsumption τ
  investment := joinedInvestment τ
  capital_nonneg := fun t _ => by
    by_cases ht : t ≤ τ
    · change 0 ≤ joinAt _ _ _ _
      rw [joinAt_left _ _ ht]
      exact (preCapital_pos τ t).le
    · change 0 ≤ joinAt _ _ _ _
      rw [joinAt_right _ _ (lt_of_not_ge ht)]
      exact sq_nonneg _
  consumption_pos := fun t _ => by
    by_cases ht : t ≤ τ
    · change 0 < joinAt _ _ _ _
      rw [joinAt_left _ _ ht]
      exact preConsumption_pos τ t
    · change 0 < joinAt _ _ _ _
      rw [joinAt_right _ _ (lt_of_not_ge ht)]
      exact mul_pos (by norm_num) (sq_pos_of_pos (tail_state_pos _))
  consumption_continuous := (joinedConsumption_continuous τ).continuousOn
  investment_continuous := (joinedInvestment_continuous τ).continuousOn
  resource := fun t _ => by
    by_cases ht : t ≤ τ
    · simp only [joinedConsumption, joinedInvestment, joinedCapital, joinAt,
        ite_eq_left ht, add_zero]
      exact pre_resource τ t
    · simp only [joinedConsumption, joinedInvestment, joinedCapital, joinAt, ite_eq_right ht]
      exact (path (2 / 3) (by norm_num)).resource (t - τ) (by linarith)
  dynamics := fun t _ => by simpa only [one_mul] using hasDerivAt_joinedCapital τ t

theorem cornerPath_nonnegativeInvestment (τ : ℝ) : (cornerPath τ).NonnegativeInvestment := by
  intro t _
  change 0 ≤ joinedInvestment τ t
  unfold joinedInvestment
  by_cases ht : t ≤ τ
  · simp [joinAt, ht]
  · rw [joinAt_right _ _ (lt_of_not_ge ht)]
    exact path_nonnegativeInvestment (2 / 3) (by norm_num) le_rfl (t - τ) (by linarith)

theorem joinedMu_pos (τ t : ℝ) : 0 < joinedMu τ t := by
  by_cases ht : t ≤ τ
  · change 0 < joinAt _ _ _ _
    rw [joinAt_left _ _ ht]
    exact mul_pos (div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)) (r_pos τ t)
  · change 0 < joinAt _ _ _ _
    rw [joinAt_right _ _ (lt_of_not_ge ht)]
    exact inv_pos.mpr (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (tail_state_pos _))

theorem joinedShadow_nonneg (τ t : ℝ) : 0 ≤ joinedShadow τ t := by
  by_cases ht : t ≤ τ
  · change 0 ≤ joinAt _ _ _ _
    rw [joinAt_left _ _ ht]
    exact (preShadow_pos ht).le
  · change 0 ≤ joinAt _ _ _ _
    rw [joinAt_right _ _ (lt_of_not_ge ht)]
    exact inv_nonneg.mpr (mul_nonneg (Real.sqrt_nonneg 3) (tail_state_pos _).le)

theorem joinedShadow_le_joinedMu (τ t : ℝ) : joinedShadow τ t ≤ joinedMu τ t := by
  by_cases ht : t ≤ τ
  · simp only [joinedShadow, joinedMu, joinAt, ite_eq_left ht]
    exact preShadow_le_preMu ht
  · simp [joinedShadow, joinedMu, joinAt, ht]

theorem joined_complementarity (τ t : ℝ) :
    (joinedShadow τ t - joinedMu τ t) * joinedInvestment τ t = 0 := by
  by_cases ht : t ≤ τ <;> simp [joinedShadow, joinedMu, joinedInvestment, joinAt, ht]

end RamseyCassKoopmans.ClosedForm.Corner


/-! # Discounted welfare after a finite transition regime -/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

theorem discount_shift (d τ t : ℝ) : discount d t = discount d τ * discount d (t - τ) := by
  simp only [discount, ← Real.exp_add]
  congr 1
  ring

theorem welfare_of_tail_eq {U c tail : ℝ → ℝ} {d τ T : ℝ}
    (hτ : 0 ≤ τ) (hT : τ ≤ T)
    (hcont : ContinuousOn (fun t => discount d t * U (c t)) (Ici 0))
    (heq : ∀ t, τ ≤ t → c t = tail (t - τ)) :
    welfare U (discount d) c T = welfare U (discount d) c τ +
      discount d τ * welfare U (discount d) tail (T - τ) := by
  have h0 : IntervalIntegrable (fun t => discount d t * U (c t)) volume 0 τ :=
    (hcont.mono (fun _ ht => ht.1)).intervalIntegrable_of_Icc hτ
  have h1 : IntervalIntegrable (fun t => discount d t * U (c t)) volume τ T :=
    (hcont.mono (fun _ ht => hτ.trans ht.1)).intervalIntegrable_of_Icc hT
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h0 h1
  have htail : (∫ t in τ..T, discount d t * U (c t)) =
      discount d τ * welfare U (discount d) tail (T - τ) := by
    calc
      _ = ∫ t in τ..T, discount d τ * (discount d (t - τ) * U (tail (t - τ))) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hT] at ht
        dsimp only
        rw [heq t ht.1, discount_shift d τ t]
        ring
      _ = discount d τ * ∫ t in τ..T, discount d (t - τ) * U (tail (t - τ)) :=
        intervalIntegral.integral_const_mul _ _
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_right
          (fun t => discount d t * U (tail t)) τ]
        simp only [sub_self, welfare]
  change (∫ t in (0 : ℝ)..T, discount d t * U (c t)) = _
  rw [← hsplit, htail]
  rfl

theorem hasWelfare_of_tail_eq {U c tail : ℝ → ℝ} {d τ J : ℝ}
    (hτ : 0 ≤ τ)
    (hcont : ContinuousOn (fun t => discount d t * U (c t)) (Ici 0))
    (heq : ∀ t, τ ≤ t → c t = tail (t - τ))
    (htail : HasWelfare U (discount d) tail J) :
    HasWelfare U (discount d) c (welfare U (discount d) c τ + discount d τ * J) := by
  have hshift : Tendsto (fun T : ℝ => T - τ) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (-τ) tendsto_id |>.congr
      (fun T => by simp only [sub_eq_add_neg, id_eq])
  have h := ((htail.comp hshift).const_mul (discount d τ)).const_add
    (welfare U (discount d) c τ)
  apply h.congr'
  filter_upwards [eventually_ge_atTop τ] with T hT
  exact (welfare_of_tail_eq hτ hT hcont heq).symm

end RamseyCassKoopmans


/-! # Verification of the constructed corner path -/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans.ClosedForm.Corner

theorem joined_utility_derivative (τ t : ℝ) :
    HasDerivAt utility (joinedMu τ t) (joinedConsumption τ t) := by
  by_cases ht : t ≤ τ
  · simp only [joinedMu, joinedConsumption, joinAt, ite_eq_left ht]
    exact pre_utility_derivative τ t
  · simp only [joinedMu, joinedConsumption, joinAt, ite_eq_right ht]
    exact hasDerivAt_utility_consumption (by norm_num : (0 : ℝ) < 2 / 3) (by linarith)

theorem joined_production_derivative (τ t : ℝ) :
    HasDerivAt Examples.production (joinedMp τ t) (joinedCapital τ t) := by
  by_cases ht : t ≤ τ
  · simp only [joinedMp, joinedCapital, joinAt, ite_eq_left ht]
    exact pre_production_derivative τ t
  · simp only [joinedMp, joinedCapital, joinAt, ite_eq_right ht]
    exact hasDerivAt_production_capital (by norm_num : (0 : ℝ) < 2 / 3) (by linarith)

noncomputable def cornerPrices (τ : ℝ) :
    SupportingPrices Examples.production utility (discount 1) 1 (cornerPath τ) where
  price := fun t => discount 1 t * joinedShadow τ t
  marginalUtility := joinedMu τ
  marginalProduct := joinedMp τ
  weight_nonneg := fun t _ => (discount_pos 1 t).le
  weight_continuous := (discount_continuous 1).continuousOn
  utility_continuous := utility_continuous.continuousOn
  marginalUtility_continuous := (joinedMu_continuous τ).continuousOn
  marginalProduct_continuous := (joinedMp_continuous τ).continuousOn
  marginalUtility_nonneg := fun t _ => (joinedMu_pos τ t).le
  utility_support := fun t ht _c hc => concave_support utility_strictConcave.concaveOn
    ((cornerPath τ).consumption_pos t ht).le hc.le (joined_utility_derivative τ t)
  production_support := fun t ht _k hk => concave_support Examples.production_concave
    ((cornerPath τ).capital_nonneg t ht) hk (joined_production_derivative τ t)
  costate := fun t _ => by
    apply hasDerivAt_discounted_costate (d := 1) (m := 1)
    simpa only [one_add_one_eq_two] using hasDerivAt_joinedShadow τ t

theorem corner_allocation (τ : ℝ) (b : FeasiblePath Examples.production 1)
    (hb : b.NonnegativeInvestment) : AllocationComparison (cornerPrices τ) b := by
  apply allocation_of_cass
  · intro t _
    exact mul_le_mul_of_nonneg_left (joinedShadow_le_joinedMu τ t) (discount_pos 1 t).le
  · intro t _
    change (discount 1 t * joinedShadow τ t - discount 1 t * joinedMu τ t) *
      joinedInvestment τ t = 0
    calc
      _ = discount 1 t * ((joinedShadow τ t - joinedMu τ t) * joinedInvestment τ t) := by ring
      _ = 0 := by rw [joined_complementarity, mul_zero]
  · exact hb

theorem shift_tendsto (τ : ℝ) : Tendsto (fun t : ℝ => t - τ) atTop atTop := by
  simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-τ) tendsto_id

theorem joinedCapital_tendsto (τ : ℝ) : Tendsto (joinedCapital τ) atTop (𝓝 (1 / 4)) :=
  tendsto_joinAt_atTop ((capital_tendsto (2 / 3)).comp (shift_tendsto τ))

theorem joinedConsumption_tendsto (τ : ℝ) : Tendsto (joinedConsumption τ) atTop (𝓝 (3 / 4)) :=
  tendsto_joinAt_atTop ((consumption_tendsto (2 / 3)).comp (shift_tendsto τ))

theorem joinedShadow_tendsto (τ : ℝ) :
    Tendsto (joinedShadow τ) atTop (𝓝 (Real.sqrt 3 * (1 / 2))⁻¹) :=
  tendsto_joinAt_atTop ((shadow_tendsto (2 / 3)).comp (shift_tendsto τ))

noncomputable def cornerValue (τ : ℝ) : ℝ :=
  welfare utility (discount 1) (joinedConsumption τ) τ +
    discount 1 τ * (2 * Real.sqrt 3 * (1 + (2 / 3)) / 3)

theorem cornerPath_hasWelfare (τ : ℝ) (hτ : 0 ≤ τ) :
    HasWelfare utility (discount 1) (cornerPath τ).consumption (cornerValue τ) := by
  apply hasWelfare_of_tail_eq (tail := consumption (2 / 3)) hτ
  · exact ((discount_continuous 1).mul (utility_continuous.comp
      (joinedConsumption_continuous τ))).continuousOn
  · intro t ht
    change joinedConsumption τ t = _
    unfold joinedConsumption
    rcases eq_or_lt_of_le ht with heq | hlt
    · subst t
      exact (joinAt_left _ _ le_rfl).trans (consumption_match τ)
    · exact joinAt_right _ _ hlt
  · exact path_hasWelfare (2 / 3) (by norm_num)

/-- This verifies the entire joined path, including its zero-investment phase. -/
theorem cornerPath_isCassOptimal (τ : ℝ) (hτ : 0 ≤ τ) :
    IsCassOptimal utility 1 (cornerPath τ) (cornerValue τ) := by
  refine ⟨cornerPath_nonnegativeInvestment τ, cornerPath_hasWelfare τ hτ, ?_⟩
  intro b hb hinit J hJ
  let K := max 4 ((cornerPath τ).capital 0)
  have hcap : ∀ k, K ≤ k → Examples.production k ≤ 1 * k :=
    fun k hk => Examples.production_capacity k ((le_max_left _ _).trans hk)
  have ha0 : (cornerPath τ).capital 0 ≤ K := le_max_right _ _
  have hb0 : b.capital 0 ≤ K := hinit ▸ ha0
  exact infinite_horizon_optimality_of_bounded_capital (cornerPrices τ) b
    (corner_allocation τ b hb) hinit (cornerPath_hasWelfare τ hτ) hJ
    (Terminal.discounted_price_tendsto_zero (d := 1) (by norm_num) (joinedShadow_tendsto τ))
    ((cornerPath τ).capital_le_capacity hcap ha0) (b.capital_le_capacity hcap hb0)

theorem cornerPath_initial (τ : ℝ) (hτ : 0 ≤ τ) :
    (cornerPath τ).capital 0 = (4 / 9) * Real.exp τ := by
  change joinedCapital τ 0 = _
  unfold joinedCapital
  rw [joinAt_left _ _ hτ]
  dsimp [preCapital, inverseFactor]
  rw [← Real.exp_nat_mul]
  congr 2
  ring

/-- Selecting the switch from any initial capital above the corner threshold. -/
theorem cornerPath_initial_from_stock {k₀ : ℝ} (hk : 4 / 9 ≤ k₀) :
    let τ := Real.log (9 * k₀ / 4)
    0 ≤ τ ∧ (cornerPath τ).capital 0 = k₀ := by
  have harg : (1 : ℝ) ≤ 9 * k₀ / 4 := by linarith
  have hτ := Real.log_nonneg harg
  refine ⟨hτ, ?_⟩
  rw [cornerPath_initial _ hτ, Real.exp_log (by linarith : 0 < 9 * k₀ / 4)]
  ring

theorem pre_welfare_integrand (τ t : ℝ) :
    discount 1 t * utility (preConsumption τ t) =
      (4 * Real.sqrt 3 / 3 * Real.exp (τ / 4)) * discount (5 / 4) t := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hscale : 2 * (2 / Real.sqrt (3 : ℝ)) = 4 * Real.sqrt 3 / 3 := by
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have he : discount 1 t * inverseFactor τ t = Real.exp (τ / 4) * discount (5 / 4) t := by
    unfold discount inverseFactor
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [utility, sqrt_preConsumption]
  calc
    _ = (2 * (2 / Real.sqrt 3)) * (discount 1 t * inverseFactor τ t) := by ring
    _ = _ := by rw [hscale, he]; ring

theorem welfare_prefix (τ : ℝ) (hτ : 0 ≤ τ) :
    welfare utility (discount 1) (cornerPath τ).consumption τ =
      16 * Real.sqrt 3 / 15 * Real.exp (τ / 4) * (1 - discount (5 / 4) τ) := by
  unfold welfare
  have he : (∫ t in (0 : ℝ)..τ, discount 1 t * utility ((cornerPath τ).consumption t)) =
      ∫ t in (0 : ℝ)..τ,
        (4 * Real.sqrt 3 / 3 * Real.exp (τ / 4)) * discount (5 / 4) t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hτ] at ht
    change discount 1 t * utility (joinedConsumption τ t) = _
    unfold joinedConsumption
    rw [joinAt_left _ _ ht.2]
    exact pre_welfare_integrand τ t
  rw [he, intervalIntegral.integral_const_mul, integral_discount (5 / 4) τ (by norm_num)]
  ring

/-- The corner's lifetime value is evaluated explicitly; the construction does
not leave its finite prefix as an unevaluated integral. -/
theorem cornerValue_eq (τ : ℝ) (hτ : 0 ≤ τ) :
    cornerValue τ = 16 * Real.sqrt 3 / 15 * Real.exp (τ / 4) +
      2 * Real.sqrt 3 / 45 * discount 1 τ := by
  have he : Real.exp (τ / 4) * discount (5 / 4) τ = discount 1 τ := by
    unfold discount
    rw [← Real.exp_add]
    congr 1
    ring
  have hprefix := welfare_prefix τ hτ
  change welfare utility (discount 1) (joinedConsumption τ) τ = _ at hprefix
  rw [cornerValue, hprefix]
  calc
    _ = 16 * Real.sqrt 3 / 15 * Real.exp (τ / 4) -
        16 * Real.sqrt 3 / 15 * (Real.exp (τ / 4) * discount (5 / 4) τ) +
        10 * Real.sqrt 3 / 9 * discount 1 τ := by ring
    _ = _ := by rw [he]; ring

end RamseyCassKoopmans.ClosedForm.Corner


/-!
# A complete arbitrary-initial-stock theorem for the square-root CRRA economy

The production and utility functions are both `2 * sqrt`, and `d = m = 1`.
This theorem includes the large-capital zero-investment regime. It is a proved
specialization, not a replacement for the general-function Cass theorem.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.ClosedForm

theorem terminal_for_paths (a b : FeasiblePath Examples.production 1) (p : ℝ → ℝ)
    (hp : Tendsto p atTop (𝓝 0)) (hinit : a.capital 0 = b.capital 0) :
    Tendsto (boundary p a.capital b.capital) atTop (𝓝 0) := by
  let K := max 4 (a.capital 0)
  have hcap : ∀ k, K ≤ k → Examples.production k ≤ 1 * k :=
    fun k hk => Examples.production_capacity k ((le_max_left _ _).trans hk)
  have ha0 : a.capital 0 ≤ K := le_max_right _ _
  have hb0 : b.capital 0 ≤ K := hinit ▸ ha0
  exact Terminal.terminal_tendsto_zero_of_bounded_capital hp
    (fun t ht => ⟨a.capital_nonneg t ht, a.capital_le_capacity hcap ha0 t ht⟩)
    (fun t ht => ⟨b.capital_nonneg t ht, b.capital_le_capacity hcap hb0 t ht⟩)

theorem utility_strictConcave_positive : StrictConcaveOn ℝ (Ioi 0) utility :=
  utility_strictConcave.subset Ioi_subset_Ici_self (convex_Ioi 0)

theorem production_strictConcave : StrictConcaveOn ℝ (Ici 0) Examples.production := by
  change StrictConcaveOn ℝ (Ici 0) utility
  exact utility_strictConcave

theorem path_unique (x₀ : ℝ) (hx : 0 < x₀)
    (b : FeasiblePath Examples.production 1)
    (hinit : (path x₀ hx).capital 0 = b.capital 0)
    (hb : HasWelfare utility (discount 1) b.consumption
      (2 * Real.sqrt 3 * (1 + x₀) / 3)) :
    ∀ t, 0 ≤ t → b.capital t = (path x₀ hx).capital t ∧
      b.consumption t = (path x₀ hx).consumption t ∧
      b.investment t = (path x₀ hx).investment t := by
  let v := supportingPrices x₀ hx
  apply path_eq_of_welfare_eq v b (allocation_of_interior v (fun _ _ => rfl))
    hinit (path_hasWelfare x₀ hx) hb
    (terminal_for_paths _ _ v.price
      (Terminal.discounted_price_tendsto_zero (d := 1) (by norm_num) (shadow_tendsto x₀)) hinit)
    utility_strictConcave_positive production_strictConcave
  · exact fun _ ht => hasDerivAt_utility_consumption hx ht
  · exact fun _ ht => hasDerivAt_production_capital hx ht
  · exact fun t _ => discount_pos 1 t
  · intro t ht
    exact inv_pos.mpr (mul_pos (Real.sqrt_pos.mpr (by norm_num)) (state_pos hx ht))
  · rfl

namespace Corner

theorem preCapital_strictAnti (τ : ℝ) : StrictAnti (preCapital τ) := by
  apply strictAnti_of_deriv_neg
  intro t
  rw [(hasDerivAt_preCapital τ t).deriv]
  exact neg_neg_of_pos (preCapital_pos τ t)

theorem preConsumption_strictAnti (τ : ℝ) : StrictAnti (preConsumption τ) := by
  apply strictAnti_of_deriv_neg
  intro t
  rw [(hasDerivAt_preConsumption τ t).deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (preConsumption_pos τ t)) (by norm_num)

theorem tailCapital_strictAnti : StrictAnti (capital (2 / 3)) := by
  intro s t hst
  have h := state_strictAnti (x₀ := 2 / 3) (by norm_num) hst
  have hs := tail_state_pos s
  have ht := tail_state_pos t
  dsimp [capital]
  nlinarith

theorem tailConsumption_strictAnti : StrictAnti (consumption (2 / 3)) := by
  intro s t hst
  exact mul_lt_mul_of_pos_left (tailCapital_strictAnti hst) (by norm_num)

theorem joinedCapital_strictAnti (τ : ℝ) : StrictAnti (joinedCapital τ) :=
  strictAnti_joinAt (preCapital_strictAnti τ)
    (fun _ _ h => tailCapital_strictAnti (sub_lt_sub_right h τ)) (capital_match τ)

theorem joinedConsumption_strictAnti (τ : ℝ) : StrictAnti (joinedConsumption τ) :=
  strictAnti_joinAt (preConsumption_strictAnti τ)
    (fun _ _ h => tailConsumption_strictAnti (sub_lt_sub_right h τ)) (consumption_match τ)

theorem cornerPath_unique (τ : ℝ) (hτ : 0 ≤ τ)
    (b : FeasiblePath Examples.production 1) (hbinvest : b.NonnegativeInvestment)
    (hinit : (cornerPath τ).capital 0 = b.capital 0)
    (hb : HasWelfare utility (discount 1) b.consumption (cornerValue τ)) :
    ∀ t, 0 ≤ t → b.capital t = (cornerPath τ).capital t ∧
      b.consumption t = (cornerPath τ).consumption t ∧
      b.investment t = (cornerPath τ).investment t := by
  let v := cornerPrices τ
  apply path_eq_of_welfare_eq v b (corner_allocation τ b hbinvest)
    hinit (cornerPath_hasWelfare τ hτ) hb
    (terminal_for_paths _ _ v.price
      (Terminal.discounted_price_tendsto_zero (d := 1) (by norm_num)
        (joinedShadow_tendsto τ)) hinit)
    utility_strictConcave_positive production_strictConcave
  · exact fun t _ => joined_utility_derivative τ t
  · exact fun t _ => joined_production_derivative τ t
  · exact fun t _ => discount_pos 1 t
  · exact fun t _ => joinedMu_pos τ t
  · rfl

end Corner

/-- Existence, optimality, uniqueness and convergence for every positive initial
capital, including both Cass regimes, in the explicitly specified CRRA economy.
Uniqueness means equality of capital, consumption and investment for all t≥0. -/
theorem exists_unique_cass_optimal_convergent_path (k₀ : ℝ) (hk : 0 < k₀) :
    ∃ (a : FeasiblePath Examples.production 1) (J : ℝ),
      a.capital 0 = k₀ ∧ IsCassOptimal utility 1 a J ∧
      Tendsto a.capital atTop (𝓝 (1 / 4)) ∧ Tendsto a.consumption atTop (𝓝 (3 / 4)) ∧
      (∀ b : FeasiblePath Examples.production 1, b.NonnegativeInvestment →
        b.capital 0 = k₀ → HasWelfare utility (discount 1) b.consumption J →
        ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
          b.consumption t = a.consumption t ∧ b.investment t = a.investment t) := by
  by_cases hsmall : k₀ ≤ 4 / 9
  · have hx := Real.sqrt_pos.mpr hk
    have hxupper : Real.sqrt k₀ ≤ 2 / 3 := by
      have hs := Real.sq_sqrt hk.le
      have hp := Real.sqrt_nonneg k₀
      nlinarith
    have hinitial : (path (Real.sqrt k₀) hx).capital 0 = k₀ := by
      rw [path_initial, Real.sq_sqrt hk.le]
    refine ⟨path (Real.sqrt k₀) hx, _, hinitial,
      path_isCassOptimal _ hx hxupper, capital_tendsto _, consumption_tendsto _, ?_⟩
    intro b _ hb hJ
    exact path_unique _ hx b (hinitial.trans hb.symm) hJ
  · let τ := Real.log (9 * k₀ / 4)
    obtain ⟨hτ, hinitial⟩ := Corner.cornerPath_initial_from_stock (le_of_not_ge hsmall)
    refine ⟨Corner.cornerPath τ, Corner.cornerValue τ, hinitial,
      Corner.cornerPath_isCassOptimal τ hτ, Corner.joinedCapital_tendsto τ,
      Corner.joinedConsumption_tendsto τ, ?_⟩
    intro b hb hinit hJ
    exact Corner.cornerPath_unique τ hτ b hb (hinitial.trans hinit.symm) hJ

end RamseyCassKoopmans.ClosedForm


/-!
# Finite welfare from bounded nonnegative felicity

This removes a separate finite-welfare assumption for every Cass competitor in
the square-root economy. The general verification library still permits utility
functions unbounded below and therefore retains its explicit welfare hypotheses.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

/-- A continuous, nonnegative, bounded felicity stream has finite discounted
welfare. This proves convergence of finite integrals, without assigning a value
to a potentially divergent infinite integral. -/
theorem exists_hasWelfare_of_nonneg_bounded
    (U c : ℝ → ℝ) {d M : ℝ} (hd : 0 < d)
    (hcont : ContinuousOn (fun t => U (c t)) (Ici 0))
    (hbound : ∀ t, 0 ≤ t → 0 ≤ U (c t) ∧ U (c t) ≤ M) :
    ∃ J, HasWelfare U (discount d) c J := by
  have hint : ∀ T, 0 ≤ T → IntervalIntegrable
      (fun t => discount d t * U (c t)) volume 0 T := by
    intro T hT
    exact (((discount_continuous d).continuousOn.mul hcont).mono
      (fun _ ht => ht.1)).intervalIntegrable_of_Icc hT
  have hmono : MonotoneOn (welfare U (discount d) c) (Ici 0) := by
    intro S hS T _ hST
    apply intervalIntegral.integral_mono_interval le_rfl hS hST
      _ (hint T (hS.trans hST))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (discount_pos d t).le (hbound t ht.1.le).1
  have hupper : ∀ T, 0 ≤ T → welfare U (discount d) c T ≤ M / d := by
    intro T hT
    have hM : 0 ≤ M := (hbound 0 le_rfl).1.trans (hbound 0 le_rfl).2
    have hle : welfare U (discount d) c T ≤ M * ((1 - discount d T) / d) := by
      calc
        _ ≤ ∫ t in (0 : ℝ)..T, M * discount d t := by
          apply intervalIntegral.integral_mono_on hT (hint T hT)
            ((continuous_const.mul (discount_continuous d)).intervalIntegrable 0 T)
          intro t ht
          change discount d t * U (c t) ≤ M * discount d t
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left
            (hbound t ht.1).2 (discount_pos d t).le
        _ = _ := by rw [intervalIntegral.integral_const_mul,
          ClosedForm.integral_discount d T hd]
    have hdpos := discount_pos d T
    have hprod : 0 ≤ M * discount d T := mul_nonneg hM hdpos.le
    apply hle.trans
    apply (le_div_iff₀ hd).mpr
    field_simp
    nlinarith
  let W : ℝ → ℝ := fun T => welfare U (discount d) c (max 0 T)
  have hmW : Monotone W := by
    intro S T hST
    exact hmono (a := max 0 S) (b := max 0 T)
      (le_max_left (0 : ℝ) S) (le_max_left (0 : ℝ) T) (max_le_max_left _ hST)
  have hbW : BddAbove (range W) := ⟨M / d, by
    rintro _ ⟨T, rfl⟩
    exact hupper _ (le_max_left _ _)⟩
  refine ⟨⨆ T, W T, (tendsto_atTop_ciSup hmW hbW).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact congrArg (welfare U (discount d) c) (max_eq_right hT)

namespace ClosedForm

/-- Finite lifetime welfare is automatic for every Cass-admissible path in this
economy, including competitors for which no Euler equation is assumed. -/
theorem cass_path_hasWelfare (b : FeasiblePath Examples.production 1)
    (hb : b.NonnegativeInvestment) :
    ∃ J, HasWelfare utility (discount 1) b.consumption J := by
  let K := max 4 (b.capital 0)
  have hcapacity : ∀ k, K ≤ k → Examples.production k ≤ 1 * k :=
    fun k hk => Examples.production_capacity k ((le_max_left _ _).trans hk)
  have hk : ∀ t, 0 ≤ t → b.capital t ≤ K :=
    b.capital_le_capacity hcapacity (le_max_right _ _)
  apply exists_hasWelfare_of_nonneg_bounded utility b.consumption
    (d := 1) (M := 2 * Real.sqrt (2 * Real.sqrt K)) (by norm_num)
    (utility_continuous.comp_continuousOn b.consumption_continuous)
  intro t ht
  have hc : b.consumption t ≤ 2 * Real.sqrt K := by
    have hr := b.resource t ht
    have hi := hb t ht
    have hs := Real.sqrt_le_sqrt (hk t ht)
    dsimp [Examples.production] at hr
    linarith
  exact ⟨mul_nonneg (by norm_num) (Real.sqrt_nonneg _),
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hc) (by norm_num)⟩

end ClosedForm
end RamseyCassKoopmans


/-!
# Cass's dynamic conclusions for a fully specified economy

Production and utility are `2 * sqrt`, and `d = m = 1`. For every `k₀ > 0`,
we construct the unique optimal path, prove monotone convergence, and prove that
all admissible competitors have finite welfare. Above `k₀ = 4/9` the construction
includes a zero-investment phase ending at `log (9*k₀/4)`.

The admissible class has continuous controls and strictly positive consumption.
These theorems do not assert the general-function Cass existence theorem, nor
Koopmans's full published characterization under his distinct utility hypotheses.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.ClosedForm

/-- Monotone capital and consumption adjustment, with a constant path precisely
at the modified golden rule. Strictness is for all nonnegative times. -/
def MonotoneTransition (a : FeasiblePath Examples.production 1) (k₀ : ℝ) : Prop :=
  (k₀ < 1 / 4 → StrictMonoOn a.capital (Ici 0) ∧
    StrictMonoOn a.consumption (Ici 0)) ∧
  (1 / 4 < k₀ → StrictAntiOn a.capital (Ici 0) ∧
    StrictAntiOn a.consumption (Ici 0)) ∧
  (k₀ = 1 / 4 → ∀ t, 0 ≤ t → a.capital t = 1 / 4 ∧ a.consumption t = 3 / 4)

theorem path_monotoneTransition (x₀ : ℝ) (hx : 0 < x₀) :
    MonotoneTransition (path x₀ hx) (x₀ ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hs : x₀ < 1 / 2 := by nlinarith
    exact ⟨capital_strictMonoOn hx hs, consumption_strictMonoOn hx hs⟩
  · intro h
    have hs : 1 / 2 < x₀ := by nlinarith
    exact ⟨capital_strictAntiOn hx hs, consumption_strictAntiOn hx hs⟩
  · intro h t _
    have hs : x₀ = 1 / 2 := by nlinarith
    subst x₀
    norm_num [path, capital, consumption, state]

theorem Corner.cornerPath_monotoneTransition {k₀ : ℝ} (hk : 4 / 9 ≤ k₀) (τ : ℝ) :
    MonotoneTransition (cornerPath τ) k₀ := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    linarith
  · intro _
    exact ⟨(joinedCapital_strictAnti τ).strictAntiOn _,
      (joinedConsumption_strictAnti τ).strictAntiOn _⟩
  · intro h
    linarith

noncomputable def optimalPath (k₀ : ℝ) (hk : 0 < k₀) : FeasiblePath Examples.production 1 :=
  if k₀ ≤ 4 / 9 then path (Real.sqrt k₀) (Real.sqrt_pos.mpr hk)
  else Corner.cornerPath (Real.log (9 * k₀ / 4))

noncomputable def optimalValue (k₀ : ℝ) : ℝ :=
  if k₀ ≤ 4 / 9 then 2 * Real.sqrt 3 * (1 + Real.sqrt k₀) / 3
  else Corner.cornerValue (Real.log (9 * k₀ / 4))

theorem optimalPath_initial (k₀ : ℝ) (hk : 0 < k₀) :
    (optimalPath k₀ hk).capital 0 = k₀ := by
  unfold optimalPath
  split_ifs with h
  · rw [path_initial, Real.sq_sqrt hk.le]
  · exact (Corner.cornerPath_initial_from_stock (le_of_not_ge h)).2

theorem optimalPath_isCassOptimal (k₀ : ℝ) (hk : 0 < k₀) :
    IsCassOptimal utility 1 (optimalPath k₀ hk) (optimalValue k₀) := by
  unfold optimalPath optimalValue
  split_ifs with h
  · apply path_isCassOptimal
    have hs := Real.sq_sqrt hk.le
    have hp := Real.sqrt_nonneg k₀
    nlinarith
  · exact Corner.cornerPath_isCassOptimal _
      (Corner.cornerPath_initial_from_stock (le_of_not_ge h)).1

theorem optimalPath_converges (k₀ : ℝ) (hk : 0 < k₀) :
    Tendsto (optimalPath k₀ hk).capital atTop (𝓝 (1 / 4)) ∧
    Tendsto (optimalPath k₀ hk).consumption atTop (𝓝 (3 / 4)) := by
  unfold optimalPath
  split_ifs
  · exact ⟨capital_tendsto _, consumption_tendsto _⟩
  · exact ⟨Corner.joinedCapital_tendsto _, Corner.joinedConsumption_tendsto _⟩

theorem optimalPath_monotone (k₀ : ℝ) (hk : 0 < k₀) :
    MonotoneTransition (optimalPath k₀ hk) k₀ := by
  unfold optimalPath
  split_ifs with h
  · simpa only [Real.sq_sqrt hk.le] using
      path_monotoneTransition (Real.sqrt k₀) (Real.sqrt_pos.mpr hk)
  · exact Corner.cornerPath_monotoneTransition (le_of_not_ge h) _

theorem optimalPath_unique (k₀ : ℝ) (hk : 0 < k₀)
    (b : FeasiblePath Examples.production 1) (hb : b.NonnegativeInvestment)
    (hinit : b.capital 0 = k₀)
    (hJ : HasWelfare utility (discount 1) b.consumption (optimalValue k₀)) :
    ∀ t, 0 ≤ t → b.capital t = (optimalPath k₀ hk).capital t ∧
      b.consumption t = (optimalPath k₀ hk).consumption t ∧
      b.investment t = (optimalPath k₀ hk).investment t := by
  unfold optimalPath optimalValue at *
  split_ifs at * with h
  · apply path_unique _ (Real.sqrt_pos.mpr hk) b _ hJ
    rw [path_initial, Real.sq_sqrt hk.le, hinit]
  · obtain ⟨hτ, hi⟩ := Corner.cornerPath_initial_from_stock (le_of_not_ge h)
    exact Corner.cornerPath_unique _ hτ b hb (hi.trans hinit.symm) hJ

/-- Complete optimal-path conclusion for this economy. Welfare existence is
proved for every competitor, rather than required from the user of the theorem.
Equality with the optimal value forces equality of the entire feasible path. -/
theorem cass_dynamic_theorem (k₀ : ℝ) (hk : 0 < k₀) :
    (optimalPath k₀ hk).capital 0 = k₀ ∧
    IsCassOptimal utility 1 (optimalPath k₀ hk) (optimalValue k₀) ∧
    MonotoneTransition (optimalPath k₀ hk) k₀ ∧
    Tendsto (optimalPath k₀ hk).capital atTop (𝓝 (1 / 4)) ∧
    Tendsto (optimalPath k₀ hk).consumption atTop (𝓝 (3 / 4)) ∧
    (∀ b : FeasiblePath Examples.production 1, b.NonnegativeInvestment →
      b.capital 0 = k₀ → ∃ Jb,
        HasWelfare utility (discount 1) b.consumption Jb ∧ Jb ≤ optimalValue k₀ ∧
        (Jb = optimalValue k₀ → ∀ t, 0 ≤ t →
          b.capital t = (optimalPath k₀ hk).capital t ∧
          b.consumption t = (optimalPath k₀ hk).consumption t ∧
          b.investment t = (optimalPath k₀ hk).investment t)) := by
  have ho := optimalPath_isCassOptimal k₀ hk
  refine ⟨optimalPath_initial k₀ hk, ho, optimalPath_monotone k₀ hk,
    (optimalPath_converges k₀ hk).1, (optimalPath_converges k₀ hk).2, ?_⟩
  intro b hb hi
  obtain ⟨Jb, hJb⟩ := cass_path_hasWelfare b hb
  refine ⟨Jb, hJb, ho.2.2 b hb ((optimalPath_initial k₀ hk).trans hi.symm) Jb hJb, ?_⟩
  intro heq
  exact optimalPath_unique k₀ hk b hb hi (heq ▸ hJb)

/-- Necessity of the constructed path follows from welfare optimality itself;
no Euler equation, transversality, or convergence is assumed of `b`. -/
theorem every_optimum_eq (k₀ : ℝ) (hk : 0 < k₀)
    (b : FeasiblePath Examples.production 1) (Jb : ℝ)
    (hb : IsCassOptimal utility 1 b Jb) (hi : b.capital 0 = k₀) :
    Jb = optimalValue k₀ ∧ ∀ t, 0 ≤ t →
      b.capital t = (optimalPath k₀ hk).capital t ∧
      b.consumption t = (optimalPath k₀ hk).consumption t ∧
      b.investment t = (optimalPath k₀ hk).investment t := by
  have ha := optimalPath_isCassOptimal k₀ hk
  have hinit := (optimalPath_initial k₀ hk).trans hi.symm
  have heq : Jb = optimalValue k₀ := le_antisymm
    (ha.2.2 b hb.1 hinit Jb hb.2.1)
    (hb.2.2 _ ha.1 hinit.symm _ ha.2.1)
  exact ⟨heq, optimalPath_unique k₀ hk b hb.1 hi (heq ▸ hb.2.1)⟩

theorem every_optimum_converges (k₀ : ℝ) (hk : 0 < k₀)
    (b : FeasiblePath Examples.production 1) (Jb : ℝ)
    (hb : IsCassOptimal utility 1 b Jb) (hi : b.capital 0 = k₀) :
    Tendsto b.capital atTop (𝓝 (1 / 4)) ∧
      Tendsto b.consumption atTop (𝓝 (3 / 4)) := by
  have heq := (every_optimum_eq k₀ hk b Jb hb hi).2
  have hlim := optimalPath_converges k₀ hk
  constructor
  · apply hlim.1.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (heq t ht).1.symm
  · apply hlim.2.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (heq t ht).2.1.symm

end RamseyCassKoopmans.ClosedForm


/-!
# Global flows for bounded Lipschitz vector fields

This analytic helper constructs trajectories and continuous dependence, rather
than placing their existence in the assumptions of a shooting theorem. Economic
vector fields will be extended from compact rectangles before it is applied.
-/

open Set Filter Metric
open scoped Topology NNReal

namespace RamseyCassKoopmans.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_global_solution {v : E → E} {L K : ℝ≥0}
    (hlip : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (v (γ t)) t := by
  have hlocal (T : ℝ) : ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Ioo (-(|T| + 1)) (|T| + 1), HasDerivAt γ (v (γ t)) t := by
    let a : ℝ≥0 := ⟨L * (|T| + 1), mul_nonneg L.coe_nonneg (by positivity)⟩
    have hpl : IsPicardLindelof (fun (_ : ℝ) => v)
        (⟨0, by constructor <;> linarith [abs_nonneg T]⟩ : Icc (-(|T| + 1)) (|T| + 1))
        x a 0 L K := by
      refine ⟨fun _ _ => hlip.lipschitzOnWith, fun _ _ => continuousOn_const,
        fun _ _ y _ => hbound y, ?_⟩
      change (L : ℝ) * max ((|T| + 1) - 0) (0 - -(|T| + 1)) ≤
        (L : ℝ) * (|T| + 1) - 0
      simp
    obtain ⟨γ, hγ0, hγ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨γ, hγ0, fun t ht => (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)⟩
  choose γ hγ0 hγ using hlocal
  have hagree (S T t : ℝ) (hs : |t| < |S| + 1) (ht : |t| < |T| + 1) :
      γ S t = γ T t := by
    let R := min (|S| + 1) (|T| + 1)
    have hR : 0 < R := lt_min (by positivity) (by positivity)
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun (_ : ℝ) => v) (s := fun _ => univ)
      (a := -R) (b := R) (t₀ := 0) (fun _ _ => hlip.lipschitzOnWith)
      ⟨by linarith, hR⟩
      (fun u hu => ⟨hγ S u ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hu.1,
        lt_of_lt_of_le hu.2 (min_le_left _ _)⟩, mem_univ _⟩)
      (fun u hu => ⟨hγ T u ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hu.1,
        lt_of_lt_of_le hu.2 (min_le_right _ _)⟩, mem_univ _⟩)
      ((hγ0 S).trans (hγ0 T).symm)
    exact abs_lt.mp (lt_min hs ht)
  refine ⟨fun t => γ t t, hγ0 0, ?_⟩
  intro t
  apply (hγ t t (abs_lt.mp (by linarith : |t| < |t| + 1))).congr_of_eventuallyEq
  have hn : {u : ℝ | |u| < |t| + 1} ∈ 𝓝 t :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp)
  filter_upwards [hn] with u hu
  exact hagree u t u (by linarith) hu

omit [CompleteSpace E] in
theorem flow_lipschitz_initial {v : E → E} {K : ℝ≥0}
    (hlip : LipschitzWith K v) (φ : E → ℝ → E)
    (h0 : ∀ x, φ x 0 = x)
    (hφ : ∀ x t, HasDerivAt (φ x) (v (φ x t)) t)
    {t : ℝ} (ht : 0 ≤ t) :
    LipschitzWith ⟨Real.exp (K * t), (Real.exp_pos _).le⟩ (fun x => φ x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := dist_le_of_trajectories_ODE (v := fun (_ : ℝ) => v)
    (a := 0) (b := t) (δ := dist x y) (fun _ => hlip)
    (HasDerivAt.continuousOn (fun u _ => hφ x u))
    (fun u _ => (hφ x u).hasDerivWithinAt)
    (HasDerivAt.continuousOn (fun u _ => hφ y u))
    (fun u _ => (hφ y u).hasDerivWithinAt)
    (by rw [h0, h0]) t ⟨ht, le_rfl⟩
  change dist (φ x t) (φ y t) ≤ Real.exp ((K : ℝ) * t) * dist x y
  simpa only [sub_zero, mul_comm] using h

/-- A bounded globally Lipschitz field has a globally defined family of actual
solutions, continuous in the initial point at each nonnegative time. -/
theorem exists_global_flow {v : E → E} {L K : ℝ≥0}
    (hlip : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) :
    ∃ φ : E → ℝ → E, (∀ x, φ x 0 = x) ∧
      (∀ x t, HasDerivAt (φ x) (v (φ x t)) t) ∧
      (∀ t, 0 ≤ t → Continuous (fun x => φ x t)) := by
  choose φ h0 hφ using exists_global_solution hlip hbound
  exact ⟨φ, h0, hφ, fun _ ht => (flow_lipschitz_initial hlip φ h0 hφ ht).continuous⟩

omit [CompleteSpace E] in
theorem flow_add {v : E → E} {K : ℝ≥0}
    (hlip : LipschitzWith K v) (φ : E → ℝ → E)
    (h0 : ∀ x, φ x 0 = x)
    (hφ : ∀ x t, HasDerivAt (φ x) (v (φ x t)) t)
    (x : E) (s t : ℝ) : φ (φ x s) t = φ x (t + s) := by
  have heq : φ (φ x s) = fun u => φ x (u + s) := by
    apply ODE_solution_unique_univ (v := fun (_ : ℝ) => v)
      (s := fun _ => univ) (t₀ := 0) (fun _ => hlip.lipschitzOnWith)
      (fun u => ⟨hφ _ u, mem_univ _⟩)
    · intro u
      refine ⟨?_, mem_univ _⟩
      convert (hφ x (u + s)).scomp u ((hasDerivAt_id u).add_const s) using 1
      · rfl
      · simp only [one_smul]
    · simp only [h0, zero_add]
  exact congrFun heq t

end RamseyCassKoopmans.ODE


/-! # Simultaneous comparison barriers for two state coordinates -/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.ODE

theorem eventually_lt_right_of_deriv_neg {f : ℝ → ℝ} {v t : ℝ}
    (hd : HasDerivAt f v t) (hv : v < 0) :
    ∀ᶠ u in 𝓝[>] t, f u < f t := by
  have hs := (hd.hasDerivWithinAt (s := Ioi t)).limsup_slope_le' (lt_irrefl t) hv
  filter_upwards [hs, self_mem_nhdsWithin] with u hu htu
  rw [slope_def_field] at hu
  have := (div_lt_iff₀ (sub_pos.mpr htu)).mp hu
  linarith

theorem eventually_below_right {f B : ℝ → ℝ} {df dB t : ℝ}
    (hf : HasDerivAt f df t) (hB : HasDerivAt B dB t)
    (hle : f t ≤ B t) (hstrict : f t = B t → df < dB) :
    ∀ᶠ u in 𝓝[>] t, f u ≤ B u := by
  rcases hle.lt_or_eq with hlt | heq
  · have hn : ∀ᶠ u in 𝓝 t, f u < B u :=
      (hf.continuousAt.sub hB.continuousAt).eventually (gt_mem_nhds (sub_neg.mpr hlt))
        |>.mono (fun _ h => sub_neg.mp h)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono (fun _ h => h.le)
  · have hn := eventually_lt_right_of_deriv_neg (hf.sub hB) (sub_neg.mpr (hstrict heq))
    filter_upwards [hn] with u hu
    change f u - B u < f t - B t at hu
    linarith

/-- Each coordinate may depend on the other. At a first contact with the
barrier, both coordinates are known to be below it simultaneously. -/
theorem pair_le_barrier {f g df dg B dB : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t)
    (hg : ∀ t, HasDerivAt g (dg t) t)
    (hB : ∀ t, HasDerivAt B (dB t) t)
    (hf0 : f 0 ≤ B 0) (hg0 : g 0 ≤ B 0)
    (hb1 : ∀ t ∈ Ico 0 T, f t = B t → g t ≤ B t → df t < dB t)
    (hb2 : ∀ t ∈ Ico 0 T, g t = B t → f t ≤ B t → dg t < dB t) :
    ∀ t ∈ Icc 0 T, f t ≤ B t ∧ g t ≤ B t := by
  let S : Set ℝ := {t | f t ≤ B t ∧ g t ≤ B t}
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
  have hgc : Continuous g := continuous_iff_continuousAt.mpr (fun t => (hg t).continuousAt)
  have hBc : Continuous B := continuous_iff_continuousAt.mpr (fun t => (hB t).continuousAt)
  have hclosed : IsClosed S := (isClosed_le hfc hBc).inter (isClosed_le hgc hBc)
  apply (hclosed.inter isClosed_Icc).Icc_subset_of_forall_exists_gt ⟨hf0, hg0⟩
  rintro t ⟨htS, ht⟩ y hy
  have h1 := eventually_below_right (hf t) (hB t) htS.1 (fun heq => hb1 t ht heq htS.2)
  have h2 := eventually_below_right (hg t) (hB t) htS.2 (fun heq => hb2 t ht heq htS.1)
  obtain ⟨u, hu1, hu2, huy⟩ := (h1.and (h2.and (Ioc_mem_nhdsGT hy))).exists
  exact ⟨u, ⟨hu1, hu2⟩, huy⟩

end RamseyCassKoopmans.ODE


/-!
# Invariant quadrants for cooperative two-dimensional dynamics

Only monotonicity in the other coordinate is assumed. A coordinate need not
increase with itself, and the vector field need not be differentiable at an
investment switch. Lipschitz continuity suffices for the comparison argument.
-/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.ODE

def Cooperative (v : ℝ × ℝ → ℝ × ℝ) : Prop :=
  (∀ k, Monotone (fun q => (v (k, q)).1)) ∧
  (∀ q, Monotone (fun k => (v (k, q)).2))

theorem hasDerivAt_fst {γ : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {t : ℝ}
    (h : HasDerivAt γ v t) : HasDerivAt (fun s => (γ s).1) v.1 t := by
  simpa using h.hasFDerivAt.fst.hasDerivAt

theorem hasDerivAt_snd {γ : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {t : ℝ}
    (h : HasDerivAt γ v t) : HasDerivAt (fun s => (γ s).2) v.2 t := by
  simpa using h.hasFDerivAt.snd.hasDerivAt

theorem Cooperative.fst_le_boundary {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {x a : ℝ × ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hx : x.1 = a.1 + B) (hy : x.2 ≤ a.2 + B) :
    (v x).1 ≤ (v a).1 + K * B := by
  let b : ℝ × ℝ := (a.1 + B, a.2 + B)
  have hdist : dist b a = B := by
    simp [b, Prod.dist_eq, abs_of_nonneg hB]
  have hcomp : dist (v b).1 (v a).1 ≤ dist (v b) (v a) := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hbound := hcomp.trans (hl.dist_le_mul b a)
  rw [hdist, Real.dist_eq] at hbound
  have hfirst : (v x).1 ≤ (v b).1 := by
    dsimp only [b]
    rw [← hx]
    exact hc.1 x.1 hy
  have hdiff := (le_abs_self ((v b).1 - (v a).1)).trans hbound
  linarith

theorem Cooperative.snd_le_boundary {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {x a : ℝ × ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hx : x.1 ≤ a.1 + B) (hy : x.2 = a.2 + B) :
    (v x).2 ≤ (v a).2 + K * B := by
  let b : ℝ × ℝ := (a.1 + B, a.2 + B)
  have hdist : dist b a = B := by
    simp [b, Prod.dist_eq, abs_of_nonneg hB]
  have hcomp : dist (v b).2 (v a).2 ≤ dist (v b) (v a) := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hbound := hcomp.trans (hl.dist_le_mul b a)
  rw [hdist, Real.dist_eq] at hbound
  have hsecond : (v x).2 ≤ (v b).2 := by
    dsimp only [b]
    rw [← hy]
    exact hc.2 x.2 hx
  have hdiff := (le_abs_self ((v b).2 - (v a).2)).trans hbound
  linarith

/-- A constant supersolution bounds a trajectory. The proof uses simultaneous
strict exponential barriers and lets their size vanish. -/
theorem solution_le_supersolution {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ}
    (ha : (v a).1 ≤ 0 ∧ (v a).2 ≤ 0)
    {γ : ℝ → ℝ × ℝ} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : (γ 0).1 ≤ a.1 ∧ (γ 0).2 ≤ a.2) :
    ∀ T, 0 ≤ T → (γ T).1 ≤ a.1 ∧ (γ T).2 ≤ a.2 := by
  intro T hT
  have hbarrier (ε : ℝ) (hε : 0 < ε) :
      (γ T).1 - a.1 ≤ ε * Real.exp (((K : ℝ) + 1) * T) ∧
      (γ T).2 - a.2 ≤ ε * Real.exp (((K : ℝ) + 1) * T) := by
    let B : ℝ → ℝ := fun t => ε * Real.exp (((K : ℝ) + 1) * t)
    have hB t : HasDerivAt B (((K : ℝ) + 1) * B t) t := by
      convert (((hasDerivAt_id t).const_mul ((K : ℝ) + 1)).exp).const_mul ε using 1
      · rfl
      · dsimp [B]
        ring
    have hpos t : 0 < B t := mul_pos hε (Real.exp_pos _)
    have h := pair_le_barrier
      (fun t => (hasDerivAt_fst (hγ t)).sub_const a.1)
      (fun t => (hasDerivAt_snd (hγ t)).sub_const a.2) hB
      (by dsimp [B]; simp only [mul_zero, Real.exp_zero, mul_one]; linarith [h0.1])
      (by dsimp [B]; simp only [mul_zero, Real.exp_zero, mul_one]; linarith [h0.2])
      (T := T) ?_ ?_ T ⟨hT, le_rfl⟩
    · exact h
    · intro t _ heq hle
      have hb := hc.fst_le_boundary hl (a := a) (hpos t).le
        (show (γ t).1 = a.1 + B t by linarith)
        (show (γ t).2 ≤ a.2 + B t by linarith)
      nlinarith [hpos t, ha.1]
    · intro t _ heq hle
      have hb := hc.snd_le_boundary hl (a := a) (hpos t).le
        (show (γ t).1 ≤ a.1 + B t by linarith)
        (show (γ t).2 = a.2 + B t by linarith)
      nlinarith [hpos t, ha.2]
  have hsmall (ε : ℝ) (hε : 0 < ε) :
      (γ T).1 ≤ a.1 + ε ∧ (γ T).2 ≤ a.2 + ε := by
    have h := hbarrier (ε / Real.exp (((K : ℝ) + 1) * T)) (div_pos hε (Real.exp_pos _))
    rw [div_mul_cancel₀ ε (Real.exp_ne_zero _)] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  exact ⟨le_of_forall_pos_le_add (fun ε hε => (hsmall ε hε).1),
    le_of_forall_pos_le_add (fun ε hε => (hsmall ε hε).2)⟩

theorem solution_le_equilibrium {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ} (ha : v a = 0)
    {γ : ℝ → ℝ × ℝ} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : (γ 0).1 ≤ a.1 ∧ (γ 0).2 ≤ a.2) :
    ∀ T, 0 ≤ T → (γ T).1 ≤ a.1 ∧ (γ T).2 ≤ a.2 :=
  solution_le_supersolution hc hl (by simp [ha]) hγ h0

theorem Cooperative.fst_le_gap {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {x a : ℝ × ℝ}
    (hx : x.1 ≤ a.1) (hy : x.2 ≤ a.2) :
    (v x).1 ≤ (v a).1 + K * (a.1 - x.1) := by
  have hdist : dist (x.1, a.2) a = a.1 - x.1 := by
    simp [Prod.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx), hx]
  have hcomp : dist (v (x.1, a.2)).1 (v a).1 ≤ dist (v (x.1, a.2)) (v a) := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hbound := hcomp.trans (hl.dist_le_mul (x.1, a.2) a)
  rw [hdist, Real.dist_eq] at hbound
  have hm := hc.1 x.1 hy
  have hd := (le_abs_self ((v (x.1, a.2)).1 - (v a).1)).trans hbound
  change (v x).1 ≤ (v (x.1, a.2)).1 at hm
  linarith

theorem Cooperative.snd_le_gap {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {x a : ℝ × ℝ}
    (hx : x.1 ≤ a.1) (hy : x.2 ≤ a.2) :
    (v x).2 ≤ (v a).2 + K * (a.2 - x.2) := by
  have hdist : dist (a.1, x.2) a = a.2 - x.2 := by
    simp [Prod.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hy), hy]
  have hcomp : dist (v (a.1, x.2)).2 (v a).2 ≤ dist (v (a.1, x.2)) (v a) := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hbound := hcomp.trans (hl.dist_le_mul (a.1, x.2) a)
  rw [hdist, Real.dist_eq] at hbound
  have hm := hc.2 x.2 hx
  have hd := (le_abs_self ((v (a.1, x.2)).2 - (v a).2)).trans hbound
  change (v x).2 ≤ (v (a.1, x.2)).2 at hm
  linarith

theorem strict_neg_of_deriv_le_mul {f df : ℝ → ℝ} {K : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (h0 : f 0 < 0)
    (hb : ∀ t, 0 ≤ t → df t ≤ K * f t) : ∀ T, 0 ≤ T → f T < 0 := by
  intro T hT
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (a := 0) (b := T) (δ := f 0) (K := K) (ε := 0)
    (HasDerivAt.continuousOn (fun t _ => hf t))
    (fun t _ r hr => by
      simpa only [slope_def_field, div_eq_mul_inv, mul_comm] using
        (hf t).hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl (fun t ht => by simpa only [add_zero] using hb t ht.1) T ⟨hT, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at h
  exact h.trans_lt (mul_neg_of_neg_of_pos h0 (Real.exp_pos _))

/-- The strict lower quadrant is also invariant; the Lipschitz estimate rules
out reaching a coordinate boundary in finite time. -/
theorem solution_lt_equilibrium {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ} (ha : v a = 0)
    {γ : ℝ → ℝ × ℝ} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : (γ 0).1 < a.1 ∧ (γ 0).2 < a.2) :
    ∀ T, 0 ≤ T → (γ T).1 < a.1 ∧ (γ T).2 < a.2 := by
  have hle := solution_le_equilibrium hc hl ha hγ ⟨h0.1.le, h0.2.le⟩
  have h1 := strict_neg_of_deriv_le_mul (K := -(K : ℝ))
    (fun t => (hasDerivAt_fst (hγ t)).sub_const a.1) (sub_neg.mpr h0.1)
    (fun t ht => by
      have hb := hc.fst_le_gap hl (hle t ht).1 (hle t ht).2
      rw [ha] at hb
      change (v (γ t)).1 ≤ 0 + K * (a.1 - (γ t).1) at hb
      nlinarith)
  have h2 := strict_neg_of_deriv_le_mul (K := -(K : ℝ))
    (fun t => (hasDerivAt_snd (hγ t)).sub_const a.2) (sub_neg.mpr h0.2)
    (fun t ht => by
      have hb := hc.snd_le_gap hl (hle t ht).1 (hle t ht).2
      rw [ha] at hb
      change (v (γ t)).2 ≤ 0 + K * (a.2 - (γ t).2) at hb
      nlinarith)
  exact fun T hT => ⟨sub_neg.mp (h1 T hT), sub_neg.mp (h2 T hT)⟩

def reflected (v : ℝ × ℝ → ℝ × ℝ) (x : ℝ × ℝ) : ℝ × ℝ := -v (-x)

theorem Cooperative.reflected {v : ℝ × ℝ → ℝ × ℝ} (hc : Cooperative v) :
    Cooperative (reflected v) := by
  constructor
  · intro k q₁ q₂ hq
    change -(v (-k, -q₁)).1 ≤ -(v (-k, -q₂)).1
    exact neg_le_neg (hc.1 (-k) (neg_le_neg hq))
  · intro q k₁ k₂ hk
    change -(v (-k₁, -q)).2 ≤ -(v (-k₂, -q)).2
    exact neg_le_neg (hc.2 (-q) (neg_le_neg hk))

theorem lipschitz_reflected {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hl : LipschitzWith K v) : LipschitzWith K (reflected v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [reflected, dist_neg_neg] using hl.dist_le_mul (-x) (-y)

theorem solution_gt_equilibrium {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ} (ha : v a = 0)
    {γ : ℝ → ℝ × ℝ} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : a.1 < (γ 0).1 ∧ a.2 < (γ 0).2) :
    ∀ T, 0 ≤ T → a.1 < (γ T).1 ∧ a.2 < (γ T).2 := by
  have hr : reflected v (-a) = 0 := by simp only [reflected, neg_neg, ha, neg_zero]
  have hd : ∀ t, HasDerivAt (fun t => -γ t) (reflected v (-γ t)) t := by
    intro t
    convert (hγ t).neg using 1
    simp only [reflected, neg_neg]
  have hh := solution_lt_equilibrium hc.reflected (lipschitz_reflected hl) hr hd
    (show (-γ 0).1 < (-a).1 ∧ (-γ 0).2 < (-a).2 from
      ⟨neg_lt_neg h0.1, neg_lt_neg h0.2⟩)
  intro T hT
  simpa only [Prod.fst_neg, Prod.snd_neg, neg_lt_neg_iff] using hh T hT

theorem solution_ge_subsolution {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ}
    (ha : 0 ≤ (v a).1 ∧ 0 ≤ (v a).2)
    {γ : ℝ → ℝ × ℝ} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : a.1 ≤ (γ 0).1 ∧ a.2 ≤ (γ 0).2) :
    ∀ T, 0 ≤ T → a.1 ≤ (γ T).1 ∧ a.2 ≤ (γ T).2 := by
  have hr : (reflected v (-a)).1 ≤ 0 ∧ (reflected v (-a)).2 ≤ 0 := by
    simpa only [reflected, neg_neg, Prod.fst_neg, Prod.snd_neg, neg_nonpos] using ha
  have hd : ∀ t, HasDerivAt (fun t => -γ t) (reflected v (-γ t)) t := by
    intro t
    convert (hγ t).neg using 1
    simp only [reflected, neg_neg]
  have hh := solution_le_supersolution hc.reflected (lipschitz_reflected hl) hr hd
    (show (-γ 0).1 ≤ (-a).1 ∧ (-γ 0).2 ≤ (-a).2 from
      ⟨neg_le_neg h0.1, neg_le_neg h0.2⟩)
  intro T hT
  simpa only [Prod.fst_neg, Prod.snd_neg, neg_le_neg_iff] using hh T hT

end RamseyCassKoopmans.ODE


/-! # Drift bounds and limits of autonomous trajectories -/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.ODE

theorem linear_lower_bound_on {f df : ℝ → ℝ} {A T c : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hAT : A ≤ T)
    (hb : ∀ t ∈ Icc A T, c ≤ df t) : c * (T - A) ≤ f T - f A := by
  exact (convex_Icc A T).mul_sub_le_image_sub_of_le_deriv
    (HasDerivAt.continuousOn (fun t _ => hf t))
    (fun t _ => (hf t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hf t).deriv]; exact hb t (interior_subset ht))
    A ⟨le_rfl, hAT⟩ T ⟨hAT, le_rfl⟩ hAT

theorem linear_upper_bound_on {f df : ℝ → ℝ} {A T c : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hAT : A ≤ T)
    (hb : ∀ t ∈ Icc A T, df t ≤ c) : f T - f A ≤ c * (T - A) := by
  have h := linear_lower_bound_on (fun t => (hf t).neg) hAT
    (c := -c) (fun t ht => neg_le_neg (hb t ht))
  change -c * (T - A) ≤ -f T - -f A at h
  linarith

theorem linear_lower_bound {f df : ℝ → ℝ} {A T c : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hAT : A ≤ T)
    (hb : ∀ t, A ≤ t → c ≤ df t) : c * (T - A) ≤ f T - f A := by
  apply (convex_Ici A).mul_sub_le_image_sub_of_le_deriv
    (HasDerivAt.continuousOn (fun t _ => hf t))
    (fun t _ => (hf t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hf t).deriv]; exact hb t (interior_subset ht))
    A (mem_Ici.mpr le_rfl) T (mem_Ici.mpr hAT) hAT

theorem linear_upper_bound {f df : ℝ → ℝ} {A T c : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hAT : A ≤ T)
    (hb : ∀ t, A ≤ t → df t ≤ c) : f T - f A ≤ c * (T - A) := by
  have h := linear_lower_bound (fun t => (hf t).neg) hAT
    (c := -c) (fun t ht => neg_le_neg (hb t ht))
  change -c * (T - A) ≤ -f T - -f A at h
  linarith

theorem not_bounded_below_of_negative_drift {f df : ℝ → ℝ} {ε B : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hε : 0 < ε)
    (hd : ∀ t, 0 ≤ t → df t ≤ -ε)
    (hb : ∀ t, 0 ≤ t → B ≤ f t) : False := by
  let T := max 0 ((f 0 - B + 1) / ε)
  have hT : 0 ≤ T := le_max_left _ _
  have htime : f 0 - B + 1 ≤ ε * T := by
    have h := le_max_right 0 ((f 0 - B + 1) / ε)
    exact (div_le_iff₀ hε).mp h |>.trans_eq (mul_comm _ _)
  have hbound := linear_upper_bound hf hT hd
  have hbelow := hb T hT
  simp only [sub_zero] at hbound
  nlinarith

theorem not_bounded_above_of_positive_drift {f df : ℝ → ℝ} {ε B : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hε : 0 < ε)
    (hd : ∀ t, 0 ≤ t → ε ≤ df t)
    (hb : ∀ t, 0 ≤ t → f t ≤ B) : False :=
  not_bounded_below_of_negative_drift (fun t => (hf t).neg) hε
    (fun t ht => neg_le_neg (hd t ht)) (fun t ht => neg_le_neg (hb t ht))

/-- A convergent differentiable function cannot have a nonzero limiting
derivative. The proof uses an eventual uniform drift bound and the mean value
theorem, rather than exchanging a derivative and a limit. -/
theorem derivative_limit_zero {f df : ℝ → ℝ} {l v : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t)
    (hlim : Tendsto f atTop (𝓝 l)) (hdlim : Tendsto df atTop (𝓝 v)) : v = 0 := by
  have hposImpossible : ∀ {f df : ℝ → ℝ} {l v : ℝ},
      (∀ t, HasDerivAt f (df t) t) → Tendsto f atTop (𝓝 l) →
      Tendsto df atTop (𝓝 v) → 0 < v → False := by
    intro f df l v hf hl hd hv
    obtain ⟨A, hA⟩ := eventually_atTop.mp
      ((hl.eventually (gt_mem_nhds (show l < l + 1 by linarith))).and
        (hd.eventually (lt_mem_nhds (show v / 2 < v by linarith))))
    have hs : ∀ t, HasDerivAt (fun u => f (u + A)) (df (t + A)) t := by
      intro t
      convert (hf (t + A)).comp t ((hasDerivAt_id t).add_const A) using 1
      · rfl
      · ring
    exact not_bounded_above_of_positive_drift hs (show 0 < v / 2 by linarith)
      (fun t ht => (hA (t + A) (by linarith)).2.le)
      (fun t ht => (hA (t + A) (by linarith)).1.le)
  rcases lt_trichotomy v 0 with hv | hv | hv
  · exact False.elim (hposImpossible (fun t => (hf t).neg) hlim.neg hdlim.neg (neg_pos.mpr hv))
  · exact hv
  · exact False.elim (hposImpossible hf hlim hdlim hv)

theorem limit_is_equilibrium {v : ℝ × ℝ → ℝ × ℝ} (hc : Continuous v)
    {γ : ℝ → ℝ × ℝ} {a : ℝ × ℝ}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (ha : Tendsto γ atTop (𝓝 a)) : v a = 0 := by
  have hv := hc.continuousAt.tendsto.comp ha
  apply Prod.ext
  · exact derivative_limit_zero (fun t => hasDerivAt_fst (hγ t))
      (continuous_fst.tendsto a |>.comp ha) (continuous_fst.tendsto (v a) |>.comp hv)
  · exact derivative_limit_zero (fun t => hasDerivAt_snd (hγ t))
      (continuous_snd.tendsto a |>.comp ha) (continuous_snd.tendsto (v a) |>.comp hv)

theorem exists_limit_of_monotone_bounded {f : ℝ → ℝ} {B : ℝ}
    (hm : MonotoneOn f (Ici 0)) (hb : ∀ t, 0 ≤ t → f t ≤ B) :
    ∃ l, Tendsto f atTop (𝓝 l) := by
  let g := fun t => f (max 0 t)
  have hmono : Monotone g := fun s t hst =>
    hm (mem_Ici.mpr (le_max_left _ _)) (mem_Ici.mpr (le_max_left _ _))
      (max_le_max_left _ hst)
  have hbound : BddAbove (range g) := ⟨B, by
    rintro _ ⟨t, rfl⟩
    exact hb _ (le_max_left _ _)⟩
  refine ⟨⨆ t, g t, (tendsto_atTop_ciSup hmono hbound).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact congrArg f (max_eq_right ht)

theorem exists_limit_of_antitone_bounded {f : ℝ → ℝ} {B : ℝ}
    (hm : AntitoneOn f (Ici 0)) (hb : ∀ t, 0 ≤ t → B ≤ f t) :
    ∃ l, Tendsto f atTop (𝓝 l) := by
  obtain ⟨l, hl⟩ := exists_limit_of_monotone_bounded
    (f := fun t => -f t) (fun _ hx _ hy hxy => neg_le_neg (hm hx hy hxy))
    (fun t ht => neg_le_neg (hb t ht))
  exact ⟨-l, by simpa only [neg_neg] using hl.neg⟩

theorem exponential_lower_bound {f df : ℝ → ℝ} {A : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t)
    (hb : ∀ t, 0 ≤ t → -A * f t ≤ df t) :
    ∀ T, 0 ≤ T → f 0 * Real.exp (-A * T) ≤ f T := by
  intro T hT
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (a := 0) (b := T) (δ := -f 0) (K := -A) (ε := 0)
    (HasDerivAt.continuousOn (fun t _ => (hf t).neg))
    (fun t _ r hr => by
      simpa only [slope_def_field, div_eq_mul_inv, mul_comm] using
        ((hf t).neg).hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl (fun t ht => by
      have hh := hb t ht.1
      change -df t ≤ -A * -f t + 0
      linarith) T ⟨hT, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at h
  change -f T ≤ -f 0 * Real.exp (-A * T) at h
  nlinarith

end RamseyCassKoopmans.ODE


/-! # A finite capital capacity from a vanishing marginal product -/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

theorem exists_capacity_of_marginal_tendsto_zero (f : ℝ → ℝ) {m k0 : ℝ}
    (hm : 0 < m) (hf : ConcaveOn ℝ (Ici 0) f)
    (hd : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hpos : ∀ k, 0 < k → 0 ≤ deriv f k)
    (hlim : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))) :
    ∃ K, k0 ≤ K ∧ ∀ k, K ≤ k → f k ≤ m * k := by
  obtain ⟨a, ha, hma⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hlim.eventually (gt_mem_nhds (half_pos hm)))).exists
  let K := max k0 (max a (2 * |f a| / m))
  refine ⟨K, le_max_left _ _, ?_⟩
  intro k hk
  have hak : a ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hratio : 2 * |f a| / m ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hmk : 2 * |f a| ≤ k * m := (div_le_iff₀ hm).mp hratio
  have hs := concave_support hf ha.le (ha.le.trans hak) (hd a ha).hasDerivAt
  have hpk := mul_le_mul_of_nonneg_right hma.le (ha.le.trans hak)
  have hpa := mul_nonneg (hpos a ha) ha.le
  have hfabs := le_abs_self (f a)
  nlinarith

end RamseyCassKoopmans


/-! # Uniqueness and necessity from a Cass certificate -/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

theorem cass_certificate_unique
    (f U q : ℝ → ℝ) (d m K Ja Jb : ℝ) (a b : FeasiblePath f m)
    (hfconc : StrictConcaveOn ℝ (Ici 0) f) (hUconc : StrictConcaveOn ℝ (Ioi 0) U)
    (hUcont : ContinuousOn U (Ioi 0))
    (hfderiv : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hUderiv : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hak : ∀ t, 0 ≤ t → 0 < a.capital t)
    (hmu : ∀ t, 0 ≤ t → 0 < deriv U (a.consumption t))
    (hq : ∀ t, 0 ≤ t → HasDerivAt q
      ((d + m) * q t - deriv U (a.consumption t) * deriv f (a.capital t)) t)
    (hwedge : ∀ t, 0 ≤ t → q t ≤ deriv U (a.consumption t))
    (hslack : ∀ t, 0 ≤ t → (q t - deriv U (a.consumption t)) * a.investment t = 0)
    (hbinvest : b.NonnegativeInvestment) (hinit : a.capital 0 = b.capital 0)
    (hcapacity : ∀ k, K ≤ k → f k ≤ m * k) (ha0 : a.capital 0 ≤ K)
    (ha : HasWelfare U (discount d) a.consumption Ja)
    (hb : HasWelfare U (discount d) b.consumption Jb)
    (htrans : Tendsto (fun t => discount d t * q t) atTop (𝓝 0)) (heq : Jb = Ja) :
    ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
      b.consumption t = a.consumption t ∧ b.investment t = a.investment t := by
  let v := cassSupportingPrices f U q d m a hfconc.concaveOn hUconc.concaveOn hUcont
    hfderiv hUderiv hfprime hUprime hak (fun t ht => (hmu t ht).le) hq
  have halloc : AllocationComparison v b := by
    apply allocation_of_cass v
    · intro t ht
      exact mul_le_mul_of_nonneg_left (hwedge t ht) (discount_pos d t).le
    · intro t ht
      change (discount d t * q t - discount d t * deriv U (a.consumption t)) * a.investment t = 0
      calc
        _ = discount d t * ((q t - deriv U (a.consumption t)) * a.investment t) := by ring
        _ = 0 := by rw [hslack t ht, mul_zero]
    · exact hbinvest
  have hterm : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0) :=
    Terminal.terminal_tendsto_zero_of_bounded_capital htrans
      (fun t ht => ⟨a.capital_nonneg t ht, a.capital_le_capacity hcapacity ha0 t ht⟩)
      (fun t ht => ⟨b.capital_nonneg t ht, b.capital_le_capacity hcapacity (hinit ▸ ha0) t ht⟩)
  exact path_eq_of_welfare_eq v b halloc hinit ha hb hterm hUconc hfconc
    (fun t ht => (hUderiv _ (a.consumption_pos t ht)).hasDerivAt)
    (fun t ht => (hfderiv _ (hak t ht)).hasDerivAt)
    (fun t _ => discount_pos d t) hmu heq

end RamseyCassKoopmans


/-! # Constructing a Lipschitz inverse of marginal utility on a compact interval

The inverse is obtained by the intermediate value theorem. Its Lipschitz bound
is proved from a strictly negative bound on the derivative of marginal utility.
Only two derivatives of utility are needed; no derivative of its curvature is
introduced. Clipping the price argument makes this inverse globally defined.
-/

open Set
open scoped NNReal

namespace RamseyCassKoopmans

def clip (a b x : ℝ) : ℝ := max a (min b x)

theorem clip_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clip a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clip_eq {a b x : ℝ} (hx : x ∈ Icc a b) : clip a b x = x := by
  simp only [clip, min_eq_right hx.2, max_eq_right hx.1]

theorem monotone_clip (a b : ℝ) : Monotone (clip a b) :=
  fun _ _ h => max_le_max_left _ (min_le_min_left _ h)

theorem lipschitz_clip (a b : ℝ) : LipschitzWith 1 (clip a b) :=
  (LipschitzWith.id.const_min b).const_max a

/-- A quantitative version of decreasing marginal utility on a compact
consumption interval. -/
theorem strong_decrease_of_deriv_bound {μ : ℝ → ℝ} {a b η : ℝ}
    (hc : ContinuousOn μ (Icc a b))
    (hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ μ x)
    (hb : ∀ x ∈ Icc a b, deriv μ x ≤ -η) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → η * (y - x) ≤ μ x - μ y := by
  intro x hx y hy hxy
  have h := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hc
    (fun z hz => (hd z (interior_subset hz)).differentiableWithinAt)
    (fun z hz => hb z (interior_subset hz)) x hx y hy hxy
  linarith

/-- Construct a global, antitone, Lipschitz consumption demand by inverting
marginal utility between two ordinary, finite, positive consumption levels.
The conclusion includes the exact inverse equation with a clipped price. -/
theorem exists_compact_demand {μ : ℝ → ℝ} {a b η : ℝ}
    (hab : a ≤ b) (hη : 0 < η) (hc : ContinuousOn μ (Icc a b))
    (hs : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → η * (y - x) ≤ μ x - μ y) :
    ∃ C : ℝ → ℝ, (∀ q, C q ∈ Icc a b) ∧ Antitone C ∧
      LipschitzWith ⟨1 / η, (one_div_pos.mpr hη).le⟩ C ∧
      ∀ q, μ (C q) = clip (μ b) (μ a) q := by
  have hμ : μ b ≤ μ a := by
    have h := hs a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
    have hp := mul_nonneg hη.le (sub_nonneg.mpr hab)
    linarith
  have hex : ∀ q, ∃ c ∈ Icc a b, μ c = clip (μ b) (μ a) q := by
    intro q
    exact intermediate_value_Icc' hab hc (clip_mem hμ q)
  choose C hC heq using hex
  have hanti : Antitone C := by
    intro p q hpq
    by_contra hn
    have hlt : C p < C q := lt_of_not_ge hn
    have hslope := hs (C p) (hC p) (C q) (hC q) hlt.le
    have hpositive := mul_pos hη (sub_pos.mpr hlt)
    rw [heq p, heq q] at hslope
    have horder := monotone_clip (μ b) (μ a) hpq
    linarith
  refine ⟨C, hC, hanti, ?_, heq⟩
  apply LipschitzWith.of_dist_le_mul
  have hord : ∀ p q, p ≤ q → dist (C p) (C q) ≤ (1 / η) * dist p q := by
    intro p q hpq
    have hCp := hanti hpq
    have hslope := hs (C q) (hC q) (C p) (hC p) hCp
    rw [heq p, heq q] at hslope
    have hclip := (lipschitz_clip (μ b) (μ a)).dist_le_mul p q
    have hclipord := monotone_clip (μ b) (μ a) hpq
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hclipord),
      abs_of_nonpos (sub_nonpos.mpr hpq)] at hclip
    simp only [NNReal.coe_one, one_mul] at hclip
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hCp),
      abs_of_nonpos (sub_nonpos.mpr hpq)]
    have hdiv : C p - C q ≤ (q - p) / η :=
      (le_div_iff₀ hη).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul, mul_one, neg_sub, mul_comm] using hdiv
  intro p q
  change dist (C p) (C q) ≤ (1 / η) * dist p q
  rcases le_total p q with hpq | hqp
  · exact hord p q hpq
  · simpa only [dist_comm] using hord q p hqp

/-- Continuous strict negativity supplies the finite curvature bound used in
the inverse construction. It is a conclusion, not an extra curvature axiom. -/
theorem exists_uniform_negative_deriv {μ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn (deriv μ) (Icc a b))
    (hn : ∀ x ∈ Icc a b, deriv μ x < 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ Icc a b, deriv μ x ≤ -η := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc
  refine ⟨-deriv μ x, neg_pos.mpr (hn x hx), ?_⟩
  intro y hy
  simp only [neg_neg]
  exact hmax hy

theorem exists_compact_demand_of_deriv {μ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ μ x)
    (hc : ContinuousOn (deriv μ) (Icc a b))
    (hn : ∀ x ∈ Icc a b, deriv μ x < 0) :
    ∃ K : ℝ≥0, ∃ C : ℝ → ℝ, (∀ q, C q ∈ Icc a b) ∧ Antitone C ∧
      LipschitzWith K C ∧ ∀ q, μ (C q) = clip (μ b) (μ a) q := by
  obtain ⟨η, hη, hb⟩ := exists_uniform_negative_deriv hab hc hn
  have hm : ContinuousOn μ (Icc a b) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := exists_compact_demand hab hη hm
    (strong_decrease_of_deriv_bound hm hd hb)
  exact ⟨_, C, hC⟩

end RamseyCassKoopmans


/-! # Bounded Lipschitz extensions for the economic differential equations -/

open Set
open scoped NNReal

namespace RamseyCassKoopmans

def BoundedLip {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F]
    (f : E → F) : Prop :=
  ∃ K M : ℝ≥0, LipschitzWith K f ∧ ∀ x, ‖f x‖ ≤ M

namespace BoundedLip

variable {E : Type*} [PseudoMetricSpace E]

theorem const (a : ℝ) : BoundedLip (fun _ : E => a) :=
  ⟨0, ‖a‖₊, LipschitzWith.const a, fun _ => le_rfl⟩

theorem sub {f g : E → ℝ} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => f x - g x) := by
  obtain ⟨K, M, hK, hM⟩ := hf
  obtain ⟨L, N, hL, hN⟩ := hg
  exact ⟨K + L, M + N, hK.sub hL,
    fun x => (norm_sub_le _ _).trans (add_le_add (hM x) (hN x))⟩

theorem mul {f g : E → ℝ} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => f x * g x) := by
  obtain ⟨K, M, hK, hM⟩ := hf
  obtain ⟨L, N, hL, hN⟩ := hg
  refine ⟨M * L + N * K, M * N, LipschitzWith.of_dist_le_mul ?_, ?_⟩
  · intro x y
    have hfxy : ‖f x - f y‖ ≤ K * dist x y := by
      simpa only [dist_eq_norm] using hK.dist_le_mul x y
    have hgxy : ‖g x - g y‖ ≤ L * dist x y := by
      simpa only [dist_eq_norm] using hL.dist_le_mul x y
    have hdecomp : f x * g x - f y * g y =
        f x * (g x - g y) + (f x - f y) * g y := by ring
    calc
      dist (f x * g x) (f y * g y)
          = ‖f x * (g x - g y) + (f x - f y) * g y‖ := by
            rw [dist_eq_norm, hdecomp]
      _ ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by
        simpa only [norm_mul] using norm_add_le
          (f x * (g x - g y)) ((f x - f y) * g y)
      _ ≤ M * (L * dist x y) + (K * dist x y) * N :=
        add_le_add
          (mul_le_mul (hM x) hgxy (norm_nonneg _) M.coe_nonneg)
          (mul_le_mul hfxy (hN y) (norm_nonneg _) (by positivity))
      _ = (↑(M * L + N * K) : ℝ) * dist x y := by
        push_cast
        ring
  · intro x
    rw [norm_mul]
    exact mul_le_mul (hM x) (hN x) (norm_nonneg _) M.coe_nonneg

theorem min_function {f g : E → ℝ} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => min (f x) (g x)) := by
  obtain ⟨K, M, hK, hM⟩ := hf
  obtain ⟨L, N, hL, hN⟩ := hg
  refine ⟨max K L, max M N, hK.min hL, fun x => ?_⟩
  rcases le_total (f x) (g x) with h | h
  · simpa only [min_eq_left h] using (hM x).trans (show (M : ℝ) ≤ max M N from le_max_left _ _)
  · simpa only [min_eq_right h] using (hN x).trans (show (N : ℝ) ≤ max M N from le_max_right _ _)

theorem max_function {f g : E → ℝ} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => max (f x) (g x)) := by
  obtain ⟨K, M, hK, hM⟩ := hf
  obtain ⟨L, N, hL, hN⟩ := hg
  refine ⟨max K L, max M N, hK.max hL, fun x => ?_⟩
  rcases le_total (f x) (g x) with h | h
  · simpa only [max_eq_right h] using (hN x).trans (show (N : ℝ) ≤ max M N from le_max_right _ _)
  · simpa only [max_eq_left h] using (hM x).trans (show (M : ℝ) ≤ max M N from le_max_left _ _)

theorem comp {D : Type*} [PseudoMetricSpace D] {f : E → ℝ} {g : D → E}
    (hf : BoundedLip f) {K : ℝ≥0} (hg : LipschitzWith K g) : BoundedLip (f ∘ g) := by
  obtain ⟨L, M, hL, hM⟩ := hf
  exact ⟨L * K, M, hL.comp hg, fun x => hM (g x)⟩

theorem prodMk {f g : E → ℝ} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => (f x, g x)) := by
  obtain ⟨K, M, hK, hM⟩ := hf
  obtain ⟨L, N, hL, hN⟩ := hg
  refine ⟨max K L, max M N, hK.prodMk hL, fun x => ?_⟩
  exact max_le_max (hM x) (hN x)

end BoundedLip

theorem boundedLip_clip {a b : ℝ} (hab : a ≤ b) : BoundedLip (clip a b) := by
  refine ⟨1, max ‖a‖₊ ‖b‖₊, lipschitz_clip a b, fun x => ?_⟩
  have hx := clip_mem hab x
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have ha := neg_abs_le a
    have hma : |a| ≤ max ‖a‖ ‖b‖ := le_max_left _ _
    change -(max ‖a‖ ‖b‖) ≤ clip a b x
    linarith [hx.1]
  · have hb := le_abs_self b
    have hmb : |b| ≤ max ‖a‖ ‖b‖ := le_max_right _ _
    change clip a b x ≤ max ‖a‖ ‖b‖
    linarith [hx.2]

/-- Clipping a continuously differentiable function to a compact argument
interval gives both global boundedness and a global Lipschitz constant. -/
theorem boundedLip_comp_clip {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hc : ContinuousOn (deriv f) (Icc a b)) : BoundedLip (f ∘ clip a b) := by
  have hfc : ContinuousOn f (Icc a b) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc.norm
  obtain ⟨w, hw, hwmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hfc.norm
  have hL : LipschitzOnWith ‖deriv f z‖₊ f (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le hd (fun x hx => hmax hx)
  refine ⟨‖deriv f z‖₊, ‖f w‖₊, LipschitzWith.of_dist_le_mul ?_, ?_⟩
  · intro x y
    exact (hL.dist_le_mul _ (clip_mem hab x) _ (clip_mem hab y)).trans
      (mul_le_mul_of_nonneg_left
        (by simpa only [NNReal.coe_one, one_mul] using (lipschitz_clip a b).dist_le_mul x y)
        (norm_nonneg _))
  · intro x
    exact hwmax (clip_mem hab x)

end RamseyCassKoopmans


/-!
# A connected shooting interval contains a trajectory avoiding both exits

Two disjoint, open, forward-invariant exit regions cannot exhaust a connected
interval of initial conditions if its endpoints enter different exit regions.
This gives an existence argument; no selected trajectory is an assumption.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.ODE

variable {E : Type*} [TopologicalSpace E]

def hits (φ : E → ℝ → E) (initial : ℝ → E) (U : Set E) : Set ℝ :=
  {a | ∃ t, 0 ≤ t ∧ φ (initial a) t ∈ U}

theorem isOpen_hits (φ : E → ℝ → E) (initial : ℝ → E)
    (hφ : ∀ t, 0 ≤ t → Continuous (fun x => φ x t))
    (hi : Continuous initial) {U : Set E} (hU : IsOpen U) :
    IsOpen (hits φ initial U) := by
  rw [isOpen_iff_mem_nhds]
  rintro a ⟨t, ht, ha⟩
  have hn := (hU.preimage ((hφ t ht).comp hi)).mem_nhds ha
  apply Filter.mem_of_superset hn
  intro b hb
  exact ⟨t, ht, hb⟩

omit [TopologicalSpace E] in
theorem disjoint_hits (φ : E → ℝ → E) (initial : ℝ → E)
    (hadd : ∀ x s t, φ (φ x s) t = φ x (t + s))
    {U V : Set E} (hUV : Disjoint U V)
    (hU : ∀ x ∈ U, ∀ t, 0 ≤ t → φ x t ∈ U)
    (hV : ∀ x ∈ V, ∀ t, 0 ≤ t → φ x t ∈ V) :
    Disjoint (hits φ initial U) (hits φ initial V) := by
  apply Set.disjoint_left.mpr
  rintro a ⟨s, _, hs⟩ ⟨t, _, ht⟩
  rcases le_total s t with hst | hts
  · have h := hU _ hs (t - s) (sub_nonneg.mpr hst)
    rw [hadd, sub_add_cancel] at h
    exact Set.disjoint_left.mp hUV h ht
  · have h := hV _ ht (s - t) (sub_nonneg.mpr hts)
    rw [hadd, sub_add_cancel] at h
    exact Set.disjoint_left.mp hUV hs h

/-- Shooting theorem for a continuous family of global trajectories. All exit
times are finite; the conclusion avoids both open exit regions at every time. -/
theorem exists_avoiding_exits (φ : E → ℝ → E) (initial : ℝ → E)
    (hφ : ∀ t, 0 ≤ t → Continuous (fun x => φ x t))
    (hadd : ∀ x s t, φ (φ x s) t = φ x (t + s))
    (hi : Continuous initial) {U V : Set E}
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hUV : Disjoint U V)
    (hU : ∀ x ∈ U, ∀ t, 0 ≤ t → φ x t ∈ U)
    (hV : ∀ x ∈ V, ∀ t, 0 ≤ t → φ x t ∈ V)
    {a b : ℝ} (hab : a ≤ b)
    (ha : a ∈ hits φ initial U) (hb : b ∈ hits φ initial V) :
    ∃ c ∈ Icc a b, ∀ t, 0 ≤ t → φ (initial c) t ∉ U ∪ V := by
  have hdis := disjoint_hits φ initial hadd hUV hU hV
  have hncover : ¬ Icc a b ⊆ hits φ initial U ∪ hits φ initial V := by
    intro hcover
    have hleft := isPreconnected_Icc.subset_left_of_subset_union
      (isOpen_hits φ initial hφ hi hUopen) (isOpen_hits φ initial hφ hi hVopen)
      hdis hcover ⟨a, ⟨⟨le_rfl, hab⟩, ha⟩⟩
    exact Set.disjoint_left.mp hdis (hleft ⟨hab, le_rfl⟩) hb
  obtain ⟨c, hc, hnot⟩ := Set.not_subset.mp hncover
  refine ⟨c, hc, ?_⟩
  intro t ht hmem
  apply hnot
  rcases hmem with hu | hv
  · exact Or.inl ⟨t, ht, hu⟩
  · exact Or.inr ⟨t, ht, hv⟩

end RamseyCassKoopmans.ODE


/-! # Constructing a trajectory between the two equilibrium escape quadrants -/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.ODE

def lowerQuadrant (a : ℝ × ℝ) : Set (ℝ × ℝ) := {x | x.1 < a.1 ∧ x.2 < a.2}
def upperQuadrant (a : ℝ × ℝ) : Set (ℝ × ℝ) := {x | a.1 < x.1 ∧ a.2 < x.2}

theorem isOpen_lowerQuadrant (a : ℝ × ℝ) : IsOpen (lowerQuadrant a) :=
  (isOpen_lt continuous_fst continuous_const).inter (isOpen_lt continuous_snd continuous_const)

theorem isOpen_upperQuadrant (a : ℝ × ℝ) : IsOpen (upperQuadrant a) :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)

theorem disjoint_quadrants (a : ℝ × ℝ) : Disjoint (lowerQuadrant a) (upperQuadrant a) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact lt_asymm hx.1 hy.1

/-- The two endpoint hypotheses concern escape of ordinary initial-value
solutions. The nonescaping trajectory in the conclusion is constructed. -/
theorem exists_solution_avoiding_quadrants
    {v : ℝ × ℝ → ℝ × ℝ} {L K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L)
    {a : ℝ × ℝ} (ha : v a = 0)
    (initial : ℝ → ℝ × ℝ) (hi : Continuous initial) {l r : ℝ} (hlr : l ≤ r)
    (hleft : ∀ γ : ℝ → ℝ × ℝ, γ 0 = initial l →
      (∀ t, HasDerivAt γ (v (γ t)) t) → ∃ t, 0 ≤ t ∧ γ t ∈ lowerQuadrant a)
    (hright : ∀ γ : ℝ → ℝ × ℝ, γ 0 = initial r →
      (∀ t, HasDerivAt γ (v (γ t)) t) → ∃ t, 0 ≤ t ∧ γ t ∈ upperQuadrant a) :
    ∃ q ∈ Icc l r, ∃ γ : ℝ → ℝ × ℝ,
      γ 0 = initial q ∧ (∀ t, HasDerivAt γ (v (γ t)) t) ∧
      ∀ t, 0 ≤ t → γ t ∉ lowerQuadrant a ∪ upperQuadrant a := by
  obtain ⟨φ, h0, hφ, hcont⟩ := exists_global_flow hl hbound
  have hlow : ∀ x ∈ lowerQuadrant a, ∀ t, 0 ≤ t → φ x t ∈ lowerQuadrant a := by
    intro x hx
    apply solution_lt_equilibrium hc hl ha (hφ x)
    simpa only [h0 x] using (show x.1 < a.1 ∧ x.2 < a.2 from hx)
  have hupp : ∀ x ∈ upperQuadrant a, ∀ t, 0 ≤ t → φ x t ∈ upperQuadrant a := by
    intro x hx
    apply solution_gt_equilibrium hc hl ha (hφ x)
    simpa only [h0 x] using (show a.1 < x.1 ∧ a.2 < x.2 from hx)
  obtain ⟨q, hq, havoid⟩ := exists_avoiding_exits φ initial hcont
    (flow_add hl φ h0 hφ) hi (isOpen_lowerQuadrant a) (isOpen_upperQuadrant a)
    (disjoint_quadrants a) hlow hupp hlr
    (hleft _ (h0 _) (hφ _)) (hright _ (h0 _) (hφ _))
  exact ⟨q, hq, φ (initial q), h0 _, hφ _, havoid⟩

theorem enters_lower_at_boundary {γ : ℝ → ℝ × ℝ} {a w : ℝ × ℝ}
    (hd : HasDerivAt γ w 0) (hk : (γ 0).1 < a.1) (hq : (γ 0).2 = a.2)
    (hv : w.2 < 0) : ∃ t, 0 < t ∧ γ t ∈ lowerQuadrant a := by
  have hknear : ∀ᶠ t in 𝓝 0, (γ t).1 < a.1 :=
    (hasDerivAt_fst hd).continuousAt.eventually (gt_mem_nhds hk)
  have hqnear := eventually_lt_right_of_deriv_neg (hasDerivAt_snd hd) hv
  have htnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hkt, hqt⟩ :=
    (htnear.and ((hknear.filter_mono nhdsWithin_le_nhds).and hqnear)).exists
  exact ⟨t, ht, hkt, hq ▸ hqt⟩

theorem enters_upper_at_boundary {γ : ℝ → ℝ × ℝ} {a w : ℝ × ℝ}
    (hd : HasDerivAt γ w 0) (hk : a.1 < (γ 0).1) (hq : (γ 0).2 = a.2)
    (hv : 0 < w.2) : ∃ t, 0 < t ∧ γ t ∈ upperQuadrant a := by
  have hneg : HasDerivAt (fun t => -γ t) (-w) 0 := hd.neg
  obtain ⟨t, ht, hmem⟩ := enters_lower_at_boundary (a := -a) hneg
    (neg_lt_neg hk) (congrArg Neg.neg hq) (neg_neg_of_pos hv)
  refine ⟨t, ht, ?_⟩
  simpa only [lowerQuadrant, upperQuadrant, mem_ofPred_eq, Prod.fst_neg,
    Prod.snd_neg, neg_lt_neg_iff] using hmem

end RamseyCassKoopmans.ODE


/-! # Cass's cooperative capital and shadow-price system

Consumption is the smaller of inverse marginal utility and current output.
Writing its marginal utility as `max q (μ (f k))` makes the price equation
continuous at a zero-investment switch. All economic identities below are
proved explicitly, including the investment constraint and complementarity.
-/

open Set
open scoped NNReal

namespace RamseyCassKoopmans

def cassConsumption (f C : ℝ → ℝ) (x : ℝ × ℝ) : ℝ := min (C x.2) (f x.1)

def cassInvestment (f C : ℝ → ℝ) (x : ℝ × ℝ) : ℝ := f x.1 - cassConsumption f C x

def cassField (f mp μ C : ℝ → ℝ) (d m : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (cassInvestment f C x - m * x.1, (d + m) * x.2 - max x.2 (μ (f x.1)) * mp x.1)

def cassExtension (f mp μ C : ℝ → ℝ) (d m kl ku ql qu : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  cassField f mp μ C d m (clip kl ku x.1, clip ql qu x.2)

theorem cass_consumption_pos {f C : ℝ → ℝ} {x : ℝ × ℝ}
    (hf : 0 < f x.1) (hC : 0 < C x.2) : 0 < cassConsumption f C x :=
  lt_min hC hf

theorem cass_investment_nonneg (f C : ℝ → ℝ) (x : ℝ × ℝ) :
    0 ≤ cassInvestment f C x := sub_nonneg.mpr (min_le_right _ _)

theorem cass_resource (f C : ℝ → ℝ) (x : ℝ × ℝ) :
    cassConsumption f C x + cassInvestment f C x = f x.1 := by
  unfold cassInvestment
  ring

theorem marginal_utility_min {μ : ℝ → ℝ} (hμ : AntitoneOn μ (Ioi 0))
    {c y : ℝ} (hc : 0 < c) (hy : 0 < y) : μ (min c y) = max (μ c) (μ y) := by
  rcases le_total c y with h | h
  · rw [min_eq_left h, max_eq_left (hμ hc hy h)]
  · rw [min_eq_right h, max_eq_right (hμ hy hc h)]

/-- This covers prices below the lowest price used in the inverse construction:
the production constraint then selects output itself as consumption. -/
theorem cass_marginal_utility {f μ C : ℝ → ℝ} {a b : ℝ} {x : ℝ × ℝ}
    (hμ : AntitoneOn μ (Ioi 0)) (ha : 0 < a)
    (hy : f x.1 ∈ Icc a b) (hC : C x.2 ∈ Icc a b)
    (hinv : μ (C x.2) = clip (μ b) (μ a) x.2) (hq : x.2 ≤ μ a) :
    μ (cassConsumption f C x) = max x.2 (μ (f x.1)) := by
  have hyp : 0 < f x.1 := ha.trans_le hy.1
  have hbp : 0 < b := hyp.trans_le hy.2
  have hby : μ b ≤ μ (f x.1) := hμ hyp hbp hy.2
  rw [cassConsumption, marginal_utility_min hμ (ha.trans_le hC.1) hyp,
    hinv, clip, min_eq_right hq]
  rw [max_assoc]
  exact max_left_comm _ _ _ |>.trans (congrArg (max x.2) (max_eq_right hby))

theorem cass_wedge_and_slack {f μ C : ℝ → ℝ} {x : ℝ × ℝ}
    (heq : μ (cassConsumption f C x) = max x.2 (μ (f x.1)))
    (hstrict : StrictAntiOn μ (Ioi 0))
    (hy : 0 < f x.1) (hC : 0 < C x.2) :
    x.2 ≤ μ (cassConsumption f C x) ∧
      (x.2 - μ (cassConsumption f C x)) * cassInvestment f C x = 0 := by
  refine ⟨heq ▸ le_max_left _ _, ?_⟩
  rcases lt_or_ge (C x.2) (f x.1) with h | h
  · have hmu : μ (f x.1) < μ (cassConsumption f C x) := by
      simpa only [cassConsumption, min_eq_left h.le] using hstrict hC hy h
    have hmax : μ (f x.1) < x.2 := by
      rw [heq] at hmu
      exact (lt_max_iff.mp hmu).resolve_right (lt_irrefl _)
    rw [heq, max_eq_left hmax.le, sub_self, zero_mul]
  · simp only [cassInvestment, cassConsumption, min_eq_right h, sub_self, mul_zero]

theorem cass_field_costate {f mp μ C : ℝ → ℝ} {d m : ℝ} {x : ℝ × ℝ}
    (heq : μ (cassConsumption f C x) = max x.2 (μ (f x.1))) :
    (cassField f mp μ C d m x).2 =
      (d + m) * x.2 - μ (cassConsumption f C x) * mp x.1 := by
  rw [heq]
  rfl

theorem cass_extension_eq {f mp μ C : ℝ → ℝ} {d m kl ku ql qu : ℝ} {x : ℝ × ℝ}
    (hk : x.1 ∈ Icc kl ku) (hq : x.2 ∈ Icc ql qu) :
    cassExtension f mp μ C d m kl ku ql qu x = cassField f mp μ C d m x := by
  simp only [cassExtension, clip_eq hk, clip_eq hq, Prod.mk.eta]

/-- Cooperation needs decreasing inverse demand and decreasing, nonnegative
marginal utility of output and marginal product. No derivative at the switch
is assumed. -/
theorem cass_extension_cooperative {f mp μ C : ℝ → ℝ} {d m kl ku ql qu : ℝ}
    (hkk : kl ≤ ku) (hC : Antitone C)
    (hH : AntitoneOn (fun k => μ (f k)) (Icc kl ku))
    (hP : AntitoneOn mp (Icc kl ku))
    (hHpos : ∀ k ∈ Icc kl ku, 0 ≤ μ (f k))
    (hPpos : ∀ k ∈ Icc kl ku, 0 ≤ mp k) :
    ODE.Cooperative (cassExtension f mp μ C d m kl ku ql qu) := by
  constructor
  · intro k p q hpq
    have hCorder := hC (monotone_clip ql qu hpq)
    have hmin := min_le_min_right (f (clip kl ku k)) hCorder
    change f _ - min (C (clip ql qu p)) _ - _ ≤
      f _ - min (C (clip ql qu q)) _ - _
    linarith
  · intro q k l hkl
    have hk := clip_mem hkk k
    have hl := clip_mem hkk l
    have horder := monotone_clip kl ku hkl
    have hmax := max_le_max_left (clip ql qu q) (hH hk hl horder)
    have hprod := mul_le_mul hmax (hP hk hl horder)
      (hPpos _ hl) ((hHpos _ hk).trans (le_max_right _ _))
    change (d + m) * _ - _ ≤ (d + m) * _ - _
    linarith

theorem cass_extension_boundedLip {f mp μ C : ℝ → ℝ} {d m kl ku ql qu : ℝ}
    (hkk : kl ≤ ku) (hqq : ql ≤ qu)
    (hf : BoundedLip (f ∘ clip kl ku))
    (hmp : BoundedLip (mp ∘ clip kl ku))
    (hmu : BoundedLip ((fun k => μ (f k)) ∘ clip kl ku))
    (hC : BoundedLip C) :
    BoundedLip (cassExtension f mp μ C d m kl ku ql qu) := by
  have hk := (boundedLip_clip hkk).comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))
  have hq := (boundedLip_clip hqq).comp (LipschitzWith.prod_snd (α := ℝ) (β := ℝ))
  have hf' := hf.comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))
  have hmp' := hmp.comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))
  have hmu' := hmu.comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))
  obtain ⟨Kq, Mq, hqLip, hqBound⟩ := hq
  have hc' := hC.comp hqLip
  have hfst := (hf'.sub (hc'.min_function hf')).sub ((BoundedLip.const m).mul hk)
  have hsnd := ((BoundedLip.const (d + m)).mul ⟨Kq, Mq, hqLip, hqBound⟩).sub
    ((BoundedLip.max_function ⟨Kq, Mq, hqLip, hqBound⟩ hmu').mul hmp')
  exact hfst.prodMk hsnd

end RamseyCassKoopmans


/-! # Monotonicity of the trajectory selected by shooting

The escape condition is used to exclude an incorrectly directed vector at an
ordinary point of the trajectory. The comparison theorem traps such a vector's
future in a rectangle; a uniform drift would then force escape in finite time.
-/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.ODE

def Avoids (γ : ℝ → ℝ × ℝ) (a : ℝ × ℝ) : Prop :=
  ∀ t, 0 ≤ t → γ t ∉ lowerQuadrant a ∪ upperQuadrant a

theorem trajectory_shift {v : ℝ × ℝ → ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (v (γ t)) t) (s : ℝ) :
    ∀ t, HasDerivAt (fun u => γ (u + s)) (v (γ (t + s))) t := by
  intro t
  convert (hd (t + s)).scomp t ((hasDerivAt_id t).add_const s) using 1
  · rfl
  · simp only [one_smul]

theorem avoids_shift {γ : ℝ → ℝ × ℝ} {a : ℝ × ℝ} (h : Avoids γ a)
    {s : ℝ} (hs : 0 ≤ s) : Avoids (fun u => γ (u + s)) a :=
  fun t ht => h (t + s) (add_nonneg ht hs)

theorem never_reaches_equilibrium {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hl : LipschitzWith K v) {a : ℝ × ℝ} (ha : v a = 0)
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : γ 0 ≠ a) : ∀ t, γ t ≠ a := by
  intro t ht
  have heq : γ = fun _ => a := by
    apply ODE_solution_unique_univ (v := fun (_ : ℝ) => v)
      (s := fun _ => univ) (t₀ := t) (fun _ => hl.lipschitzOnWith)
      (fun u => ⟨hd u, mem_univ _⟩)
      (fun u => ⟨by simpa only [ha] using hasDerivAt_const u a, mem_univ _⟩) ht
  exact h0 (congrFun heq 0)

theorem enters_lower_at_first_boundary {γ : ℝ → ℝ × ℝ} {a w : ℝ × ℝ}
    (hd : HasDerivAt γ w 0) (hk : (γ 0).1 = a.1) (hq : (γ 0).2 < a.2)
    (hv : w.1 < 0) : ∃ t, 0 < t ∧ γ t ∈ lowerQuadrant a := by
  have hswap : HasDerivAt (fun t => ((γ t).2, (γ t).1)) (w.2, w.1) 0 :=
    (hasDerivAt_snd hd).prodMk (hasDerivAt_fst hd)
  obtain ⟨t, ht, hmem⟩ := enters_lower_at_boundary (a := (a.2, a.1)) hswap hq hk hv
  exact ⟨t, ht, hmem.2, hmem.1⟩

theorem enters_upper_at_first_boundary {γ : ℝ → ℝ × ℝ} {a w : ℝ × ℝ}
    (hd : HasDerivAt γ w 0) (hk : (γ 0).1 = a.1) (hq : a.2 < (γ 0).2)
    (hv : 0 < w.1) : ∃ t, 0 < t ∧ γ t ∈ upperQuadrant a := by
  have hswap : HasDerivAt (fun t => ((γ t).2, (γ t).1)) (w.2, w.1) 0 :=
    (hasDerivAt_snd hd).prodMk (hasDerivAt_fst hd)
  obtain ⟨t, ht, hmem⟩ := enters_upper_at_boundary (a := (a.2, a.1)) hswap hq hk hv
  exact ⟨t, ht, hmem.2, hmem.1⟩

theorem avoids_first_ne {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hl : LipschitzWith K v) {a : ℝ × ℝ} (ha : v a = 0)
    (haxis : ∀ x : ℝ × ℝ, x.1 = a.1 →
      (x.2 < a.2 → (v x).1 < 0) ∧ (a.2 < x.2 → 0 < (v x).1))
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : γ 0 ≠ a) (havoid : Avoids γ a) :
    ∀ T, 0 ≤ T → (γ T).1 ≠ a.1 := by
  intro T hT hk
  have hdshift := trajectory_shift hd T 0
  simp only [zero_add] at hdshift
  rcases lt_trichotomy (γ T).2 a.2 with hq | hq | hq
  · obtain ⟨s, hs, hmem⟩ := enters_lower_at_first_boundary (a := a) hdshift
      (by simpa only [zero_add] using hk) (by simpa only [zero_add] using hq) ((haxis _ hk).1 hq)
    exact havoid (s + T) (add_nonneg hs.le hT) (Or.inl hmem)
  · exact never_reaches_equilibrium hl ha hd h0 T (Prod.ext hk hq)
  · obtain ⟨s, hs, hmem⟩ := enters_upper_at_first_boundary (a := a) hdshift
      (by simpa only [zero_add] using hk) (by simpa only [zero_add] using hq) ((haxis _ hk).2 hq)
    exact havoid (s + T) (add_nonneg hs.le hT) (Or.inr hmem)

theorem first_stays_below {γ : ℝ → ℝ × ℝ} {a : ℝ × ℝ}
    (hc : Continuous γ) (h0 : (γ 0).1 < a.1)
    (hne : ∀ t, 0 ≤ t → (γ t).1 ≠ a.1) : ∀ t, 0 ≤ t → (γ t).1 < a.1 := by
  intro t ht
  by_contra hn
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc ht hc.fst.continuousOn
    (show a.1 ∈ Icc (γ 0).1 (γ t).1 from ⟨h0.le, le_of_not_gt hn⟩)
  exact hne s hs.1 heq

theorem first_stays_above {γ : ℝ → ℝ × ℝ} {a : ℝ × ℝ}
    (hc : Continuous γ) (h0 : a.1 < (γ 0).1)
    (hne : ∀ t, 0 ≤ t → (γ t).1 ≠ a.1) : ∀ t, 0 ≤ t → a.1 < (γ t).1 := by
  intro t ht
  by_contra hn
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc' ht hc.fst.continuousOn
    (show a.1 ∈ Icc (γ t).1 (γ 0).1 from ⟨le_of_not_gt hn, h0.le⟩)
  exact hne s hs.1 heq

/-- On the lower-capital branch, a nonpositive capital velocity would force
the price below the steady price. The drift bound concerns finite rectangles
of points, not an assumed property of a selected solution. -/
theorem lower_branch_velocity {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ}
    (hprice : ∀ x : ℝ × ℝ, x.1 < a.1 → a.2 ≤ x.2 → (v x).2 < 0)
    (hdrift : ∀ b : ℝ × ℝ, b.1 < a.1 → a.2 ≤ b.2 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ × ℝ,
        x.1 ≤ b.1 → a.2 ≤ x.2 → x.2 ≤ b.2 → (v x).2 ≤ -ε)
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hk : ∀ t, 0 ≤ t → (γ t).1 < a.1) (havoid : Avoids γ a) :
    ∀ t, 0 ≤ t → 0 < (v (γ t)).1 ∧ (v (γ t)).2 < 0 := by
  have hq : ∀ t, 0 ≤ t → a.2 ≤ (γ t).2 := by
    intro t ht
    by_contra hn
    exact havoid t ht (Or.inl ⟨hk t ht, lt_of_not_ge hn⟩)
  intro t ht
  have hv2 := hprice (γ t) (hk t ht) (hq t ht)
  refine ⟨?_, hv2⟩
  by_contra hn
  have hs := trajectory_shift hd t
  have hle := solution_le_supersolution hc hl
    (a := γ t) ⟨le_of_not_gt hn, hv2.le⟩ hs
    (by simp only [zero_add]; exact ⟨le_rfl, le_rfl⟩)
  obtain ⟨ε, hε, he⟩ := hdrift (γ t) (hk t ht) (hq t ht)
  exact not_bounded_below_of_negative_drift (fun s => hasDerivAt_snd (hs s)) hε
    (fun s hs0 => he _ (hle s hs0).1 (hq _ (add_nonneg hs0 ht)) (hle s hs0).2)
    (fun s hs0 => hq _ (add_nonneg hs0 ht))

theorem lower_branch_monotone {v : ℝ × ℝ → ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hv : ∀ t, 0 ≤ t → 0 < (v (γ t)).1 ∧ (v (γ t)).2 < 0) :
    StrictMonoOn (fun t => (γ t).1) (Ici 0) ∧
      StrictAntiOn (fun t => (γ t).2) (Ici 0) := by
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (HasDerivAt.continuousOn (fun t _ => hasDerivAt_fst (hd t)))
    intro t ht
    rw [(hasDerivAt_fst (hd t)).deriv]
    exact (hv t (interior_subset ht)).1
  · apply strictAntiOn_of_deriv_neg (convex_Ici 0)
      (HasDerivAt.continuousOn (fun t _ => hasDerivAt_snd (hd t)))
    intro t ht
    rw [(hasDerivAt_snd (hd t)).deriv]
    exact (hv t (interior_subset ht)).2

/-- On the upper-capital branch, the two possible incorrect directions are
excluded separately. The second drift condition includes an investment corner:
it can force capital down even when the price equation is not the Euler equation. -/
theorem upper_branch_velocity {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ}
    (hcross : ∀ b : ℝ × ℝ, a.1 < b.1 → b.2 ≤ a.2 →
      0 ≤ (v b).1 → 0 < (v b).2)
    (hup : ∀ b : ℝ × ℝ, a.1 < b.1 → b.2 ≤ a.2 → 0 ≤ (v b).1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ × ℝ,
        b.1 ≤ x.1 → b.2 ≤ x.2 → x.2 ≤ a.2 → ε ≤ (v x).2)
    (hdown : ∀ b : ℝ × ℝ, a.1 < b.1 → b.2 ≤ a.2 → (v b).2 ≤ 0 →
      (v b).1 ≤ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ × ℝ,
        a.1 ≤ x.1 → x.1 ≤ b.1 → x.2 ≤ b.2 → (v x).1 ≤ -ε)
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hk : ∀ t, 0 ≤ t → a.1 < (γ t).1) (havoid : Avoids γ a) :
    ∀ t, 0 ≤ t → (v (γ t)).1 < 0 ∧ 0 < (v (γ t)).2 := by
  have hq : ∀ t, 0 ≤ t → (γ t).2 ≤ a.2 := by
    intro t ht
    by_contra hn
    exact havoid t ht (Or.inr ⟨hk t ht, lt_of_not_ge hn⟩)
  intro t ht
  have hs := trajectory_shift hd t
  constructor
  · by_contra hn
    have hv1 : 0 ≤ (v (γ t)).1 := le_of_not_gt hn
    have hv2 := hcross (γ t) (hk t ht) (hq t ht) hv1
    have hge := solution_ge_subsolution hc hl (a := γ t) ⟨hv1, hv2.le⟩ hs
      (by simp only [zero_add]; exact ⟨le_rfl, le_rfl⟩)
    obtain ⟨ε, hε, he⟩ := hup (γ t) (hk t ht) (hq t ht) hv1
    exact not_bounded_above_of_positive_drift (fun s => hasDerivAt_snd (hs s)) hε
      (fun s hs0 => he _ (hge s hs0).1 (hge s hs0).2 (hq _ (add_nonneg hs0 ht)))
      (fun s hs0 => hq _ (add_nonneg hs0 ht))
  · by_contra hn
    have hv2 : (v (γ t)).2 ≤ 0 := le_of_not_gt hn
    obtain ⟨hv1, ε, hε, he⟩ := hdown (γ t) (hk t ht) (hq t ht) hv2
    have hle := solution_le_supersolution hc hl (a := γ t) ⟨hv1, hv2⟩ hs
      (by simp only [zero_add]; exact ⟨le_rfl, le_rfl⟩)
    exact not_bounded_below_of_negative_drift (fun s => hasDerivAt_fst (hs s)) hε
      (fun s hs0 => he _ (hk _ (add_nonneg hs0 ht)).le (hle s hs0).1 (hle s hs0).2)
      (fun s hs0 => (hk _ (add_nonneg hs0 ht)).le)

theorem upper_branch_monotone {v : ℝ × ℝ → ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hv : ∀ t, 0 ≤ t → (v (γ t)).1 < 0 ∧ 0 < (v (γ t)).2) :
    StrictAntiOn (fun t => (γ t).1) (Ici 0) ∧
      StrictMonoOn (fun t => (γ t).2) (Ici 0) := by
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Ici 0)
      (HasDerivAt.continuousOn (fun t _ => hasDerivAt_fst (hd t)))
    intro t ht
    rw [(hasDerivAt_fst (hd t)).deriv]
    exact (hv t (interior_subset ht)).1
  · apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (HasDerivAt.continuousOn (fun t _ => hasDerivAt_snd (hd t)))
    intro t ht
    rw [(hasDerivAt_snd (hd t)).deriv]
    exact (hv t (interior_subset ht)).2

theorem lower_branch_limit {v : ℝ × ℝ → ℝ × ℝ} (hc : Continuous v)
    {γ : ℝ → ℝ × ℝ} {a : ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hk : ∀ t, 0 ≤ t → (γ t).1 ≤ a.1)
    (hq : ∀ t, 0 ≤ t → a.2 ≤ (γ t).2)
    (hm : MonotoneOn (fun t => (γ t).1) (Ici 0))
    (ha : AntitoneOn (fun t => (γ t).2) (Ici 0)) :
    ∃ b : ℝ × ℝ, Tendsto γ atTop (𝓝 b) ∧ v b = 0 ∧
      b.1 ∈ Icc (γ 0).1 a.1 ∧ b.2 ∈ Icc a.2 (γ 0).2 := by
  obtain ⟨k, hklim⟩ := exists_limit_of_monotone_bounded hm hk
  obtain ⟨q, hqlim⟩ := exists_limit_of_antitone_bounded ha hq
  have hlim : Tendsto γ atTop (𝓝 (k, q)) := hklim.prodMk_nhds hqlim
  refine ⟨(k, q), hlim, limit_is_equilibrium hc hd hlim, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ge_of_tendsto hklim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht)
  · exact le_of_tendsto hklim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hk t ht)
  · exact ge_of_tendsto hqlim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hq t ht)
  · exact le_of_tendsto hqlim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact ha (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht)

theorem upper_branch_limit {v : ℝ × ℝ → ℝ × ℝ} (hc : Continuous v)
    {γ : ℝ → ℝ × ℝ} {a : ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hk : ∀ t, 0 ≤ t → a.1 ≤ (γ t).1)
    (hq : ∀ t, 0 ≤ t → (γ t).2 ≤ a.2)
    (ha : AntitoneOn (fun t => (γ t).1) (Ici 0))
    (hm : MonotoneOn (fun t => (γ t).2) (Ici 0)) :
    ∃ b : ℝ × ℝ, Tendsto γ atTop (𝓝 b) ∧ v b = 0 ∧
      b.1 ∈ Icc a.1 (γ 0).1 ∧ b.2 ∈ Icc (γ 0).2 a.2 := by
  obtain ⟨k, hklim⟩ := exists_limit_of_antitone_bounded ha hk
  obtain ⟨q, hqlim⟩ := exists_limit_of_monotone_bounded hm hq
  have hlim : Tendsto γ atTop (𝓝 (k, q)) := hklim.prodMk_nhds hqlim
  refine ⟨(k, q), hlim, limit_is_equilibrium hc hd hlim, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ge_of_tendsto hklim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hk t ht)
  · exact le_of_tendsto hklim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact ha (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht)
  · exact ge_of_tendsto hqlim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht)
  · exact le_of_tendsto hqlim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hq t ht)

end RamseyCassKoopmans.ODE


/-! # Finite economic data for the general Cass shooting argument

This structure records ordinary functions and inequalities on compact intervals.
It contains no trajectory, existence assertion, convergence assumption, or
optimality certificate. Its lemmas establish the phase inequalities needed by
the analytic construction. Marginal product and marginal utility are identified
with actual derivatives when applying this construction to a utility problem.
-/

open Set
open scoped NNReal

namespace RamseyCassKoopmans

structure CassPhase where
  f : ℝ → ℝ
  mp : ℝ → ℝ
  μ : ℝ → ℝ
  C : ℝ → ℝ
  d : ℝ
  m : ℝ
  kl : ℝ
  ku : ℝ
  ks : ℝ
  ca : ℝ
  cb : ℝ
  qs : ℝ
  Q : ℝ
  d_pos : 0 < d
  m_pos : 0 < m
  kl_pos : 0 < kl
  kl_lt : kl < ks
  ku_gt : ks < ku
  ca_pos : 0 < ca
  ca_le_cb : ca ≤ cb
  f_mem : ∀ k ∈ Icc kl ku, f k ∈ Icc ca cb
  f_mono : MonotoneOn f (Icc kl ku)
  mp_pos : ∀ k ∈ Icc kl ku, 0 < mp k
  mp_anti : StrictAntiOn mp (Icc kl ku)
  mp_star : mp ks = d + m
  μ_pos : ∀ c, 0 < c → 0 < μ c
  μ_anti : StrictAntiOn μ (Ioi 0)
  C_mem : ∀ q, C q ∈ Icc ca cb
  C_anti : Antitone C
  inverse : ∀ q, μ (C q) = clip (μ cb) (μ ca) q
  Q_eq : Q = μ ca
  qs_pos : 0 < qs
  qs_lt : qs < Q
  ca_lt_surplus : ca < f ks - m * ks
  qs_eq : qs = μ (f ks - m * ks)

namespace CassPhase

def stock (p : CassPhase) (k : ℝ) : ℝ := clip p.kl p.ku k
def price (p : CassPhase) (q : ℝ) : ℝ := clip 0 p.Q q
def point (p : CassPhase) (x : ℝ × ℝ) : ℝ × ℝ := (p.stock x.1, p.price x.2)
def field (p : CassPhase) : ℝ × ℝ → ℝ × ℝ :=
  cassExtension p.f p.mp p.μ p.C p.d p.m p.kl p.ku 0 p.Q

theorem stock_mem (p : CassPhase) (k : ℝ) : p.stock k ∈ Icc p.kl p.ku :=
  clip_mem (p.kl_lt.trans p.ku_gt).le k

theorem price_mem (p : CassPhase) (q : ℝ) : p.price q ∈ Icc 0 p.Q :=
  clip_mem (p.qs_pos.trans p.qs_lt).le q

theorem stock_pos (p : CassPhase) (k : ℝ) : 0 < p.stock k :=
  p.kl_pos.trans_le (p.stock_mem k).1

theorem output_pos (p : CassPhase) (k : ℝ) : 0 < p.f (p.stock k) :=
  p.ca_pos.trans_le (p.f_mem _ (p.stock_mem k)).1

theorem demand_pos (p : CassPhase) (q : ℝ) : 0 < p.C (p.price q) :=
  p.ca_pos.trans_le (p.C_mem _).1

theorem marginal (p : CassPhase) (x : ℝ × ℝ) :
    p.μ (cassConsumption p.f p.C (p.point x)) =
      max (p.price x.2) (p.μ (p.f (p.stock x.1))) :=
  cass_marginal_utility p.μ_anti.antitoneOn p.ca_pos
    (p.f_mem _ (p.stock_mem _)) (p.C_mem _) (p.inverse _)
    (by rw [← p.Q_eq]; exact (p.price_mem _).2)

theorem cooperative (p : CassPhase) : ODE.Cooperative p.field := by
  apply cass_extension_cooperative (p.kl_lt.trans p.ku_gt).le p.C_anti
  · intro x hx y hy hxy
    exact p.μ_anti.antitoneOn
      (p.ca_pos.trans_le (p.f_mem x hx).1)
      (p.ca_pos.trans_le (p.f_mem y hy).1) (p.f_mono hx hy hxy)
  · exact p.mp_anti.antitoneOn
  · exact fun k hk => (p.μ_pos _ (p.ca_pos.trans_le (p.f_mem k hk).1)).le
  · exact fun k hk => (p.mp_pos k hk).le

theorem stock_lt_star (p : CassPhase) {k : ℝ} (hk : k < p.ks) : p.stock k < p.ks := by
  exact max_lt p.kl_lt ((min_le_right p.ku k).trans_lt hk)

theorem stock_gt_star (p : CassPhase) {k : ℝ} (hk : p.ks < k) : p.ks < p.stock k := by
  exact (lt_min p.ku_gt hk).trans_le (le_max_right _ _)

theorem stock_ge_star (p : CassPhase) {k : ℝ} (hk : p.ks ≤ k) : p.ks ≤ p.stock k := by
  exact (le_min p.ku_gt.le hk).trans (le_max_right _ _)

theorem price_ge_star (p : CassPhase) {q : ℝ} (hq : p.qs ≤ q) : p.qs ≤ p.price q := by
  exact (le_min p.qs_lt.le hq).trans (le_max_right _ _)

theorem price_mono (p : CassPhase) : Monotone p.price := monotone_clip 0 p.Q
theorem stock_mono (p : CassPhase) : Monotone p.stock := monotone_clip p.kl p.ku

theorem mp_above_target (p : CassPhase) {k : ℝ} (hk : k < p.ks) :
    p.d + p.m < p.mp (p.stock k) := by
  rw [← p.mp_star]
  exact p.mp_anti (p.stock_mem k) ⟨p.kl_lt.le, p.ku_gt.le⟩ (p.stock_lt_star hk)

theorem mp_below_target (p : CassPhase) {k : ℝ} (hk : p.ks < k) :
    p.mp (p.stock k) < p.d + p.m := by
  rw [← p.mp_star]
  exact p.mp_anti ⟨p.kl_lt.le, p.ku_gt.le⟩ (p.stock_mem k) (p.stock_gt_star hk)

/-- The price decreases uniformly on every rectangle strictly left of steady
capital and above steady price, including points beyond the artificial clips. -/
theorem lower_price_drift (p : CassPhase) {b : ℝ × ℝ} (hb : b.1 < p.ks) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ × ℝ,
      x.1 ≤ b.1 → p.qs ≤ x.2 → (p.field x).2 ≤ -ε := by
  let ε := (p.mp (p.stock b.1) - (p.d + p.m)) * p.qs
  refine ⟨ε, mul_pos (sub_pos.mpr (p.mp_above_target hb)) p.qs_pos, ?_⟩
  intro x hk hq
  have hmp := p.mp_anti.antitoneOn (p.stock_mem _) (p.stock_mem _) (p.stock_mono hk)
  have hp := p.price_ge_star hq
  have hmpx := p.mp_pos _ (p.stock_mem x.1)
  have hm := mul_le_mul_of_nonneg_right
    (le_max_left (p.price x.2) (p.μ (p.f (p.stock x.1)))) hmpx.le
  have hfactor : (p.mp (p.stock b.1) - (p.d + p.m)) * p.qs ≤
      (p.mp (p.stock x.1) - (p.d + p.m)) * p.price x.2 :=
    mul_le_mul (sub_le_sub_right hmp _) hp p.qs_pos.le
      (by linarith [p.mp_above_target hb])
  change (p.d + p.m) * p.price x.2 -
    max (p.price x.2) (p.μ (p.f (p.stock x.1))) * p.mp (p.stock x.1) ≤ -ε
  dsimp [ε]
  nlinarith

theorem lower_price_negative (p : CassPhase) {x : ℝ × ℝ}
    (hk : x.1 < p.ks) (hq : p.qs ≤ x.2) : (p.field x).2 < 0 := by
  obtain ⟨ε, hε, he⟩ := p.lower_price_drift (b := x) hk
  exact (he x le_rfl hq).trans_lt (neg_neg_of_pos hε)

theorem interior_price (p : CassPhase) {x : ℝ × ℝ}
    (hz : 0 < cassInvestment p.f p.C (p.point x)) :
    p.μ (cassConsumption p.f p.C (p.point x)) = p.price x.2 ∧
      0 < p.price x.2 := by
  have hc : 0 < cassConsumption p.f p.C (p.point x) :=
    cass_consumption_pos (p.output_pos _) (p.demand_pos _)
  have hlt : cassConsumption p.f p.C (p.point x) < p.f (p.stock x.1) :=
    sub_pos.mp hz
  have hμ := p.μ_anti hc (p.output_pos _) hlt
  rw [p.marginal x] at hμ
  have hprice : p.μ (p.f (p.stock x.1)) < p.price x.2 :=
    (lt_max_iff.mp hμ).resolve_right (lt_irrefl _)
  exact ⟨(p.marginal x).trans (max_eq_left hprice.le),
    (p.μ_pos _ (p.output_pos _)).trans hprice⟩

theorem interior_field_price (p : CassPhase) {x : ℝ × ℝ}
    (hz : 0 < cassInvestment p.f p.C (p.point x)) :
    (p.field x).2 = (p.d + p.m - p.mp (p.stock x.1)) * p.price x.2 := by
  have hh := (p.interior_price hz).1
  rw [p.marginal x] at hh
  change (p.d + p.m) * p.price x.2 -
    max (p.price x.2) (p.μ (p.f (p.stock x.1))) * p.mp (p.stock x.1) = _
  rw [hh]
  ring

theorem upper_cross (p : CassPhase) {x : ℝ × ℝ}
    (hk : p.ks < x.1) (hv : 0 ≤ (p.field x).1) : 0 < (p.field x).2 := by
  have hz : 0 < cassInvestment p.f p.C (p.point x) := by
    have hm := mul_pos p.m_pos (p.stock_pos x.1)
    change 0 ≤ cassInvestment p.f p.C (p.point x) - p.m * p.stock x.1 at hv
    linarith
  rw [p.interior_field_price hz]
  exact mul_pos (sub_pos.mpr (p.mp_below_target hk)) (p.interior_price hz).2

theorem investment_mono (p : CassPhase) {x y : ℝ × ℝ}
    (hk : x.1 ≤ y.1) (hq : x.2 ≤ y.2) :
    cassInvestment p.f p.C (p.point x) ≤ cassInvestment p.f p.C (p.point y) := by
  have hf := p.f_mono (p.stock_mem _) (p.stock_mem _) (p.stock_mono hk)
  have hC := p.C_anti (p.price_mono hq)
  change p.f (p.stock x.1) - min (p.C (p.price x.2)) (p.f (p.stock x.1)) ≤
    p.f (p.stock y.1) - min (p.C (p.price y.2)) (p.f (p.stock y.1))
  simp only [min_def]
  split_ifs <;> linarith

theorem upper_price_drift (p : CassPhase) {b : ℝ × ℝ}
    (hb : p.ks < b.1) (hv : 0 ≤ (p.field b).1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ × ℝ,
      b.1 ≤ x.1 → b.2 ≤ x.2 → ε ≤ (p.field x).2 := by
  have hz : 0 < cassInvestment p.f p.C (p.point b) := by
    have hm := mul_pos p.m_pos (p.stock_pos b.1)
    change 0 ≤ cassInvestment p.f p.C (p.point b) - p.m * p.stock b.1 at hv
    linarith
  let ε := (p.d + p.m - p.mp (p.stock b.1)) * p.price b.2
  refine ⟨ε, mul_pos (sub_pos.mpr (p.mp_below_target hb)) (p.interior_price hz).2, ?_⟩
  intro x hk hq
  have hzx := hz.trans_le (p.investment_mono hk hq)
  rw [p.interior_field_price hzx]
  exact mul_le_mul
    (sub_le_sub_left (p.mp_anti.antitoneOn (p.stock_mem _) (p.stock_mem _) (p.stock_mono hk)) _)
    (p.price_mono hq) (p.interior_price hz).2.le
    (sub_pos.mpr (p.mp_below_target (hb.trans_le hk))).le

theorem upper_corner_drift (p : CassPhase) {b : ℝ × ℝ}
    (hb : p.ks < b.1) (hv : (p.field b).2 ≤ 0) :
    (p.field b).1 ≤ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ × ℝ,
      p.ks ≤ x.1 → x.1 ≤ b.1 → x.2 ≤ b.2 → (p.field x).1 ≤ -ε := by
  have hzb : cassInvestment p.f p.C (p.point b) = 0 := by
    by_contra hn
    have hz := lt_of_le_of_ne (cass_investment_nonneg p.f p.C (p.point b)) (Ne.symm hn)
    have hp : 0 < (p.field b).2 := by
      rw [p.interior_field_price hz]
      exact mul_pos (sub_pos.mpr (p.mp_below_target hb)) (p.interior_price hz).2
    linarith
  have hxb : (p.field b).1 = -p.m * p.stock b.1 := by
    change cassInvestment p.f p.C (p.point b) - p.m * p.stock b.1 = _
    rw [hzb]
    ring
  refine ⟨hxb ▸ (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.m_pos.le)
    (p.stock_pos b.1).le), p.m * p.ks, mul_pos p.m_pos (p.kl_pos.trans p.kl_lt), ?_⟩
  intro x hstar hk hq
  have hzx : cassInvestment p.f p.C (p.point x) = 0 :=
    le_antisymm (hzb ▸ p.investment_mono hk hq) (cass_investment_nonneg p.f p.C (p.point x))
  change cassInvestment p.f p.C (p.point x) - p.m * p.stock x.1 ≤ -(p.m * p.ks)
  rw [hzx, zero_sub]
  exact neg_le_neg (mul_le_mul_of_nonneg_left (p.stock_ge_star hstar) p.m_pos.le)

end CassPhase
end RamseyCassKoopmans


/-! # The equilibrium and the direction of crossing its capital axis -/

open Set

namespace RamseyCassKoopmans.CassPhase

def steady (p : CassPhase) : ℝ × ℝ := (p.ks, p.qs)
def surplus (p : CassPhase) : ℝ := p.f p.ks - p.m * p.ks

theorem ks_pos (p : CassPhase) : 0 < p.ks := p.kl_pos.trans p.kl_lt

theorem surplus_pos (p : CassPhase) : 0 < p.surplus := p.ca_pos.trans p.ca_lt_surplus

theorem surplus_lt_output (p : CassPhase) : p.surplus < p.f p.ks := by
  have hp := mul_pos p.m_pos p.ks_pos
  dsimp [surplus]
  linarith

theorem surplus_lt_cb (p : CassPhase) : p.surplus < p.cb :=
  p.surplus_lt_output.trans_le (p.f_mem _ ⟨p.kl_lt.le, p.ku_gt.le⟩).2

theorem bottom_price_lt (p : CassPhase) : p.μ p.cb < p.qs := by
  rw [p.qs_eq]
  exact p.μ_anti p.surplus_pos (p.surplus_pos.trans p.surplus_lt_cb) p.surplus_lt_cb

theorem stock_steady (p : CassPhase) : p.stock p.ks = p.ks :=
  clip_eq ⟨p.kl_lt.le, p.ku_gt.le⟩

theorem price_steady (p : CassPhase) : p.price p.qs = p.qs :=
  clip_eq ⟨p.qs_pos.le, p.qs_lt.le⟩

theorem price_lt_steady (p : CassPhase) {q : ℝ} (hq : q < p.qs) : p.price q < p.qs :=
  max_lt p.qs_pos ((min_le_right _ _).trans_lt hq)

theorem price_gt_steady (p : CassPhase) {q : ℝ} (hq : p.qs < q) : p.qs < p.price q :=
  (lt_min p.qs_lt hq).trans_le (le_max_right _ _)

theorem inverse_price (p : CassPhase) (q : ℝ) :
    p.μ (p.C (p.price q)) = max (p.μ p.cb) (p.price q) := by
  rw [p.inverse, clip, ← p.Q_eq, min_eq_right (p.price_mem q).2]

theorem demand_at_steady (p : CassPhase) : p.C p.qs = p.surplus := by
  apply p.μ_anti.injOn (p.ca_pos.trans_le (p.C_mem _).1) p.surplus_pos
  have h := p.inverse_price p.qs
  rw [p.price_steady, max_eq_right p.bottom_price_lt.le] at h
  exact h.trans p.qs_eq

theorem demand_gt_surplus (p : CassPhase) {q : ℝ} (hq : q < p.qs) :
    p.surplus < p.C (p.price q) := by
  have hμ : p.μ (p.C (p.price q)) < p.qs := by
    rw [p.inverse_price]
    exact max_lt p.bottom_price_lt (p.price_lt_steady hq)
  by_contra hn
  have h := p.μ_anti.antitoneOn (p.demand_pos q) p.surplus_pos (le_of_not_gt hn)
  rw [surplus, ← p.qs_eq] at h
  linarith

theorem demand_lt_surplus (p : CassPhase) {q : ℝ} (hq : p.qs < q) :
    p.C (p.price q) < p.surplus := by
  have hμ : p.qs < p.μ (p.C (p.price q)) := by
    rw [p.inverse_price]
    exact (p.price_gt_steady hq).trans_le (le_max_right _ _)
  by_contra hn
  have h := p.μ_anti.antitoneOn p.surplus_pos (p.demand_pos q) (le_of_not_gt hn)
  rw [surplus, ← p.qs_eq] at h
  linarith

theorem field_steady (p : CassPhase) : p.field p.steady = 0 := by
  have hcons : cassConsumption p.f p.C (p.point p.steady) = p.surplus := by
    change min (p.C (p.price p.qs)) (p.f (p.stock p.ks)) = _
    rw [p.price_steady, p.stock_steady, p.demand_at_steady, min_eq_left p.surplus_lt_output.le]
  have hmu : p.μ (p.f p.ks) < p.qs := by
    rw [p.qs_eq]
    exact p.μ_anti p.surplus_pos (p.surplus_pos.trans p.surplus_lt_output) p.surplus_lt_output
  apply Prod.ext
  · change p.f (p.stock p.ks) - cassConsumption p.f p.C (p.point p.steady) -
      p.m * p.stock p.ks = 0
    rw [hcons, p.stock_steady]
    dsimp [surplus]
    ring
  · change (p.d + p.m) * p.price p.qs -
      max (p.price p.qs) (p.μ (p.f (p.stock p.ks))) * p.mp (p.stock p.ks) = 0
    rw [p.price_steady, p.stock_steady, p.mp_star, max_eq_left hmu.le]
    ring

theorem field_first_axis (p : CassPhase) (x : ℝ × ℝ) (hk : x.1 = p.ks) :
    (x.2 < p.qs → (p.field x).1 < 0) ∧ (p.qs < x.2 → 0 < (p.field x).1) := by
  have hs : p.stock x.1 = p.ks := hk ▸ p.stock_steady
  constructor
  · intro hq
    have hmin := lt_min (p.demand_gt_surplus hq) p.surplus_lt_output
    change p.f (p.stock x.1) - min (p.C (p.price x.2)) (p.f (p.stock x.1)) -
      p.m * p.stock x.1 < 0
    rw [hs]
    dsimp [surplus] at hmin
    linarith
  · intro hq
    have hlt := p.demand_lt_surplus hq
    change 0 < p.f (p.stock x.1) - min (p.C (p.price x.2)) (p.f (p.stock x.1)) -
      p.m * p.stock x.1
    rw [hs, min_eq_left (hlt.trans p.surplus_lt_output).le]
    dsimp [surplus] at hlt
    linarith

/-- The clipped field has exactly one equilibrium, even outside its clipping
rectangle. Hence a limiting trajectory cannot converge to an artificial root. -/
theorem field_zero_unique (p : CassPhase) {x : ℝ × ℝ} (hv : p.field x = 0) :
    x = p.steady := by
  have h1 := congrArg Prod.fst hv
  have h2 := congrArg Prod.snd hv
  change cassInvestment p.f p.C (p.point x) - p.m * p.stock x.1 = 0 at h1
  change (p.field x).2 = 0 at h2
  have hz : 0 < cassInvestment p.f p.C (p.point x) := by
    have hm := mul_pos p.m_pos (p.stock_pos x.1)
    linarith
  rw [p.interior_field_price hz] at h2
  have hmp : p.mp (p.stock x.1) = p.d + p.m := by
    have hh := (mul_eq_zero.mp h2).resolve_right (ne_of_gt (p.interior_price hz).2)
    linarith
  have hstock : p.stock x.1 = p.ks := p.mp_anti.injOn (p.stock_mem _)
    ⟨p.kl_lt.le, p.ku_gt.le⟩ (hmp.trans p.mp_star.symm)
  have hk : x.1 = p.ks := by
    rcases lt_trichotomy x.1 p.ks with h | h | h
    · exact False.elim (lt_irrefl _ (hstock ▸ p.stock_lt_star h))
    · exact h
    · exact False.elim (lt_irrefl _ (hstock ▸ p.stock_gt_star h))
  have hc : cassConsumption p.f p.C (p.point x) = p.surplus := by
    change p.f (p.stock x.1) - cassConsumption p.f p.C (p.point x) -
      p.m * p.stock x.1 = 0 at h1
    rw [hstock] at h1
    dsimp [surplus]
    linarith
  have hp : p.price x.2 = p.qs := by
    have hh := (p.interior_price hz).1
    rw [hc, surplus, ← p.qs_eq] at hh
    exact hh.symm
  have hq : x.2 = p.qs := by
    rcases lt_trichotomy x.2 p.qs with h | h | h
    · exact False.elim (lt_irrefl _ (hp ▸ p.price_lt_steady h))
    · exact h
    · exact False.elim (lt_irrefl _ (hp ▸ p.price_gt_steady h))
  exact Prod.ext hk hq

end RamseyCassKoopmans.CassPhase


/-! # Finite shooting endpoints from ordinary velocity bounds

The price starts sufficiently far outside the clipped price interval that it
cannot return to that interval before capital crosses the equilibrium stock.
The bounds and crossing times are explicit; endpoint escape is proved.
-/

open Set
open scoped NNReal

namespace RamseyCassKoopmans.ODE

theorem coordinate_bounds {v : ℝ × ℝ → ℝ × ℝ} {B : ℝ≥0}
    (hb : ∀ x, ‖v x‖ ≤ B) (x : ℝ × ℝ) :
    -(B : ℝ) ≤ (v x).2 ∧ (v x).2 ≤ B := by
  have h : ‖(v x).2‖ ≤ B := (le_max_right ‖(v x).1‖ ‖(v x).2‖).trans (hb x)
  exact abs_le.mp h

theorem exists_low_endpoint {v : ℝ × ℝ → ℝ × ℝ} {B : ℝ≥0}
    (hbound : ∀ x, ‖v x‖ ≤ B) {a : ℝ × ℝ} (ha : 0 < a.2)
    {ε : ℝ} (hε : 0 < ε)
    (hdown : ∀ x : ℝ × ℝ, x.2 ≤ 0 → (v x).1 ≤ -ε) (k0 : ℝ) :
    ∃ l : ℝ, l < 0 ∧ ∀ γ : ℝ → ℝ × ℝ, γ 0 = (k0, l) →
      (∀ t, HasDerivAt γ (v (γ t)) t) → ∃ t, 0 ≤ t ∧ γ t ∈ lowerQuadrant a := by
  let T := (max 0 (k0 - a.1) + 1) / ε
  have hT : 0 < T := div_pos (by linarith [le_max_left (0 : ℝ) (k0 - a.1)]) hε
  have htime : k0 - a.1 < ε * T := by
    have heq : ε * T = max 0 (k0 - a.1) + 1 := by dsimp [T]; field_simp
    rw [heq]
    linarith [le_max_right (0 : ℝ) (k0 - a.1)]
  let l := -(B : ℝ) * T - 1
  have hl : l < 0 := by dsimp [l]; nlinarith [B.coe_nonneg]
  refine ⟨l, hl, ?_⟩
  intro γ h0 hd
  have hq : ∀ t ∈ Icc 0 T, (γ t).2 < 0 := by
    intro t ht
    have h := linear_upper_bound (fun u => hasDerivAt_snd (hd u)) ht.1
      (fun u _ => (coordinate_bounds hbound (γ u)).2)
    rw [h0] at h
    change (γ t).2 - l ≤ (B : ℝ) * (t - 0) at h
    dsimp [l] at h
    nlinarith [mul_le_mul_of_nonneg_left ht.2 B.coe_nonneg]
  have hk := linear_upper_bound_on (fun u => hasDerivAt_fst (hd u)) hT.le
    (fun t ht => hdown (γ t) (hq t ht).le)
  rw [h0] at hk
  change (γ T).1 - k0 ≤ -ε * (T - 0) at hk
  refine ⟨T, hT.le, ?_⟩
  constructor
  · linarith
  · exact (hq T ⟨hT.le, le_rfl⟩).trans ha

theorem exists_high_endpoint {v : ℝ × ℝ → ℝ × ℝ} {B : ℝ≥0}
    (hbound : ∀ x, ‖v x‖ ≤ B) {a : ℝ × ℝ} {Q ε : ℝ}
    (hQ : a.2 < Q) (hε : 0 < ε)
    (hup : ∀ x : ℝ × ℝ, x.1 ≤ a.1 → Q ≤ x.2 → ε ≤ (v x).1) (k0 : ℝ) :
    ∃ r : ℝ, Q < r ∧ ∀ γ : ℝ → ℝ × ℝ, γ 0 = (k0, r) →
      (∀ t, HasDerivAt γ (v (γ t)) t) → ∃ t, 0 ≤ t ∧ γ t ∈ upperQuadrant a := by
  let T := (max 0 (a.1 - k0) + 1) / ε
  have hT : 0 < T := div_pos (by linarith [le_max_left (0 : ℝ) (a.1 - k0)]) hε
  have htime : a.1 - k0 < ε * T := by
    have heq : ε * T = max 0 (a.1 - k0) + 1 := by dsimp [T]; field_simp
    rw [heq]
    linarith [le_max_right (0 : ℝ) (a.1 - k0)]
  let r := Q + (B : ℝ) * T + 1
  have hr : Q < r := by dsimp [r]; nlinarith [B.coe_nonneg]
  refine ⟨r, hr, ?_⟩
  intro γ h0 hd
  by_contra hn
  push Not at hn
  have hq : ∀ t ∈ Icc 0 T, Q < (γ t).2 := by
    intro t ht
    have h := linear_lower_bound (fun u => hasDerivAt_snd (hd u)) ht.1
      (fun u _ => (coordinate_bounds hbound (γ u)).1)
    rw [h0] at h
    change -(B : ℝ) * (t - 0) ≤ (γ t).2 - r at h
    dsimp [r] at h
    nlinarith [mul_le_mul_of_nonneg_left ht.2 B.coe_nonneg]
  have hk : ∀ t ∈ Icc 0 T, (γ t).1 ≤ a.1 := by
    intro t ht
    by_contra hnk
    exact hn t ht.1 ⟨lt_of_not_ge hnk, hQ.trans (hq t ht)⟩
  have h := linear_lower_bound_on (fun u => hasDerivAt_fst (hd u)) hT.le
    (fun t ht => hup (γ t) (hk t ht) (hq t ht).le)
  rw [h0] at h
  change ε * (T - 0) ≤ (γ T).1 - k0 at h
  have hkT := hk T ⟨hT.le, le_rfl⟩
  linarith

end RamseyCassKoopmans.ODE


/-! # Constructed convergent solutions of the clipped Cass system

Shooting endpoints are derived from bounded velocity and the two extreme-price
capital drifts. Monotonicity, confinement of capital between its initial and
steady stocks, and convergence follow from the constructed solution. Removing
the price clip additionally requires the quantitative price bound.
-/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.CassPhase

theorem demand_at_zero (p : CassPhase) : p.C 0 = p.cb := by
  apply p.μ_anti.injOn (p.ca_pos.trans_le (p.C_mem _).1) (p.ca_pos.trans_le p.ca_le_cb)
  rw [p.inverse, clip, min_eq_right (p.μ_pos p.ca p.ca_pos).le,
    max_eq_left (p.μ_pos p.cb (p.ca_pos.trans_le p.ca_le_cb)).le]

theorem demand_at_top (p : CassPhase) : p.C p.Q = p.ca := by
  apply p.μ_anti.injOn (p.ca_pos.trans_le (p.C_mem _).1) p.ca_pos
  rw [p.inverse, p.Q_eq]
  exact clip_eq ⟨p.μ_anti.antitoneOn p.ca_pos (p.ca_pos.trans_le p.ca_le_cb) p.ca_le_cb, le_rfl⟩

theorem low_capital_drift (p : CassPhase) (x : ℝ × ℝ) (hq : x.2 ≤ 0) :
    (p.field x).1 ≤ -(p.m * p.kl) := by
  have hp : p.price x.2 = 0 := by
    dsimp [price, clip]
    rw [min_eq_right (hq.trans (p.qs_pos.trans p.qs_lt).le), max_eq_left hq]
  change p.f (p.stock x.1) - min (p.C (p.price x.2)) (p.f (p.stock x.1)) -
    p.m * p.stock x.1 ≤ _
  rw [hp, p.demand_at_zero, min_eq_right (p.f_mem _ (p.stock_mem _)).2, sub_self, zero_sub]
  exact neg_le_neg (mul_le_mul_of_nonneg_left (p.stock_mem _).1 p.m_pos.le)

theorem high_capital_drift (p : CassPhase)
    (hnet : MonotoneOn (fun k => p.f k - p.m * k) (Icc p.kl p.ks))
    (x : ℝ × ℝ) (hk : x.1 ≤ p.ks) (hq : p.Q ≤ x.2) :
    p.f p.kl - p.m * p.kl - p.ca ≤ (p.field x).1 := by
  have hp : p.price x.2 = p.Q := by
    dsimp [price, clip]
    rw [min_eq_left hq, max_eq_right (p.qs_pos.trans p.qs_lt).le]
  have hstock : p.stock x.1 ≤ p.ks :=
    max_le p.kl_lt.le ((min_le_right _ _).trans hk)
  have hn := hnet ⟨le_rfl, p.kl_lt.le⟩ ⟨(p.stock_mem _).1, hstock⟩ (p.stock_mem _).1
  change _ ≤ p.f (p.stock x.1) - min (p.C (p.price x.2)) (p.f (p.stock x.1)) -
    p.m * p.stock x.1
  rw [hp, p.demand_at_top, min_eq_left (p.f_mem _ (p.stock_mem _)).1]
  linarith

theorem exists_avoiding_solution (p : CassPhase) (hb : BoundedLip p.field)
    (hnet : MonotoneOn (fun k => p.f k - p.m * k) (Icc p.kl p.ks))
    (hfloor : p.ca < p.f p.kl - p.m * p.kl) (k0 : ℝ) :
    ∃ γ : ℝ → ℝ × ℝ, (γ 0).1 = k0 ∧
      (∀ t, HasDerivAt γ (p.field (γ t)) t) ∧ ODE.Avoids γ p.steady := by
  obtain ⟨K, B, hlip, hbound⟩ := hb
  obtain ⟨l, hl, hleft⟩ := ODE.exists_low_endpoint hbound (a := p.steady) p.qs_pos
    (mul_pos p.m_pos p.kl_pos) p.low_capital_drift k0
  obtain ⟨r, hr, hright⟩ := ODE.exists_high_endpoint hbound (a := p.steady) p.qs_lt
    (sub_pos.mpr hfloor) (p.high_capital_drift hnet) k0
  obtain ⟨q, _, γ, h0, hd, hav⟩ := ODE.exists_solution_avoiding_quadrants
    p.cooperative hlip hbound p.field_steady (fun q => (k0, q))
    (continuous_const.prodMk continuous_id)
    (show l ≤ r from (hl.trans (p.qs_pos.trans (p.qs_lt.trans hr))).le) hleft hright
  exact ⟨γ, congrArg Prod.fst h0, hd, hav⟩

theorem lower_avoiding_converges (p : CassPhase) {K : ℝ≥0}
    (hlip : LipschitzWith K p.field) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hav : ODE.Avoids γ p.steady) (h0 : (γ 0).1 < p.ks) :
    Tendsto γ atTop (𝓝 p.steady) ∧
      StrictMonoOn (fun t => (γ t).1) (Ici 0) ∧
      StrictAntiOn (fun t => (γ t).2) (Ici 0) ∧
      ∀ t, 0 ≤ t → (γ t).1 < p.ks ∧ p.qs ≤ (γ t).2 := by
  have hne : γ 0 ≠ p.steady := by
    intro heq
    have hh := congrArg Prod.fst heq
    change (γ 0).1 = p.ks at hh
    linarith
  have hγcont : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hk := ODE.first_stays_below (a := p.steady) hγcont h0
    (ODE.avoids_first_ne hlip p.field_steady p.field_first_axis hd hne hav)
  have hq : ∀ t, 0 ≤ t → p.qs ≤ (γ t).2 := by
    intro t ht
    by_contra hn
    exact hav t ht (Or.inl ⟨hk t ht, lt_of_not_ge hn⟩)
  have hv := ODE.lower_branch_velocity p.cooperative hlip (a := p.steady)
    (fun x hx hqx => p.lower_price_negative hx hqx)
    (fun b hb _ => by
      obtain ⟨ε, hε, he⟩ := p.lower_price_drift hb
      exact ⟨ε, hε, fun x hx hqx _ => he x hx hqx⟩) hd hk hav
  obtain ⟨hm, ha⟩ := ODE.lower_branch_monotone hd hv
  obtain ⟨b, hb, hzero, _, _⟩ := ODE.lower_branch_limit hlip.continuous hd
    (fun t ht => (hk t ht).le) hq hm.monotoneOn ha.antitoneOn
  rw [p.field_zero_unique hzero] at hb
  exact ⟨hb, hm, ha, fun t ht => ⟨hk t ht, hq t ht⟩⟩

theorem upper_avoiding_converges (p : CassPhase) {K : ℝ≥0}
    (hlip : LipschitzWith K p.field) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hav : ODE.Avoids γ p.steady) (h0 : p.ks < (γ 0).1) :
    Tendsto γ atTop (𝓝 p.steady) ∧
      StrictAntiOn (fun t => (γ t).1) (Ici 0) ∧
      StrictMonoOn (fun t => (γ t).2) (Ici 0) ∧
      ∀ t, 0 ≤ t → p.ks < (γ t).1 ∧ (γ t).2 ≤ p.qs := by
  have hne : γ 0 ≠ p.steady := by
    intro heq
    have hh := congrArg Prod.fst heq
    change (γ 0).1 = p.ks at hh
    linarith
  have hγcont : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hk := ODE.first_stays_above (a := p.steady) hγcont h0
    (ODE.avoids_first_ne hlip p.field_steady p.field_first_axis hd hne hav)
  have hq : ∀ t, 0 ≤ t → (γ t).2 ≤ p.qs := by
    intro t ht
    by_contra hn
    exact hav t ht (Or.inr ⟨hk t ht, lt_of_not_ge hn⟩)
  have hv := ODE.upper_branch_velocity p.cooperative hlip (a := p.steady)
    (fun b hb _ hv => p.upper_cross hb hv)
    (fun b hb _ hv => by
      obtain ⟨ε, hε, he⟩ := p.upper_price_drift hb hv
      exact ⟨ε, hε, fun x hx hqx _ => he x hx hqx⟩)
    (fun b hb _ hv => p.upper_corner_drift hb hv) hd hk hav
  obtain ⟨ha, hm⟩ := ODE.upper_branch_monotone hd hv
  obtain ⟨b, hb, hzero, _, _⟩ := ODE.upper_branch_limit hlip.continuous hd
    (fun t ht => (hk t ht).le) hq ha.antitoneOn hm.monotoneOn
  rw [p.field_zero_unique hzero] at hb
  exact ⟨hb, ha, hm, fun t ht => ⟨hk t ht, hq t ht⟩⟩

end RamseyCassKoopmans.CassPhase


/-! # Removing the auxiliary clipping bounds

For the upper branch, the signs exclude nonpositive prices directly. For the
lower branch, an explicit exponential price bound and a finite capital drift
exclude prices as large as the upper clip. Capital confinement follows from
the proved monotonicity on both branches.
-/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.CassPhase

theorem nonpositive_price_velocity (p : CassPhase) {x : ℝ × ℝ} (hq : x.2 ≤ 0) :
    (p.field x).2 < 0 := by
  have hp : p.price x.2 = 0 := by
    dsimp [price, clip]
    rw [min_eq_right (hq.trans (p.qs_pos.trans p.qs_lt).le), max_eq_left hq]
  change (p.d + p.m) * p.price x.2 -
    max (p.price x.2) (p.μ (p.f (p.stock x.1))) * p.mp (p.stock x.1) < 0
  rw [hp, mul_zero, max_eq_right (p.μ_pos _ (p.output_pos _)).le, zero_sub]
  exact neg_neg_of_pos (mul_pos (p.μ_pos _ (p.output_pos _)) (p.mp_pos _ (p.stock_mem _)))

theorem upper_clips_inactive (p : CassPhase) {K : ℝ≥0}
    (hlip : LipschitzWith K p.field) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hav : ODE.Avoids γ p.steady) (h0 : p.ks < (γ 0).1)
    (hku : (γ 0).1 ≤ p.ku) :
    ∀ t, 0 ≤ t → p.point (γ t) = γ t ∧ 0 < (γ t).2 := by
  obtain ⟨_, ha, _, hside⟩ := p.upper_avoiding_converges hlip hd hav h0
  have hv := ODE.upper_branch_velocity p.cooperative hlip (a := p.steady)
    (fun b hb _ hv => p.upper_cross hb hv)
    (fun b hb _ hv => by
      obtain ⟨ε, hε, he⟩ := p.upper_price_drift hb hv
      exact ⟨ε, hε, fun x hx hqx _ => he x hx hqx⟩)
    (fun b hb _ hv => p.upper_corner_drift hb hv) hd
    (fun t ht => (hside t ht).1) hav
  intro t ht
  have hq : 0 < (γ t).2 := by
    by_contra hn
    have hneg := p.nonpositive_price_velocity (le_of_not_gt hn)
    linarith [(hv t ht).2]
  refine ⟨Prod.ext ?_ ?_, hq⟩
  · exact clip_eq ⟨(p.kl_lt.trans (hside t ht).1).le,
      (ha.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht).trans hku⟩
  · exact clip_eq ⟨hq.le, (hside t ht).2.trans p.qs_lt.le⟩

theorem lower_exponential_price (p : CassPhase) {K : ℝ≥0}
    (hlip : LipschitzWith K p.field) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hav : ODE.Avoids γ p.steady) (h0 : (γ 0).1 < p.ks) :
    ∀ t, 0 ≤ t → (γ 0).2 * Real.exp (-p.mp p.kl * t) ≤ (γ t).2 := by
  obtain ⟨_, _, _, hside⟩ := p.lower_avoiding_converges hlip hd hav h0
  have hv := ODE.lower_branch_velocity p.cooperative hlip (a := p.steady)
    (fun x hx hqx => p.lower_price_negative hx hqx)
    (fun b hb _ => by
      obtain ⟨ε, hε, he⟩ := p.lower_price_drift hb
      exact ⟨ε, hε, fun x hx hqx _ => he x hx hqx⟩) hd
    (fun t ht => (hside t ht).1) hav
  apply ODE.exponential_lower_bound (fun t => ODE.hasDerivAt_snd (hd t))
  intro t ht
  have hz : 0 < cassInvestment p.f p.C (p.point (γ t)) := by
    have hh := (hv t ht).1
    change 0 < cassInvestment p.f p.C (p.point (γ t)) - p.m * p.stock (γ t).1 at hh
    linarith [mul_pos p.m_pos (p.stock_pos (γ t).1)]
  rw [p.interior_field_price hz]
  have hmp : p.mp (p.stock (γ t).1) ≤ p.mp p.kl :=
    p.mp_anti.antitoneOn ⟨le_rfl, (p.kl_lt.trans p.ku_gt).le⟩
      (p.stock_mem _) (p.stock_mem _).1
  have hqpos := p.qs_pos.trans_le (hside t ht).2
  have hpq : p.price (γ t).2 ≤ (γ t).2 := max_le hqpos.le (min_le_right _ _)
  have hprod := mul_le_mul hmp hpq (p.price_mem _).1
    (p.mp_pos _ ⟨le_rfl, (p.kl_lt.trans p.ku_gt).le⟩).le
  have hrate := mul_nonneg (add_pos p.d_pos p.m_pos).le (p.price_mem (γ t).2).1
  nlinarith

/-- A finite, checkable price threshold suffices to remove the upper price
clip. `hpush` is an inequality for points, not a trajectory hypothesis. -/
theorem lower_initial_price_lt_top (p : CassPhase) {K : ℝ≥0}
    (hlip : LipschitzWith K p.field) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hav : ODE.Avoids γ p.steady) (h0 : (γ 0).1 < p.ks)
    {H ε T : ℝ} (hT : 0 ≤ T)
    (hlarge : H * Real.exp (p.mp p.kl * T) ≤ p.Q)
    (htime : p.ks - (γ 0).1 ≤ ε * T)
    (hpush : ∀ x : ℝ × ℝ, (γ 0).1 ≤ x.1 → x.1 ≤ p.ks → H ≤ x.2 → ε ≤ (p.field x).1) :
    (γ 0).2 < p.Q := by
  by_contra hn
  have hQ0 : p.Q ≤ (γ 0).2 := le_of_not_gt hn
  obtain ⟨_, hm, _, hside⟩ := p.lower_avoiding_converges hlip hd hav h0
  have hq0 : 0 < (γ 0).2 := p.qs_pos.trans_le (hside 0 le_rfl).2
  have hq : ∀ t ∈ Icc 0 T, H ≤ (γ t).2 := by
    intro t ht
    have hmp := p.mp_pos p.kl ⟨le_rfl, (p.kl_lt.trans p.ku_gt).le⟩
    have hexp : Real.exp (-p.mp p.kl * T) ≤ Real.exp (-p.mp p.kl * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.2 (neg_nonpos.mpr hmp.le))
    have hmul := mul_le_mul_of_nonneg_right (hlarge.trans hQ0) (Real.exp_pos (-p.mp p.kl * T)).le
    have hid : (H * Real.exp (p.mp p.kl * T)) * Real.exp (-p.mp p.kl * T) = H := by
      rw [mul_assoc, ← Real.exp_add]
      have he : p.mp p.kl * T + -p.mp p.kl * T = 0 := by ring
      rw [he, Real.exp_zero, mul_one]
    rw [hid] at hmul
    exact (hmul.trans (mul_le_mul_of_nonneg_left hexp hq0.le)).trans
      (p.lower_exponential_price hlip hd hav h0 t ht.1)
  have hk := ODE.linear_lower_bound_on (fun t => ODE.hasDerivAt_fst (hd t)) hT
    (fun t ht => hpush (γ t)
      (hm.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht.1) ht.1)
      (hside t ht.1).1.le (hq t ht))
  have hlast := (hside T hT).1
  linarith

theorem lower_clips_inactive (p : CassPhase) {K : ℝ≥0}
    (hlip : LipschitzWith K p.field) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hav : ODE.Avoids γ p.steady) (h0 : (γ 0).1 < p.ks)
    (hkl : p.kl ≤ (γ 0).1) (hq0 : (γ 0).2 ≤ p.Q) :
    ∀ t, 0 ≤ t → p.point (γ t) = γ t ∧ 0 < (γ t).2 := by
  obtain ⟨_, hm, ha, hside⟩ := p.lower_avoiding_converges hlip hd hav h0
  intro t ht
  have hq := p.qs_pos.trans_le (hside t ht).2
  refine ⟨Prod.ext ?_ ?_, hq⟩
  · exact clip_eq ⟨hkl.trans (hm.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht),
      ((hside t ht).1.trans p.ku_gt).le⟩
  · exact clip_eq ⟨hq.le, (ha.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht).trans hq0⟩

end RamseyCassKoopmans.CassPhase


/-! # A constructed trajectory for finite, explicitly checkable economic data

The quantitative price bound removes the price clip; monotonicity removes the
capital clip. The resulting global future trajectory satisfies the original
Cass field. Neither a trajectory nor its convergence is an input.
-/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.CassPhase

theorem demand_inverse (p : CassPhase) {c : ℝ} (hc : c ∈ Icc p.ca p.cb) :
    p.C (p.μ c) = c := by
  have hcpos := p.ca_pos.trans_le hc.1
  apply p.μ_anti.injOn (p.ca_pos.trans_le (p.C_mem _).1) hcpos
  rw [p.inverse]
  exact clip_eq ⟨p.μ_anti.antitoneOn hcpos (hcpos.trans_le hc.2) hc.2,
    p.μ_anti.antitoneOn p.ca_pos hcpos hc.1⟩

theorem finite_price_capital_drift (p : CassPhase)
    (hnet : MonotoneOn (fun k => p.f k - p.m * k) (Icc p.kl p.ks))
    {c : ℝ} (hc : c ∈ Icc p.ca p.cb)
    (x : ℝ × ℝ) (hk : x.1 ≤ p.ks) (hq : p.μ c ≤ x.2) :
    p.f p.kl - p.m * p.kl - c ≤ (p.field x).1 := by
  have hcprice : p.μ c ≤ p.Q := by
    rw [p.Q_eq]
    exact p.μ_anti.antitoneOn p.ca_pos (p.ca_pos.trans_le hc.1) hc.1
  have hprice : p.μ c ≤ p.price x.2 :=
    (le_min hcprice hq).trans (le_max_right _ _)
  have hC : p.C (p.price x.2) ≤ c := by
    simpa only [p.demand_inverse hc] using p.C_anti hprice
  have hstock : p.stock x.1 ≤ p.ks := max_le p.kl_lt.le ((min_le_right _ _).trans hk)
  have hn := hnet ⟨le_rfl, p.kl_lt.le⟩ ⟨(p.stock_mem _).1, hstock⟩ (p.stock_mem _).1
  have hcons := (min_le_left (p.C (p.price x.2)) (p.f (p.stock x.1))).trans hC
  change _ ≤ p.f (p.stock x.1) - min (p.C (p.price x.2)) (p.f (p.stock x.1)) -
    p.m * p.stock x.1
  linarith

/-- The original, unclipped capital and shadow-price trajectory is constructed
for any initial stock in the stated box. All extra conditions are finite scalar
inequalities or regularity of ordinary functions. -/
theorem exists_convergent_trajectory (p : CassPhase) (hb : BoundedLip p.field)
    (hnet : MonotoneOn (fun k => p.f k - p.m * k) (Icc p.kl p.ks))
    {c T k0 : ℝ} (hc : c ∈ Icc p.ca p.cb)
    (hgap : c < p.f p.kl - p.m * p.kl) (hT : 0 ≤ T)
    (hlarge : p.μ c * Real.exp (p.mp p.kl * T) ≤ p.Q)
    (htime : p.ks - k0 ≤ (p.f p.kl - p.m * p.kl - c) * T)
    (hk0 : k0 ∈ Icc p.kl p.ku) :
    ∃ γ : ℝ → ℝ × ℝ, (γ 0).1 = k0 ∧
      (∀ t, HasDerivAt γ (p.field (γ t)) t) ∧
      (∀ t, 0 ≤ t → p.point (γ t) = γ t ∧ 0 < (γ t).2) ∧
      Tendsto γ atTop (𝓝 p.steady) ∧
      (k0 < p.ks → StrictMonoOn (fun t => (γ t).1) (Ici 0) ∧
        StrictAntiOn (fun t => (γ t).2) (Ici 0)) ∧
      (p.ks < k0 → StrictAntiOn (fun t => (γ t).1) (Ici 0) ∧
        StrictMonoOn (fun t => (γ t).2) (Ici 0)) ∧
      (k0 = p.ks → ∀ t, γ t = p.steady) := by
  obtain ⟨K, B, hlip, hbound⟩ := hb
  rcases lt_trichotomy k0 p.ks with hbelow | heq | habove
  · obtain ⟨γ, h0, hd, hav⟩ :=
      p.exists_avoiding_solution ⟨K, B, hlip, hbound⟩ hnet (hc.1.trans_lt hgap) k0
    have hk : (γ 0).1 < p.ks := h0 ▸ hbelow
    obtain ⟨hlim, hm, ha, _⟩ := p.lower_avoiding_converges hlip hd hav hk
    have hq0 : (γ 0).2 < p.Q := p.lower_initial_price_lt_top hlip hd hav hk hT hlarge
      (h0 ▸ htime) (fun x _ hx hq => p.finite_price_capital_drift hnet hc x hx hq)
    exact ⟨γ, h0, hd, p.lower_clips_inactive hlip hd hav hk (h0 ▸ hk0.1) hq0.le,
      hlim, (fun _ => ⟨hm, ha⟩), (fun h => False.elim (lt_asymm hbelow h)),
      fun h => False.elim (lt_irrefl _ (h ▸ hbelow))⟩
  · refine ⟨fun _ => p.steady, heq.symm, ?_, ?_, tendsto_const_nhds, ?_, ?_, fun _ _ => rfl⟩
    · intro t
      simpa only [p.field_steady] using hasDerivAt_const t p.steady
    · intro t _
      exact ⟨Prod.ext p.stock_steady p.price_steady, p.qs_pos⟩
    · intro h
      exact False.elim (lt_irrefl _ (heq ▸ h))
    · intro h
      exact False.elim (lt_irrefl _ (heq ▸ h))
  · obtain ⟨γ, h0, hd, hav⟩ :=
      p.exists_avoiding_solution ⟨K, B, hlip, hbound⟩ hnet (hc.1.trans_lt hgap) k0
    have hk : p.ks < (γ 0).1 := h0 ▸ habove
    obtain ⟨hlim, ha, hm, _⟩ := p.upper_avoiding_converges hlip hd hav hk
    exact ⟨γ, h0, hd, p.upper_clips_inactive hlip hd hav hk (h0 ▸ hk0.2),
      hlim, (fun h => False.elim (lt_asymm habove h)), (fun _ => ⟨ha, hm⟩),
      fun h => False.elim (lt_irrefl _ (h ▸ habove))⟩

end RamseyCassKoopmans.CassPhase


/-! # Choosing the finite data from the Inada condition on marginal utility

The consumption floor and upper price are selected after the finite travel-time
bound is computed. The Inada limit supplies a large enough upper price, so the
quantitative condition used to remove clipping is derived here.
-/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans

structure CassConstructionData (f mp μ : ℝ → ℝ) (d m k0 ks : ℝ) where
  phase : CassPhase
  production_eq : phase.f = f
  marginalProduct_eq : phase.mp = mp
  marginalUtility_eq : phase.μ = μ
  discount_eq : phase.d = d
  dilution_eq : phase.m = m
  steady_eq : phase.ks = ks
  bounded : BoundedLip phase.field
  demand_bounded : BoundedLip phase.C
  production_bounded : BoundedLip (phase.f ∘ clip phase.kl phase.ku)
  net_mono : MonotoneOn (fun k => phase.f k - phase.m * k) (Icc phase.kl phase.ks)
  c : ℝ
  T : ℝ
  consumption_mem : c ∈ Icc phase.ca phase.cb
  net_gap : c < phase.f phase.kl - phase.m * phase.kl
  time_nonneg : 0 ≤ T
  price_large : phase.μ c * Real.exp (phase.mp phase.kl * T) ≤ phase.Q
  time_large : phase.ks - k0 ≤ (phase.f phase.kl - phase.m * phase.kl - c) * T
  initial_mem : k0 ∈ Icc phase.kl phase.ku

/-- No compact inverse, price bound or nonstationary path is assumed. All are
constructed from functions, their ordinary derivatives, and an Inada limit. -/
theorem exists_cass_finite_data (f mp μ : ℝ → ℝ) (d m kl ku ks k0 : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hkl : 0 < kl) (hlstar : kl < ks) (hstaru : ks < ku)
    (hk0 : k0 ∈ Icc kl ku)
    (hfderiv : ∀ k ∈ Icc kl ku, HasDerivAt f (mp k) k)
    (hmpcont : ContinuousOn mp (Icc kl ku))
    (hmpdiff : ∀ k ∈ Icc kl ku, DifferentiableAt ℝ mp k)
    (hmpprime : ContinuousOn (deriv mp) (Icc kl ku))
    (hfmono : MonotoneOn f (Icc kl ku))
    (hmpanti : StrictAntiOn mp (Icc kl ku))
    (hmppos : ∀ k ∈ Icc kl ku, 0 < mp k) (hmpstar : mp ks = d + m)
    (hnet : MonotoneOn (fun k => f k - m * k) (Icc kl ks))
    (hnetpos : 0 < f kl - m * kl)
    (hμpos : ∀ c, 0 < c → 0 < μ c) (hμanti : StrictAntiOn μ (Ioi 0))
    (hμdiff : ∀ c, 0 < c → DifferentiableAt ℝ μ c)
    (hμprime : ContinuousOn (deriv μ) (Ioi 0))
    (hμneg : ∀ c, 0 < c → deriv μ c < 0)
    (hμInada : Tendsto μ (𝓝[>] (0 : ℝ)) atTop) :
    Nonempty (CassConstructionData f mp μ d m k0 ks) := by
  let c := (f kl - m * kl) / 2
  have hcpos : 0 < c := half_pos hnetpos
  have hcnet : c < f kl - m * kl := by dsimp [c]; linarith
  have hkspos := hkl.trans hlstar
  have hnetstar : f kl - m * kl ≤ f ks - m * ks :=
    hnet ⟨le_rfl, hlstar.le⟩ ⟨hlstar.le, le_rfl⟩ hlstar.le
  have hcstar : c < f ks - m * ks := hcnet.trans_le hnetstar
  have hstarpos := hcpos.trans hcstar
  have hnetout : f kl - m * kl < f kl := by nlinarith [mul_pos hm hkl]
  have hflpos := hnetpos.trans hnetout
  have hflu : f kl ≤ f ku :=
    hfmono ⟨le_rfl, (hlstar.trans hstaru).le⟩ ⟨(hlstar.trans hstaru).le, le_rfl⟩
      (hlstar.trans hstaru).le
  let cb := f ku + 1
  have hcbpos : 0 < cb := by dsimp [cb]; linarith
  have hc_cb : c < cb := by dsimp [cb]; linarith
  let T := (ks - kl + 1) / (f kl - m * kl - c)
  have hT : 0 < T := div_pos (by linarith) (sub_pos.mpr hcnet)
  have htime : ks - k0 ≤ (f kl - m * kl - c) * T := by
    have ht : (f kl - m * kl - c) * T = ks - kl + 1 := by
      dsimp [T]
      field_simp [ne_of_gt (sub_pos.mpr hcnet)]
    rw [ht]
    linarith [hk0.1]
  let H := μ c * Real.exp (mp kl * T)
  have hcapos : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  have hcnear : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < c :=
    (gt_mem_nhds hcpos).filter_mono nhdsWithin_le_nhds
  obtain ⟨ca, hca, hca_c, hlarge⟩ :=
    (hcapos.and (hcnear.and (hμInada.eventually_ge_atTop H))).exists
  have hcab : ca ≤ cb := (hca_c.trans hc_cb).le
  have hμinterval : Icc ca cb ⊆ Ioi (0 : ℝ) := fun _ hx => hca.trans_le hx.1
  obtain ⟨KC, C, hCmem, hCanti, hCLip, hCinv⟩ := exists_compact_demand_of_deriv hcab
    (fun x hx => hμdiff x (hμinterval hx)) (hμprime.mono hμinterval)
    (fun x hx => hμneg x (hμinterval hx))
  have hCL : BoundedLip C := ⟨KC, ‖cb‖₊, hCLip, fun q => by
    rw [Real.norm_eq_abs, abs_of_pos (hca.trans_le (hCmem q).1)]
    exact (hCmem q).2.trans (le_abs_self cb)⟩
  have hfmem : ∀ k ∈ Icc kl ku, f k ∈ Icc ca cb := by
    intro k hk
    have hlo := hfmono ⟨le_rfl, (hlstar.trans hstaru).le⟩ hk hk.1
    have hhi := hfmono hk ⟨(hlstar.trans hstaru).le, le_rfl⟩ hk.2
    constructor
    · exact (hca_c.trans (hcnet.trans hnetout)).le.trans hlo
    · dsimp [cb]; linarith
  let p : CassPhase := {
    f := f, mp := mp, μ := μ, C := C, d := d, m := m,
    kl := kl, ku := ku, ks := ks, ca := ca, cb := cb,
    qs := μ (f ks - m * ks), Q := μ ca,
    d_pos := hd, m_pos := hm, kl_pos := hkl, kl_lt := hlstar, ku_gt := hstaru,
    ca_pos := hca, ca_le_cb := hcab, f_mem := hfmem, f_mono := hfmono,
    mp_pos := hmppos, mp_anti := hmpanti, mp_star := hmpstar,
    μ_pos := hμpos, μ_anti := hμanti, C_mem := hCmem, C_anti := hCanti,
    inverse := hCinv, Q_eq := rfl, qs_pos := hμpos _ hstarpos,
    qs_lt := hμanti hca hstarpos (hca_c.trans hcstar),
    ca_lt_surplus := hca_c.trans hcstar, qs_eq := rfl }
  have hfprime : ContinuousOn (deriv f) (Icc kl ku) :=
    hmpcont.congr (fun k hk => (hfderiv k hk).deriv)
  have hFL : BoundedLip (f ∘ clip kl ku) := boundedLip_comp_clip (hlstar.trans hstaru).le
    (fun k hk => (hfderiv k hk).differentiableAt) hfprime
  have hPL : BoundedLip (mp ∘ clip kl ku) :=
    boundedLip_comp_clip (hlstar.trans hstaru).le hmpdiff hmpprime
  have hμL : BoundedLip (μ ∘ clip ca cb) := boundedLip_comp_clip hcab
    (fun x hx => hμdiff x (hμinterval hx)) (hμprime.mono hμinterval)
  have hHL : BoundedLip ((fun k => μ (f k)) ∘ clip kl ku) := by
    obtain ⟨KF, MF, hFLip, hFbound⟩ := hFL
    have hcomp := hμL.comp hFLip
    have heq : (μ ∘ clip ca cb) ∘ (f ∘ clip kl ku) = (fun k => μ (f k)) ∘ clip kl ku := by
      funext x
      simp only [Function.comp_apply, clip_eq (hfmem _ (clip_mem (hlstar.trans hstaru).le x))]
    exact heq ▸ hcomp
  have hpBound : BoundedLip p.field := cass_extension_boundedLip (hlstar.trans hstaru).le
    (hμpos ca hca).le hFL hPL hHL hCL
  exact ⟨{
    phase := p, production_eq := rfl, marginalProduct_eq := rfl,
    marginalUtility_eq := rfl, discount_eq := rfl, dilution_eq := rfl, steady_eq := rfl,
    bounded := hpBound, demand_bounded := hCL, production_bounded := hFL,
    net_mono := hnet, c := c, T := T,
    consumption_mem := ⟨hca_c.le, hc_cb.le⟩, net_gap := hcnet, time_nonneg := hT.le,
    price_large := hlarge, time_large := htime, initial_mem := hk0 }⟩

end RamseyCassKoopmans


/-! # From the primitive growth assumptions to the shooting construction

This file chooses the stationary stock, the capital box, and every finite price
bound from the Inada and curvature assumptions. The only smoothness required is
continuous first and second derivatives on the positive half-line.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

theorem exists_cass_data_of_inada (f U : ℝ → ℝ) (d m k0 : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hk0 : 0 < k0)
    (hfconc : StrictConcaveOn ℝ (Ici 0) f) (hfzero : f 0 = 0)
    (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hfprimepos : ∀ k, 0 < k → 0 < deriv f k)
    (hfsecond : ∀ k, 0 < k → DifferentiableAt ℝ (deriv f) k)
    (hfsecondcont : ContinuousOn (deriv (deriv f)) (Ioi 0))
    (hfInada0 : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop)
    (hfInadaTop : Tendsto (deriv f) atTop (𝓝 (0 : ℝ)))
    (hUconc : StrictConcaveOn ℝ (Ioi 0) U)
    (hUdiff : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hUprimepos : ∀ c, 0 < c → 0 < deriv U c)
    (hUsecond : ∀ c, 0 < c → DifferentiableAt ℝ (deriv U) c)
    (hUsecondcont : ContinuousOn (deriv (deriv U)) (Ioi 0))
    (hUsecondneg : ∀ c, 0 < c → deriv (deriv U) c < 0)
    (hUInada0 : Tendsto (deriv U) (𝓝[>] (0 : ℝ)) atTop) :
    ∃ ks : ℝ, 0 < ks ∧ deriv f ks = d + m ∧
      Nonempty (CassConstructionData f (deriv f) (deriv U) d m k0 ks) := by
  obtain ⟨ks, hks, _⟩ := existsUnique_stationary_capital_of_inada f d m
    (add_pos hd hm) hfconc hfdiff hfprime hfInada0 hfInadaTop
  let kl := min k0 ks / 2
  let ku := max k0 ks + 1
  have hkl : 0 < kl := half_pos (lt_min hk0 hks.1)
  have hkl0 : kl < k0 := by
    have hmin := min_le_left k0 ks
    have hp := lt_min hk0 hks.1
    dsimp [kl]
    linarith
  have hlstar : kl < ks := by
    have hmin := min_le_right k0 ks
    have hp := lt_min hk0 hks.1
    dsimp [kl]
    linarith
  have hstaru : ks < ku := by dsimp [ku]; linarith [le_max_right k0 ks]
  have hku0 : k0 < ku := by dsimp [ku]; linarith [le_max_left k0 ks]
  have hsub : Icc kl ku ⊆ Ioi (0 : ℝ) := fun _ hx => hkl.trans_le hx.1
  have hsubnet : Icc kl ks ⊆ Ioi (0 : ℝ) := fun _ hx => hkl.trans_le hx.1
  have hanti := production_deriv_strictAnti f hfconc hfdiff
  have hfcont : ContinuousOn f (Icc kl ku) :=
    fun k hk => (hfdiff k (hsub hk)).continuousAt.continuousWithinAt
  have hfmono : MonotoneOn f (Icc kl ku) := monotoneOn_of_deriv_nonneg (convex_Icc kl ku)
    hfcont (fun k hk => (hfdiff k (hsub (interior_subset hk))).differentiableWithinAt)
    (fun k hk => (hfprimepos k (hsub (interior_subset hk))).le)
  have hnetDeriv : ∀ k ∈ Icc kl ks,
      HasDerivAt (fun x => f x - m * x) (deriv f k - m) k := by
    intro k hk
    convert (hfdiff k (hsubnet hk)).hasDerivAt.sub ((hasDerivAt_id k).const_mul m) using 1
    · rfl
    · ring
  have hnet : MonotoneOn (fun k => f k - m * k) (Icc kl ks) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc kl ks)
      (HasDerivAt.continuousOn hnetDeriv)
      (fun k hk => (hnetDeriv k (interior_subset hk)).differentiableAt.differentiableWithinAt)
    intro k hk
    have hkmem := interior_subset hk
    have hmp := hanti.antitoneOn (hsubnet hkmem) hks.1 hkmem.2
    rw [hks.2] at hmp
    rw [(hnetDeriv k hkmem).deriv]
    linarith
  have hnetpos : 0 < f kl - m * kl := by
    have hgap := marginal_product_times_capital_lt_output f kl hfconc hfzero hkl (hfdiff kl hkl)
    have hmp := hanti hkl hks.1 hlstar
    rw [hks.2] at hmp
    have hprod := mul_pos (show 0 < deriv f kl - m by linarith) hkl
    nlinarith
  have hμanti : StrictAntiOn (deriv U) (Ioi 0) := hUconc.strictAntiOn_deriv hUdiff
  refine ⟨ks, hks.1, hks.2, ?_⟩
  exact exists_cass_finite_data f (deriv f) (deriv U) d m kl ku ks k0 hd hm hkl hlstar hstaru
    ⟨hkl0.le, hku0.le⟩
    (fun k hk => (hfdiff k (hsub hk)).hasDerivAt) (hfprime.mono hsub)
    (fun k hk => hfsecond k (hsub hk)) (hfsecondcont.mono hsub) hfmono
    (hanti.mono hsub) (fun k hk => hfprimepos k (hsub hk)) hks.2 hnet hnetpos
    hUprimepos hμanti hUsecond hUsecondcont hUsecondneg hUInada0

end RamseyCassKoopmans


/-! # Turning the constructed trajectory into an economic feasible path -/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.CassPhase

theorem consumption_continuous (p : CassPhase) (hC : Continuous p.C)
    (hf : Continuous (p.f ∘ clip p.kl p.ku)) :
    Continuous (fun x : ℝ × ℝ => cassConsumption p.f p.C (p.point x)) :=
  (hC.comp ((lipschitz_clip 0 p.Q).continuous.comp continuous_snd)).min
    (hf.comp continuous_fst)

theorem investment_continuous (p : CassPhase) (hC : Continuous p.C)
    (hf : Continuous (p.f ∘ clip p.kl p.ku)) :
    Continuous (fun x : ℝ × ℝ => cassInvestment p.f p.C (p.point x)) :=
  (hf.comp continuous_fst).sub (p.consumption_continuous hC hf)

theorem consumption_mem (p : CassPhase) (x : ℝ × ℝ) :
    cassConsumption p.f p.C (p.point x) ∈ Icc p.ca p.cb := by
  exact ⟨le_min (p.C_mem _).1 (p.f_mem _ (p.stock_mem _)).1,
    (min_le_left _ _).trans (p.C_mem _).2⟩

theorem consumption_steady (p : CassPhase) :
    cassConsumption p.f p.C (p.point p.steady) = p.surplus := by
  change min (p.C (p.price p.qs)) (p.f (p.stock p.ks)) = _
  rw [p.price_steady, p.stock_steady, p.demand_at_steady, min_eq_left p.surplus_lt_output.le]

noncomputable def feasiblePath (p : CassPhase) (γ : ℝ → ℝ × ℝ)
    (hC : Continuous p.C) (hf : Continuous (p.f ∘ clip p.kl p.ku))
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t) : FeasiblePath p.f p.m where
  capital := fun t => (γ t).1
  consumption := fun t => cassConsumption p.f p.C (p.point (γ t))
  investment := fun t => cassInvestment p.f p.C (p.point (γ t))
  capital_nonneg := fun t ht => by
    have hk := congrArg Prod.fst (hclip t ht)
    exact hk ▸ (p.stock_pos (γ t).1).le
  consumption_pos := fun t _ => p.ca_pos.trans_le (p.consumption_mem (γ t)).1
  consumption_continuous := (p.consumption_continuous hC hf).comp_continuousOn
    (HasDerivAt.continuousOn (fun t _ => hd t))
  investment_continuous := (p.investment_continuous hC hf).comp_continuousOn
    (HasDerivAt.continuousOn (fun t _ => hd t))
  resource := fun t ht => by
    have hr := cass_resource p.f p.C (p.point (γ t))
    rw [hclip t ht] at hr
    simpa only [hclip t ht] using hr
  dynamics := fun t ht => by
    have h := ODE.hasDerivAt_fst (hd t)
    have hk := congrArg Prod.fst (hclip t ht)
    change HasDerivAt (fun t => (γ t).1)
      (cassInvestment p.f p.C (p.point (γ t)) - p.m * p.stock (γ t).1) t at h
    change p.stock (γ t).1 = (γ t).1 at hk
    rw [hk] at h
    exact h

theorem path_capital_pos (p : CassPhase) (γ : ℝ → ℝ × ℝ)
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t) :
    ∀ t, 0 ≤ t → 0 < (γ t).1 := by
  intro t ht
  have hk := congrArg Prod.fst (hclip t ht)
  exact hk ▸ p.stock_pos (γ t).1

theorem path_costate (p : CassPhase) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t) :
    ∀ t, 0 ≤ t → HasDerivAt (fun t => (γ t).2)
      ((p.d + p.m) * (γ t).2 -
        p.μ (cassConsumption p.f p.C (p.point (γ t))) * p.mp (γ t).1) t := by
  intro t ht
  have h := ODE.hasDerivAt_snd (hd t)
  have hk := congrArg Prod.fst (hclip t ht)
  have hq := congrArg Prod.snd (hclip t ht)
  change p.stock (γ t).1 = (γ t).1 at hk
  change p.price (γ t).2 = (γ t).2 at hq
  change HasDerivAt (fun t => (γ t).2)
    ((p.d + p.m) * p.price (γ t).2 -
      max (p.price (γ t).2) (p.μ (p.f (p.stock (γ t).1))) * p.mp (p.stock (γ t).1)) t at h
  rw [← p.marginal (γ t), hk, hq] at h
  exact h

theorem path_wedge_slack (p : CassPhase) {γ : ℝ → ℝ × ℝ}
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t) :
    ∀ t, 0 ≤ t → (γ t).2 ≤ p.μ (cassConsumption p.f p.C (p.point (γ t))) ∧
      ((γ t).2 - p.μ (cassConsumption p.f p.C (p.point (γ t)))) *
        cassInvestment p.f p.C (p.point (γ t)) = 0 := by
  intro t ht
  have hw := cass_wedge_and_slack (p.marginal (γ t)) p.μ_anti (p.output_pos _) (p.demand_pos _)
  have hq := congrArg Prod.snd (hclip t ht)
  change p.price (γ t).2 = (γ t).2 at hq
  change p.price (γ t).2 ≤ _ ∧ (p.price (γ t).2 - _) * _ = 0 at hw
  rw [hq] at hw
  exact hw

theorem consumption_converges (p : CassPhase) (hC : Continuous p.C)
    (hf : Continuous (p.f ∘ clip p.kl p.ku)) {γ : ℝ → ℝ × ℝ}
    (hlim : Tendsto γ atTop (𝓝 p.steady)) :
    Tendsto (fun t => cassConsumption p.f p.C (p.point (γ t))) atTop (𝓝 p.surplus) := by
  have h := (p.consumption_continuous hC hf).continuousAt.tendsto.comp hlim
  simpa only [p.consumption_steady, Function.comp_def] using h

end RamseyCassKoopmans.CassPhase


/-! # Finite welfare for bounded, possibly negative felicity -/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

theorem exists_hasWelfare_of_abs_bounded (U c : ℝ → ℝ) {d M : ℝ} (hd : 0 < d)
    (hcont : ContinuousOn (fun t => U (c t)) (Ici 0))
    (hb : ∀ t, 0 ≤ t → |U (c t)| ≤ M) : ∃ J, HasWelfare U (discount d) c J := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0 le_rfl)
  let Up : ℝ → ℝ := fun x => max (U x) 0
  let Un : ℝ → ℝ := fun x => max (-U x) 0
  have hpc : ContinuousOn (fun t => Up (c t)) (Ici 0) := hcont.sup continuousOn_const
  have hnc : ContinuousOn (fun t => Un (c t)) (Ici 0) := hcont.neg.sup continuousOn_const
  obtain ⟨Jp, hp⟩ := exists_hasWelfare_of_nonneg_bounded Up c hd hpc (fun t ht =>
    ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hb t ht)) hM⟩)
  obtain ⟨Jn, hn⟩ := exists_hasWelfare_of_nonneg_bounded Un c hd hnc (fun t ht =>
    ⟨le_max_right _ _, max_le ((neg_le_abs _).trans (hb t ht)) hM⟩)
  have hid : ∀ x, Up x - Un x = U x := by
    intro x
    dsimp [Up, Un]
    rcases le_total 0 (U x) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
      ring
  have hW : ∀ T, 0 ≤ T → welfare Up (discount d) c T - welfare Un (discount d) c T =
      welfare U (discount d) c T := by
    intro T hT
    have hpi : IntervalIntegrable (fun t => discount d t * Up (c t)) volume 0 T :=
      (((discount_continuous d).continuousOn.mul hpc).mono
      (fun _ ht => ht.1)).intervalIntegrable_of_Icc hT
    have hni : IntervalIntegrable (fun t => discount d t * Un (c t)) volume 0 T :=
      (((discount_continuous d).continuousOn.mul hnc).mono
      (fun _ ht => ht.1)).intervalIntegrable_of_Icc hT
    unfold welfare
    rw [← intervalIntegral.integral_sub hpi hni]
    apply intervalIntegral.integral_congr
    intro t _
    change discount d t * Up (c t) - discount d t * Un (c t) = discount d t * U (c t)
    rw [← mul_sub, hid]
  refine ⟨Jp - Jn, (hp.sub hn).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact hW T hT

theorem exists_hasWelfare_of_compact_consumption (U c : ℝ → ℝ) {a b d : ℝ}
    (hd : 0 < d) (hab : a ≤ b) (hU : ContinuousOn U (Icc a b))
    (hc : ContinuousOn c (Ici 0)) (hb : ∀ t, 0 ≤ t → c t ∈ Icc a b) :
    ∃ J, HasWelfare U (discount d) c J := by
  obtain ⟨x, _, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hU.norm
  apply exists_hasWelfare_of_abs_bounded U c hd (hU.comp hc hb)
  exact fun t ht => hmax (hb t ht)

end RamseyCassKoopmans


/-! # Consumption monotonicity and eventual interior investment

The result retains corners. Strict consumption monotonicity follows from
`U'(c)=max(q,U'(f(k)))`; it does not differentiate consumption at a switch.
Positive steady replacement investment implies that all corners end in finite
time. No assertion of a single crossing is needed for this conclusion.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.CassPhase

theorem positive_investment_of_nondecreasing_capital
    {f : ℝ → ℝ} {m : ℝ} (a : FeasiblePath f m) (hm : 0 < m)
    (hpos : ∀ t, 0 ≤ t → 0 < a.capital t)
    (hk : MonotoneOn a.capital (Ici 0)) : ∀ t, 0 ≤ t → 0 < a.investment t := by
  intro t ht
  by_contra hz
  have hdneg : a.investment t - m * a.capital t < 0 :=
    sub_neg.mpr ((le_of_not_gt hz).trans_lt (mul_pos hm (hpos t ht)))
  have hneg := ODE.eventually_lt_right_of_deriv_neg (a.dynamics t ht) hdneg
  have hright : ∀ᶠ u in 𝓝[>] t, t < u := self_mem_nhdsWithin
  obtain ⟨u, hu, htu⟩ := (hneg.and hright).exists
  exact not_lt_of_ge (hk ht (ht.trans htu.le) htu.le) hu

theorem production_strictMono (p : CassPhase) (hmp : p.mp = deriv p.f)
    (hf : ∀ k, 0 < k → DifferentiableAt ℝ p.f k) :
    StrictMonoOn p.f (Icc p.kl p.ku) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun k hk => (hf k (p.kl_pos.trans_le hk.1)).continuousAt.continuousWithinAt)
  intro k hk
  rw [← hmp]
  exact p.mp_pos k (interior_subset hk)

theorem consumption_lt_of_coordinates (p : CassPhase)
    (hf : StrictMonoOn p.f (Icc p.kl p.ku)) {x y : ℝ × ℝ}
    (hx : p.point x = x) (hy : p.point y = y)
    (hk : x.1 < y.1) (hq : y.2 < x.2) :
    cassConsumption p.f p.C (p.point x) < cassConsumption p.f p.C (p.point y) := by
  have hxk : p.stock x.1 = x.1 := congrArg Prod.fst hx
  have hyk : p.stock y.1 = y.1 := congrArg Prod.fst hy
  have hxq : p.price x.2 = x.2 := congrArg Prod.snd hx
  have hyq : p.price y.2 = y.2 := congrArg Prod.snd hy
  have hfx : 0 < p.f x.1 := hxk ▸ p.output_pos x.1
  have hfy : 0 < p.f y.1 := hyk ▸ p.output_pos y.1
  have hfm := hf (hxk ▸ p.stock_mem x.1) (hyk ▸ p.stock_mem y.1) hk
  have hμ : p.μ (cassConsumption p.f p.C (p.point y)) <
      p.μ (cassConsumption p.f p.C (p.point x)) := by
    rw [p.marginal y, p.marginal x, hxk, hyk, hxq, hyq]
    exact max_lt_max hq (p.μ_anti hfx hfy hfm)
  by_contra h
  have hle := p.μ_anti.antitoneOn (p.ca_pos.trans_le (p.consumption_mem y).1)
    (p.ca_pos.trans_le (p.consumption_mem x).1) (le_of_not_gt h)
  exact not_le_of_gt hμ hle

theorem consumption_strictMono (p : CassPhase)
    (hf : StrictMonoOn p.f (Icc p.kl p.ku)) {γ : ℝ → ℝ × ℝ}
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t)
    (hk : StrictMonoOn (fun t => (γ t).1) (Ici 0))
    (hq : StrictAntiOn (fun t => (γ t).2) (Ici 0)) :
    StrictMonoOn (fun t => cassConsumption p.f p.C (p.point (γ t))) (Ici 0) := by
  intro s hs t ht hst
  exact p.consumption_lt_of_coordinates hf (hclip s hs) (hclip t ht)
    (hk hs ht hst) (hq hs ht hst)

theorem consumption_strictAnti (p : CassPhase)
    (hf : StrictMonoOn p.f (Icc p.kl p.ku)) {γ : ℝ → ℝ × ℝ}
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t)
    (hk : StrictAntiOn (fun t => (γ t).1) (Ici 0))
    (hq : StrictMonoOn (fun t => (γ t).2) (Ici 0)) :
    StrictAntiOn (fun t => cassConsumption p.f p.C (p.point (γ t))) (Ici 0) := by
  intro s hs t ht hst
  exact p.consumption_lt_of_coordinates hf (hclip t ht) (hclip s hs)
    (hk hs ht hst) (hq hs ht hst)

theorem investment_converges (p : CassPhase) (hC : Continuous p.C)
    (hf : Continuous (p.f ∘ clip p.kl p.ku)) {γ : ℝ → ℝ × ℝ}
    (hlim : Tendsto γ atTop (𝓝 p.steady)) :
    Tendsto (fun t => cassInvestment p.f p.C (p.point (γ t))) atTop (𝓝 (p.m * p.ks)) := by
  have h := (p.investment_continuous hC hf).continuousAt.tendsto.comp hlim
  have hsteady : cassInvestment p.f p.C (p.point p.steady) = p.m * p.ks := by
    change p.f (p.stock p.ks) - cassConsumption p.f p.C (p.point p.steady) = _
    rw [p.stock_steady, p.consumption_steady]
    dsimp [surplus]
    ring
  simpa only [hsteady, Function.comp_def] using h

theorem eventually_positive_investment (p : CassPhase) (hC : Continuous p.C)
    (hf : Continuous (p.f ∘ clip p.kl p.ku)) {γ : ℝ → ℝ × ℝ}
    (hlim : Tendsto γ atTop (𝓝 p.steady)) :
    ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → 0 < cassInvestment p.f p.C (p.point (γ t)) := by
  have hz : 0 < p.m * p.ks := mul_pos p.m_pos (p.kl_pos.trans p.kl_lt)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((p.investment_converges hC hf hlim).eventually (lt_mem_nhds hz))
  exact ⟨max 0 T, le_max_left _ _, fun t ht => hT t ((le_max_right _ _).trans ht)⟩

theorem saving_rate_converges (p : CassPhase) (hC : Continuous p.C)
    (hf : Continuous (p.f ∘ clip p.kl p.ku)) {γ : ℝ → ℝ × ℝ}
    (hlim : Tendsto γ atTop (𝓝 p.steady)) :
    Tendsto (fun t => cassInvestment p.f p.C (p.point (γ t)) / p.f (p.stock (γ t).1))
      atTop (𝓝 (p.m * p.ks / p.f p.ks)) ∧
      0 < p.m * p.ks / p.f p.ks ∧ p.m * p.ks / p.f p.ks < 1 := by
  have houtput : 0 < p.f p.ks := p.stock_steady ▸ p.output_pos p.ks
  have hn : 0 < p.m * p.ks := mul_pos p.m_pos (p.kl_pos.trans p.kl_lt)
  have hden : Tendsto (fun t => p.f (p.stock (γ t).1)) atTop (𝓝 (p.f p.ks)) := by
    have hh := (hf.continuousAt.tendsto.comp hlim.fst_nhds)
    change Tendsto (fun t => p.f (p.stock (γ t).1)) atTop (𝓝 (p.f (p.stock p.ks))) at hh
    rwa [p.stock_steady] at hh
  refine ⟨(p.investment_converges hC hf hlim).div hden houtput.ne', div_pos hn houtput, ?_⟩
  apply (div_lt_one houtput).mpr
  linarith [p.ca_lt_surplus, p.ca_pos]

end RamseyCassKoopmans.CassPhase


/-! # Welfare dominance without assuming competitor welfare convergence

The comparison is defined using finite-horizon integrals: for every positive
epsilon, the competitor's welfare advantage is eventually less than epsilon.
This includes competitors whose lifetime utility diverges or has no real limit.
It is not an assertion that each competitor has finite lifetime welfare.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

def AsymptoticallyDominates (U w ca cb : ℝ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ᶠ T in atTop, welfare U w cb T - welfare U w ca T < ε

theorem asymptotic_dominance_of_terminal_limit
    {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0)) :
    AsymptoticallyDominates U w a.consumption b.consumption := by
  intro ε hε
  filter_upwards [eventually_ge_atTop (0 : ℝ), hterminal.eventually (gt_mem_nhds hε)] with T hT hB
  exact (finite_horizon_comparison v b halloc hinit hT).trans_lt hB

theorem AsymptoticallyDominates.finite_welfare_le {U w ca cb : ℝ → ℝ} {Ja Jb : ℝ}
    (h : AsymptoticallyDominates U w ca cb) (ha : HasWelfare U w ca Ja)
    (hb : HasWelfare U w cb Jb) : Jb ≤ Ja := by
  by_contra hn
  have hp : 0 < (Jb - Ja) / 2 := half_pos (sub_pos.mpr (lt_of_not_ge hn))
  have hh : Jb - Ja ≤ (Jb - Ja) / 2 :=
    le_of_tendsto (hb.sub ha) ((h _ hp).mono (fun _ hx => hx.le))
  linarith

end RamseyCassKoopmans


/-! # Optimality of the constructed general Cass path -/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans

theorem CassPhase.constructed_optimal (p : CassPhase) (U : ℝ → ℝ)
    (hmp : p.mp = deriv p.f) (hμ : p.μ = deriv U)
    (hfconc : ConcaveOn ℝ (Ici 0) p.f) (hUconc : ConcaveOn ℝ (Ioi 0) U)
    (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ p.f k)
    (hUdiff : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv p.f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hC : Continuous p.C) (hf : Continuous (p.f ∘ clip p.kl p.ku))
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t)
    (hlim : Tendsto γ atTop (𝓝 p.steady))
    {K : ℝ} (hk0 : (γ 0).1 ≤ K) (hcapacity : ∀ k, K ≤ k → p.f k ≤ p.m * k) :
    ∃ J, IsCassOptimal U p.d (p.feasiblePath γ hC hf hd hclip) J := by
  let a := p.feasiblePath γ hC hf hd hclip
  have hUcont : ContinuousOn U (Ioi 0) :=
    fun c hc => (hUdiff c hc).continuousAt.continuousWithinAt
  obtain ⟨J, hJ⟩ := exists_hasWelfare_of_compact_consumption U a.consumption p.d_pos p.ca_le_cb
    (hUcont.mono (fun _ hx => p.ca_pos.trans_le hx.1)) a.consumption_continuous
    (fun t _ => p.consumption_mem (γ t))
  refine ⟨J, ?_⟩
  have hcostate := p.path_costate hd hclip
  rw [hmp, hμ] at hcostate
  have hwedge := p.path_wedge_slack hclip
  rw [hμ] at hwedge
  apply cass_certificate_is_optimal p.f U (fun t => (γ t).2) p.d p.m K J a
    hfconc hUconc hUcont hfdiff hUdiff hfprime hUprime
    (p.path_capital_pos γ hclip)
  · intro t ht
    have hq := congrArg Prod.snd (hclip t ht)
    exact hq ▸ (p.price_mem (γ t).2).1
  · exact hcostate
  · exact fun t ht => (hwedge t ht).1
  · exact fun t ht => (hwedge t ht).2
  · exact fun t _ => cass_investment_nonneg p.f p.C (p.point (γ t))
  · exact hcapacity
  · exact hk0
  · exact hJ
  · exact Terminal.discounted_price_tendsto_zero p.d_pos hlim.snd_nhds

theorem CassPhase.constructed_unique (p : CassPhase) (U : ℝ → ℝ)
    (hmp : p.mp = deriv p.f) (hμ : p.μ = deriv U)
    (hfconc : StrictConcaveOn ℝ (Ici 0) p.f) (hUconc : StrictConcaveOn ℝ (Ioi 0) U)
    (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ p.f k)
    (hUdiff : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv p.f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hC : Continuous p.C) (hf : Continuous (p.f ∘ clip p.kl p.ku))
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t)
    (hlim : Tendsto γ atTop (𝓝 p.steady))
    {K Ja Jb : ℝ} (hk0 : (γ 0).1 ≤ K) (hcapacity : ∀ k, K ≤ k → p.f k ≤ p.m * k)
    (ha : HasWelfare U (discount p.d) (p.feasiblePath γ hC hf hd hclip).consumption Ja)
    (b : FeasiblePath p.f p.m) (hbinv : b.NonnegativeInvestment)
    (hi : (γ 0).1 = b.capital 0) (hb : HasWelfare U (discount p.d) b.consumption Jb)
    (heq : Jb = Ja) :
    ∀ t, 0 ≤ t → b.capital t = (γ t).1 ∧
      b.consumption t = cassConsumption p.f p.C (p.point (γ t)) ∧
      b.investment t = cassInvestment p.f p.C (p.point (γ t)) := by
  let a := p.feasiblePath γ hC hf hd hclip
  have hUcont : ContinuousOn U (Ioi 0) :=
    fun c hc => (hUdiff c hc).continuousAt.continuousWithinAt
  have hcostate := p.path_costate hd hclip
  rw [hmp, hμ] at hcostate
  have hwedge := p.path_wedge_slack hclip
  rw [hμ] at hwedge
  apply cass_certificate_unique p.f U (fun t => (γ t).2) p.d p.m K Ja Jb a b
    hfconc hUconc hUcont hfdiff hUdiff hfprime hUprime (p.path_capital_pos γ hclip)
  · intro t ht
    rw [← hμ]
    exact p.μ_pos _ (a.consumption_pos t ht)
  · exact hcostate
  · exact fun t ht => (hwedge t ht).1
  · exact fun t ht => (hwedge t ht).2
  · exact hbinv
  · exact hi
  · exact hcapacity
  · exact hk0
  · exact ha
  · exact hb
  · exact Terminal.discounted_price_tendsto_zero p.d_pos hlim.snd_nhds
  · exact heq

/-- Every feasible Cass competitor is compared, without an assumption that its
discounted objective has a finite real limit. -/
theorem CassPhase.constructed_dominates (p : CassPhase) (U : ℝ → ℝ)
    (hmp : p.mp = deriv p.f) (hμ : p.μ = deriv U)
    (hfconc : ConcaveOn ℝ (Ici 0) p.f) (hUconc : ConcaveOn ℝ (Ioi 0) U)
    (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ p.f k)
    (hUdiff : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv p.f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hC : Continuous p.C) (hf : Continuous (p.f ∘ clip p.kl p.ku))
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t)
    (hlim : Tendsto γ atTop (𝓝 p.steady))
    {K : ℝ} (hk0 : (γ 0).1 ≤ K) (hcapacity : ∀ k, K ≤ k → p.f k ≤ p.m * k)
    (b : FeasiblePath p.f p.m) (hb : b.NonnegativeInvestment) (hi : (γ 0).1 = b.capital 0) :
    AsymptoticallyDominates U (discount p.d)
      (p.feasiblePath γ hC hf hd hclip).consumption b.consumption := by
  let a := p.feasiblePath γ hC hf hd hclip
  have hUcont : ContinuousOn U (Ioi 0) :=
    fun c hc => (hUdiff c hc).continuousAt.continuousWithinAt
  have hcostate := p.path_costate hd hclip
  rw [hmp, hμ] at hcostate
  have hmu : ∀ t, 0 ≤ t → 0 ≤ deriv U (a.consumption t) := by
    intro t ht
    rw [← hμ]
    exact (p.μ_pos _ (a.consumption_pos t ht)).le
  let v := cassSupportingPrices p.f U (fun t => (γ t).2) p.d p.m a
    hfconc hUconc hUcont hfdiff hUdiff hfprime hUprime (p.path_capital_pos γ hclip) hmu hcostate
  have hw := p.path_wedge_slack hclip
  rw [hμ] at hw
  have halloc : AllocationComparison v b := by
    apply allocation_of_cass v
    · intro t ht
      exact mul_le_mul_of_nonneg_left (hw t ht).1 (discount_pos p.d t).le
    · intro t ht
      change (discount p.d t * (γ t).2 - discount p.d t * deriv U (a.consumption t)) *
        a.investment t = 0
      rw [← mul_sub, mul_assoc]
      change discount p.d t * (((γ t).2 - deriv U
        (cassConsumption p.f p.C (p.point (γ t)))) * cassInvestment p.f p.C (p.point (γ t))) = 0
      rw [(hw t ht).2, mul_zero]
    · exact hb
  apply asymptotic_dominance_of_terminal_limit v b halloc hi
  exact Terminal.terminal_tendsto_zero_of_bounded_capital
    (Terminal.discounted_price_tendsto_zero p.d_pos hlim.snd_nhds)
    (fun t ht => ⟨a.capital_nonneg t ht, a.capital_le_capacity hcapacity hk0 t ht⟩)
    (fun t ht => ⟨b.capital_nonneg t ht, b.capital_le_capacity hcapacity (hi ▸ hk0) t ht⟩)

theorem CassConstructionData.exists_optimal
    {f U : ℝ → ℝ} {d m k0 ks : ℝ}
    (D : CassConstructionData f (deriv f) (deriv U) d m k0 ks)
    (hfconc : StrictConcaveOn ℝ (Ici 0) f) (hUconc : StrictConcaveOn ℝ (Ioi 0) U)
    (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hUdiff : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    {K : ℝ} (hkK : k0 ≤ K) (hcapacity : ∀ k, K ≤ k → f k ≤ m * k) :
    ∃ a : FeasiblePath f m, ∃ J : ℝ, a.capital 0 = k0 ∧ IsCassOptimal U d a J ∧
      Tendsto a.capital atTop (𝓝 ks) ∧
      Tendsto a.consumption atTop (𝓝 (f ks - m * ks)) ∧
      (k0 < ks → StrictMonoOn a.capital (Ici 0)) ∧
      (ks < k0 → StrictAntiOn a.capital (Ici 0)) ∧
      (k0 < ks → StrictMonoOn a.consumption (Ici 0)) ∧
      (ks < k0 → StrictAntiOn a.consumption (Ici 0)) ∧
      (k0 < ks → ∀ t, 0 ≤ t → 0 < a.investment t) ∧
      (k0 = ks → ∀ t, a.capital t = ks ∧ a.consumption t = f ks - m * ks ∧
        a.investment t = m * ks) ∧
      (∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → 0 < a.investment t) ∧
      (∀ b : FeasiblePath f m, b.NonnegativeInvestment → b.capital 0 = k0 →
        AsymptoticallyDominates U (discount d) a.consumption b.consumption) ∧
      (∀ (b : FeasiblePath f m) (Jb : ℝ), IsCassOptimal U d b Jb → b.capital 0 = k0 →
        Jb = J ∧ ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
          b.consumption t = a.consumption t ∧ b.investment t = a.investment t) := by
  let p := D.phase
  obtain ⟨_, _, hCLip, _⟩ := D.demand_bounded
  obtain ⟨_, _, hFLip, _⟩ := D.production_bounded
  obtain ⟨γ, h0, hd, hclipq, hlim, hbelow, habove, hconstant⟩ := p.exists_convergent_trajectory
    D.bounded D.net_mono D.consumption_mem D.net_gap D.time_nonneg D.price_large
    D.time_large D.initial_mem
  have hclip := fun t ht => (hclipq t ht).1
  have hprod : p.f = f := D.production_eq
  have hmul : p.μ = deriv U := D.marginalUtility_eq
  have hmp : p.mp = deriv p.f := by rw [hprod]; exact D.marginalProduct_eq
  have hdil : p.m = m := D.dilution_eq
  have hdis : p.d = d := D.discount_eq
  have hsteady : p.ks = ks := D.steady_eq
  have hfconc' : StrictConcaveOn ℝ (Ici 0) p.f := hprod ▸ hfconc
  have hfdiff' : ∀ k, 0 < k → DifferentiableAt ℝ p.f k := hprod ▸ hfdiff
  have hfprime' : ContinuousOn (deriv p.f) (Ioi 0) := hprod ▸ hfprime
  have hcapacity' : ∀ k, K ≤ k → p.f k ≤ p.m * k := by simpa only [hprod, hdil] using hcapacity
  obtain ⟨J, hJ⟩ :=
    p.constructed_optimal U hmp hmul hfconc'.concaveOn hUconc.concaveOn
      hfdiff' hUdiff hfprime' hUprime
    hCLip.continuous hFLip.continuous hd hclip hlim (h0 ▸ hkK) hcapacity'
  let a := p.feasiblePath γ hCLip.continuous hFLip.continuous hd hclip
  have hresult : ∃ a : FeasiblePath p.f p.m, ∃ J : ℝ,
      a.capital 0 = k0 ∧ IsCassOptimal U p.d a J ∧
      Tendsto a.capital atTop (𝓝 p.ks) ∧
      Tendsto a.consumption atTop (𝓝 (p.f p.ks - p.m * p.ks)) ∧
      (k0 < p.ks → StrictMonoOn a.capital (Ici 0)) ∧
      (p.ks < k0 → StrictAntiOn a.capital (Ici 0)) ∧
      (k0 < p.ks → StrictMonoOn a.consumption (Ici 0)) ∧
      (p.ks < k0 → StrictAntiOn a.consumption (Ici 0)) ∧
      (k0 < p.ks → ∀ t, 0 ≤ t → 0 < a.investment t) ∧
      (k0 = p.ks → ∀ t, a.capital t = p.ks ∧ a.consumption t = p.f p.ks - p.m * p.ks ∧
        a.investment t = p.m * p.ks) ∧
      (∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → 0 < a.investment t) ∧
      (∀ b : FeasiblePath p.f p.m, b.NonnegativeInvestment → b.capital 0 = k0 →
        AsymptoticallyDominates U (discount p.d) a.consumption b.consumption) ∧
      (∀ (b : FeasiblePath p.f p.m) (Jb : ℝ), IsCassOptimal U p.d b Jb → b.capital 0 = k0 →
        Jb = J ∧ ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
          b.consumption t = a.consumption t ∧ b.investment t = a.investment t) := by
    refine ⟨a, J, h0, hJ, hlim.fst_nhds,
      p.consumption_converges hCLip.continuous hFLip.continuous hlim,
      (fun h => (hbelow h).1), (fun h => (habove h).1),
      (fun h => p.consumption_strictMono (p.production_strictMono hmp hfdiff') hclip
        (hbelow h).1 (hbelow h).2),
      (fun h => p.consumption_strictAnti (p.production_strictMono hmp hfdiff') hclip
        (habove h).1 (habove h).2),
      (fun h => CassPhase.positive_investment_of_nondecreasing_capital a p.m_pos
        (p.path_capital_pos γ hclip) (hbelow h).1.monotoneOn), ?_,
      p.eventually_positive_investment hCLip.continuous hFLip.continuous hlim, ?_, ?_⟩
    · intro heq t
      change (γ t).1 = p.ks ∧ cassConsumption p.f p.C (p.point (γ t)) = p.surplus ∧
        cassInvestment p.f p.C (p.point (γ t)) = p.m * p.ks
      rw [hconstant heq t, p.consumption_steady]
      refine ⟨rfl, rfl, ?_⟩
      change p.f (p.stock p.ks) - cassConsumption p.f p.C (p.point p.steady) = _
      rw [p.stock_steady, p.consumption_steady]
      dsimp [CassPhase.surplus]
      ring
    · intro b hb hi
      exact p.constructed_dominates U hmp hmul hfconc'.concaveOn hUconc.concaveOn hfdiff' hUdiff
        hfprime' hUprime hCLip.continuous hFLip.continuous hd hclip hlim
        (h0 ▸ hkK) hcapacity' b hb (h0.trans hi.symm)
    · intro b Jb hb hi
      have hinit : a.capital 0 = b.capital 0 := h0.trans hi.symm
      have heq : Jb = J := le_antisymm
        (hJ.2.2 b hb.1 hinit Jb hb.2.1) (hb.2.2 a hJ.1 hinit.symm J hJ.2.1)
      exact ⟨heq, p.constructed_unique U hmp hmul hfconc' hUconc hfdiff' hUdiff hfprime' hUprime
        hCLip.continuous hFLip.continuous hd hclip hlim (h0 ▸ hkK) hcapacity'
        hJ.2.1 b hb.1 hinit hb.2.1 heq⟩
  rw [hprod, hdil, hdis, hsteady] at hresult
  exact hresult

end RamseyCassKoopmans


/-! # The general positive-discount Cass construction

For every positive initial stock, the primitive Inada and curvature assumptions
give a constructed feasible optimal path, convergence of capital and consumption,
strict movement of nonstationary capital toward the steady state, and uniqueness
of every optimum in the stated continuous-control, finite-welfare class.

Neither existence, a selected initial consumption, convergence, transversality,
nor a stable manifold is assumed. The possible zero-investment corner is retained
throughout the construction and the verification certificate.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

theorem cass_general_dynamic (f U : ℝ → ℝ) (d m k0 : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hk0 : 0 < k0)
    (hfconc : StrictConcaveOn ℝ (Ici 0) f) (hfzero : f 0 = 0)
    (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hfprimepos : ∀ k, 0 < k → 0 < deriv f k)
    (hfsecond : ∀ k, 0 < k → DifferentiableAt ℝ (deriv f) k)
    (hfsecondcont : ContinuousOn (deriv (deriv f)) (Ioi 0))
    (hfInada0 : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop)
    (hfInadaTop : Tendsto (deriv f) atTop (𝓝 (0 : ℝ)))
    (hUconc : StrictConcaveOn ℝ (Ioi 0) U)
    (hUdiff : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hUprimepos : ∀ c, 0 < c → 0 < deriv U c)
    (hUsecond : ∀ c, 0 < c → DifferentiableAt ℝ (deriv U) c)
    (hUsecondcont : ContinuousOn (deriv (deriv U)) (Ioi 0))
    (hUsecondneg : ∀ c, 0 < c → deriv (deriv U) c < 0)
    (hUInada0 : Tendsto (deriv U) (𝓝[>] (0 : ℝ)) atTop) :
    ∃ ks : ℝ, 0 < ks ∧ deriv f ks = d + m ∧
      ∃ a : FeasiblePath f m, ∃ J : ℝ, a.capital 0 = k0 ∧ IsCassOptimal U d a J ∧
        Tendsto a.capital atTop (𝓝 ks) ∧
        Tendsto a.consumption atTop (𝓝 (f ks - m * ks)) ∧
        (k0 < ks → StrictMonoOn a.capital (Ici 0)) ∧
        (ks < k0 → StrictAntiOn a.capital (Ici 0)) ∧
        (k0 < ks → StrictMonoOn a.consumption (Ici 0)) ∧
        (ks < k0 → StrictAntiOn a.consumption (Ici 0)) ∧
        (k0 < ks → ∀ t, 0 ≤ t → 0 < a.investment t) ∧
        (k0 = ks → ∀ t, a.capital t = ks ∧ a.consumption t = f ks - m * ks ∧
          a.investment t = m * ks) ∧
        (∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → 0 < a.investment t) ∧
        (∀ b : FeasiblePath f m, b.NonnegativeInvestment → b.capital 0 = k0 →
          AsymptoticallyDominates U (discount d) a.consumption b.consumption) ∧
        (∀ (b : FeasiblePath f m) (Jb : ℝ), IsCassOptimal U d b Jb → b.capital 0 = k0 →
          Jb = J ∧ ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
            b.consumption t = a.consumption t ∧ b.investment t = a.investment t) := by
  obtain ⟨ks, hks, hstationary, ⟨D⟩⟩ := exists_cass_data_of_inada f U d m k0 hd hm hk0
    hfconc hfzero hfdiff hfprime hfprimepos hfsecond hfsecondcont hfInada0 hfInadaTop
    hUconc hUdiff hUprimepos hUsecond hUsecondcont hUsecondneg hUInada0
  obtain ⟨K, hkK, hcapacity⟩ := exists_capacity_of_marginal_tendsto_zero f hm hfconc.concaveOn
    hfdiff (fun k hk => (hfprimepos k hk).le) hfInadaTop
  have hUprime : ContinuousOn (deriv U) (Ioi 0) :=
    fun c hc => (hUsecond c hc).continuousAt.continuousWithinAt
  exact ⟨ks, hks, hstationary,
    D.exists_optimal hfconc hUconc hfdiff hUdiff hfprime hUprime hkK hcapacity⟩

end RamseyCassKoopmans


/-! # Price decay from an eventually negative logarithmic derivative -/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.ODE

theorem exponential_upper_bound_on {f df : ℝ → ℝ} {A T K : ℝ} (hAT : A ≤ T)
    (hf : ∀ t ∈ Icc A T, HasDerivAt f (df t) t)
    (hb : ∀ t ∈ Icc A T, df t ≤ K * f t) :
    f T ≤ f A * Real.exp (K * (T - A)) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (a := A) (b := T) (δ := f A) (K := K) (ε := 0)
    (HasDerivAt.continuousOn hf)
    (fun t ht r hr => by
      simpa only [slope_def_field, div_eq_mul_inv, mul_comm] using
        ((hf t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt).liminf_right_slope_le hr)
    le_rfl (fun t ht => by simpa using hb t ⟨ht.1, ht.2.le⟩) T ⟨hAT, le_rfl⟩
  rwa [gronwallBound_ε0] at h

theorem tendsto_zero_of_negative_logarithmic_derivative {f a : ℝ → ℝ} {L : ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (a t * f t) t)
    (hn : ∀ t, 0 ≤ t → 0 ≤ f t) (ha : Tendsto a atTop (𝓝 L)) (hL : L < 0) :
    Tendsto f atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp (ha.eventually (gt_mem_nhds (show L < L / 2 by linarith)))
  let B := max 0 A
  have hB : 0 ≤ B := le_max_left _ _
  have hbound : ∀ T, B ≤ T → f T ≤ f B * Real.exp ((L / 2) * (T - B)) := by
    intro T hT
    apply exponential_upper_bound_on hT (fun t ht => hf t (hB.trans ht.1))
    intro t ht
    exact mul_le_mul_of_nonneg_right (hA t ((le_max_right _ _).trans ht.1)).le
      (hn t (hB.trans ht.1))
  have hl : Tendsto (fun T => f B * Real.exp ((L / 2) * (T - B))) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      ((tendsto_atTop_add_const_right atTop (-B) tendsto_id).const_mul_atTop_of_neg
        (show L / 2 < 0 by linarith))
    simpa only [sub_eq_add_neg, mul_zero, Function.comp_def, id_eq] using he.const_mul (f B)
  apply squeeze_zero'
    ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht => hn t ht))
    ((eventually_ge_atTop B).mono (fun t ht => hbound t ht)) hl

end RamseyCassKoopmans.ODE


/-! # Hamiltonian identities along regular interior Euler paths

These are identities for actual derivatives and finite integrals. They provide
an independent diagnostic for a proposed infinite-horizon Euler trajectory.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

noncomputable def currentHamiltonian (U g k c q : ℝ → ℝ) (t : ℝ) : ℝ :=
  U (c t) + q t * (g (k t) - c t)

theorem hasDerivAt_currentHamiltonian {U g k c q : ℝ → ℝ} {d gp cd t : ℝ}
    (hU : HasDerivAt U (q t) (c t)) (hg : HasDerivAt g gp (k t))
    (hk : HasDerivAt k (g (k t) - c t) t) (hc : HasDerivAt c cd t)
    (hq : HasDerivAt q ((d - gp) * q t) t) :
    HasDerivAt (currentHamiltonian U g k c q)
      (d * q t * (g (k t) - c t)) t := by
  convert (hU.comp t hc).add (hq.mul ((hg.comp t hk).sub hc)) using 1
  · rfl
  · dsimp
    ring

theorem hasDerivAt_discountedHamiltonian {U g k c q : ℝ → ℝ} {d gp cd t : ℝ}
    (hU : HasDerivAt U (q t) (c t)) (hg : HasDerivAt g gp (k t))
    (hk : HasDerivAt k (g (k t) - c t) t) (hc : HasDerivAt c cd t)
    (hq : HasDerivAt q ((d - gp) * q t) t) :
    HasDerivAt (fun s => discount d s * currentHamiltonian U g k c q s)
      (-d * (discount d t * U (c t))) t := by
  convert (hasDerivAt_discount d t).mul
    (hasDerivAt_currentHamiltonian hU hg hk hc hq) using 1
  dsimp [currentHamiltonian]
  ring

/-- A vanishing discounted primitive determines the welfare limit, rather than
assuming that the improper objective exists. -/
theorem hasWelfare_of_primitive {U c F : ℝ → ℝ} {d : ℝ}
    (hcont : ContinuousOn (fun t => U (c t)) (Ici 0))
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (-(discount d t * U (c t))) t)
    (hlim : Tendsto F atTop (𝓝 0)) : HasWelfare U (discount d) c (F 0) := by
  have hid : ∀ T, 0 ≤ T → welfare U (discount d) c T = F 0 - F T := by
    intro T hT
    have hi : IntervalIntegrable (fun t => discount d t * U (c t)) volume 0 T :=
      (((discount_continuous d).continuousOn.mul hcont).mono
        (fun _ ht => ht.1)).intervalIntegrable_of_Icc hT
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hF t (by rw [uIcc_of_le hT] at ht; exact ht.1)) hi.neg
    rw [intervalIntegral.integral_neg] at heq
    change -welfare U (discount d) c T = F T - F 0 at heq
    linarith
  have h := (tendsto_const_nhds (x := F 0) (f := atTop)).sub hlim
  simp only [sub_zero] at h
  exact h.congr' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact (hid T hT).symm)

end RamseyCassKoopmans


/-! # An asymptotically linear utility boundary example

`f(k) = 8 k / (1+k)`, `U(c) = c - 1/c`, and `d=m=1`.
The capacity is 7 and the discounted steady state is `(k,c)=(1,3)`.
Utility is strictly increasing and strictly concave, and tends to minus infinity
at zero, but its marginal utility tends to 1 at infinity.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans.KoopmansBoundary

noncomputable def production (k : ℝ) : ℝ := 8 - 8 / (1 + k)
noncomputable def marginalProduct (k : ℝ) : ℝ := 8 / (1 + k)^2
noncomputable def utility (c : ℝ) : ℝ := c - c⁻¹
noncomputable def marginalUtility (c : ℝ) : ℝ := 1 + c⁻¹ ^ 2

theorem production_formula {k : ℝ} (hk : 0 ≤ k) : production k = 8 * k / (1 + k) := by
  dsimp [production]
  field_simp
  ring

theorem production_deriv {k : ℝ} (hk : 1 + k ≠ 0) :
    HasDerivAt production (marginalProduct k) k := by
  convert ((hasDerivAt_const k (8 : ℝ)).div ((hasDerivAt_id k).const_add 1) hk).const_sub 8 using 1
  · rfl
  · dsimp [marginalProduct]
    ring

theorem marginalProduct_deriv {k : ℝ} (hk : 1 + k ≠ 0) :
    HasDerivAt marginalProduct (-16 / (1 + k)^3) k := by
  convert (hasDerivAt_const k (8 : ℝ)).div (((hasDerivAt_id k).const_add 1).pow 2)
    (pow_ne_zero _ hk) using 1
  · rfl
  · dsimp
    field_simp
    ring

theorem utility_deriv {c : ℝ} (hc : c ≠ 0) : HasDerivAt utility (marginalUtility c) c := by
  convert (hasDerivAt_id c).sub (hasDerivAt_inv hc) using 1
  · rfl
  · simp [marginalUtility, inv_pow]

theorem marginalUtility_deriv {c : ℝ} (hc : c ≠ 0) :
    HasDerivAt marginalUtility (-2 / c^3) c := by
  convert ((hasDerivAt_inv hc).pow 2).const_add 1 using 1
  · rfl
  · dsimp
    field_simp

theorem deriv_production {k : ℝ} (hk : 1 + k ≠ 0) : deriv production k = marginalProduct k :=
  (production_deriv hk).deriv

theorem deriv_utility {c : ℝ} (hc : c ≠ 0) : deriv utility c = marginalUtility c :=
  (utility_deriv hc).deriv

theorem production_continuous : ContinuousOn production (Ici 0) :=
  fun k hk => (production_deriv (by linarith [show 0 ≤ k from hk])).continuousAt.continuousWithinAt

theorem utility_continuous : ContinuousOn utility (Ioi 0) :=
  fun _ hc => (utility_deriv (ne_of_gt hc)).continuousAt.continuousWithinAt

theorem production_second {k : ℝ} (hk : 0 ≤ k) :
    HasDerivAt (deriv production) (-16 / (1 + k)^3) k := by
  apply (marginalProduct_deriv (by linarith)).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds (show k ≠ -1 by linarith)] with x hx
  exact deriv_production (by intro hh; apply hx; linarith)

theorem utility_second {c : ℝ} (hc : 0 < c) :
    HasDerivAt (deriv utility) (-2 / c^3) c := by
  apply (marginalUtility_deriv hc.ne').congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hc.ne'] with x hx
  exact deriv_utility hx

theorem production_strictConcave : StrictConcaveOn ℝ (Ici 0) production := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ici 0) production_continuous
  intro k hk
  change 0 ≤ k at hk
  change deriv (deriv production) k < 0
  rw [(production_second hk).deriv]
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

theorem utility_strictConcave : StrictConcaveOn ℝ (Ioi 0) utility := by
  apply strictConcaveOn_of_deriv2_neg' (convex_Ioi 0) utility_continuous
  intro c hc
  change 0 < c at hc
  change deriv (deriv utility) c < 0
  rw [(utility_second hc).deriv]
  exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

theorem marginalProduct_pos {k : ℝ} (hk : 0 ≤ k) : 0 < marginalProduct k := by
  dsimp [marginalProduct]
  positivity

theorem marginalUtility_pos (c : ℝ) : 0 < marginalUtility c := by
  dsimp [marginalUtility]
  positivity

theorem production_stationary : production 0 = 0 ∧ production 7 = 7 ∧
    production 1 = 4 ∧ marginalProduct 0 = 8 ∧ marginalProduct 1 = 2 := by
  norm_num [production, marginalProduct]

theorem capacity_for_each_dilution {m : ℝ} (hm : 0 < m) (hm8 : m < 8) :
    ∃ k, 0 < k ∧ production k = m * k := by
  refine ⟨8 / m - 1, ?_, ?_⟩
  · have hh : 1 < 8 / m := (lt_div_iff₀ hm).mpr (by simpa using hm8)
    linarith
  · dsimp [production]
    rw [show 1 + (8 / m - 1) = 8 / m by ring]
    field_simp

/-- The displayed appendix A2 scalar assumptions, together with the positive
discount bound, hold for the explicit economy. -/
theorem displayed_assumptions : production 0 = 0 ∧
    (∀ k, 0 ≤ k → 0 < deriv production k ∧ deriv (deriv production) k < 0) ∧
    (∀ m, 0 < m → m < deriv production 0 → ∃ k, 0 < k ∧ production k = m * k) ∧
    (∀ c, 0 < c → 0 < deriv utility c ∧ deriv (deriv utility) c < 0) ∧
    (0 < (1 : ℝ) ∧ 1 < deriv production 0 - 1) := by
  refine ⟨production_stationary.1, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [deriv_production (by linarith), (production_second hk).deriv]
    exact ⟨marginalProduct_pos hk, div_neg_of_neg_of_pos (by norm_num) (by positivity)⟩
  · intro m hm hm8
    rw [deriv_production (by norm_num), production_stationary.2.2.2.1] at hm8
    exact capacity_for_each_dilution hm hm8
  · intro c hc
    rw [deriv_utility hc.ne', (utility_second hc).deriv]
    exact ⟨marginalUtility_pos c, div_neg_of_neg_of_pos (by norm_num) (by positivity)⟩
  · rw [deriv_production (by norm_num), production_stationary.2.2.2.1]
    norm_num

theorem marginalProduct_limit : Tendsto marginalProduct atTop (𝓝 0) := by
  change Tendsto (fun k : ℝ => 8 / (1 + k)^2) atTop (𝓝 0)
  have h := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).comp
    (tendsto_atTop_add_const_left atTop 1 tendsto_id)).pow 2
  convert h.const_mul 8 using 1 <;> simp [div_eq_mul_inv, inv_pow]

theorem marginalUtility_limit : Tendsto marginalUtility atTop (𝓝 1) := by
  change Tendsto (fun c : ℝ => 1 + c⁻¹ ^ 2) atTop (𝓝 1)
  simpa using ((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2).const_add 1

theorem utility_at_zero : Tendsto utility (𝓝[>] (0 : ℝ)) atBot := by
  apply tendsto_atBot.2
  intro b
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num),
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).eventually (eventually_ge_atTop (1 - b))] with c hc hi
  dsimp [utility]
  linarith [hc.2]

theorem hamiltonian_at_capacity {c : ℝ} (hc : 0 < c) :
    utility c + marginalUtility c * (production 7 - 7 - c) = -2 / c := by
  norm_num [utility, marginalUtility, production]
  field_simp
  ring

theorem reciprocal_bound {c : ℝ} (hc : 0 < c) : 0 ≤ 2 / c ∧ 2 / c ≤ marginalUtility c := by
  refine ⟨(div_pos (by norm_num) hc).le, ?_⟩
  dsimp [marginalUtility]
  rw [div_eq_mul_inv]
  nlinarith [sq_nonneg (c⁻¹ - 1)]

theorem production_capacity {k : ℝ} (hk : 7 ≤ k) : production k ≤ 1 * k := by
  rw [production_formula (by linarith), one_mul]
  apply (div_le_iff₀ (by linarith : 0 < 1 + k)).mpr
  nlinarith [mul_nonneg (show 0 ≤ k by linarith) (sub_nonneg.mpr hk)]

end RamseyCassKoopmans.KoopmansBoundary


/-! # A positive-welfare feasible competitor from the capacity stock -/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans.KoopmansBoundary

noncomputable def competitorCapital (t : ℝ) : ℝ := 1 + 6 * discount 1 t
noncomputable def competitorConsumption (t : ℝ) : ℝ := production (competitorCapital t) - 1

theorem competitorCapital_ge_one (t : ℝ) : 1 ≤ competitorCapital t := by
  dsimp [competitorCapital]
  linarith [discount_pos 1 t]

theorem competitorCapital_deriv (t : ℝ) :
    HasDerivAt competitorCapital (1 - competitorCapital t) t := by
  convert ((hasDerivAt_discount 1 t).const_mul 6).const_add 1 using 1
  · rfl
  · dsimp [competitorCapital]
    ring

theorem competitorConsumption_bounds (t : ℝ) :
    3 ≤ competitorConsumption t ∧ competitorConsumption t ≤ 7 := by
  have hk := competitorCapital_ge_one t
  have hden : 0 < 1 + competitorCapital t := by linarith
  have hi : 8 / (1 + competitorCapital t) ≤ 4 :=
    (div_le_iff₀ hden).mpr (by linarith)
  dsimp [competitorConsumption, production]
  constructor
  · linarith
  · linarith [div_nonneg (show (0 : ℝ) ≤ 8 by norm_num) hden.le]

theorem competitorConsumption_continuous : Continuous competitorConsumption := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (((production_deriv (by linarith [competitorCapital_ge_one t])).comp t
    (competitorCapital_deriv t)).sub_const 1).continuousAt

noncomputable def competitor : FeasiblePath production 1 where
  capital := competitorCapital
  consumption := competitorConsumption
  investment := fun _ => 1
  capital_nonneg := fun t _ => le_trans (by norm_num) (competitorCapital_ge_one t)
  consumption_pos := fun t _ => lt_of_lt_of_le (by norm_num) (competitorConsumption_bounds t).1
  consumption_continuous := competitorConsumption_continuous.continuousOn
  investment_continuous := continuousOn_const
  resource := fun _ _ => sub_add_cancel _ _
  dynamics := fun t _ => by simpa only [one_mul] using competitorCapital_deriv t

theorem competitor_initial : competitor.capital 0 = 7 := by
  norm_num [competitor, competitorCapital, discount]

theorem competitor_felicity_bounds (t : ℝ) :
    8 / 3 ≤ utility (competitor.consumption t) ∧ utility (competitor.consumption t) ≤ 7 := by
  have hc := competitorConsumption_bounds t
  have hcpos : 0 < competitorConsumption t := by linarith
  have hi : (competitorConsumption t)⁻¹ ≤ 1 / 3 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hcpos).mpr (by linarith)
  change 8 / 3 ≤ competitorConsumption t - (competitorConsumption t)⁻¹ ∧
    competitorConsumption t - (competitorConsumption t)⁻¹ ≤ 7
  constructor
  · linarith
  · linarith [inv_pos.mpr hcpos]

theorem competitor_welfare : ∃ J, HasWelfare utility (discount 1) competitor.consumption J ∧
    8 / 3 ≤ J := by
  have hcont : ContinuousOn (fun t => utility (competitor.consumption t)) (Ici 0) :=
    utility_continuous.comp competitor.consumption_continuous competitor.consumption_pos
  obtain ⟨J, hJ⟩ := exists_hasWelfare_of_nonneg_bounded utility competitor.consumption
    (d := 1) (M := 7) (by norm_num) hcont (fun t _ =>
      ⟨le_trans (by norm_num) (competitor_felicity_bounds t).1, (competitor_felicity_bounds t).2⟩)
  refine ⟨J, hJ, ?_⟩
  have hbound : ∀ T, 0 ≤ T → (8 / 3) * (1 - discount 1 T) ≤
      welfare utility (discount 1) competitor.consumption T := by
    intro T hT
    have hi : IntervalIntegrable (fun t => discount 1 t * utility (competitor.consumption t))
        volume 0 T := (((discount_continuous 1).continuousOn.mul hcont).mono
          (fun _ ht => ht.1)).intervalIntegrable_of_Icc hT
    calc
      _ = ∫ t in (0 : ℝ)..T, (8 / 3) * discount 1 t := by
        rw [intervalIntegral.integral_const_mul, ClosedForm.integral_discount 1 T (by norm_num)]
        simp
      _ ≤ _ := by
        apply intervalIntegral.integral_mono_on hT
          ((continuous_const.mul (discount_continuous 1)).intervalIntegrable 0 T) hi
        intro t _
        change (8 / 3) * discount 1 t ≤ discount 1 t * utility (competitor.consumption t)
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left
          (competitor_felicity_bounds t).1 (discount_pos 1 t).le
  have hl : Tendsto (fun T => (8 / 3) * (1 - discount 1 T)) atTop (𝓝 (8 / 3)) := by
    have hd := Terminal.discounted_price_tendsto_zero (mu := fun _ => (1 : ℝ))
      (d := 1) (by norm_num) tendsto_const_nhds
    simp only [mul_one] at hd
    simpa [discount] using ((tendsto_const_nhds (x := (1 : ℝ))).sub hd).const_mul (8 / 3 : ℝ)
  exact le_of_tendsto_of_tendsto hl hJ (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact hbound T hT)

end RamseyCassKoopmans.KoopmansBoundary


/-! # No regular convergent Euler path from capacity in the boundary example

The conclusion does not assume consumption convergence or either monotonicity. A hypothetical
convergent Euler path would have negative welfare by the Hamiltonian identity,
but the verification theorem would make it dominate an explicit competitor whose
welfare is at least 8/3. Both welfare limits are proved, not assumed.

This rules out the regular convergent Euler characterization in this economy.
It does not, by itself, claim nonexistence in every possible class of generalized
or impulsive controls.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.KoopmansBoundary

theorem production_prime_continuous : ContinuousOn (deriv production) (Ioi 0) :=
  fun _ hk => (production_second hk.le).continuousAt.continuousWithinAt

theorem utility_prime_continuous : ContinuousOn (deriv utility) (Ioi 0) :=
  fun _ hc => (utility_second hc).continuousAt.continuousWithinAt

theorem production_prime_limit : Tendsto (deriv production) atTop (𝓝 0) := by
  apply marginalProduct_limit.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with k hk
  exact (deriv_production (by linarith)).symm

theorem capital_positive (a : FeasiblePath production 1) :
    ∀ t, 0 ≤ t → 0 < a.capital t := by
  intro t ht
  rcases (a.capital_nonneg t ht).lt_or_eq with hp | heq
  · exact hp
  · have hz : a.investment t < 0 := by
      have hr := a.resource t ht
      rw [← heq, production_stationary.1] at hr
      linarith [a.consumption_pos t ht]
    have hdneg : a.investment t - 1 * a.capital t < 0 := by rw [← heq]; linarith
    have hneg := ODE.eventually_lt_right_of_deriv_neg (a.dynamics t ht) hdneg
    have hright : ∀ᶠ u in 𝓝[>] t, t < u := self_mem_nhdsWithin
    obtain ⟨u, hu, htu⟩ := (hneg.and hright).exists
    linarith [a.capital_nonneg u (ht.trans htu.le)]

theorem no_convergent_euler_path (a : FeasiblePath production 1) (cd : ℝ → ℝ)
    (hinit : a.capital 0 = 7)
    (hc : ∀ t, 0 ≤ t → HasDerivAt a.consumption (cd t) t)
    (heuler : ∀ t, 0 ≤ t →
      deriv (deriv utility) (a.consumption t) * cd t =
        deriv utility (a.consumption t) * (1 + 1 - deriv production (a.capital t)))
    (hklim : Tendsto a.capital atTop (𝓝 1)) : False := by
  have hkpos := capital_positive a
  let g : ℝ → ℝ := fun k => production k - k
  let q : ℝ → ℝ := fun t => deriv utility (a.consumption t)
  let H := currentHamiltonian utility g a.capital a.consumption q
  let F : ℝ → ℝ := fun t => discount 1 t * H t
  let P : ℝ → ℝ := fun t => discount 1 t * q t
  have hq : ∀ t, 0 ≤ t → HasDerivAt q
      ((1 - (deriv production (a.capital t) - 1)) * q t) t := by
    intro t ht
    have h := euler_implies_current_value_costate (hc t ht)
      ((utility_second (a.consumption_pos t ht)).differentiableAt.hasDerivAt) (heuler t ht)
    convert h using 1
    dsimp [q]
    ring
  have hF : ∀ t, 0 ≤ t → HasDerivAt F (-(discount 1 t * utility (a.consumption t))) t := by
    intro t ht
    have hU := (utility_deriv (a.consumption_pos t ht).ne').differentiableAt.hasDerivAt
    have hg : HasDerivAt g (deriv production (a.capital t) - 1) (a.capital t) :=
      ((production_deriv (by linarith [hkpos t ht])).differentiableAt.hasDerivAt).sub
        (hasDerivAt_id _)
    have hk : HasDerivAt a.capital (g (a.capital t) - a.consumption t) t := by
      convert a.dynamics t ht using 1
      dsimp [g]
      linarith [a.resource t ht]
    simpa only [neg_one_mul] using hasDerivAt_discountedHamiltonian hU hg hk (hc t ht) (hq t ht)
  have hqpos : ∀ t, 0 ≤ t → 0 < q t := by
    intro t ht
    dsimp [q]
    rw [deriv_utility (a.consumption_pos t ht).ne']
    exact marginalUtility_pos _
  have hPD : ∀ t, 0 ≤ t → HasDerivAt P ((1 - deriv production (a.capital t)) * P t) t := by
    intro t ht
    convert (hasDerivAt_discount 1 t).mul (hq t ht) using 1
    dsimp [P]
    ring
  have hcoeff : Tendsto (fun t => 1 - deriv production (a.capital t)) atTop (𝓝 (-1)) := by
    have hh := (production_prime_continuous.continuousAt
      (isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1))).tendsto.comp hklim
    rw [deriv_production (by norm_num), production_stationary.2.2.2.2] at hh
    convert (tendsto_const_nhds (x := (1 : ℝ))).sub hh using 1
    · rfl
    · norm_num
  have hPn : ∀ t, 0 ≤ t → 0 ≤ P t :=
    fun t ht => (mul_pos (discount_pos 1 t) (hqpos t ht)).le
  have hprice : Tendsto P atTop (𝓝 0) :=
    ODE.tendsto_zero_of_negative_logarithmic_derivative hPD hPn hcoeff (by norm_num)
  have hgL : Tendsto (fun t => g (a.capital t)) atTop (𝓝 3) := by
    have h :=
      ((production_deriv (by norm_num : (1 : ℝ) + 1 ≠ 0)).continuousAt.tendsto.comp hklim).sub hklim
    convert h using 1
    · rfl
    · norm_num [production]
  have hR : Tendsto (fun t => discount 1 t * (2 / a.consumption t)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hprice
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact mul_nonneg (discount_pos 1 t).le (reciprocal_bound (a.consumption_pos t ht)).1
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      change discount 1 t * (2 / a.consumption t) ≤ discount 1 t * deriv utility (a.consumption t)
      rw [deriv_utility (a.consumption_pos t ht).ne']
      exact mul_le_mul_of_nonneg_left (reciprocal_bound (a.consumption_pos t ht)).2
        (discount_pos 1 t).le
  have hFL : Tendsto F atTop (𝓝 0) := by
    have hh := (hprice.mul hgL).sub hR
    simp only [zero_mul, sub_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hcap := hamiltonian_at_capacity (a.consumption_pos t ht)
    rw [production_stationary.2.1, sub_self, zero_sub] at hcap
    dsimp [P, F, H, currentHamiltonian, q]
    rw [deriv_utility (a.consumption_pos t ht).ne']
    have hscaled := congrArg (fun z : ℝ => discount 1 t * z) hcap
    rw [neg_div] at hscaled
    nlinarith [hscaled]
  have hJ := hasWelfare_of_primitive
    (utility_continuous.comp a.consumption_continuous a.consumption_pos) hF hFL
  have hF0 : F 0 = -2 / a.consumption 0 := by
    dsimp [F, H, currentHamiltonian, g, q]
    rw [hinit, deriv_utility (a.consumption_pos 0 le_rfl).ne']
    norm_num [discount]
    exact hamiltonian_at_capacity (a.consumption_pos 0 le_rfl)
  obtain ⟨Jb, hb, hJb⟩ := competitor_welfare
  have hcostate : ∀ t, 0 ≤ t → HasDerivAt q
      ((1 + 1) * q t - deriv utility (a.consumption t) * deriv production (a.capital t)) t := by
    intro t ht
    convert hq t ht using 1
    dsimp [q]
    ring
  let v := cassSupportingPrices production utility q 1 1 a
    production_strictConcave.concaveOn utility_strictConcave.concaveOn utility_continuous
    (fun k hk => (production_deriv (by linarith)).differentiableAt)
    (fun _ hc => (utility_deriv hc.ne').differentiableAt)
    production_prime_continuous utility_prime_continuous hkpos
    (fun t ht => (hqpos t ht).le) hcostate
  have hoptimal := infinite_horizon_optimality_of_bounded_capital v competitor
    (allocation_of_interior v (fun _ _ => rfl)) (hinit.trans competitor_initial.symm) hJ hb hprice
    (a.capital_le_capacity (fun _ hk => production_capacity hk) hinit.le)
    (competitor.capital_le_capacity (fun _ hk => production_capacity hk) competitor_initial.le)
  rw [hF0] at hoptimal
  have hneg : -2 / a.consumption 0 < 0 :=
    div_neg_of_neg_of_pos (by norm_num) (a.consumption_pos 0 le_rfl)
  linarith

end RamseyCassKoopmans.KoopmansBoundary

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# Certified Cass optima, time shifts, and time consistency

`CassPrimitives` bundles the Inada and curvature assumptions of
`cass_general_dynamic`. `CassCertificate` records a current-value costate with
the wedge, complementary slackness and transversality conditions. We prove:

* `exists_certified`: from every positive stock the constructed optimum carries
  a certificate;
* `CassCertificate.isCassOptimal`, `CassCertificate.eq_of_isCassOptimal`: a
  certificate makes a path optimal, and every optimum with the same initial stock
  coincides with it;
* `FeasiblePath.shift`, `CassCertificate.shift`: the tail of a certified path
  after any date is a certified path from the stock it has reached;
* `CassCertificate.dynamics`: every certified path converges monotonically to the
  steady state (transferred from the construction by uniqueness);
* `CassCertificate.tail_eq`: time consistency, the tail of an optimum is the
  optimum from the stock reached.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

/-- The primitive assumptions of `cass_general_dynamic`. -/
structure CassPrimitives (f U : ℝ → ℝ) (d m : ℝ) : Prop where
  d_pos : 0 < d
  m_pos : 0 < m
  f_conc : StrictConcaveOn ℝ (Ici 0) f
  f_zero : f 0 = 0
  f_diff : ∀ k, 0 < k → DifferentiableAt ℝ f k
  f_prime_cont : ContinuousOn (deriv f) (Ioi 0)
  f_prime_pos : ∀ k, 0 < k → 0 < deriv f k
  f_second : ∀ k, 0 < k → DifferentiableAt ℝ (deriv f) k
  f_second_cont : ContinuousOn (deriv (deriv f)) (Ioi 0)
  f_inada0 : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop
  f_inadaTop : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))
  U_conc : StrictConcaveOn ℝ (Ioi 0) U
  U_diff : ∀ c, 0 < c → DifferentiableAt ℝ U c
  U_prime_pos : ∀ c, 0 < c → 0 < deriv U c
  U_second : ∀ c, 0 < c → DifferentiableAt ℝ (deriv U) c
  U_second_cont : ContinuousOn (deriv (deriv U)) (Ioi 0)
  U_second_neg : ∀ c, 0 < c → deriv (deriv U) c < 0
  U_inada0 : Tendsto (deriv U) (𝓝[>] (0 : ℝ)) atTop

theorem CassPrimitives.U_cont (P : CassPrimitives f U d m) : ContinuousOn U (Ioi 0) :=
  fun c hc => (P.U_diff c hc).continuousAt.continuousWithinAt

theorem CassPrimitives.U_prime_cont (P : CassPrimitives f U d m) :
    ContinuousOn (deriv U) (Ioi 0) :=
  fun c hc => (P.U_second c hc).continuousAt.continuousWithinAt

theorem CassPrimitives.existsUnique_steady (P : CassPrimitives f U d m) :
    ∃! k : ℝ, 0 < k ∧ deriv f k = d + m :=
  existsUnique_stationary_capital_of_inada f d m (add_pos P.d_pos P.m_pos) P.f_conc
    P.f_diff P.f_prime_cont P.f_inada0 P.f_inadaTop

/-- The modified-Golden-Rule steady state, `f'(k*) = d + m`. -/
noncomputable def cassSteady (P : CassPrimitives f U d m) : ℝ :=
  Classical.choose P.existsUnique_steady.exists

theorem cassSteady_spec (P : CassPrimitives f U d m) :
    0 < cassSteady P ∧ deriv f (cassSteady P) = d + m :=
  Classical.choose_spec P.existsUnique_steady.exists

theorem cassSteady_eq (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k)
    (he : deriv f k = d + m) : cassSteady P = k :=
  P.existsUnique_steady.unique (cassSteady_spec P) ⟨hk, he⟩

theorem CassPrimitives.exists_capacity (P : CassPrimitives f U d m) (k0 : ℝ) :
    ∃ K, k0 ≤ K ∧ ∀ k, K ≤ k → f k ≤ m * k :=
  exists_capacity_of_marginal_tendsto_zero f P.m_pos P.f_conc.concaveOn P.f_diff
    (fun k hk => (P.f_prime_pos k hk).le) P.f_inadaTop

/-- A current-value costate certifying a Cass path: the costate equation, the
investment wedge, complementary slackness, transversality and finite welfare. -/
structure CassCertificate (f U : ℝ → ℝ) (d m : ℝ) (a : FeasiblePath f m) (q : ℝ → ℝ) : Prop where
  capital_pos : ∀ t, 0 ≤ t → 0 < a.capital t
  investment_nonneg : a.NonnegativeInvestment
  price_nonneg : ∀ t, 0 ≤ t → 0 ≤ q t
  costate : ∀ t, 0 ≤ t → HasDerivAt q
    ((d + m) * q t - deriv U (a.consumption t) * deriv f (a.capital t)) t
  wedge : ∀ t, 0 ≤ t → q t ≤ deriv U (a.consumption t)
  slack : ∀ t, 0 ≤ t → (q t - deriv U (a.consumption t)) * a.investment t = 0
  transversality : Tendsto (fun t => discount d t * q t) atTop (𝓝 0)
  welfare : ∃ J, HasWelfare U (discount d) a.consumption J

/-- From every positive stock, the constructed optimum carries a certificate. -/
theorem exists_certified (P : CassPrimitives f U d m) {k0 : ℝ} (hk0 : 0 < k0) :
    ∃ a : FeasiblePath f m, ∃ q : ℝ → ℝ, a.capital 0 = k0 ∧ CassCertificate f U d m a q := by
  obtain ⟨ks, _, _, ⟨D⟩⟩ := exists_cass_data_of_inada f U d m k0 P.d_pos P.m_pos hk0
    P.f_conc P.f_zero P.f_diff P.f_prime_cont P.f_prime_pos P.f_second P.f_second_cont
    P.f_inada0 P.f_inadaTop P.U_conc P.U_diff P.U_prime_pos P.U_second P.U_second_cont
    P.U_second_neg P.U_inada0
  let p := D.phase
  obtain ⟨_, _, hCLip, _⟩ := D.demand_bounded
  obtain ⟨_, _, hFLip, _⟩ := D.production_bounded
  obtain ⟨γ, h0, hd, hclipq, hlim, -, -, -⟩ := p.exists_convergent_trajectory
    D.bounded D.net_mono D.consumption_mem D.net_gap D.time_nonneg D.price_large
    D.time_large D.initial_mem
  have hclip := fun t ht => (hclipq t ht).1
  have hmul : p.μ = deriv U := D.marginalUtility_eq
  have hmp : p.mp = deriv p.f := by rw [D.production_eq]; exact D.marginalProduct_eq
  have hres : ∃ a : FeasiblePath p.f p.m, ∃ q : ℝ → ℝ, a.capital 0 = k0 ∧
      CassCertificate p.f U p.d p.m a q := by
    let a := p.feasiblePath γ hCLip.continuous hFLip.continuous hd hclip
    have hcostate := p.path_costate hd hclip
    rw [hmp, hmul] at hcostate
    have hwedge := p.path_wedge_slack hclip
    rw [hmul] at hwedge
    refine ⟨a, fun t => (γ t).2, h0, ⟨p.path_capital_pos γ hclip,
      fun t _ => cass_investment_nonneg p.f p.C (p.point (γ t)), ?_, hcostate,
      fun t ht => (hwedge t ht).1, fun t ht => (hwedge t ht).2,
      Terminal.discounted_price_tendsto_zero p.d_pos hlim.snd_nhds, ?_⟩⟩
    · intro t ht
      have hq := congrArg Prod.snd (hclip t ht)
      exact hq ▸ (p.price_mem (γ t).2).1
    · exact exists_hasWelfare_of_compact_consumption U a.consumption p.d_pos p.ca_le_cb
        (P.U_cont.mono (fun _ hx => p.ca_pos.trans_le hx.1)) a.consumption_continuous
        (fun t _ => p.consumption_mem (γ t))
  rw [D.production_eq, D.dilution_eq, D.discount_eq] at hres
  exact hres

/-- A certificate makes the path optimal in the library's Cass class. -/
theorem CassCertificate.isCassOptimal (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) {J : ℝ}
    (hJ : HasWelfare U (discount d) a.consumption J) : IsCassOptimal U d a J := by
  obtain ⟨K, hK, hcap⟩ := P.exists_capacity (a.capital 0)
  exact cass_certificate_is_optimal f U q d m K J a P.f_conc.concaveOn P.U_conc.concaveOn
    P.U_cont P.f_diff P.U_diff P.f_prime_cont P.U_prime_cont hc.capital_pos hc.price_nonneg
    hc.costate hc.wedge hc.slack hc.investment_nonneg hcap hK hJ hc.transversality

/-- Every optimum with the same initial stock coincides with a certified path. -/
theorem CassCertificate.eq_of_isCassOptimal (P : CassPrimitives f U d m)
    {a b : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) {Ja Jb : ℝ}
    (ha : HasWelfare U (discount d) a.consumption Ja) (hb : IsCassOptimal U d b Jb)
    (hi : a.capital 0 = b.capital 0) :
    Jb = Ja ∧ ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
      b.consumption t = a.consumption t ∧ b.investment t = a.investment t := by
  obtain ⟨K, hK, hcap⟩ := P.exists_capacity (a.capital 0)
  have hopt := hc.isCassOptimal P ha
  have heq : Jb = Ja := le_antisymm (hopt.2.2 b hb.1 hi Jb hb.2.1)
    (hb.2.2 a hc.investment_nonneg hi.symm Ja ha)
  refine ⟨heq, cass_certificate_unique f U q d m K Ja Jb a b P.f_conc P.U_conc P.U_cont
    P.f_diff P.U_diff P.f_prime_cont P.U_prime_cont hc.capital_pos ?_ hc.costate hc.wedge
    hc.slack hb.1 hi hcap hK ha hb.2.1 hc.transversality heq⟩
  exact fun t ht => P.U_prime_pos _ (a.consumption_pos t ht)

/-- Two certified paths from the same stock coincide at every nonnegative time. -/
theorem CassCertificate.eq (P : CassPrimitives f U d m) {a b : FeasiblePath f m}
    {qa qb : ℝ → ℝ} (ha : CassCertificate f U d m a qa) (hb : CassCertificate f U d m b qb)
    (hi : a.capital 0 = b.capital 0) :
    ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
      b.consumption t = a.consumption t ∧ b.investment t = a.investment t := by
  obtain ⟨Ja, hJa⟩ := ha.welfare
  obtain ⟨Jb, hJb⟩ := hb.welfare
  exact (ha.eq_of_isCassOptimal P hJa (hb.isCassOptimal P hJb) hi).2

/-- The path from date `T` on, re-indexed to start at time zero. -/
noncomputable def FeasiblePath.shift (a : FeasiblePath f m) (T : ℝ) (hT : 0 ≤ T) :
    FeasiblePath f m where
  capital := fun t => a.capital (T + t)
  consumption := fun t => a.consumption (T + t)
  investment := fun t => a.investment (T + t)
  capital_nonneg := fun _ ht => a.capital_nonneg _ (add_nonneg hT ht)
  consumption_pos := fun _ ht => a.consumption_pos _ (add_nonneg hT ht)
  consumption_continuous := a.consumption_continuous.comp
    (continuous_const.add continuous_id).continuousOn
    (fun _ ht => add_nonneg hT (mem_Ici.mp ht))
  investment_continuous := a.investment_continuous.comp
    (continuous_const.add continuous_id).continuousOn
    (fun _ ht => add_nonneg hT (mem_Ici.mp ht))
  resource := fun _ ht => a.resource _ (add_nonneg hT ht)
  dynamics := fun t ht => (a.dynamics _ (add_nonneg hT ht)).comp_const_add T t

@[simp] theorem FeasiblePath.shift_capital (a : FeasiblePath f m) {T : ℝ} (hT : 0 ≤ T)
    (t : ℝ) : (a.shift T hT).capital t = a.capital (T + t) := rfl

@[simp] theorem FeasiblePath.shift_consumption (a : FeasiblePath f m) {T : ℝ} (hT : 0 ≤ T)
    (t : ℝ) : (a.shift T hT).consumption t = a.consumption (T + t) := rfl

@[simp] theorem FeasiblePath.shift_investment (a : FeasiblePath f m) {T : ℝ} (hT : 0 ≤ T)
    (t : ℝ) : (a.shift T hT).investment t = a.investment (T + t) := rfl

/-- Welfare of the tail: `W_tail = (J - W(T)) / discount T`. -/
theorem hasWelfare_shift (P : CassPrimitives f U d m) (a : FeasiblePath f m) {T J : ℝ}
    (hT : 0 ≤ T) (hJ : HasWelfare U (discount d) a.consumption J) :
    HasWelfare U (discount d) (a.shift T hT).consumption
      ((J - welfare U (discount d) a.consumption T) / discount d T) := by
  have hcont : ContinuousOn (fun t => discount d t * U (a.consumption t)) (Ici 0) :=
    (discount_continuous d).continuousOn.mul
      (P.U_cont.comp a.consumption_continuous (fun t ht => a.consumption_pos t ht))
  have hsplit : ∀ s, 0 ≤ s → welfare U (discount d) (a.shift T hT).consumption s =
      (welfare U (discount d) a.consumption (T + s) -
        welfare U (discount d) a.consumption T) / discount d T := by
    intro s hs
    have h := welfare_of_tail_eq (tail := (a.shift T hT).consumption) (T := T + s) hT
      (by linarith) hcont (fun t ht => by
        simp only [FeasiblePath.shift_consumption]
        congr 1
        ring)
    rw [show T + s - T = s by ring] at h
    rw [h]
    field_simp [(discount_pos d T).ne']
    ring
  have hlim : Tendsto (fun s => (welfare U (discount d) a.consumption (T + s) -
      welfare U (discount d) a.consumption T) / discount d T) atTop
      (𝓝 ((J - welfare U (discount d) a.consumption T) / discount d T)) :=
    ((hJ.comp (tendsto_atTop_add_const_left atTop T tendsto_id)).sub_const _).div_const _
  exact hlim.congr' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact (hsplit s hs).symm)

/-- The tail of a certified path is certified from the stock it has reached. -/
theorem CassCertificate.shift (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) {T : ℝ} (hT : 0 ≤ T) :
    CassCertificate f U d m (a.shift T hT) (fun t => q (T + t)) := by
  obtain ⟨J, hJ⟩ := hc.welfare
  refine ⟨fun t ht => hc.capital_pos _ (add_nonneg hT ht),
    fun t ht => hc.investment_nonneg _ (add_nonneg hT ht),
    fun t ht => hc.price_nonneg _ (add_nonneg hT ht),
    fun t ht => (hc.costate _ (add_nonneg hT ht)).comp_const_add T t,
    fun t ht => hc.wedge _ (add_nonneg hT ht), fun t ht => hc.slack _ (add_nonneg hT ht),
    ?_, ⟨_, hasWelfare_shift P a hT hJ⟩⟩
  have h := (hc.transversality.comp (tendsto_atTop_add_const_left atTop T tendsto_id)).const_mul
    (Real.exp (d * T))
  rw [mul_zero] at h
  refine h.congr (fun t => ?_)
  simp only [Function.comp_apply, discount, id]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Every certified path converges monotonically to the steady state; the facts are
transferred from the construction of `cass_general_dynamic` by uniqueness. -/
theorem CassCertificate.dynamics (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) :
    Tendsto a.capital atTop (𝓝 (cassSteady P)) ∧
      Tendsto a.consumption atTop
        (𝓝 (f (cassSteady P) - m * cassSteady P)) ∧
      (a.capital 0 < cassSteady P →
        StrictMonoOn a.capital (Ici 0) ∧ StrictMonoOn a.consumption (Ici 0)) ∧
      (cassSteady P < a.capital 0 →
        StrictAntiOn a.capital (Ici 0) ∧ StrictAntiOn a.consumption (Ici 0)) ∧
      (a.capital 0 = cassSteady P → ∀ t, 0 ≤ t → a.capital t = cassSteady P ∧
        a.consumption t = f (cassSteady P) - m * cassSteady P) := by
  obtain ⟨ks, hks, hstat, b, Jb, hb0, hbopt, hbk, hbc, hbmk, hbak, hbmc, hbac, -, hbconst,
    -, -, -⟩ := cass_general_dynamic f U d m (a.capital 0) P.d_pos P.m_pos (hc.capital_pos 0 le_rfl)
    P.f_conc P.f_zero P.f_diff P.f_prime_cont P.f_prime_pos P.f_second P.f_second_cont
    P.f_inada0 P.f_inadaTop P.U_conc P.U_diff P.U_prime_pos P.U_second P.U_second_cont
    P.U_second_neg P.U_inada0
  have hks' : cassSteady P = ks := cassSteady_eq P hks hstat
  obtain ⟨Ja, hJa⟩ := hc.welfare
  have heq := (hc.eq_of_isCassOptimal P hJa hbopt hb0.symm).2
  have hk : EqOn a.capital b.capital (Ici 0) := fun t ht => ((heq t ht).1).symm
  have hcon : EqOn a.consumption b.consumption (Ici 0) := fun t ht => ((heq t ht).2.1).symm
  have hev : ∀ᶠ t in atTop, t ∈ Ici (0 : ℝ) := eventually_ge_atTop 0
  rw [hks']
  refine ⟨hbk.congr' (hev.mono fun t ht => (hk ht).symm),
    hbc.congr' (hev.mono fun t ht => (hcon ht).symm), fun h => ?_, fun h => ?_, fun h t ht => ?_⟩
  · exact ⟨(hbmk h).congr hk.symm, (hbmc h).congr hcon.symm⟩
  · exact ⟨(hbak h).congr hk.symm, (hbac h).congr hcon.symm⟩
  · obtain ⟨h1, h2, -⟩ := hbconst h t
    exact ⟨(hk ht).trans h1, (hcon ht).trans h2⟩

/-- Below the steady state a certified path stays strictly below it; above, strictly
above. -/
theorem CassCertificate.capital_bounds (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) :
    (a.capital 0 < cassSteady P → ∀ t, 0 ≤ t → a.capital t < cassSteady P ∧
      a.consumption t < f (cassSteady P) - m * cassSteady P) ∧
    (cassSteady P < a.capital 0 → ∀ t, 0 ≤ t → cassSteady P < a.capital t ∧
      f (cassSteady P) - m * cassSteady P < a.consumption t) := by
  obtain ⟨hk, hcon, hbelow, habove, -⟩ := hc.dynamics P
  have hev : ∀ t : ℝ, 0 ≤ t → ∀ᶠ s : ℝ in atTop, t + 1 ≤ s := fun t _ =>
    eventually_ge_atTop (t + 1)
  have hm1 : ∀ t, 0 ≤ t → t + 1 ∈ Ici (0 : ℝ) := fun t ht => by
    simp only [mem_Ici]; linarith
  have hms : ∀ t s : ℝ, 0 ≤ t → t + 1 ≤ s → s ∈ Ici (0 : ℝ) := fun t s ht hs => by
    simp only [mem_Ici]; linarith
  have hlt : ∀ t : ℝ, t < t + 1 := fun t => by linarith
  refine ⟨fun h t ht => ⟨?_, ?_⟩, fun h t ht => ⟨?_, ?_⟩⟩
  · have hmono := (hbelow h).1
    exact (hmono (show t ∈ Ici 0 from ht) (hm1 t ht) (hlt t)).trans_le (ge_of_tendsto hk
      ((hev t ht).mono fun s hs => hmono.monotoneOn (hm1 t ht) (hms t s ht hs) hs))
  · have hmono := (hbelow h).2
    exact (hmono (show t ∈ Ici 0 from ht) (hm1 t ht) (hlt t)).trans_le (ge_of_tendsto hcon
      ((hev t ht).mono fun s hs => hmono.monotoneOn (hm1 t ht) (hms t s ht hs) hs))
  · have hanti := (habove h).1
    exact lt_of_le_of_lt (le_of_tendsto hk ((hev t ht).mono fun s hs =>
      hanti.antitoneOn (hm1 t ht) (hms t s ht hs) hs))
      (hanti (show t ∈ Ici 0 from ht) (hm1 t ht) (hlt t))
  · have hanti := (habove h).2
    exact lt_of_le_of_lt (le_of_tendsto hcon ((hev t ht).mono fun s hs =>
      hanti.antitoneOn (hm1 t ht) (hms t s ht hs) hs))
      (hanti (show t ∈ Ici 0 from ht) (hm1 t ht) (hlt t))

end RamseyCassKoopmans

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# The Cass policy function, non-crossing paths, and absolute convergence

The optimal consumption policy `policy P k` is initial consumption on the unique
optimum from `k`. By time consistency (`consumption_eq_policy`) every optimal path
satisfies `c(t) = policy P (k(t))`: the saddle path is the graph of the policy.

Below the steady state every optimal path passes through every higher stock, so
all optimal paths from stocks in `(0, k*)` are time translates of one another
(`exists_shift_of_lt`); the same holds above `k*`. Consequences:

* `policy_strictMono`: consumption is strictly increasing in capital;
* `capital_lt_of_lt`, `consumption_lt_of_lt`: optimal paths of identical economies
  never cross, and the poorer economy consumes strictly less at every date;
* `absolute_convergence`: identical economies converge to each other in capital,
  consumption, and the capital ratio.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

/-- The steady-state consumption `c* = f(k*) - m k*`. -/
noncomputable def cassSteadyConsumption (P : CassPrimitives f U d m) : ℝ :=
  f (cassSteady P) - m * cassSteady P

/-- The certified optimum from a positive stock. -/
noncomputable def optimalPath (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k) :
    FeasiblePath f m :=
  Classical.choose (exists_certified P hk)

theorem optimalPath_spec (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k) :
    ∃ q, (optimalPath P hk).capital 0 = k ∧ CassCertificate f U d m (optimalPath P hk) q :=
  Classical.choose_spec (exists_certified P hk)

/-- Optimal consumption as a function of current capital. -/
noncomputable def policy (P : CassPrimitives f U d m) (k : ℝ) : ℝ :=
  if hk : 0 < k then (optimalPath P hk).consumption 0 else 0

/-- Time consistency: along any certified path, consumption is the policy
evaluated at current capital. -/
theorem consumption_eq_policy (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) {t : ℝ} (ht : 0 ≤ t) :
    a.consumption t = policy P (a.capital t) := by
  have hkt := hc.capital_pos t ht
  obtain ⟨qo, ho0, hoc⟩ := optimalPath_spec P hkt
  have hs := hc.shift P ht
  have heq := (hoc.eq P hs (by simp only [FeasiblePath.shift_capital, add_zero]; exact ho0))
    0 le_rfl
  simp only [policy, hkt, ↓reduceDIte]
  simpa only [FeasiblePath.shift_consumption, add_zero] using heq.2.1

/-- Time consistency for the whole tail: from date `T` on, a certified path is the
optimum from the stock reached. -/
theorem tail_eq_optimalPath (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t, 0 ≤ t → a.capital (T + t) = (optimalPath P (hc.capital_pos T hT)).capital t ∧
      a.consumption (T + t) = (optimalPath P (hc.capital_pos T hT)).consumption t := by
  obtain ⟨qo, ho0, hoc⟩ := optimalPath_spec P (hc.capital_pos T hT)
  intro t ht
  have heq := hoc.eq P (hc.shift P hT)
    (by simp only [FeasiblePath.shift_capital, add_zero]; exact ho0) t ht
  exact ⟨heq.1, heq.2.1⟩

theorem policy_steady (P : CassPrimitives f U d m) :
    policy P (cassSteady P) = cassSteadyConsumption P := by
  have hks := (cassSteady_spec P).1
  obtain ⟨q, h0, hc⟩ := optimalPath_spec P hks
  have := ((hc.dynamics P).2.2.2.2 h0 0 le_rfl).2
  simp only [policy, hks, ↓reduceDIte]
  exact this

/-- Below the steady state, an optimal path reaches every higher stock below `k*`
at a positive date. -/
theorem exists_hit_of_lt (P : CassPrimitives f U d m) {a : FeasiblePath f m} {q : ℝ → ℝ}
    (hc : CassCertificate f U d m a q) {k1 : ℝ} (h01 : a.capital 0 < k1)
    (h1s : k1 < cassSteady P) : ∃ τ, 0 < τ ∧ a.capital τ = k1 := by
  obtain ⟨hk, -, -, -, -⟩ := hc.dynamics P
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((hk.eventually (lt_mem_nhds h1s)).and
    (eventually_ge_atTop (0 : ℝ)))
  have hT0 := (hT T le_rfl).2
  obtain ⟨τ, hτ, hτeq⟩ := intermediate_value_Icc hT0
    (a.capital_continuous.mono (fun _ hx => hx.1)) ⟨h01.le, (hT T le_rfl).1.le⟩
  refine ⟨τ, lt_of_le_of_ne hτ.1 ?_, hτeq⟩
  rintro rfl
  exact (ne_of_lt h01) hτeq

/-- Above the steady state, an optimal path reaches every lower stock above `k*`. -/
theorem exists_hit_of_gt (P : CassPrimitives f U d m) {a : FeasiblePath f m} {q : ℝ → ℝ}
    (hc : CassCertificate f U d m a q) {k1 : ℝ} (h01 : k1 < a.capital 0)
    (h1s : cassSteady P < k1) : ∃ τ, 0 < τ ∧ a.capital τ = k1 := by
  obtain ⟨hk, -, -, -, -⟩ := hc.dynamics P
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((hk.eventually (gt_mem_nhds h1s)).and
    (eventually_ge_atTop (0 : ℝ)))
  have hT0 := (hT T le_rfl).2
  obtain ⟨τ, hτ, hτeq⟩ := intermediate_value_Icc' hT0
    (a.capital_continuous.mono (fun _ hx => hx.1)) ⟨(hT T le_rfl).1.le, h01.le⟩
  refine ⟨τ, lt_of_le_of_ne hτ.1 ?_, hτeq⟩
  rintro rfl
  exact (ne_of_gt h01) hτeq

/-- On either side of the steady state, optimal paths are time translates: the path
from the stock nearer to `k*` is the tail of the path from the stock farther away. -/
theorem exists_shift_of_between (P : CassPrimitives f U d m) {a b : FeasiblePath f m}
    {qa qb : ℝ → ℝ} (ha : CassCertificate f U d m a qa) (hb : CassCertificate f U d m b qb)
    (hbetween : (a.capital 0 < b.capital 0 ∧ b.capital 0 < cassSteady P) ∨
      (cassSteady P < b.capital 0 ∧ b.capital 0 < a.capital 0)) :
    ∃ τ, 0 < τ ∧ ∀ t, 0 ≤ t → b.capital t = a.capital (τ + t) ∧
      b.consumption t = a.consumption (τ + t) := by
  obtain ⟨τ, hτ, hτeq⟩ : ∃ τ, 0 < τ ∧ a.capital τ = b.capital 0 := by
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact exists_hit_of_lt P ha h1 h2
    · exact exists_hit_of_gt P ha h2 h1
  refine ⟨τ, hτ, fun t ht => ?_⟩
  have heq := ha.shift P hτ.le |>.eq P hb
    (by simp only [FeasiblePath.shift_capital, add_zero]; exact hτeq) t ht
  exact ⟨heq.1, heq.2.1⟩

/-- Optimal paths of identical economies never cross. -/
theorem capital_lt_of_lt (P : CassPrimitives f U d m) {a b : FeasiblePath f m}
    {qa qb : ℝ → ℝ} (ha : CassCertificate f U d m a qa) (hb : CassCertificate f U d m b qb)
    (h0 : a.capital 0 < b.capital 0) {t : ℝ} (ht : 0 ≤ t) : a.capital t < b.capital t := by
  set ks := cassSteady P
  obtain ⟨-, -, habelow, -, haconst⟩ := ha.dynamics P
  obtain ⟨-, -, -, hbabove, hbconst⟩ := hb.dynamics P
  obtain ⟨hab1, -⟩ := ha.capital_bounds P
  obtain ⟨-, hbb2⟩ := hb.capital_bounds P
  rcases lt_trichotomy (b.capital 0) ks with h1 | h1 | h1
  · -- both below: `b` is a tail of `a`
    obtain ⟨τ, hτ, hshift⟩ := exists_shift_of_between P ha hb (Or.inl ⟨h0, h1⟩)
    rw [(hshift t ht).1]
    exact (habelow (h0.trans h1)).1 ht (by simp only [mem_Ici]; linarith) (by linarith)
  · rw [(hbconst h1 t ht).1]
    exact ((hab1 (lt_of_lt_of_eq h0 h1)) t ht).1
  · rcases lt_trichotomy (a.capital 0) ks with h2 | h2 | h2
    · exact ((hab1 h2) t ht).1.trans ((hbb2 h1) t ht).1
    · rw [(haconst h2 t ht).1]
      exact ((hbb2 h1) t ht).1
    · -- both above: `a` is a tail of `b`
      obtain ⟨τ, hτ, hshift⟩ := exists_shift_of_between P hb ha (Or.inr ⟨h2, h0⟩)
      rw [(hshift t ht).1]
      exact (hbabove h1).1 ht (by simp only [mem_Ici]; linarith) (by linarith)

/-- The optimal consumption policy is strictly increasing in capital. -/
theorem policy_strictMono (P : CassPrimitives f U d m) : StrictMonoOn (policy P) (Ioi 0) := by
  intro k0 hk0 k1 hk1 h01
  have hk0' : (0 : ℝ) < k0 := hk0
  have hk1' : (0 : ℝ) < k1 := hk1
  obtain ⟨qa, ha0, ha⟩ := optimalPath_spec P hk0'
  obtain ⟨qb, hb0, hb⟩ := optimalPath_spec P hk1'
  set a := optimalPath P hk0'
  set b := optimalPath P hk1'
  have hpa : policy P k0 = a.consumption 0 := by simp only [policy, hk0', ↓reduceDIte, a]
  have hpb : policy P k1 = b.consumption 0 := by simp only [policy, hk1', ↓reduceDIte, b]
  rw [hpa, hpb]
  set ks := cassSteady P
  obtain ⟨-, -, habelow, -, -⟩ := ha.dynamics P
  obtain ⟨-, -, -, hbabove, hbconst⟩ := hb.dynamics P
  obtain ⟨hab1, -⟩ := ha.capital_bounds P
  obtain ⟨-, hbb2⟩ := hb.capital_bounds P
  have hh0 : a.capital 0 < b.capital 0 := by rw [ha0, hb0]; exact h01
  rcases lt_trichotomy (b.capital 0) ks with h1 | h1 | h1
  · obtain ⟨τ, hτ, hshift⟩ := exists_shift_of_between P ha hb (Or.inl ⟨hh0, h1⟩)
    rw [(hshift 0 le_rfl).2, add_zero]
    exact (habelow (hh0.trans h1)).2 (mem_Ici.mpr le_rfl) hτ.le hτ
  · rw [(hbconst h1 0 le_rfl).2]
    exact ((hab1 (lt_of_lt_of_eq hh0 h1)) 0 le_rfl).2
  · rcases lt_trichotomy (a.capital 0) ks with h2 | h2 | h2
    · exact ((hab1 h2) 0 le_rfl).2.trans ((hbb2 h1) 0 le_rfl).2
    · obtain ⟨-, -, -, -, haconst⟩ := ha.dynamics P
      rw [(haconst h2 0 le_rfl).2]
      exact ((hbb2 h1) 0 le_rfl).2
    · obtain ⟨τ, hτ, hshift⟩ := exists_shift_of_between P hb ha (Or.inr ⟨h2, hh0⟩)
      rw [(hshift 0 le_rfl).2, add_zero]
      exact (hbabove h1).2 (mem_Ici.mpr le_rfl) hτ.le hτ

/-- The poorer economy consumes strictly less at every date. -/
theorem consumption_lt_of_lt (P : CassPrimitives f U d m) {a b : FeasiblePath f m}
    {qa qb : ℝ → ℝ} (ha : CassCertificate f U d m a qa) (hb : CassCertificate f U d m b qb)
    (h0 : a.capital 0 < b.capital 0) {t : ℝ} (ht : 0 ≤ t) :
    a.consumption t < b.consumption t := by
  rw [consumption_eq_policy P ha ht, consumption_eq_policy P hb ht]
  exact policy_strictMono P (ha.capital_pos t ht) (hb.capital_pos t ht)
    (capital_lt_of_lt P ha hb h0 ht)

/-- Absolute convergence: two identical economies converge to each other in capital,
in consumption, and in the capital ratio, whatever their initial stocks. -/
theorem absolute_convergence (P : CassPrimitives f U d m) {a b : FeasiblePath f m}
    {qa qb : ℝ → ℝ} (ha : CassCertificate f U d m a qa) (hb : CassCertificate f U d m b qb) :
    Tendsto (fun t => b.capital t - a.capital t) atTop (𝓝 0) ∧
      Tendsto (fun t => b.consumption t - a.consumption t) atTop (𝓝 0) ∧
      Tendsto (fun t => b.capital t / a.capital t) atTop (𝓝 1) := by
  obtain ⟨hak, hac, -⟩ := ha.dynamics P
  obtain ⟨hbk, hbc, -⟩ := hb.dynamics P
  have hks := (cassSteady_spec P).1
  refine ⟨by simpa only [sub_self] using hbk.sub hak, by simpa only [sub_self] using hbc.sub hac,
    ?_⟩
  have := hbk.div hak (ne_of_gt hks)
  rw [div_self (ne_of_gt hks)] at this
  exact this

end RamseyCassKoopmans

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# Analysis lemmas for the local convergence rate

* `hasDerivAt_of_comp_eq`: if `μ ∘ g = q` near `t`, `μ'(g t) ≠ 0` and `g` is
  continuous and locally injective at `t`, then `g' = q' / μ'`.
* `tendsto_div_of_deriv_tendsto`: if `φ' → L` then `φ t / t → L`.
* `riccati_tendsto`: a positive solution of `S' = S² - D S + B` with `D → d > 0` and
  `B → -A < 0` converges to the positive root `(d + √(d² + 4A)) / 2`. Solutions
  above that root blow up in finite time and solutions below it turn negative, so
  a positive solution defined for all large times has no other option.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

theorem hasDerivAt_of_comp_eq {g μ q : ℝ → ℝ} {t μ' q' : ℝ}
    (hg : ContinuousAt g t) (hμ : HasDerivAt μ μ' (g t)) (hμ' : μ' ≠ 0)
    (hq : HasDerivAt q q' t) (heq : ∀ᶠ s in 𝓝 t, μ (g s) = q s)
    (hinj : ∀ᶠ s in 𝓝[≠] t, g s ≠ g t) : HasDerivAt g (q' / μ') t := by
  rw [hasDerivAt_iff_tendsto_slope] at hq hμ ⊢
  have hgt : Tendsto g (𝓝[≠] t) (𝓝[≠] (g t)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hg.tendsto.mono_left nhdsWithin_le_nhds) hinj
  have hslope := hμ.comp hgt
  have hdiv := hq.div hslope hμ'
  have heqt : μ (g t) = q t := heq.self_of_nhds
  refine hdiv.congr' ?_
  filter_upwards [hinj, nhdsWithin_le_nhds heq, self_mem_nhdsWithin,
    hslope.eventually (eventually_ne_nhds hμ')] with s hs hμs hst hsl
  change slope q t s / slope μ (g t) (g s) = slope g t s
  change slope μ (g t) (g s) ≠ 0 at hsl
  rw [slope_def_field] at hsl
  rw [slope_def_field, slope_def_field, slope_def_field, ← hμs, ← heqt]
  have hst' : s - t ≠ 0 := sub_ne_zero.mpr hst
  have hgs : g s - g t ≠ 0 := sub_ne_zero.mpr hs
  have hnum : μ (g s) - μ (g t) ≠ 0 := by
    intro h0
    apply hsl
    rw [h0, zero_div]
  field_simp

/-- If the derivative of `φ` tends to `L`, then `φ t / t → L`. -/
theorem tendsto_div_of_deriv_tendsto {φ φ' : ℝ → ℝ} {L T0 : ℝ}
    (hφ : ∀ t, T0 ≤ t → HasDerivAt φ (φ' t) t) (hlim : Tendsto φ' atTop (𝓝 L)) :
    Tendsto (fun t => φ t / t) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T1, hT1⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  set T := max (max T0 T1) 1
  have hT0 : T0 ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have hT1' : T1 ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  have hTpos : 0 < T := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ψ : ℝ → ℝ := fun t => φ t - L * t
  have hmvt : ∀ t, T ≤ t → |ψ t - ψ T| ≤ ε / 2 * (t - T) := by
    intro t ht
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := ψ) (f' := fun s => φ' s - L)
      (fun s hs => (((hφ s (hT0.trans hs.1)).sub ((hasDerivAt_id s).const_mul L)).congr_deriv
        (by simp)).hasDerivWithinAt)
      (fun s hs => by
        rw [Real.norm_eq_abs]
        exact (hT1 s (hT1'.trans hs.1)).le) t ⟨ht, le_rfl⟩
    simpa only [Real.norm_eq_abs] using h
  obtain ⟨T2, hT2⟩ : ∃ T2, ∀ t, T2 ≤ t → |ψ T| / t < ε / 2 := by
    obtain ⟨T2, hT2⟩ := Metric.tendsto_atTop.mp
      (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun t : ℝ => |ψ T| / t) atTop (𝓝 0))
      (ε / 2) (half_pos hε)
    refine ⟨T2, fun t ht => ?_⟩
    have := hT2 t ht
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  refine ⟨max T T2, fun t ht => ?_⟩
  have htT : T ≤ t := (le_max_left _ _).trans ht
  have htpos : 0 < t := hTpos.trans_le htT
  have hb := hmvt t htT
  have hc := hT2 t ((le_max_right _ _).trans ht)
  rw [Real.dist_eq]
  have hrewrite : φ t / t - L = (ψ T + (ψ t - ψ T)) / t := by
    simp only [ψ]
    field_simp
    ring
  rw [hrewrite, abs_div, abs_of_pos htpos, div_lt_iff₀ htpos]
  have h1 : |ψ T + (ψ t - ψ T)| ≤ |ψ T| + |ψ t - ψ T| := abs_add_le _ _
  have h2 : |ψ T| < ε / 2 * t := by rwa [div_lt_iff₀ htpos] at hc
  nlinarith

/-- The quotient rule for `S = v/u` with `u' = u D - v` and `v' = u B` gives the
Riccati right-hand side. -/
theorem riccati_algebra {u v D B u' v' : ℝ} (hu : u ≠ 0) (hu' : u' = u * D - v)
    (hv' : v' = u * B) : (v' * u - v * u') / u ^ 2 = (v / u) ^ 2 - D * (v / u) + B := by
  subst hu' hv'
  field_simp
  ring

/-- A positive solution of the Riccati equation `S' = S² - D S + B`, with `D → d > 0`
and `B → -A < 0`, converges to the positive root `(d + √(d² + 4A)) / 2`. -/
theorem riccati_tendsto {S D B : ℝ → ℝ} {d A T0 : ℝ} (hd : 0 < d) (hA : 0 < A)
    (hS : ∀ t, T0 ≤ t → HasDerivAt S (S t ^ 2 - D t * S t + B t) t)
    (hpos : ∀ t, T0 ≤ t → 0 < S t)
    (hD : Tendsto D atTop (𝓝 d)) (hB : Tendsto B atTop (𝓝 (-A))) :
    Tendsto S atTop (𝓝 ((d + Real.sqrt (d ^ 2 + 4 * A)) / 2)) := by
  set r := Real.sqrt (d ^ 2 + 4 * A) with hr_def
  have hr2 : r ^ 2 = d ^ 2 + 4 * A := Real.sq_sqrt (by positivity)
  have hr : d < r := by
    rw [hr_def]
    exact (Real.lt_sqrt hd.le).mpr (by linarith)
  set x := (d + r) / 2 with hx_def
  set y := (d - r) / 2 with hy_def
  have hy : y < 0 := by rw [hy_def]; linarith
  have hx : 0 < x := by rw [hx_def]; linarith
  have hfac : ∀ s : ℝ, s ^ 2 - d * s - A = (s - x) * (s - y) := by
    intro s
    rw [hx_def, hy_def]
    linear_combination (1 / 4 : ℝ) * hr2
  have hcont : ∀ a b, T0 ≤ a → ContinuousOn S (Icc a b) := fun a b ha =>
    HasDerivAt.continuousOn (fun t ht => hS t (ha.trans ht.1))
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e := min (ε / 2) (x / 2) with he_def
  have he : 0 < e := lt_min (half_pos hε) (half_pos hx)
  have heε : e < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hex : e ≤ x / 2 := min_le_right _ _
  set η := min 1 (min (e / 2) (min (e * x / 8) (-(e * y) / (4 * (x + 1))))) with hη_def
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηe : η ≤ e / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηex : η ≤ e * x / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηy : η ≤ -(e * y) / (4 * (x + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hηpos : 0 < η := by
    apply lt_min one_pos (lt_min (half_pos he) (lt_min (by positivity) ?_))
    apply div_pos (by nlinarith) (by linarith)
  have hηy' : η * (x + 1) ≤ -(e * y) / 4 := by
    have := (le_div_iff₀ (by linarith : (0 : ℝ) < 4 * (x + 1))).mp hηy
    nlinarith
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hD η hηpos
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hB η hηpos
  set N := max T0 (max N1 N2)
  have hNT0 : T0 ≤ N := le_max_left _ _
  have hDN : ∀ t, N ≤ t → |D t - d| < η := fun t ht => by
    have := hN1 t ((le_max_left _ _).trans ((le_max_right _ _).trans ht))
    rwa [Real.dist_eq] at this
  have hBN : ∀ t, N ≤ t → |B t + A| < η := fun t ht => by
    have := hN2 t ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
    rwa [Real.dist_eq, sub_neg_eq_add] at this
  -- the right-hand side, rewritten around the limiting quadratic
  have hF : ∀ t, S t ^ 2 - D t * S t + B t =
      (S t - x) * (S t - y) + (d - D t) * S t + (B t + A) := by
    intro t
    have := hfac (S t)
    linarith
  -- lower bound: once below `x - e`, a positive solution is driven to zero
  have hlower : ∀ t, N ≤ t → x - e ≤ S t := by
    intro t1 ht1
    by_contra hlt
    push Not at hlt
    set c0 := -(e * y) / 4 with hc0
    have hc0pos : 0 < c0 := by rw [hc0]; nlinarith
    set b := t1 + S t1 / c0 + 1
    have htb : t1 ≤ b := by
      have := div_pos (hpos t1 (hNT0.trans ht1)) hc0pos
      linarith
    have hcmp := image_le_of_deriv_right_lt_deriv_boundary' (a := t1) (b := b)
      (f := S) (f' := fun t => S t ^ 2 - D t * S t + B t)
      (hcont t1 b (hNT0.trans ht1))
      (fun t ht => (hS t (hNT0.trans (ht1.trans ht.1))).hasDerivWithinAt)
      (B := fun t => S t1 - c0 * (t - t1)) (B' := fun _ => -c0)
      (by simp) (by fun_prop)
      (fun t _ => ((((hasDerivAt_id t).sub_const t1).const_mul c0).const_sub (S t1)).congr_deriv
        (by simp) |>.hasDerivWithinAt)
      (by
        intro t ht hSB
        have htN : N ≤ t := ht1.trans ht.1
        have hSpos := hpos t (hNT0.trans htN)
        have hSle : S t ≤ S t1 := by
          rw [hSB]
          have : 0 ≤ c0 * (t - t1) := mul_nonneg hc0pos.le (sub_nonneg.mpr ht.1)
          linarith
        have hSx : S t - x ≤ -e := by linarith
        have hSy : 0 ≤ S t - y := by linarith
        have hprod : (S t - x) * (S t - y) ≤ -e * (S t - y) :=
          mul_le_mul_of_nonneg_right hSx hSy
        have h1 : (d - D t) * S t ≤ η * S t :=
          mul_le_mul_of_nonneg_right (by linarith [abs_lt.mp (hDN t htN)]) hSpos.le
        have h2 : B t + A ≤ η := (le_abs_self _).trans (hBN t htN).le
        have h5 : η * S t ≤ η * x := mul_le_mul_of_nonneg_left (by linarith) hηpos.le
        have h6 : 0 ≤ e * S t := mul_nonneg he.le hSpos.le
        change S t ^ 2 - D t * S t + B t < -c0
        rw [hF t]
        linarith)
    have hb : S b ≤ S t1 - c0 * (b - t1) := hcmp ⟨htb, le_rfl⟩
    have hbpos := hpos b (hNT0.trans (ht1.trans htb))
    have : S t1 - c0 * (b - t1) = -c0 := by
      simp only [b]
      field_simp
      ring
    linarith
  -- upper bound: once above `x + e`, a solution grows, then blows up in finite time
  have hupper : ∀ t, N ≤ t → S t ≤ x + e := by
    intro t1 ht1
    by_contra hgt
    push Not at hgt
    have hT1 : T0 ≤ t1 := hNT0.trans ht1
    set c1 := e * x / 4 with hc1
    have hc1pos : 0 < c1 := by rw [hc1]; positivity
    set M := 4 * (d + A + 2) with hM
    have hMpos : 1 ≤ M := by rw [hM]; linarith
    set b1 := t1 + M / c1
    have htb1 : t1 ≤ b1 := by have := div_pos (by linarith : (0 : ℝ) < M) hc1pos; linarith
    -- stage A: linear growth at rate `c1`
    have hgrow := image_le_of_deriv_right_lt_deriv_boundary' (a := t1) (b := b1)
      (f := fun t => S t1 + c1 * (t - t1)) (f' := fun _ => c1)
      (by fun_prop)
      (fun t _ => ((((hasDerivAt_id t).sub_const t1).const_mul c1).const_add (S t1)).congr_deriv
        (by simp) |>.hasDerivWithinAt)
      (B := S) (B' := fun t => S t ^ 2 - D t * S t + B t) (by simp) (hcont t1 b1 hT1)
      (fun t ht => (hS t (hT1.trans ht.1)).hasDerivWithinAt)
      (by
        intro t ht hSB
        have htN : N ≤ t := ht1.trans ht.1
        have hge : S t1 ≤ S t := by
          rw [← hSB]
          have : 0 ≤ c1 * (t - t1) := mul_nonneg hc1pos.le (sub_nonneg.mpr ht.1)
          linarith
        have hSx : e ≤ S t - x := by linarith
        have hSy : S t ≤ S t - y := by linarith
        have hSpos : 0 < S t := by linarith
        have hprod : e * S t ≤ (S t - x) * (S t - y) :=
          mul_le_mul hSx hSy hSpos.le (by linarith)
        have h1 : -η * S t ≤ (d - D t) * S t :=
          mul_le_mul_of_nonneg_right (by linarith [abs_lt.mp (hDN t htN)]) hSpos.le
        have h2 : -η ≤ B t + A := by linarith [abs_lt.mp (hBN t htN)]
        have hxS : x ≤ S t := by linarith
        have h3 : (e - η) * x ≤ (e - η) * S t := mul_le_mul_of_nonneg_left hxS (by linarith)
        have h4 : η * x ≤ e / 2 * x := mul_le_mul_of_nonneg_right hηe hx.le
        change c1 < S t ^ 2 - D t * S t + B t
        rw [hF t, hc1]
        linarith)
    have hSb1 : M < S b1 := by
      have h : S t1 + c1 * (b1 - t1) ≤ S b1 := hgrow ⟨htb1, le_rfl⟩
      have : c1 * (b1 - t1) = M := by simp only [b1]; field_simp; ring
      linarith
    -- stage B: `1/S` falls at rate at least `1/2`, so it reaches zero in finite time
    have hb1T : T0 ≤ b1 := hT1.trans htb1
    have hSb1pos : 0 < S b1 := by linarith
    set φ0 := (S b1)⁻¹
    have hφ0 : 0 < φ0 := inv_pos.mpr hSb1pos
    have hφ0M : φ0 < M⁻¹ := inv_strictAnti₀ (by linarith) hSb1
    set b2 := b1 + 2 * φ0 + 1
    have htb2 : b1 ≤ b2 := by linarith
    have hinvd : ∀ t, T0 ≤ t → HasDerivAt (fun s => (S s)⁻¹)
        (-(S t ^ 2 - D t * S t + B t) / S t ^ 2) t := fun t ht =>
      (hS t ht).inv (ne_of_gt (hpos t ht))
    have hdecay := image_le_of_deriv_right_lt_deriv_boundary' (a := b1) (b := b2)
      (f := fun s => (S s)⁻¹) (f' := fun t => -(S t ^ 2 - D t * S t + B t) / S t ^ 2)
      (HasDerivAt.continuousOn (fun t ht => hinvd t (hb1T.trans ht.1)))
      (fun t ht => (hinvd t (hb1T.trans ht.1)).hasDerivWithinAt)
      (B := fun t => φ0 - (t - b1) / 2) (B' := fun _ => -(1 / 2))
      (by simp [φ0]) (by fun_prop)
      (fun t _ => (((hasDerivAt_id t).sub_const b1).div_const 2).const_sub φ0 |>.congr_deriv
        (by simp) |>.hasDerivWithinAt)
      (by
        intro t ht hφB
        have htN : N ≤ t := ht1.trans (htb1.trans ht.1)
        have hSpos := hpos t (hb1T.trans ht.1)
        have hφB' : (S t)⁻¹ = φ0 - (t - b1) / 2 := hφB
        have hφle : (S t)⁻¹ ≤ φ0 := by
          rw [hφB']
          have : 0 ≤ (t - b1) / 2 := div_nonneg (sub_nonneg.mpr ht.1) (by norm_num)
          linarith
        have hSM : M < S t := by
          have h := hφle.trans_lt hφ0M
          rwa [inv_lt_inv₀ hSpos (by linarith)] at h
        have h1 : -η * S t ≤ (d - D t) * S t :=
          mul_le_mul_of_nonneg_right (by linarith [abs_lt.mp (hDN t htN)]) hSpos.le
        have h2 : -η ≤ B t + A := by linarith [abs_lt.mp (hBN t htN)]
        have hS1 : 1 ≤ S t := hMpos.trans hSM.le
        have hMS : M * S t ≤ S t * S t := mul_le_mul_of_nonneg_right hSM.le hSpos.le
        have hAS : (A + 1) * 1 ≤ (A + 1) * S t := mul_le_mul_of_nonneg_left hS1 (by linarith)
        have hηS : η * S t ≤ 1 * S t := mul_le_mul_of_nonneg_right hη1 hSpos.le
        have hquad : 3 / 4 * S t ^ 2 ≤ S t ^ 2 - D t * S t + B t := by
          rw [hF t, ← hfac (S t), hM] at *
          nlinarith
        have hsq : 0 < S t ^ 2 := by positivity
        change -(S t ^ 2 - D t * S t + B t) / S t ^ 2 < -(1 / 2)
        rw [div_lt_iff₀ hsq]
        linarith)
    have hb2 : (S b2)⁻¹ ≤ φ0 - (b2 - b1) / 2 := hdecay ⟨htb2, le_rfl⟩
    have hb2pos := inv_pos.mpr (hpos b2 (hb1T.trans htb2))
    have : φ0 - (b2 - b1) / 2 = -(1 / 2) := by simp only [b2]; ring
    linarith
  refine ⟨N, fun t ht => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have h1 := hlower t ht
  have h2 := hupper t ht
  constructor <;> linarith

end RamseyCassKoopmans

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# The exact local speed of convergence of the Cass optimum

Let `A = f''(k*) U'(c*) / U''(c*) > 0` and `β* = (√(d² + 4A) - d) / 2`, the stable
root of the linearized saddle. Assuming `f''(k*) < 0`:

* `slope_tendsto`: along every nonstationary optimum,
  `(c(t) - c*) / (k(t) - k*) → d + β*`. The slope obeys a Riccati equation whose
  other solutions blow up or turn negative (`riccati_tendsto`), so the optimum is
  forced onto the stable direction; no stable-manifold theorem is assumed.
* `speed_tendsto`: the instantaneous proportional speed `k̇ / (k - k*) → -β*`;
* `capital_rate`, `consumption_rate`: `log |k(t) - k*| / t → -β*` and
  `log |c(t) - c*| / t → -β*`;
* `policy_hasDerivAt`: the policy function is differentiable at `k*` with slope
  `d + β*`, the slope of the stable eigenvector.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

/-- `A = f''(k*) U'(c*) / U''(c*)`. -/
noncomputable def cassCurvature (P : CassPrimitives f U d m) : ℝ :=
  deriv (deriv f) (cassSteady P) * deriv U (cassSteadyConsumption P) /
    deriv (deriv U) (cassSteadyConsumption P)

/-- The stable root `β* = (√(d² + 4A) - d) / 2` of the linearized Cass system. -/
noncomputable def cassSpeed (P : CassPrimitives f U d m) : ℝ :=
  (Real.sqrt (d ^ 2 + 4 * cassCurvature P) - d) / 2

theorem cassSteadyConsumption_pos (P : CassPrimitives f U d m) :
    0 < cassSteadyConsumption P :=
  stationary_consumption_pos f (cassSteady P) d m P.f_conc P.f_zero (cassSteady_spec P).1
    (P.f_diff _ (cassSteady_spec P).1) P.d_pos.le (cassSteady_spec P).2

theorem cassCurvature_pos (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) : 0 < cassCurvature P := by
  have hc := cassSteadyConsumption_pos P
  exact div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hf2 (P.U_prime_pos _ hc))
    (P.U_second_neg _ hc)

theorem cassSpeed_pos (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) : 0 < cassSpeed P := by
  have hA := cassCurvature_pos P hf2
  have hd := P.d_pos
  have : d < Real.sqrt (d ^ 2 + 4 * cassCurvature P) :=
    (Real.lt_sqrt hd.le).mpr (by linarith)
  unfold cassSpeed
  linarith

theorem stable_root_eq (P : CassPrimitives f U d m) :
    (d + Real.sqrt (d ^ 2 + 4 * cassCurvature P)) / 2 = d + cassSpeed P := by
  unfold cassSpeed
  ring

/-- Eventually the optimum invests strictly: transferred from the construction. -/
theorem CassCertificate.eventually_positive_investment (P : CassPrimitives f U d m)
    {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) :
    ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → 0 < a.investment t := by
  obtain ⟨ks, hks, hstat, b, Jb, hb0, hbopt, -, -, -, -, -, -, -, -, ⟨T, hT, hTpos⟩, -, -⟩ :=
    cass_general_dynamic f U d m (a.capital 0) P.d_pos P.m_pos (hc.capital_pos 0 le_rfl)
      P.f_conc P.f_zero P.f_diff P.f_prime_cont P.f_prime_pos P.f_second P.f_second_cont
      P.f_inada0 P.f_inadaTop P.U_conc P.U_diff P.U_prime_pos P.U_second P.U_second_cont
      P.U_second_neg P.U_inada0
  obtain ⟨Ja, hJa⟩ := hc.welfare
  have heq := (hc.eq_of_isCassOptimal P hJa hbopt hb0.symm).2
  exact ⟨T, hT, fun t ht => by
    rw [← (heq t (hT.trans ht)).2.2]
    exact hTpos t ht⟩

/-- The capital equation `k̇ = f(k) - m k - c`. -/
theorem FeasiblePath.hasDerivAt_capital' (a : FeasiblePath f m) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt a.capital (f (a.capital t) - m * a.capital t - a.consumption t) t := by
  have h := a.dynamics t ht
  have hr := a.resource t ht
  convert h using 1
  linarith

/-- Along a nonstationary optimum the capital and consumption gaps share a sign. -/
theorem CassCertificate.gap_sign (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) (hne : a.capital 0 ≠ cassSteady P)
    {t : ℝ} (ht : 0 ≤ t) :
    a.capital t - cassSteady P ≠ 0 ∧
      0 < (a.consumption t - cassSteadyConsumption P) / (a.capital t - cassSteady P) := by
  obtain ⟨hb1, hb2⟩ := hc.capital_bounds P
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨hk, hcn⟩ := hb1 h t ht
    refine ⟨sub_ne_zero.mpr (ne_of_lt hk), div_pos_of_neg_of_neg ?_ (sub_neg.mpr hk)⟩
    exact sub_neg.mpr hcn
  · obtain ⟨hk, hcn⟩ := hb2 h t ht
    exact ⟨sub_ne_zero.mpr (ne_of_gt hk), div_pos (sub_pos.mpr hcn) (sub_pos.mpr hk)⟩

/-- In the interior phase consumption obeys `ċ = -(U'/U'')(c) (f'(k) - (d + m))`. -/
theorem CassCertificate.hasDerivAt_consumption (P : CassPrimitives f U d m)
    {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q)
    (hne : a.capital 0 ≠ cassSteady P) {T0 : ℝ} (hT0 : 0 ≤ T0)
    (hint : ∀ t, T0 ≤ t → 0 < a.investment t) {t : ℝ} (ht : T0 < t) :
    HasDerivAt a.consumption
      (-(deriv U (a.consumption t)) / deriv (deriv U) (a.consumption t) *
        (deriv f (a.capital t) - (d + m))) t := by
  have ht0 : 0 ≤ t := hT0.trans ht.le
  have hct := a.consumption_pos t ht0
  have hqeq : ∀ s, T0 ≤ s → q s = deriv U (a.consumption s) := by
    intro s hs
    have h := hc.slack s (hT0.trans hs)
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · exact absurd h (ne_of_gt (hint s hs))
  obtain ⟨-, -, hbelow, habove, -⟩ := hc.dynamics P
  have hinjOn : InjOn a.consumption (Ici 0) := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hbelow h).2.injOn
    · exact (habove h).2.injOn
  have hd := hasDerivAt_of_comp_eq (g := a.consumption) (μ := deriv U) (q := q)
    ((a.consumption_continuous t ht0).continuousAt (Ici_mem_nhds (hT0.trans_lt ht)))
    (P.U_second _ hct).hasDerivAt (ne_of_lt (P.U_second_neg _ hct)) (hc.costate t ht0)
    (by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact (hqeq s hs.le).symm)
    (by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (hT0.trans_lt ht)),
        self_mem_nhdsWithin] with s hs hst
      exact fun h => hst (hinjOn (mem_Ici.mpr (le_of_lt hs)) (mem_Ici.mpr ht0) h))
  refine hd.congr_deriv ?_
  rw [hqeq t ht.le]
  have hne' := ne_of_lt (P.U_second_neg _ hct)
  field_simp
  ring

/-- Along every nonstationary optimum the slope `(c - c*)/(k - k*)` converges to the
stable eigenvector slope `d + β*`. -/
theorem slope_tendsto (P : CassPrimitives f U d m) (hf2 : deriv (deriv f) (cassSteady P) < 0)
    {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q)
    (hne : a.capital 0 ≠ cassSteady P) :
    Tendsto (fun t => (a.consumption t - cassSteadyConsumption P) / (a.capital t - cassSteady P))
      atTop (𝓝 (d + cassSpeed P)) := by
  set ks := cassSteady P with hks_def
  set cs := cassSteadyConsumption P with hcs_def
  have hks := (cassSteady_spec P).1
  have hfks : deriv f ks = d + m := (cassSteady_spec P).2
  have hcs : 0 < cs := cassSteadyConsumption_pos P
  obtain ⟨T0, hT0, hint⟩ := hc.eventually_positive_investment P
  obtain ⟨hk, hcon, -⟩ := hc.dynamics P
  set u : ℝ → ℝ := fun t => a.capital t - ks
  set v : ℝ → ℝ := fun t => a.consumption t - cs
  set D : ℝ → ℝ := fun t => (f (a.capital t) - f ks) / (a.capital t - ks) - m
  set σ : ℝ → ℝ := fun c => -(deriv U c) / deriv (deriv U) c
  set B : ℝ → ℝ := fun t =>
    σ (a.consumption t) * ((deriv f (a.capital t) - deriv f ks) / (a.capital t - ks))
  have hS : ∀ t, T0 + 1 ≤ t → HasDerivAt (fun s => v s / u s)
      ((v t / u t) ^ 2 - D t * (v t / u t) + B t) t := by
    intro t ht
    have htT : T0 < t := by linarith
    have ht0 : 0 ≤ t := by linarith
    obtain ⟨hu0, -⟩ := hc.gap_sign P hne ht0
    have hkd := a.hasDerivAt_capital' ht0
    have hcd := hc.hasDerivAt_consumption P hne hT0 hint htT
    have hu : a.capital t - ks ≠ 0 := hu0
    have hμ2 : deriv (deriv U) (a.consumption t) ≠ 0 :=
      ne_of_lt (P.U_second_neg _ (a.consumption_pos t ht0))
    have hdiv := (hcd.sub_const cs).div (hkd.sub_const ks) hu
    refine hdiv.congr_deriv (riccati_algebra hu ?_ ?_)
    · have hcsdef : cs = f ks - m * ks := rfl
      simp only [D]
      rw [hcsdef]
      field_simp
      ring
    · simp only [B, σ]
      rw [hfks]
      field_simp
  have hpos : ∀ t, T0 + 1 ≤ t → 0 < v t / u t := fun t ht =>
    (hc.gap_sign P hne (by linarith)).2
  -- the capital path approaches `k*` from one side
  have hkne : Tendsto a.capital atTop (𝓝[≠] ks) :=
    tendsto_nhdsWithin_iff.mpr ⟨hk, by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact sub_ne_zero.mp (hc.gap_sign P hne ht).1⟩
  have hD : Tendsto D atTop (𝓝 d) := by
    have h := (hasDerivAt_iff_tendsto_slope.mp (P.f_diff ks hks).hasDerivAt).comp hkne
    have h2 := h.sub_const m
    rw [hfks, show d + m - m = d by ring] at h2
    refine h2.congr (fun t => ?_)
    simp only [Function.comp_apply, D, slope_def_field]
  have hB : Tendsto B atTop (𝓝 (-cassCurvature P)) := by
    have hslope := (hasDerivAt_iff_tendsto_slope.mp (P.f_second ks hks).hasDerivAt).comp hkne
    have hμ : ContinuousAt (deriv U) cs := (P.U_second cs hcs).continuousAt
    have hμ' : ContinuousAt (deriv (deriv U)) cs :=
      P.U_second_cont.continuousAt (Ioi_mem_nhds hcs)
    have hσ : Tendsto (fun t => σ (a.consumption t)) atTop (𝓝 (σ cs)) :=
      (hμ.tendsto.comp hcon).neg.div (hμ'.tendsto.comp hcon) (ne_of_lt (P.U_second_neg cs hcs))
    have h := hσ.mul hslope
    have heq : σ cs * deriv (deriv f) ks = -cassCurvature P := by
      simp only [σ, cassCurvature]
      ring
    rw [heq] at h
    refine h.congr (fun t => ?_)
    simp only [Function.comp_apply, B, slope_def_field]
  have := riccati_tendsto P.d_pos (cassCurvature_pos P hf2) hS hpos hD hB
  rwa [stable_root_eq] at this

/-- The instantaneous proportional speed of convergence tends to `β*`:
`k̇ / (k - k*) → -β*`. -/
theorem speed_tendsto (P : CassPrimitives f U d m) (hf2 : deriv (deriv f) (cassSteady P) < 0)
    {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q)
    (hne : a.capital 0 ≠ cassSteady P) :
    Tendsto (fun t => (f (a.capital t) - m * a.capital t - a.consumption t) /
      (a.capital t - cassSteady P)) atTop (𝓝 (-cassSpeed P)) := by
  set ks := cassSteady P
  have hks := (cassSteady_spec P).1
  have hfks : deriv f ks = d + m := (cassSteady_spec P).2
  obtain ⟨hk, -, -⟩ := hc.dynamics P
  have hkne : Tendsto a.capital atTop (𝓝[≠] ks) :=
    tendsto_nhdsWithin_iff.mpr ⟨hk, by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact sub_ne_zero.mp (hc.gap_sign P hne ht).1⟩
  have hD := ((hasDerivAt_iff_tendsto_slope.mp (P.f_diff ks hks).hasDerivAt).comp hkne).sub_const m
  have h := hD.sub (slope_tendsto P hf2 hc hne)
  rw [hfks, show d + m - m - (d + cassSpeed P) = -cassSpeed P by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hu : a.capital t - ks ≠ 0 := (hc.gap_sign P hne ht).1
  have hu2 : a.capital t - cassSteady P ≠ 0 := hu
  have hcs : cassSteadyConsumption P = f ks - m * ks := rfl
  simp only [Function.comp_apply, slope_def_field]
  rw [hcs]
  field_simp
  ring

/-- Capital converges at exactly the rate `β*`: `log |k(t) - k*| / t → -β*`. -/
theorem capital_rate (P : CassPrimitives f U d m) (hf2 : deriv (deriv f) (cassSteady P) < 0)
    {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q)
    (hne : a.capital 0 ≠ cassSteady P) :
    Tendsto (fun t => Real.log |a.capital t - cassSteady P| / t) atTop
      (𝓝 (-cassSpeed P)) := by
  have hφ : ∀ t, 0 ≤ t → HasDerivAt (fun s => Real.log (a.capital s - cassSteady P))
      ((f (a.capital t) - m * a.capital t - a.consumption t) / (a.capital t - cassSteady P)) t :=
    fun t ht => ((a.hasDerivAt_capital' ht).sub_const _).log (hc.gap_sign P hne ht).1
  simpa only [Real.log_abs] using tendsto_div_of_deriv_tendsto hφ (speed_tendsto P hf2 hc hne)

/-- Consumption converges at the same rate: `log |c(t) - c*| / t → -β*`. -/
theorem consumption_rate (P : CassPrimitives f U d m) (hf2 : deriv (deriv f) (cassSteady P) < 0)
    {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q)
    (hne : a.capital 0 ≠ cassSteady P) :
    Tendsto (fun t => Real.log |a.consumption t - cassSteadyConsumption P| / t) atTop
      (𝓝 (-cassSpeed P)) := by
  set S := fun t => (a.consumption t - cassSteadyConsumption P) / (a.capital t - cassSteady P)
  have hSlim := slope_tendsto P hf2 hc hne
  have hx : 0 < d + cassSpeed P := add_pos P.d_pos (cassSpeed_pos P hf2)
  have hlogS : Tendsto (fun t => Real.log (S t) / t) atTop (𝓝 0) :=
    ((Real.continuousAt_log (ne_of_gt hx)).tendsto.comp hSlim).div_atTop tendsto_id
  have h := hlogS.add (capital_rate P hf2 hc hne)
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  obtain ⟨hu, hSpos⟩ := hc.gap_sign P hne ht
  have hv : a.consumption t - cassSteadyConsumption P =
      S t * (a.capital t - cassSteady P) := by
    simp only [S]
    field_simp
  rw [hv, abs_mul, abs_of_pos hSpos, Real.log_mul (ne_of_gt hSpos) (abs_ne_zero.mpr hu),
    add_div]

/-- The policy function is differentiable at the steady state, with the slope of the
stable eigenvector. -/
theorem policy_hasDerivAt (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) :
    HasDerivAt (policy P) (d + cassSpeed P) (cassSteady P) := by
  set ks := cassSteady P
  have hks := (cassSteady_spec P).1
  rw [hasDerivAt_iff_tendsto_slope, ← nhdsLT_sup_nhdsGT, tendsto_sup]
  -- the slope of the policy at a stock reached by a path equals the path slope there
  have hslope : ∀ {a : FeasiblePath f m} {q : ℝ → ℝ}, CassCertificate f U d m a q →
      ∀ t, 0 ≤ t → a.capital t ≠ ks →
        slope (policy P) ks (a.capital t) =
          (a.consumption t - cassSteadyConsumption P) / (a.capital t - ks) := by
    intro a q hc t ht _
    rw [slope_def_field, ← consumption_eq_policy P hc ht, policy_steady]
  constructor
  · -- from below, along the optimum from `k*/2`
    have hk0 : 0 < ks / 2 := half_pos hks
    obtain ⟨q, h0, hc⟩ := optimalPath_spec P hk0
    set a := optimalPath P hk0
    have hne : a.capital 0 ≠ ks := by rw [h0]; linarith
    have hlt : a.capital 0 < ks := by rw [h0]; linarith
    obtain ⟨hk, -, -⟩ := hc.dynamics P
    have hS := slope_tendsto P hf2 hc hne
    rw [Metric.tendsto_nhds] at hS ⊢
    intro ε hε
    obtain ⟨T, hT⟩ := eventually_atTop.mp ((hS ε hε).and (eventually_ge_atTop (0 : ℝ)))
    have hTlt : a.capital T < ks := ((hc.capital_bounds P).1 hlt T (hT T le_rfl).2).1
    filter_upwards [Ioo_mem_nhdsLT hTlt] with k hk'
    obtain ⟨T', hT'⟩ := eventually_atTop.mp ((hk.eventually (lt_mem_nhds hk'.2)).and
      (eventually_ge_atTop T))
    obtain ⟨t, htmem, htk⟩ := intermediate_value_Icc (hT' T' le_rfl).2
      (a.capital_continuous.mono (fun s hs => (hT T le_rfl).2.trans hs.1))
      ⟨hk'.1.le, (hT' T' le_rfl).1.le⟩
    have ht0 : 0 ≤ t := (hT T le_rfl).2.trans htmem.1
    rw [← htk, hslope hc t ht0 (by rw [htk]; exact ne_of_lt hk'.2)]
    exact (hT t htmem.1).1
  · -- from above, along the optimum from `2 k*`
    have hk0 : 0 < 2 * ks := by linarith
    obtain ⟨q, h0, hc⟩ := optimalPath_spec P hk0
    set a := optimalPath P hk0
    have hne : a.capital 0 ≠ ks := by rw [h0]; linarith
    have hgt : ks < a.capital 0 := by rw [h0]; linarith
    obtain ⟨hk, -, -⟩ := hc.dynamics P
    have hS := slope_tendsto P hf2 hc hne
    rw [Metric.tendsto_nhds] at hS ⊢
    intro ε hε
    obtain ⟨T, hT⟩ := eventually_atTop.mp ((hS ε hε).and (eventually_ge_atTop (0 : ℝ)))
    have hTgt : ks < a.capital T := ((hc.capital_bounds P).2 hgt T (hT T le_rfl).2).1
    filter_upwards [Ioo_mem_nhdsGT hTgt] with k hk'
    obtain ⟨T', hT'⟩ := eventually_atTop.mp ((hk.eventually (gt_mem_nhds hk'.1)).and
      (eventually_ge_atTop T))
    obtain ⟨t, htmem, htk⟩ := intermediate_value_Icc' (hT' T' le_rfl).2
      (a.capital_continuous.mono (fun s hs => (hT T le_rfl).2.trans hs.1))
      ⟨(hT' T' le_rfl).1.le, hk'.2.le⟩
    have ht0 : 0 ≤ t := (hT T le_rfl).2.trans htmem.1
    rw [← htk, hslope hc t ht0 (by rw [htk]; exact ne_of_gt hk'.1)]
    exact (hT t htmem.1).1

end RamseyCassKoopmans

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# Cass comparative statics and comparative dynamics

**Statics.** The steady state solves `f'(k*) = d + m`, so `k* = g(d + m)` for the
inverse marginal product `g = marginalInverse`. We prove `g` is strictly decreasing
and, where `f''(k*) < 0`, differentiable with `g' = 1 / f''(k*)` (inverse function
theorem). Hence `∂k*/∂d = ∂k*/∂m = 1/f''(k*) < 0`, `∂c*/∂d = d/f''(k*) < 0`,
`∂c*/∂m = d/f''(k*) - k* < 0`; with productivity `A f`, `k*` rises with `A`.

**Dynamics.** `patience_rise`: starting at the old steady state, a permanent fall
in the discount rate makes capital rise strictly to the new, higher steady state;
consumption falls strictly on impact below the old steady-state level, then rises
strictly to a higher new level. `impatience_rise` is the mirror image.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

theorem CassPrimitives.existsUnique_marginal (P : CassPrimitives f U d m) {r : ℝ}
    (hr : 0 < r) : ∃! k : ℝ, 0 < k ∧ deriv f k = r :=
  existsUnique_positive_root_of_inada (deriv f) r hr P.f_prime_cont
    (production_deriv_strictAnti f P.f_conc P.f_diff) P.f_inada0 P.f_inadaTop

/-- The inverse marginal product: the unique positive capital with `f'(k) = r`. -/
noncomputable def marginalInverse (P : CassPrimitives f U d m) (r : ℝ) : ℝ :=
  if hr : 0 < r then Classical.choose (P.existsUnique_marginal hr).exists else 0

theorem marginalInverse_spec (P : CassPrimitives f U d m) {r : ℝ} (hr : 0 < r) :
    0 < marginalInverse P r ∧ deriv f (marginalInverse P r) = r := by
  simp only [marginalInverse, hr, ↓reduceDIte]
  exact Classical.choose_spec (P.existsUnique_marginal hr).exists

theorem marginalInverse_eq (P : CassPrimitives f U d m) {r k : ℝ} (hk : 0 < k)
    (he : deriv f k = r) : marginalInverse P r = k := by
  have hr : 0 < r := he ▸ P.f_prime_pos k hk
  exact (P.existsUnique_marginal hr).unique (marginalInverse_spec P hr) ⟨hk, he⟩

theorem marginalInverse_deriv (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k) :
    marginalInverse P (deriv f k) = k := marginalInverse_eq P hk rfl

/-- The steady state of any economy sharing the technology `f` is `g(δ + μ)`. -/
theorem cassSteady_eq_marginalInverse (P : CassPrimitives f U d m) {V : ℝ → ℝ} {δ μ : ℝ}
    (P' : CassPrimitives f V δ μ) : cassSteady P' = marginalInverse P (δ + μ) := by
  have hr : 0 < δ + μ := add_pos P'.d_pos P'.m_pos
  exact cassSteady_eq P' (marginalInverse_spec P hr).1 (marginalInverse_spec P hr).2

theorem marginalInverse_strictAnti (P : CassPrimitives f U d m) :
    StrictAntiOn (marginalInverse P) (Ioi 0) := by
  intro r hr s hs hrs
  have hr' : (0 : ℝ) < r := hr
  have hs' : (0 : ℝ) < s := hs
  by_contra hle
  push Not at hle
  have hanti := (production_deriv_strictAnti f P.f_conc P.f_diff).antitoneOn
    (marginalInverse_spec P hr').1 (marginalInverse_spec P hs').1 hle
  rw [(marginalInverse_spec P hr').2, (marginalInverse_spec P hs').2] at hanti
  linarith

/-- Inverse function theorem: `g' = 1 / f''(g(r))` where `f''(g(r)) ≠ 0`. -/
theorem marginalInverse_hasDerivAt (P : CassPrimitives f U d m) {r : ℝ} (hr : 0 < r)
    (hf2 : deriv (deriv f) (marginalInverse P r) ≠ 0) :
    HasDerivAt (marginalInverse P) (deriv (deriv f) (marginalInverse P r))⁻¹ r := by
  obtain ⟨hk, hkr⟩ := marginalInverse_spec P hr
  set k := marginalInverse P r
  have hstrict : HasStrictDerivAt (deriv f) (deriv (deriv f) k) k :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      ((lt_mem_nhds hk).mono (fun y hy => (P.f_second y hy).hasDerivAt))
      (P.f_second_cont.continuousAt (Ioi_mem_nhds hk))
  have h := hstrict.to_local_left_inverse hf2
    ((lt_mem_nhds hk).mono (fun y hy => marginalInverse_deriv P hy))
  rw [hkr] at h
  exact h.hasDerivAt

/-- `∂k*/∂d = 1/f''(k*) < 0`. -/
theorem steady_hasDerivAt_discount (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) :
    HasDerivAt (fun δ => marginalInverse P (δ + m)) (deriv (deriv f) (cassSteady P))⁻¹ d ∧
      (deriv (deriv f) (cassSteady P))⁻¹ < 0 := by
  have hr : 0 < d + m := add_pos P.d_pos P.m_pos
  have heq := cassSteady_eq_marginalInverse P P
  rw [heq] at hf2 ⊢
  exact ⟨(marginalInverse_hasDerivAt P hr (ne_of_lt hf2)).comp_add_const d m,
    inv_lt_zero.mpr hf2⟩

/-- `∂k*/∂m = 1/f''(k*) < 0`. -/
theorem steady_hasDerivAt_dilution (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) :
    HasDerivAt (fun μ => marginalInverse P (d + μ)) (deriv (deriv f) (cassSteady P))⁻¹ m := by
  have hr : 0 < d + m := add_pos P.d_pos P.m_pos
  have heq := cassSteady_eq_marginalInverse P P
  rw [heq] at hf2 ⊢
  exact (marginalInverse_hasDerivAt P hr (ne_of_lt hf2)).comp_const_add d m

/-- `∂c*/∂d = d / f''(k*) < 0`. -/
theorem steadyConsumption_hasDerivAt_discount (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) :
    HasDerivAt (fun δ => f (marginalInverse P (δ + m)) - m * marginalInverse P (δ + m))
      (d * (deriv (deriv f) (cassSteady P))⁻¹) d ∧
      d * (deriv (deriv f) (cassSteady P))⁻¹ < 0 := by
  obtain ⟨hg, hneg⟩ := steady_hasDerivAt_discount P hf2
  have heq := cassSteady_eq_marginalInverse P P
  have hks := (cassSteady_spec P)
  have hfd : HasDerivAt f (deriv f (marginalInverse P (d + m))) (marginalInverse P (d + m)) :=
    (P.f_diff _ (heq ▸ hks.1)).hasDerivAt
  have h := (hfd.comp d hg).sub (hg.const_mul m)
  refine ⟨h.congr_deriv ?_, mul_neg_of_pos_of_neg P.d_pos hneg⟩
  rw [← heq, hks.2]
  ring

/-- `∂c*/∂m = d / f''(k*) - k* < 0`. -/
theorem steadyConsumption_hasDerivAt_dilution (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) :
    HasDerivAt (fun μ => f (marginalInverse P (d + μ)) - μ * marginalInverse P (d + μ))
      (d * (deriv (deriv f) (cassSteady P))⁻¹ - cassSteady P) m ∧
      d * (deriv (deriv f) (cassSteady P))⁻¹ - cassSteady P < 0 := by
  have hg := steady_hasDerivAt_dilution P hf2
  have hneg := (steady_hasDerivAt_discount P hf2).2
  have heq := cassSteady_eq_marginalInverse P P
  have hks := (cassSteady_spec P)
  have hfd : HasDerivAt f (deriv f (marginalInverse P (d + m))) (marginalInverse P (d + m)) :=
    (P.f_diff _ (heq ▸ hks.1)).hasDerivAt
  have h := (hfd.comp m hg).sub ((hasDerivAt_id m).mul hg)
  refine ⟨h.congr_deriv ?_, by nlinarith [P.d_pos, hks.1]⟩
  simp only [id]
  rw [← heq, hks.2]
  ring

/-- A more impatient economy has less steady-state capital and consumption. -/
theorem steady_strictAnti_discount (P1 : CassPrimitives f U d m) {d' : ℝ}
    (P2 : CassPrimitives f U d' m) (hdd : d < d') :
    cassSteady P2 < cassSteady P1 ∧ cassSteadyConsumption P2 < cassSteadyConsumption P1 := by
  rw [cassSteady_eq_marginalInverse P1 P2, cassSteady_eq_marginalInverse P1 P1]
  have hlt : marginalInverse P1 (d' + m) < marginalInverse P1 (d + m) :=
    marginalInverse_strictAnti P1 (add_pos P1.d_pos P1.m_pos)
      (add_pos P2.d_pos P2.m_pos) (by linarith)
  refine ⟨hlt, ?_⟩
  simp only [cassSteadyConsumption]
  rw [cassSteady_eq_marginalInverse P1 P2, cassSteady_eq_marginalInverse P1 P1]
  set k1 := marginalInverse P1 (d + m)
  set k2 := marginalInverse P1 (d' + m)
  have hk1 := marginalInverse_spec P1 (add_pos P1.d_pos P1.m_pos)
  have hk2 := marginalInverse_spec P1 (add_pos P2.d_pos P2.m_pos)
  -- concavity: `f(k1) - f(k2) > f'(k1) (k1 - k2) = (d + m)(k1 - k2) > m (k1 - k2)`
  have hs := strict_concave_support P1.f_conc (mem_Ici.mpr hk1.1.le) (mem_Ici.mpr hk2.1.le)
    (P1.f_diff k1 hk1.1).hasDerivAt (ne_of_lt hlt)
  rw [hk1.2] at hs
  have := mul_pos P1.d_pos (sub_pos.mpr hlt)
  nlinarith

/-- A larger dilution rate lowers steady-state capital. -/
theorem steady_strictAnti_dilution' (P1 : CassPrimitives f U d m) {m' : ℝ}
    (P2 : CassPrimitives f U d m') (hmm : m < m') : cassSteady P2 < cassSteady P1 := by
  rw [cassSteady_eq_marginalInverse P1 P2, cassSteady_eq_marginalInverse P1 P1]
  exact marginalInverse_strictAnti P1 (add_pos P1.d_pos P1.m_pos)
    (add_pos P2.d_pos P2.m_pos) (by linarith)

/-- Higher productivity `A f` raises steady-state capital: its steady state is
`g((d + m)/A)`. -/
theorem steady_productivity (P : CassPrimitives f U d m) {A : ℝ} (hA : 0 < A)
    (PA : CassPrimitives (fun k => A * f k) U d m) :
    cassSteady PA = marginalInverse P ((d + m) / A) := by
  have hr : 0 < (d + m) / A := div_pos (add_pos P.d_pos P.m_pos) hA
  obtain ⟨hk, hkr⟩ := marginalInverse_spec P hr
  apply cassSteady_eq PA hk
  rw [deriv_const_mul A (P.f_diff _ hk), hkr]
  field_simp

theorem steady_strictMono_productivity (P : CassPrimitives f U d m) {A1 A2 : ℝ}
    (hA1 : 0 < A1) (hA : A1 < A2) (P1 : CassPrimitives (fun k => A1 * f k) U d m)
    (P2 : CassPrimitives (fun k => A2 * f k) U d m) : cassSteady P1 < cassSteady P2 := by
  rw [steady_productivity P hA1 P1, steady_productivity P (hA1.trans hA) P2]
  have hr := add_pos P.d_pos P.m_pos
  exact marginalInverse_strictAnti P (div_pos hr (hA1.trans hA)) (div_pos hr hA1)
    (div_lt_div_of_pos_left hr hA1 hA)

/-- `z(t) = (k(t) - k₀) e^{-λt}` is monotone in the direction of the sign of
`k̇ - λ (k - k₀)`: the Gronwall step behind the impact effects. -/
theorem gap_exp_hasDerivAt (a : FeasiblePath f m) (k₀ lam : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => (a.capital s - k₀) * Real.exp (-lam * s))
      ((f (a.capital t) - m * a.capital t - a.consumption t - lam * (a.capital t - k₀)) *
        Real.exp (-lam * t)) t := by
  have he : HasDerivAt (fun s => Real.exp (-lam * s)) (Real.exp (-lam * t) * (-lam)) t := by
    have := ((hasDerivAt_id t).const_mul (-lam)).exp
    simpa only [id, mul_one] using this
  refine (((a.hasDerivAt_capital' ht).sub_const k₀).mul he).congr_deriv ?_
  ring

/-- A permanent rise in patience, starting from the old steady state: capital rises
strictly to the new, higher steady state; consumption falls strictly on impact
below the old steady-state level and then rises strictly to a higher new level. -/
theorem patience_rise (P1 : CassPrimitives f U d m) {d' : ℝ} (P2 : CassPrimitives f U d' m)
    (hdd : d' < d) {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d' m a q)
    (h0 : a.capital 0 = cassSteady P1) :
    cassSteady P1 < cassSteady P2 ∧ StrictMonoOn a.capital (Ici 0) ∧
      StrictMonoOn a.consumption (Ici 0) ∧
      a.consumption 0 < cassSteadyConsumption P1 ∧
      cassSteadyConsumption P1 < cassSteadyConsumption P2 ∧
      Tendsto a.capital atTop (𝓝 (cassSteady P2)) ∧
      Tendsto a.consumption atTop (𝓝 (cassSteadyConsumption P2)) := by
  obtain ⟨hlt, hclt⟩ := steady_strictAnti_discount P2 P1 hdd
  obtain ⟨hk, hcon, hbelow, -, -⟩ := hc.dynamics P2
  obtain ⟨hmono, hcmono⟩ := hbelow (h0 ▸ hlt)
  refine ⟨hlt, hmono, hcmono, ?_, hclt, hk, hcon⟩
  by_contra hge
  push Not at hge
  set k1 := cassSteady P1
  have hk1 := cassSteady_spec P1
  -- then `k̇ ≤ d (k - k1)`, so `(k - k1) e^{-dt}` is antitone and `k ≤ k1`
  have hanti : AntitoneOn (fun s => (a.capital s - k1) * Real.exp (-d * s)) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (HasDerivAt.continuousOn (fun s hs => gap_exp_hasDerivAt a k1 d hs))
      (fun s hs => (gap_exp_hasDerivAt a k1 d (interior_subset hs)).differentiableAt
        |>.differentiableWithinAt)
    intro s hs
    have hs0 : 0 ≤ s := interior_subset hs
    rw [(gap_exp_hasDerivAt a k1 d hs0).deriv]
    apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
    have hcs : a.consumption 0 ≤ a.consumption s := hcmono.monotoneOn (mem_Ici.mpr le_rfl) hs0 hs0
    have hsup := concave_support P1.f_conc.concaveOn (mem_Ici.mpr hk1.1.le)
      (a.capital_nonneg s hs0) (P1.f_diff k1 hk1.1).hasDerivAt
    rw [hk1.2] at hsup
    simp only [cassSteadyConsumption] at hge
    nlinarith
  have h1 := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr zero_le_one) zero_le_one
  simp only [mul_zero, Real.exp_zero, mul_one, h0, sub_self] at h1
  have hk1pos : a.capital 0 < a.capital 1 := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr zero_le_one)
    zero_lt_one
  have := mul_pos (sub_pos.mpr (h0 ▸ hk1pos)) (Real.exp_pos (-d))
  linarith

/-- A permanent rise in impatience, starting from the old steady state: capital falls
strictly to the new, lower steady state; consumption jumps strictly above the old
steady-state level and then falls strictly to a lower new level. -/
theorem impatience_rise (P1 : CassPrimitives f U d m) {d' : ℝ} (P2 : CassPrimitives f U d' m)
    (hdd : d < d') {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d' m a q)
    (h0 : a.capital 0 = cassSteady P1) :
    cassSteady P2 < cassSteady P1 ∧ StrictAntiOn a.capital (Ici 0) ∧
      StrictAntiOn a.consumption (Ici 0) ∧
      cassSteadyConsumption P1 < a.consumption 0 ∧
      cassSteadyConsumption P2 < cassSteadyConsumption P1 ∧
      Tendsto a.capital atTop (𝓝 (cassSteady P2)) ∧
      Tendsto a.consumption atTop (𝓝 (cassSteadyConsumption P2)) := by
  obtain ⟨hlt, hclt⟩ := steady_strictAnti_discount P1 P2 hdd
  obtain ⟨hk, hcon, -, habove, -⟩ := hc.dynamics P2
  obtain ⟨hanti, hcanti⟩ := habove (h0 ▸ hlt)
  refine ⟨hlt, hanti, hcanti, ?_, hclt, hk, hcon⟩
  by_contra hle
  push Not at hle
  set k1 := cassSteady P1
  set k2 := cassSteady P2
  have hk2 := cassSteady_spec P2
  have hbnd := (hc.capital_bounds P2).2 (h0 ▸ hlt)
  -- then `k̇ ≥ d' (k - k1)`, so `(k - k1) e^{-d't}` is monotone and `k ≥ k1`
  have hmono : MonotoneOn (fun s => (a.capital s - k1) * Real.exp (-d' * s)) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (HasDerivAt.continuousOn (fun s hs => gap_exp_hasDerivAt a k1 d' hs))
      (fun s hs => (gap_exp_hasDerivAt a k1 d' (interior_subset hs)).differentiableAt
        |>.differentiableWithinAt)
    intro s hs
    have hs0 : 0 ≤ s := interior_subset hs
    rw [(gap_exp_hasDerivAt a k1 d' hs0).deriv]
    apply mul_nonneg _ (Real.exp_pos _).le
    have hcs : a.consumption s ≤ a.consumption 0 :=
      hcanti.antitoneOn (mem_Ici.mpr le_rfl) hs0 hs0
    have hks := (hbnd s hs0).1
    have hkle : a.capital s ≤ k1 := by
      rw [← h0]
      exact hanti.antitoneOn (mem_Ici.mpr le_rfl) hs0 hs0
    have hkpos : 0 < a.capital s := hk2.1.trans hks
    have hsup := concave_support P2.f_conc.concaveOn (mem_Ici.mpr hkpos.le)
      (mem_Ici.mpr (hkpos.le.trans hkle)) (P2.f_diff _ hkpos).hasDerivAt
    have hfd : deriv f (a.capital s) ≤ d' + m := by
      rw [← hk2.2]
      exact (production_deriv_strictAnti f P2.f_conc P2.f_diff).antitoneOn hk2.1 hkpos hks.le
    have hprod : deriv f (a.capital s) * (k1 - a.capital s) ≤ (d' + m) * (k1 - a.capital s) :=
      mul_le_mul_of_nonneg_right hfd (sub_nonneg.mpr hkle)
    simp only [cassSteadyConsumption] at hle
    nlinarith
  have h1 := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr zero_le_one) zero_le_one
  simp only [mul_zero, Real.exp_zero, mul_one, h0, sub_self] at h1
  have hk1lt : a.capital 1 < a.capital 0 := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr zero_le_one)
    zero_lt_one
  have := mul_pos (sub_pos.mpr (h0 ▸ hk1lt)) (Real.exp_pos (-d'))
  linarith

end RamseyCassKoopmans

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# The Cass value function: monotonicity, strict concavity, and a supergradient

`value P k` is the optimal lifetime welfare from capital `k`. We prove:

* `value_spec`, `value_ge`: it is attained by the certified optimum and bounds the
  welfare of every Cass-feasible path from `k`;
* `value_strictMono`: it is strictly increasing. From a higher stock, copying the
  lower optimum's investment leaves strictly more output to consume;
* `value_strictConcave`: it is strictly concave. A mixture of two optimal paths is
  feasible, and strict concavity of `f` gives it strictly more consumption;
* `value_le_supergradient`: the initial current-value costate is a supergradient,
  `V(k₁) ≤ V(k₀) + q(0) (k₁ - k₀)`, from the verification comparison with unequal
  initial stocks (`finite_horizon_comparison'`).

The envelope theorem `V'(k₀) = q(0)` is in `CassEnvelope`.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

/-- A continuous positive function on `[0, ∞)` with a positive limit lies in a
compact subinterval of `(0, ∞)`. -/
theorem exists_pos_bounds {c : ℝ → ℝ} (hc : ContinuousOn c (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < c t) {L : ℝ} (hL : 0 < L) (hlim : Tendsto c atTop (𝓝 L)) :
    ∃ lo hi, 0 < lo ∧ lo ≤ hi ∧ ∀ t, 0 ≤ t → lo ≤ c t ∧ c t ≤ hi := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((hlim.eventually (lt_mem_nhds (half_lt_self hL))).and
    ((hlim.eventually (gt_mem_nhds (lt_add_one L)))))
  set T' := max T 0
  have hT' : 0 ≤ T' := le_max_right _ _
  obtain ⟨x, hx, hxmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT')
    (hc.mono (fun _ ht => ht.1))
  obtain ⟨y, hy, hymax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT')
    (hc.mono (fun _ ht => ht.1))
  have hxpos := hpos x hx.1
  refine ⟨min (L / 2) (c x), max (L + 1) (c y), lt_min (half_pos hL) hxpos,
    (min_le_left _ _).trans (by linarith [le_max_left (L + 1) (c y)]), fun t ht => ?_⟩
  rcases le_total t T' with htT | htT
  · exact ⟨(min_le_right _ _).trans (hxmin ⟨ht, htT⟩),
      (hymax ⟨ht, htT⟩).trans (le_max_right _ _)⟩
  · have h := hT t ((le_max_left _ _).trans htT)
    exact ⟨(min_le_left _ _).trans h.1.le, h.2.le.trans (le_max_left _ _)⟩

theorem CassPrimitives.f_cont (P : CassPrimitives f U d m) : ContinuousOn f (Ioi 0) :=
  fun k hk => (P.f_diff k hk).continuousAt.continuousWithinAt

theorem CassPrimitives.f_strictMono (P : CassPrimitives f U d m) : StrictMonoOn f (Ioi 0) :=
  strictMonoOn_of_deriv_pos (convex_Ioi 0) P.f_cont
    (fun k hk => by rw [interior_Ioi] at hk; exact P.f_prime_pos k hk)

theorem CassPrimitives.U_strictMono (P : CassPrimitives f U d m) : StrictMonoOn U (Ioi 0) :=
  strictMonoOn_of_deriv_pos (convex_Ioi 0) P.U_cont
    (fun c hc => by rw [interior_Ioi] at hc; exact P.U_prime_pos c hc)

/-- Welfare exists for a path whose consumption stays in a compact positive interval. -/
theorem CassPrimitives.exists_welfare (P : CassPrimitives f U d m) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Ici 0)) {lo hi : ℝ} (hlo : 0 < lo) (hlh : lo ≤ hi)
    (hb : ∀ t, 0 ≤ t → lo ≤ c t ∧ c t ≤ hi) : ∃ J, HasWelfare U (discount d) c J :=
  exists_hasWelfare_of_compact_consumption U c P.d_pos hlh
    (P.U_cont.mono (fun _ hx => hlo.trans_le hx.1)) hc (fun t ht => ⟨(hb t ht).1, (hb t ht).2⟩)

/-- The certified optimum's welfare exists. -/
theorem optimalPath_welfare (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k) :
    ∃ J, HasWelfare U (discount d) (optimalPath P hk).consumption J := by
  obtain ⟨q, -, hc⟩ := optimalPath_spec P hk
  exact hc.welfare

/-- Optimal lifetime welfare from capital `k`. -/
noncomputable def value (P : CassPrimitives f U d m) (k : ℝ) : ℝ :=
  if hk : 0 < k then Classical.choose (optimalPath_welfare P hk) else 0

theorem value_spec (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k) :
    HasWelfare U (discount d) (optimalPath P hk).consumption (value P k) := by
  simp only [value, hk, ↓reduceDIte]
  exact Classical.choose_spec (optimalPath_welfare P hk)

/-- The value bounds the welfare of every Cass-feasible path from `k`. -/
theorem value_ge (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k) {b : FeasiblePath f m}
    (hb : b.NonnegativeInvestment) (hb0 : b.capital 0 = k) {J : ℝ}
    (hJ : HasWelfare U (discount d) b.consumption J) : J ≤ value P k := by
  obtain ⟨q, h0, hc⟩ := optimalPath_spec P hk
  exact (hc.isCassOptimal P (value_spec P hk)).2.2 b hb (h0.trans hb0.symm) J hJ

/-- A certified path from `k` attains the value. -/
theorem value_eq (P : CassPrimitives f U d m) {a : FeasiblePath f m} {q : ℝ → ℝ}
    (hc : CassCertificate f U d m a q) {J : ℝ} (hJ : HasWelfare U (discount d) a.consumption J) :
    value P (a.capital 0) = J := by
  have hk := hc.capital_pos 0 le_rfl
  obtain ⟨qo, h0, hoc⟩ := optimalPath_spec P hk
  exact ((hc.eq_of_isCassOptimal P hJ (hoc.isCassOptimal P (value_spec P hk)) h0.symm).1)

/-- The finite-horizon comparison with unequal initial stocks: the boundary term at
time zero is retained. -/
theorem finite_horizon_comparison' {w : ℝ → ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) {T : ℝ} (hT : 0 ≤ T) :
    welfare U w b.consumption T - welfare U w a.consumption T ≤
      boundary v.price a.capital b.capital T - boundary v.price a.capital b.capital 0 := by
  have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
  have haint :=
    ((welfare_integrand_continuous v a).mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
  have hbint :=
    ((welfare_integrand_continuous v b).mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
  have hBint := ((boundaryRate_continuous v b).mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
  have hFTC : (∫ t in (0 : ℝ)..T, boundaryRate v b t) =
      boundary v.price a.capital b.capital T - boundary v.price a.capital b.capital 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hBint
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact hasDerivAt_boundary v b ht.1
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..T,
      (w t * U (a.consumption t) - w t * U (b.consumption t)) + boundaryRate v b t := by
    apply intervalIntegral.integral_nonneg hT
    intro t ht
    simpa only [mul_sub] using pointwise_comparison v b halloc ht.1
  rw [intervalIntegral.integral_add (haint.sub hbint) hBint,
    intervalIntegral.integral_sub haint hbint, hFTC] at hnonneg
  change welfare U w a.consumption T - welfare U w b.consumption T +
    (boundary v.price a.capital b.capital T - boundary v.price a.capital b.capital 0) ≥ 0
    at hnonneg
  linarith

/-- The initial current-value costate is a supergradient of the value function. -/
theorem value_le_supergradient (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) {k1 : ℝ} (hk1 : 0 < k1) :
    value P k1 ≤ value P (a.capital 0) + q 0 * (k1 - a.capital 0) := by
  obtain ⟨Ja, hJa⟩ := hc.welfare
  rw [value_eq P hc hJa]
  obtain ⟨qb, hb0, hbc⟩ := optimalPath_spec P hk1
  set b := optimalPath P hk1
  have hJb := value_spec P hk1
  let v := cassSupportingPrices f U q d m a P.f_conc.concaveOn P.U_conc.concaveOn P.U_cont
    P.f_diff P.U_diff P.f_prime_cont P.U_prime_cont hc.capital_pos
    (fun t ht => (P.U_prime_pos _ (a.consumption_pos t ht)).le) hc.costate
  have halloc : AllocationComparison v b := by
    apply allocation_of_cass v
    · intro t ht
      exact mul_le_mul_of_nonneg_left (hc.wedge t ht) (discount_pos d t).le
    · intro t ht
      change (discount d t * q t - discount d t * deriv U (a.consumption t)) *
        a.investment t = 0
      calc
        _ = discount d t * ((q t - deriv U (a.consumption t)) * a.investment t) := by ring
        _ = 0 := by rw [hc.slack t ht, mul_zero]
    · exact hbc.investment_nonneg
  obtain ⟨K, hK, hcap⟩ := P.exists_capacity (max (a.capital 0) k1)
  have hterm : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0) :=
    Terminal.terminal_tendsto_zero_of_bounded_capital hc.transversality
      (fun t ht => ⟨a.capital_nonneg t ht,
        a.capital_le_capacity hcap ((le_max_left _ _).trans hK) t ht⟩)
      (fun t ht => ⟨b.capital_nonneg t ht,
        b.capital_le_capacity hcap (hb0 ▸ (le_max_right _ _).trans hK) t ht⟩)
  have hle : value P k1 - Ja ≤ 0 - boundary v.price a.capital b.capital 0 :=
    le_of_tendsto_of_tendsto (hJb.sub hJa) (hterm.sub_const _)
      (by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        exact finite_horizon_comparison' v b halloc hT)
  have hB0 : boundary v.price a.capital b.capital 0 = q 0 * (a.capital 0 - k1) := by
    simp only [boundary, v, cassSupportingPrices, discount, mul_zero, Real.exp_zero, one_mul, hb0]
  rw [hB0] at hle
  linarith

/-- The path that copies `a`'s investment from a different initial stock. -/
noncomputable def FeasiblePath.mimic (P : CassPrimitives f U d m) (a : FeasiblePath f m)
    (Δ : ℝ) (hk : ∀ t, 0 ≤ t → 0 < a.capital t + Δ * Real.exp (-m * t))
    (hc : ∀ t, 0 ≤ t → 0 < f (a.capital t + Δ * Real.exp (-m * t)) - a.investment t) :
    FeasiblePath f m where
  capital := fun t => a.capital t + Δ * Real.exp (-m * t)
  consumption := fun t => f (a.capital t + Δ * Real.exp (-m * t)) - a.investment t
  investment := a.investment
  capital_nonneg := fun t ht => (hk t ht).le
  consumption_pos := hc
  consumption_continuous := by
    apply ContinuousOn.sub _ a.investment_continuous
    exact P.f_cont.comp (a.capital_continuous.add (continuousOn_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn))
      (fun t ht => hk t ht)
  investment_continuous := a.investment_continuous
  resource := fun t _ => by ring
  dynamics := fun t ht => by
    have he : HasDerivAt (fun s => Δ * Real.exp (-m * s)) (Δ * (Real.exp (-m * t) * (-m))) t := by
      have := ((hasDerivAt_id t).const_mul (-m)).exp.const_mul Δ
      simpa only [id, mul_one] using this
    refine ((a.dynamics t ht).add he).congr_deriv ?_
    ring

/-- The value function is strictly increasing. -/
theorem value_strictMono (P : CassPrimitives f U d m) : StrictMonoOn (value P) (Ioi 0) := by
  intro k0 hk0 k1 hk1 h01
  have hk0' : (0 : ℝ) < k0 := hk0
  obtain ⟨q, ha0, hc⟩ := optimalPath_spec P hk0'
  set a := optimalPath P hk0'
  set Δ := k1 - k0
  have hΔ : 0 < Δ := sub_pos.mpr h01
  have hkb : ∀ t, 0 ≤ t → a.capital t < a.capital t + Δ * Real.exp (-m * t) := fun t _ => by
    have := mul_pos hΔ (Real.exp_pos (-m * t))
    linarith
  have hcb : ∀ t, 0 ≤ t → a.consumption t <
      f (a.capital t + Δ * Real.exp (-m * t)) - a.investment t := fun t ht => by
    have hf := P.f_strictMono (hc.capital_pos t ht) ((hc.capital_pos t ht).trans (hkb t ht))
      (hkb t ht)
    have hr := a.resource t ht
    linarith
  let b := a.mimic P Δ (fun t ht => (hc.capital_pos t ht).trans (hkb t ht))
    (fun t ht => (a.consumption_pos t ht).trans (hcb t ht))
  have hb0 : b.capital 0 = k1 := by
    change a.capital 0 + Δ * Real.exp (-m * 0) = k1
    rw [ha0, mul_zero, Real.exp_zero, mul_one]
    ring
  -- `b`'s consumption is bounded between `a`'s lower bound and output at a capacity
  obtain ⟨hk, hcon, -⟩ := hc.dynamics P
  obtain ⟨lo, hi, hlo, hlh, hbd⟩ := exists_pos_bounds a.consumption_continuous
    a.consumption_pos (cassSteadyConsumption_pos P) hcon
  obtain ⟨K, hK, hcap⟩ := P.exists_capacity (a.capital 0)
  have hkK : ∀ t, 0 ≤ t → a.capital t ≤ K := a.capital_le_capacity hcap hK
  have hbub : ∀ t, 0 ≤ t → b.consumption t ≤ f (K + Δ) := fun t ht => by
    change f (a.capital t + Δ * Real.exp (-m * t)) - a.investment t ≤ f (K + Δ)
    have hz := hc.investment_nonneg t ht
    have hle : a.capital t + Δ * Real.exp (-m * t) ≤ K + Δ := by
      have := mul_le_of_le_one_right hΔ.le (Real.exp_le_one_iff.mpr
        (by nlinarith [P.m_pos, ht] : -m * t ≤ 0))
      linarith [hkK t ht]
    have hmono := P.f_strictMono.monotoneOn ((hc.capital_pos t ht).trans (hkb t ht))
      (show (0 : ℝ) < K + Δ by linarith [hc.capital_pos t ht, hkK t ht]) hle
    linarith
  obtain ⟨Jb, hJb⟩ := P.exists_welfare b.consumption_continuous hlo
    (show lo ≤ f (K + Δ) from ((hbd 0 le_rfl).1.trans (hcb 0 le_rfl).le).trans (hbub 0 le_rfl))
    (fun t ht => ⟨((hbd t ht).1.trans (hcb t ht).le), hbub t ht⟩)
  have hvb := value_ge P hk1 (b := b) hc.investment_nonneg hb0 hJb
  have hva := value_spec P hk0'
  -- strictly positive welfare gain
  have hgain : 0 < Jb - value P k0 := by
    apply positive_limit_of_integral_nonneg_of_pos (F := fun t =>
      discount d t * U (b.consumption t) - discount d t * U (a.consumption t)) (t₀ := 0)
    · exact ((discount_continuous d).continuousOn.mul (P.U_cont.comp b.consumption_continuous
        b.consumption_pos)).sub ((discount_continuous d).continuousOn.mul
        (P.U_cont.comp a.consumption_continuous a.consumption_pos))
    · intro t ht
      have := P.U_strictMono (a.consumption_pos t ht) (b.consumption_pos t ht) (hcb t ht)
      nlinarith [discount_pos d t]
    · exact le_rfl
    · have := P.U_strictMono (a.consumption_pos 0 le_rfl) (b.consumption_pos 0 le_rfl)
        (hcb 0 le_rfl)
      nlinarith [discount_pos d 0]
    · refine (hJb.sub hva).congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
      have h1 : IntervalIntegrable (fun t => discount d t * U (b.consumption t)) volume 0 T :=
        (((discount_continuous d).continuousOn.mul (P.U_cont.comp
        b.consumption_continuous b.consumption_pos)).mono hsub).intervalIntegrable_of_Icc hT
      have h2 : IntervalIntegrable (fun t => discount d t * U (a.consumption t)) volume 0 T :=
        (((discount_continuous d).continuousOn.mul (P.U_cont.comp
        a.consumption_continuous a.consumption_pos)).mono hsub).intervalIntegrable_of_Icc hT
      simp only [welfare]
      exact (intervalIntegral.integral_sub h1 h2).symm
  linarith

/-- The mixture of two paths: capital and investment are averaged, and consumption
takes the output at averaged capital net of averaged investment. -/
noncomputable def FeasiblePath.mix (P : CassPrimitives f U d m) (a b : FeasiblePath f m)
    (θ : ℝ)
    (hk : ∀ t, 0 ≤ t → 0 < θ * a.capital t + (1 - θ) * b.capital t)
    (hc : ∀ t, 0 ≤ t → 0 < f (θ * a.capital t + (1 - θ) * b.capital t) -
      (θ * a.investment t + (1 - θ) * b.investment t)) : FeasiblePath f m where
  capital := fun t => θ * a.capital t + (1 - θ) * b.capital t
  consumption := fun t => f (θ * a.capital t + (1 - θ) * b.capital t) -
    (θ * a.investment t + (1 - θ) * b.investment t)
  investment := fun t => θ * a.investment t + (1 - θ) * b.investment t
  capital_nonneg := fun t ht => (hk t ht).le
  consumption_pos := hc
  consumption_continuous := by
    apply ContinuousOn.sub _ ((continuousOn_const.mul a.investment_continuous).add
      (continuousOn_const.mul b.investment_continuous))
    exact P.f_cont.comp ((continuousOn_const.mul a.capital_continuous).add
      (continuousOn_const.mul b.capital_continuous)) (fun t ht => hk t ht)
  investment_continuous := (continuousOn_const.mul a.investment_continuous).add
      (continuousOn_const.mul b.investment_continuous)
  resource := fun t _ => by ring
  dynamics := fun t ht => by
    refine (((a.dynamics t ht).const_mul θ).add
      ((b.dynamics t ht).const_mul (1 - θ))).congr_deriv ?_
    ring

/-- The value function is strictly concave. -/
theorem value_strictConcave (P : CassPrimitives f U d m) :
    StrictConcaveOn ℝ (Ioi 0) (value P) := by
  refine ⟨convex_Ioi 0, fun k0 hk0 k1 hk1 hne θ θ' hθ hθ' hsum => ?_⟩
  have hk0' : (0 : ℝ) < k0 := hk0
  have hk1' : (0 : ℝ) < k1 := hk1
  obtain ⟨qa, ha0, hca⟩ := optimalPath_spec P hk0'
  obtain ⟨qb, hb0, hcb⟩ := optimalPath_spec P hk1'
  set a := optimalPath P hk0'
  set b := optimalPath P hk1'
  have hθ'' : θ' = 1 - θ := by linarith
  subst hθ''
  have hkm : ∀ t, 0 ≤ t → 0 < θ * a.capital t + (1 - θ) * b.capital t := fun t ht => by
    have := mul_pos hθ (hca.capital_pos t ht)
    have := mul_pos hθ' (hcb.capital_pos t ht)
    linarith
  -- concavity of `f`: mixed output is at least the mixture of outputs
  have hfmix : ∀ t, 0 ≤ t → θ * f (a.capital t) + (1 - θ) * f (b.capital t) ≤
      f (θ * a.capital t + (1 - θ) * b.capital t) := fun t ht =>
    P.f_conc.concaveOn.2 (a.capital_nonneg t ht) (b.capital_nonneg t ht) hθ.le hθ'.le
      (by ring)
  have hcm : ∀ t, 0 ≤ t → θ * a.consumption t + (1 - θ) * b.consumption t ≤
      f (θ * a.capital t + (1 - θ) * b.capital t) -
        (θ * a.investment t + (1 - θ) * b.investment t) := fun t ht => by
    have := hfmix t ht
    have ha := a.resource t ht
    have hb := b.resource t ht
    nlinarith
  have hcpos : ∀ t, 0 ≤ t → 0 < θ * a.consumption t + (1 - θ) * b.consumption t :=
    fun t ht => by
      have := mul_pos hθ (a.consumption_pos t ht)
      have := mul_pos hθ' (b.consumption_pos t ht)
      linarith
  let c := a.mix P b θ hkm (fun t ht => (hcpos t ht).trans_le (hcm t ht))
  have hc0 : c.capital 0 = θ • k0 + (1 - θ) • k1 := by
    change θ * a.capital 0 + (1 - θ) * b.capital 0 = _
    rw [ha0, hb0, smul_eq_mul, smul_eq_mul]
  -- bounds for the welfare of the mixture
  obtain ⟨-, hacon, -⟩ := hca.dynamics P
  obtain ⟨-, hbcon, -⟩ := hcb.dynamics P
  obtain ⟨loa, hia, hloa, -, hbda⟩ := exists_pos_bounds a.consumption_continuous
    a.consumption_pos (cassSteadyConsumption_pos P) hacon
  obtain ⟨lob, hib, hlob, -, hbdb⟩ := exists_pos_bounds b.consumption_continuous
    b.consumption_pos (cassSteadyConsumption_pos P) hbcon
  obtain ⟨K, hK, hcap⟩ := P.exists_capacity (max k0 k1)
  have hkKa := a.capital_le_capacity hcap (ha0 ▸ (le_max_left _ _).trans hK)
  have hkKb := b.capital_le_capacity hcap (hb0 ▸ (le_max_right _ _).trans hK)
  set lo := min loa lob
  have hlo : 0 < lo := lt_min hloa hlob
  have hclo : ∀ t, 0 ≤ t → lo ≤ c.consumption t := fun t ht => by
    have h1 := (hbda t ht).1
    have h2 := (hbdb t ht).1
    have h3 : lo ≤ θ * a.consumption t + (1 - θ) * b.consumption t := by
      have := mul_le_mul_of_nonneg_left ((min_le_left loa lob).trans h1) hθ.le
      have := mul_le_mul_of_nonneg_left ((min_le_right loa lob).trans h2) hθ'.le
      nlinarith
    exact h3.trans (hcm t ht)
  have hchi : ∀ t, 0 ≤ t → c.consumption t ≤ f K := fun t ht => by
    change f (θ * a.capital t + (1 - θ) * b.capital t) -
      (θ * a.investment t + (1 - θ) * b.investment t) ≤ f K
    have hz : 0 ≤ θ * a.investment t + (1 - θ) * b.investment t := by
      have := mul_nonneg hθ.le (hca.investment_nonneg t ht)
      have := mul_nonneg hθ'.le (hcb.investment_nonneg t ht)
      linarith
    have hkle : θ * a.capital t + (1 - θ) * b.capital t ≤ K := by
      have := mul_le_mul_of_nonneg_left (hkKa t ht) hθ.le
      have := mul_le_mul_of_nonneg_left (hkKb t ht) hθ'.le
      nlinarith
    have := P.f_strictMono.monotoneOn (hkm t ht) ((hkm t ht).trans_le hkle) hkle
    linarith
  obtain ⟨Jc, hJc⟩ := P.exists_welfare c.consumption_continuous hlo
    ((hclo 0 le_rfl).trans (hchi 0 le_rfl)) (fun t ht => ⟨hclo t ht, hchi t ht⟩)
  have hcinv : c.NonnegativeInvestment := fun t ht => by
    have := mul_nonneg hθ.le (hca.investment_nonneg t ht)
    have := mul_nonneg hθ'.le (hcb.investment_nonneg t ht)
    change 0 ≤ θ * a.investment t + (1 - θ) * b.investment t
    linarith
  have hvc := value_ge P (show 0 < θ • k0 + (1 - θ) • k1 from hc0 ▸ hkm 0 le_rfl) hcinv hc0 hJc
  have hva := value_spec P hk0'
  have hvb := value_spec P hk1'
  -- the strict gain at time zero from strict concavity of `f`
  have hstrict0 : θ * a.consumption 0 + (1 - θ) * b.consumption 0 < c.consumption 0 := by
    have hne' : a.capital 0 ≠ b.capital 0 := by rw [ha0, hb0]; exact hne
    have hf := P.f_conc.2 (a.capital_nonneg 0 le_rfl) (b.capital_nonneg 0 le_rfl) hne' hθ hθ'
      (by ring)
    simp only [smul_eq_mul] at hf
    have ha := a.resource 0 le_rfl
    have hb := b.resource 0 le_rfl
    change _ < f (θ * a.capital 0 + (1 - θ) * b.capital 0) -
      (θ * a.investment 0 + (1 - θ) * b.investment 0)
    nlinarith
  have hUmix : ∀ t, 0 ≤ t → θ * U (a.consumption t) + (1 - θ) * U (b.consumption t) ≤
      U (c.consumption t) := fun t ht => by
    have h1 := P.U_conc.concaveOn.2 (a.consumption_pos t ht) (b.consumption_pos t ht) hθ.le
      hθ'.le (by ring)
    simp only [smul_eq_mul] at h1
    have h2 := P.U_strictMono.monotoneOn (hcpos t ht) (c.consumption_pos t ht) (hcm t ht)
    linarith
  have hgain : 0 < Jc - (θ * value P k0 + (1 - θ) * value P k1) := by
    apply positive_limit_of_integral_nonneg_of_pos (F := fun t =>
      discount d t * U (c.consumption t) - (θ * (discount d t * U (a.consumption t)) +
        (1 - θ) * (discount d t * U (b.consumption t)))) (t₀ := 0)
    · have hU : ∀ e : FeasiblePath f m,
          ContinuousOn (fun t => discount d t * U (e.consumption t)) (Ici 0) := fun e =>
        (discount_continuous d).continuousOn.mul (P.U_cont.comp e.consumption_continuous
          e.consumption_pos)
      exact (hU c).sub (((hU a).const_smul θ).add ((hU b).const_smul (1 - θ)))
    · intro t ht
      have := hUmix t ht
      nlinarith [discount_pos d t]
    · exact le_rfl
    · have h1 := P.U_conc.concaveOn.2 (a.consumption_pos 0 le_rfl) (b.consumption_pos 0 le_rfl)
        hθ.le hθ'.le (by ring)
      simp only [smul_eq_mul] at h1
      have h2 := P.U_strictMono (hcpos 0 le_rfl) (c.consumption_pos 0 le_rfl) hstrict0
      nlinarith [discount_pos d 0]
    · refine (hJc.sub ((hva.const_mul θ).add (hvb.const_mul (1 - θ)))).congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
      have hI : ∀ e : FeasiblePath f m, IntervalIntegrable
          (fun t => discount d t * U (e.consumption t)) volume 0 T := fun e =>
        (((discount_continuous d).continuousOn.mul (P.U_cont.comp e.consumption_continuous
          e.consumption_pos)).mono hsub).intervalIntegrable_of_Icc hT
      simp only [welfare]
      rw [intervalIntegral.integral_sub (hI c) (((hI a).const_mul θ).add
        ((hI b).const_mul (1 - θ))), intervalIntegral.integral_add ((hI a).const_mul θ)
        ((hI b).const_mul (1 - θ)), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
  simp only [smul_eq_mul] at hvc ⊢
  linarith

end RamseyCassKoopmans

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# The envelope theorem for the Cass value function

`value_hasDerivAt`: for a certified optimum `(a, q)` from `k₀`,
`V'(k₀) = q(0)`, the initial current-value costate; when the optimum invests at
time zero this is `U'(c(0))` (`value_deriv_eq_marginal_utility`).

The proof follows Clausen and Strub (2020), *Reverse calculus and nested
optimization*, J. Econ. Theory 187: a function squeezed between a lower and an
upper support function that touch it at `k₀` and share a derivative there is
differentiable with that derivative (`clausen_strub_sandwich`). The upper support
is the affine supergradient bound `V(k₀) + q(0)(k - k₀)`. The lower support is the
welfare `L(k)` of the path that copies the optimum's investment from `k`; its
derivative at `k₀` is identified from the costate identity
`q(0) = ∫₀^∞ e^{-(d+m)t} U'(c) f'(k) dt` and uniform continuity of `U'` and `f'`.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

/-- Clausen–Strub sandwich: a function lying between two functions that touch it at
`x₀` and are differentiable there with a common derivative `D` has derivative `D`. -/
theorem clausen_strub_sandwich {V L H : ℝ → ℝ} {x₀ D : ℝ}
    (hL : HasDerivAt L D x₀) (hH : HasDerivAt H D x₀)
    (hLV : ∀ᶠ x in 𝓝 x₀, L x ≤ V x) (hVH : ∀ᶠ x in 𝓝 x₀, V x ≤ H x)
    (hLx : L x₀ = V x₀) (hHx : H x₀ = V x₀) : HasDerivAt V D x₀ := by
  rw [hasDerivAt_iff_tendsto_slope] at hL hH ⊢
  rw [← nhdsLT_sup_nhdsGT, tendsto_sup] at hL hH ⊢
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hH.1 hL.1 ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds hVH, self_mem_nhdsWithin] with x hx hlt
      rw [slope_def_field, slope_def_field, ← hHx]
      exact div_le_div_of_nonpos_of_le (sub_nonpos.mpr (le_of_lt hlt)) (by linarith)
    · filter_upwards [nhdsWithin_le_nhds hLV, self_mem_nhdsWithin] with x hx hlt
      rw [slope_def_field, slope_def_field, ← hLx]
      exact div_le_div_of_nonpos_of_le (sub_nonpos.mpr (le_of_lt hlt)) (by linarith)
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL.2 hH.2 ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds hLV, self_mem_nhdsWithin] with x hx hgt
      rw [slope_def_field, slope_def_field, ← hLx]
      exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr (le_of_lt hgt))
    · filter_upwards [nhdsWithin_le_nhds hVH, self_mem_nhdsWithin] with x hx hgt
      rw [slope_def_field, slope_def_field, ← hHx]
      exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr (le_of_lt hgt))

/-- Consumption of the path copying `a`'s investment from stock `a.capital 0 + Δ`. -/
noncomputable def mimicConsumption (a : FeasiblePath f m) (Δ t : ℝ) : ℝ :=
  f (a.capital t + Δ * Real.exp (-m * t)) - a.investment t

theorem integral_exp_neg_le {r : ℝ} (hr : 0 < r) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, Real.exp (-r * t) ≤ 1 / r := by
  have hd : ∀ t, HasDerivAt (fun s => -Real.exp (-r * s) / r) (Real.exp (-r * t)) t := by
    intro t
    have := (((hasDerivAt_id t).const_mul (-r)).exp.neg).div_const r
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (Continuous.intervalIntegrable (by fun_prop) 0 T)]
  have := Real.exp_pos (-r * T)
  simp only [mul_zero, Real.exp_zero]
  rw [div_sub_div_same, show -Real.exp (-r * T) - -1 = 1 - Real.exp (-r * T) by ring]
  exact div_le_div_of_nonneg_right (by linarith) hr.le

set_option maxHeartbeats 1000000 in
-- The envelope proof assembles many local estimates in one context; the fresh-source
-- audit, which elaborates every module in a single file, needs the larger budget.
/-- The envelope theorem: `V'(k₀) = q(0)`. -/
theorem value_hasDerivAt (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) :
    HasDerivAt (value P) (q 0) (a.capital 0) := by
  classical
  set k0 := a.capital 0 with hk0_def
  have hk0 : 0 < k0 := hc.capital_pos 0 le_rfl
  obtain ⟨Ja, hJa⟩ := hc.welfare
  have hVa : value P k0 = Ja := value_eq P hc hJa
  have hm := P.m_pos
  have hdm : 0 < d + m := add_pos P.d_pos hm
  -- compact bounds for the optimum
  obtain ⟨hk, hcon, -⟩ := hc.dynamics P
  obtain ⟨kmin, kmax, hkmin, -, hkbd⟩ := exists_pos_bounds a.capital_continuous
    hc.capital_pos (cassSteady_spec P).1 hk
  obtain ⟨cmin, cmax, hcmin, -, hcbd⟩ := exists_pos_bounds a.consumption_continuous
    a.consumption_pos (cassSteadyConsumption_pos P) hcon
  set k1 := kmin / 2 with hk1_def
  have hk1 : 0 < k1 := half_pos hkmin
  set Mf := deriv f k1
  have hMf : 0 < Mf := P.f_prime_pos k1 hk1
  have hfanti := production_deriv_strictAnti f P.f_conc P.f_diff
  -- output is Lipschitz with constant `Mf` above `k1`
  have hlip : ∀ x y, k1 ≤ x → k1 ≤ y → |f y - f x| ≤ Mf * |y - x| := by
    intro x y hx hy
    have hx0 : 0 < x := hk1.trans_le hx
    have hy0 : 0 < y := hk1.trans_le hy
    have h1 := concave_support P.f_conc.concaveOn (mem_Ici.mpr hx0.le) (mem_Ici.mpr hy0.le)
      (P.f_diff x hx0).hasDerivAt
    have h2 := concave_support P.f_conc.concaveOn (mem_Ici.mpr hy0.le) (mem_Ici.mpr hx0.le)
      (P.f_diff y hy0).hasDerivAt
    have hfx : 0 < deriv f x ∧ deriv f x ≤ Mf :=
      ⟨P.f_prime_pos x hx0, hfanti.antitoneOn hk1 hx0 hx⟩
    have hfy : 0 < deriv f y ∧ deriv f y ≤ Mf :=
      ⟨P.f_prime_pos y hy0, hfanti.antitoneOn hk1 hy0 hy⟩
    rw [abs_le]
    rcases le_total x y with hxy | hxy
    · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
      constructor <;> nlinarith
    · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      constructor <;> nlinarith
  set δ0 := min (kmin / 2) (min 1 (cmin / (2 * Mf)))
  have hδ0 : 0 < δ0 := lt_min hk1 (lt_min one_pos (div_pos hcmin (by linarith)))
  set cmax' := f (kmax + 1)
  -- the mimic path is admissible for `|Δ| < δ0`
  have hexp : ∀ t, 0 ≤ t → 0 < Real.exp (-m * t) ∧ Real.exp (-m * t) ≤ 1 := fun t ht =>
    ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by nlinarith)⟩
  have hkb : ∀ Δ, |Δ| < δ0 → ∀ t, 0 ≤ t →
      k1 ≤ a.capital t + Δ * Real.exp (-m * t) ∧ a.capital t + Δ * Real.exp (-m * t) ≤ kmax + 1 ∧
        |a.capital t + Δ * Real.exp (-m * t) - a.capital t| ≤ |Δ| := by
    intro Δ hΔ t ht
    obtain ⟨he0, he1⟩ := hexp t ht
    have habs : |Δ * Real.exp (-m * t)| ≤ |Δ| := by
      rw [abs_mul, abs_of_pos he0]
      exact mul_le_of_le_one_right (abs_nonneg _) he1
    have hΔk : |Δ| < kmin / 2 := hΔ.trans_le (min_le_left _ _)
    have hΔ1 : |Δ| < 1 := hΔ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    obtain ⟨hlo, hhi⟩ := hkbd t ht
    have := neg_abs_le (Δ * Real.exp (-m * t))
    have := le_abs_self (Δ * Real.exp (-m * t))
    refine ⟨by linarith, by linarith, ?_⟩
    rw [show a.capital t + Δ * Real.exp (-m * t) - a.capital t = Δ * Real.exp (-m * t) by ring]
    exact habs
  have hcb : ∀ Δ, |Δ| < δ0 → ∀ t, 0 ≤ t →
      cmin / 2 ≤ mimicConsumption a Δ t ∧ mimicConsumption a Δ t ≤ cmax' ∧
        |mimicConsumption a Δ t - a.consumption t| ≤ Mf * |Δ| := by
    intro Δ hΔ t ht
    obtain ⟨hb1, hb2, hb3⟩ := hkb Δ hΔ t ht
    have hdiff : |mimicConsumption a Δ t - a.consumption t| ≤ Mf * |Δ| := by
      have hr := a.resource t ht
      have heq : mimicConsumption a Δ t - a.consumption t =
          f (a.capital t + Δ * Real.exp (-m * t)) - f (a.capital t) := by
        simp only [mimicConsumption]
        linarith
      rw [heq]
      exact (hlip _ _ (by linarith [(hkbd t ht).1]) hb1).trans
        (mul_le_mul_of_nonneg_left hb3 hMf.le)
    have hΔc : Mf * |Δ| ≤ cmin / 2 := by
      have h := hΔ.le.trans ((min_le_right _ _).trans (min_le_right _ _))
      rw [le_div_iff₀ (by linarith)] at h
      linarith
    refine ⟨?_, ?_, hdiff⟩
    · have := (abs_le.mp hdiff).1
      linarith [(hcbd t ht).1]
    · have hz := hc.investment_nonneg t ht
      have hmono := P.f_strictMono.monotoneOn (hk1.trans_le hb1)
        (show (0 : ℝ) < kmax + 1 by linarith [(hkbd t ht).1, (hkbd t ht).2]) hb2
      simp only [mimicConsumption]
      linarith
  have hcbpos : ∀ Δ, |Δ| < δ0 → ∀ t, 0 ≤ t → 0 < mimicConsumption a Δ t := fun Δ hΔ t ht =>
    (half_pos hcmin).trans_le (hcb Δ hΔ t ht).1
  let b : ∀ Δ, |Δ| < δ0 → FeasiblePath f m := fun Δ hΔ => a.mimic P Δ
    (fun t ht => hk1.trans_le (hkb Δ hΔ t ht).1) (hcbpos Δ hΔ)
  have hbcons : ∀ Δ hΔ, (b Δ hΔ).consumption = mimicConsumption a Δ := fun _ _ => rfl
  have hb0 : ∀ Δ hΔ, (b Δ hΔ).capital 0 = k0 + Δ := fun Δ hΔ => by
    change a.capital 0 + Δ * Real.exp (-m * 0) = k0 + Δ
    rw [mul_zero, Real.exp_zero, mul_one]
  have hbwel : ∀ Δ, |Δ| < δ0 → ∃ J, HasWelfare U (discount d) (mimicConsumption a Δ) J :=
    fun Δ hΔ => P.exists_welfare (b Δ hΔ).consumption_continuous (half_pos hcmin)
      ((hcb Δ hΔ 0 le_rfl).1.trans (hcb Δ hΔ 0 le_rfl).2.1)
      (fun t ht => ⟨(hcb Δ hΔ t ht).1, (hcb Δ hΔ t ht).2.1⟩)
  -- the lower support function
  let L : ℝ → ℝ := fun k => if h : ∃ J, HasWelfare U (discount d) (mimicConsumption a (k - k0)) J
    then Classical.choose h else value P k
  have hLspec : ∀ k, |k - k0| < δ0 →
      HasWelfare U (discount d) (mimicConsumption a (k - k0)) (L k) := fun k hk => by
    simp only [L, hbwel (k - k0) hk, ↓reduceDIte]
    exact Classical.choose_spec (hbwel (k - k0) hk)
  have hmim0 : ∀ t, 0 ≤ t → mimicConsumption a 0 t = a.consumption t := fun t ht => by
    simp only [mimicConsumption, zero_mul, add_zero]
    linarith [a.resource t ht]
  have hwcongr : ∀ {c1 c2 : ℝ → ℝ}, (∀ t, 0 ≤ t → c1 t = c2 t) → ∀ T, 0 ≤ T →
      welfare U (discount d) c1 T = welfare U (discount d) c2 T := by
    intro c1 c2 h T hT
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    simp only [h t ht.1]
  have hL0 : L k0 = value P k0 := by
    have h1 := hLspec k0 (by rw [sub_self, abs_zero]; exact hδ0)
    rw [sub_self] at h1
    have h2 : HasWelfare U (discount d) (mimicConsumption a 0) Ja :=
      hJa.congr' (by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        exact (hwcongr hmim0 T hT).symm)
    rw [hVa]
    exact tendsto_nhds_unique h1 h2
  -- the integrand of the derivative estimate
  set g : ℝ → ℝ → ℝ := fun Δ t => Real.exp (-(d + m) * t) *
    (deriv U (mimicConsumption a Δ t) * deriv f (a.capital t + Δ * Real.exp (-m * t)))
  have hgcont : ∀ Δ, |Δ| < δ0 → ContinuousOn (g Δ) (Ici 0) := fun Δ hΔ => by
    have hkc : ContinuousOn (fun t => a.capital t + Δ * Real.exp (-m * t)) (Ici 0) :=
      a.capital_continuous.add (continuousOn_const.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      ((P.U_prime_cont.comp (b Δ hΔ).consumption_continuous (hcbpos Δ hΔ)).mul
        (P.f_prime_cont.comp hkc (fun t ht => hk1.trans_le (hkb Δ hΔ t ht).1)))
  -- the costate identity: `∫₀^T g 0 → q(0)`
  have hq0 : Tendsto (fun T => ∫ t in (0 : ℝ)..T, g 0 t) atTop (𝓝 (q 0)) := by
    have hQ : ∀ t, 0 ≤ t → HasDerivAt (fun s => Real.exp (-(d + m) * s) * q s) (-(g 0 t)) t := by
      intro t ht
      have he := ((hasDerivAt_id t).const_mul (-(d + m))).exp
      refine (he.mul (hc.costate t ht)).congr_deriv ?_
      simp only [g, id, zero_mul, add_zero, hmim0 t ht]
      ring
    have hFTC : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, g 0 t =
        q 0 - Real.exp (-(d + m) * T) * q T := by
      intro T hT
      have hint : IntervalIntegrable (fun t => -(g 0 t)) volume 0 T :=
        ((hgcont 0 (by rw [abs_zero]; exact hδ0)).neg.mono
          (fun _ ht => ht.1)).intervalIntegrable_of_Icc hT
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => by
        rw [uIcc_of_le hT] at ht; exact hQ t ht.1) hint
      rw [intervalIntegral.integral_neg] at h
      simp only [mul_zero, Real.exp_zero, one_mul] at h
      linarith
    have hdecay : Tendsto (fun T => Real.exp (-(d + m) * T) * q T) atTop (𝓝 0) := by
      have h := hc.transversality.mul (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hm))
      rw [zero_mul] at h
      refine h.congr (fun T => ?_)
      simp only [Function.comp_apply, discount, id]
      rw [mul_comm, ← mul_assoc, ← Real.exp_add]
      ring_nf
    have := (hdecay.const_sub (q 0))
    rw [sub_zero] at this
    exact this.congr' (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact (hFTC T hT).symm)
  -- pointwise welfare gain bound
  have hpoint : ∀ Δ, |Δ| < δ0 → ∀ t, 0 ≤ t →
      Δ * g Δ t ≤ discount d t * U (mimicConsumption a Δ t) -
        discount d t * U (mimicConsumption a 0 t) := by
    intro Δ hΔ t ht
    have hca := a.consumption_pos t ht
    have hcΔ := hcbpos Δ hΔ t ht
    obtain ⟨hkΔ, -, -⟩ := hkb Δ hΔ t ht
    have hkΔpos : 0 < a.capital t + Δ * Real.exp (-m * t) := hk1.trans_le hkΔ
    have hU := concave_support P.U_conc.concaveOn hcΔ hca (P.U_diff _ hcΔ).hasDerivAt
    have hf := concave_support P.f_conc.concaveOn (mem_Ici.mpr hkΔpos.le)
      (mem_Ici.mpr (hc.capital_pos t ht).le) (P.f_diff _ hkΔpos).hasDerivAt
    have hr := a.resource t ht
    have hUp := (P.U_prime_pos _ hcΔ).le
    rw [hmim0 t ht]
    have hcdiff : mimicConsumption a Δ t - a.consumption t =
        f (a.capital t + Δ * Real.exp (-m * t)) - f (a.capital t) := by
      simp only [mimicConsumption]; linarith
    have hstep : deriv U (mimicConsumption a Δ t) *
        (deriv f (a.capital t + Δ * Real.exp (-m * t)) * (Δ * Real.exp (-m * t))) ≤
        U (mimicConsumption a Δ t) - U (a.consumption t) := by
      have h1 : deriv f (a.capital t + Δ * Real.exp (-m * t)) * (Δ * Real.exp (-m * t)) ≤
          mimicConsumption a Δ t - a.consumption t := by
        rw [hcdiff]
        have : a.capital t - (a.capital t + Δ * Real.exp (-m * t)) = -(Δ * Real.exp (-m * t)) :=
          by ring
        rw [this] at hf
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hUp
      linarith
    have hdisc : discount d t * Real.exp (-m * t) = Real.exp (-(d + m) * t) := by
      simp only [discount, ← Real.exp_add]
      ring_nf
    have := mul_le_mul_of_nonneg_left hstep (discount_pos d t).le
    calc Δ * g Δ t = discount d t * (deriv U (mimicConsumption a Δ t) *
          (deriv f (a.capital t + Δ * Real.exp (-m * t)) * (Δ * Real.exp (-m * t)))) := by
          simp only [g]
          rw [← hdisc]
          ring
      _ ≤ discount d t * (U (mimicConsumption a Δ t) - U (a.consumption t)) := this
      _ = _ := by ring
  -- uniform continuity of the integrand in `Δ`
  set MU := deriv U (cmin / 2)
  have hMU : 0 < MU := P.U_prime_pos _ (half_pos hcmin)
  have hUanti := P.U_conc.strictAntiOn_deriv P.U_diff
  have hucf := isCompact_Icc.uniformContinuousOn_of_continuous
    (P.f_prime_cont.mono (fun x hx => hk1.trans_le hx.1) :
      ContinuousOn (deriv f) (Icc k1 (kmax + 1)))
  have hucU := isCompact_Icc.uniformContinuousOn_of_continuous
    (P.U_prime_cont.mono (fun x hx => (half_pos hcmin).trans_le hx.1) :
      ContinuousOn (deriv U) (Icc (cmin / 2) cmax'))
  rw [Metric.uniformContinuousOn_iff] at hucf hucU
  have hcamem : ∀ t, 0 ≤ t → a.consumption t ∈ Icc (cmin / 2) cmax' := fun t ht => by
    have := hcb 0 (by rw [abs_zero]; exact hδ0) t ht
    rw [hmim0 t ht] at this
    exact ⟨this.1, this.2.1⟩
  have huniform : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ δ ≤ δ0 ∧ ∀ Δ, |Δ| < δ → ∀ t, 0 ≤ t →
      |g Δ t - g 0 t| ≤ ε * Real.exp (-(d + m) * t) := by
    intro ε hε
    obtain ⟨δf, hδf, hf⟩ := hucf (ε / (2 * (MU + 1))) (by positivity)
    obtain ⟨δU, hδU, hU⟩ := hucU (ε / (2 * (Mf + 1))) (by positivity)
    refine ⟨min δ0 (min δf (δU / (Mf + 1))), lt_min hδ0 (lt_min hδf (by positivity)),
      min_le_left _ _, fun Δ hΔ t ht => ?_⟩
    have hΔ0 : |Δ| < δ0 := hΔ.trans_le (min_le_left _ _)
    have hΔf : |Δ| < δf := hΔ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hΔU : |Δ| < δU / (Mf + 1) := hΔ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨hkΔ1, hkΔ2, hkΔ3⟩ := hkb Δ hΔ0 t ht
    obtain ⟨hcΔ1, hcΔ2, hcΔ3⟩ := hcb Δ hΔ0 t ht
    have hkamem : a.capital t ∈ Icc k1 (kmax + 1) :=
      ⟨by linarith [(hkbd t ht).1], by linarith [(hkbd t ht).2]⟩
    have hdf : |deriv f (a.capital t + Δ * Real.exp (-m * t)) - deriv f (a.capital t)| <
        ε / (2 * (MU + 1)) := by
      have := hf _ ⟨hkΔ1, hkΔ2⟩ _ hkamem (by rw [Real.dist_eq]; exact hkΔ3.trans_lt hΔf)
      rwa [Real.dist_eq] at this
    have hdU : |deriv U (mimicConsumption a Δ t) - deriv U (a.consumption t)| <
        ε / (2 * (Mf + 1)) := by
      have hlt : Mf * |Δ| < δU := by
        have := (lt_div_iff₀ (by linarith : (0 : ℝ) < Mf + 1)).mp hΔU
        nlinarith [abs_nonneg Δ]
      have := hU _ ⟨hcΔ1, hcΔ2⟩ _ (hcamem t ht) (by rw [Real.dist_eq]; exact hcΔ3.trans_lt hlt)
      rwa [Real.dist_eq] at this
    have hUb : 0 < deriv U (mimicConsumption a Δ t) ∧ deriv U (mimicConsumption a Δ t) ≤ MU :=
      ⟨P.U_prime_pos _ (hcbpos Δ hΔ0 t ht),
        hUanti.antitoneOn (half_pos hcmin) (hcbpos Δ hΔ0 t ht) hcΔ1⟩
    have hfb : 0 < deriv f (a.capital t) ∧ deriv f (a.capital t) ≤ Mf :=
      ⟨P.f_prime_pos _ (hc.capital_pos t ht), hfanti.antitoneOn hk1 (hc.capital_pos t ht)
        hkamem.1⟩
    have hdiff : g Δ t - g 0 t = Real.exp (-(d + m) * t) *
        (deriv U (mimicConsumption a Δ t) *
          (deriv f (a.capital t + Δ * Real.exp (-m * t)) - deriv f (a.capital t)) +
        deriv f (a.capital t) *
          (deriv U (mimicConsumption a Δ t) - deriv U (a.consumption t))) := by
      simp only [g, zero_mul, add_zero, hmim0 t ht]
      ring
    rw [hdiff, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm ε]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have h1 : |deriv U (mimicConsumption a Δ t) *
        (deriv f (a.capital t + Δ * Real.exp (-m * t)) - deriv f (a.capital t))| ≤ ε / 2 := by
      rw [abs_mul, abs_of_pos hUb.1]
      have := mul_le_mul hUb.2 hdf.le (abs_nonneg _) hMU.le
      have h2 : MU * (ε / (2 * (MU + 1))) ≤ ε / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have h2 : |deriv f (a.capital t) *
        (deriv U (mimicConsumption a Δ t) - deriv U (a.consumption t))| ≤ ε / 2 := by
      rw [abs_mul, abs_of_pos hfb.1]
      have := mul_le_mul hfb.2 hdU.le (abs_nonneg _) hMf.le
      have h3 : Mf * (ε / (2 * (Mf + 1))) ≤ ε / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
      _ = ε := by ring
  -- the lower support has derivative `q(0)` at `k0`
  have hLV : ∀ k, |k - k0| < δ0 → L k ≤ value P k := fun k hk => by
    have hkpos : 0 < k := by
      have := (abs_lt.mp hk).1
      have : δ0 ≤ kmin / 2 := min_le_left _ _
      linarith [(hkbd 0 le_rfl).1]
    exact value_ge P hkpos (b := b (k - k0) hk) hc.investment_nonneg
      ((hb0 (k - k0) hk).trans (by ring)) (hLspec k hk)
  have hnearδ0 : ∀ᶠ k in 𝓝 k0, |k - k0| < δ0 := by
    have := Metric.ball_mem_nhds k0 hδ0
    filter_upwards [this] with k hk
    rwa [Metric.mem_ball, Real.dist_eq] at hk
  have hLder : HasDerivAt L (q 0) k0 := by
    rw [hasDerivAt_iff_isLittleO]
    refine Asymptotics.IsLittleO.of_bound (fun ε hε => ?_)
    obtain ⟨δ, hδ, hδδ0, hunif⟩ := huniform (ε * (d + m)) (by positivity)
    have hnear : ∀ᶠ k in 𝓝 k0, |k - k0| < δ := by
      filter_upwards [Metric.ball_mem_nhds k0 hδ] with k hk
      rwa [Metric.mem_ball, Real.dist_eq] at hk
    filter_upwards [hnear] with k hk
    set Δ := k - k0
    have hΔ0 : |Δ| < δ0 := hk.trans_le hδδ0
    -- upper bound from `L ≤ V ≤ V(k0) + q(0)(k - k0)`
    have hup : L k - L k0 ≤ q 0 * Δ := by
      have h1 := hLV k hΔ0
      have hkpos : 0 < k := by
        have := (abs_lt.mp hΔ0).1
        have : δ0 ≤ kmin / 2 := min_le_left _ _
        linarith [(hkbd 0 le_rfl).1]
      have h2 := value_le_supergradient P hc hkpos
      rw [hL0]
      linarith
    -- lower bound from the pointwise gain and the costate identity
    have hlow : q 0 * Δ - ε * |Δ| ≤ L k - L k0 := by
      have hWk := hLspec k hΔ0
      have hW0 := hLspec k0 (by rw [sub_self, abs_zero]; exact hδ0)
      rw [sub_self] at hW0
      have hlimit : Tendsto (fun T => Δ * ∫ t in (0 : ℝ)..T, g 0 t) atTop (𝓝 (Δ * q 0)) :=
        hq0.const_mul Δ
      have hle : Δ * q 0 - ε * |Δ| ≤ L k - L k0 := by
        apply le_of_tendsto_of_tendsto (hlimit.sub_const (ε * |Δ|)) (hWk.sub hW0)
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
        have hIΔ : IntervalIntegrable (g Δ) volume 0 T :=
          ((hgcont Δ hΔ0).mono hsub).intervalIntegrable_of_Icc hT
        have hI0 : IntervalIntegrable (g 0) volume 0 T :=
          ((hgcont 0 (by rw [abs_zero]; exact hδ0)).mono hsub).intervalIntegrable_of_Icc hT
        have hUc : ∀ e : ℝ, |e| < δ0 → IntervalIntegrable
            (fun t => discount d t * U (mimicConsumption a e t)) volume 0 T := fun e he =>
          (((discount_continuous d).continuousOn.mul (P.U_cont.comp
            (b e he).consumption_continuous (hcbpos e he))).mono hsub).intervalIntegrable_of_Icc hT
        -- `Δ ∫ g Δ ≤ W_Δ(T) - W_0(T)`
        have hgain : Δ * ∫ t in (0 : ℝ)..T, g Δ t ≤
            welfare U (discount d) (mimicConsumption a Δ) T -
              welfare U (discount d) (mimicConsumption a 0) T := by
          simp only [welfare]
          rw [← intervalIntegral.integral_sub (hUc Δ hΔ0) (hUc 0 (by rw [abs_zero]; exact hδ0)),
            ← intervalIntegral.integral_const_mul]
          exact intervalIntegral.integral_mono_on hT (hIΔ.const_mul Δ)
            ((hUc Δ hΔ0).sub (hUc 0 (by rw [abs_zero]; exact hδ0)))
            (fun t ht => hpoint Δ hΔ0 t ht.1)
        -- `|∫ g Δ - ∫ g 0| ≤ ε`
        have hclose : |(∫ t in (0 : ℝ)..T, g Δ t) - ∫ t in (0 : ℝ)..T, g 0 t| ≤ ε := by
          rw [← intervalIntegral.integral_sub hIΔ hI0]
          have hexpI : IntervalIntegrable (fun t => ε * (d + m) * Real.exp (-(d + m) * t))
              volume 0 T := Continuous.intervalIntegrable (by fun_prop) 0 T
          calc |∫ t in (0 : ℝ)..T, g Δ t - g 0 t|
              ≤ ∫ t in (0 : ℝ)..T, ε * (d + m) * Real.exp (-(d + m) * t) := by
                rw [abs_le]
                constructor
                · have hexpN : IntervalIntegrable
                      (fun t => -(ε * (d + m) * Real.exp (-(d + m) * t))) volume 0 T := hexpI.neg
                  have h := intervalIntegral.integral_mono_on hT hexpN (hIΔ.sub hI0)
                    (fun t ht => show -(ε * (d + m) * Real.exp (-(d + m) * t)) ≤ g Δ t - g 0 t
                      from (abs_le.mp (hunif Δ hk t ht.1)).1)
                  rw [intervalIntegral.integral_neg] at h
                  exact h
                · exact intervalIntegral.integral_mono_on hT (hIΔ.sub hI0) hexpI
                    (fun t ht => (abs_le.mp (hunif Δ hk t ht.1)).2)
            _ = ε * (d + m) * ∫ t in (0 : ℝ)..T, Real.exp (-(d + m) * t) :=
                intervalIntegral.integral_const_mul _ _
            _ ≤ ε * (d + m) * (1 / (d + m)) :=
                mul_le_mul_of_nonneg_left (integral_exp_neg_le hdm T) (by positivity)
            _ = ε := by field_simp
        have hmul : |Δ * (∫ t in (0 : ℝ)..T, g Δ t) - Δ * ∫ t in (0 : ℝ)..T, g 0 t| ≤
            ε * |Δ| := by
          rw [← mul_sub, abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right hclose (abs_nonneg _)
        have := (abs_le.mp hmul).1
        linarith
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, abs_le]
    constructor <;> nlinarith [abs_nonneg Δ]
  -- the sandwich
  have hH : HasDerivAt (fun k => value P k0 + q 0 * (k - k0)) (q 0) k0 := by
    have := ((hasDerivAt_id k0).sub_const k0).const_mul (q 0) |>.const_add (value P k0)
    simpa only [id, mul_one] using this
  refine clausen_strub_sandwich hLder hH ?_ ?_ hL0 (by ring)
  · filter_upwards [hnearδ0] with k hk
    exact hLV k hk
  · filter_upwards [hnearδ0] with k hk
    have hkpos : 0 < k := by
      have := (abs_lt.mp hk).1
      have : δ0 ≤ kmin / 2 := min_le_left _ _
      linarith [(hkbd 0 le_rfl).1]
    exact value_le_supergradient P hc hkpos

/-- When the optimum invests at time zero, `V'(k₀) = U'(c(0))`. -/
theorem value_deriv_eq_marginal_utility (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) (hz : 0 < a.investment 0) :
    HasDerivAt (value P) (deriv U (a.consumption 0)) (a.capital 0) := by
  have h := hc.slack 0 le_rfl
  have hq : q 0 = deriv U (a.consumption 0) := by
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · exact absurd h (ne_of_gt hz)
  rw [← hq]
  exact value_hasDerivAt P hc

end RamseyCassKoopmans

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# Competitive decentralization of the Cass optimum

Households own the capital stock (per effective worker), rent it to firms at the
rental rate `R(t)`, supply labour for the wage `w(t)`, and choose consumption and
gross investment subject to the budget `c + z = R k + w`, accumulation
`k̇ = z - m k`, nonnegative assets, and irreversible investment `z ≥ 0`, the
household counterpart of Cass's constraint. Competitive firms rent capital until
`R = f'(k)`, and pay `w = f(k) - k f'(k)` (`firm_optimal`: this maximizes profit,
which is zero).

* `second_welfare_theorem`: the certified Cass optimum, with these prices, is a
  competitive equilibrium: no household plan asymptotically improves on it.
  Household assets may grow without bound; the comparison still closes because
  the boundary term is at most the discounted value of the planner's capital.
* `first_welfare_theorem`: every competitive-equilibrium allocation is Cass
  optimal, hence equals the unique optimum (`equilibrium_eq_optimum`).
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

/-- A household plan given rental and wage paths. -/
structure HouseholdPlan (R w : ℝ → ℝ) (m : ℝ) where
  capital : ℝ → ℝ
  consumption : ℝ → ℝ
  investment : ℝ → ℝ
  capital_nonneg : ∀ t, 0 ≤ t → 0 ≤ capital t
  consumption_pos : ∀ t, 0 ≤ t → 0 < consumption t
  consumption_continuous : ContinuousOn consumption (Ici 0)
  investment_continuous : ContinuousOn investment (Ici 0)
  investment_nonneg : ∀ t, 0 ≤ t → 0 ≤ investment t
  budget : ∀ t, 0 ≤ t → consumption t + investment t = R t * capital t + w t
  dynamics : ∀ t, 0 ≤ t → HasDerivAt capital (investment t - m * capital t) t

/-- A competitive equilibrium: firm optimality, feasibility, and household
optimality against every household plan from the same initial assets. -/
structure CompetitiveEquilibrium (f U R w : ℝ → ℝ) (d m : ℝ) (a : FeasiblePath f m) : Prop where
  capital_pos : ∀ t, 0 ≤ t → 0 < a.capital t
  rental : ∀ t, 0 ≤ t → R t = deriv f (a.capital t)
  wage : ∀ t, 0 ≤ t → w t = f (a.capital t) - a.capital t * deriv f (a.capital t)
  investment_nonneg : a.NonnegativeInvestment
  welfare : ∃ J, HasWelfare U (discount d) a.consumption J
  household_optimal : ∀ b : HouseholdPlan R w m, b.capital 0 = a.capital 0 →
    AsymptoticallyDominates U (discount d) a.consumption b.consumption

/-- Competitive firms: at `R = f'(k)` and `w = f(k) - k f'(k)` the capital stock
`k` maximizes profit `f(x) - R x - w`, and maximal profit is zero. -/
theorem firm_optimal (P : CassPrimitives f U d m) {k x : ℝ} (hk : 0 < k) (hx : 0 ≤ x) :
    f x - deriv f k * x - (f k - k * deriv f k) ≤ 0 ∧
      f k - deriv f k * k - (f k - k * deriv f k) = 0 := by
  have h := concave_support P.f_conc.concaveOn (mem_Ici.mpr hk.le) (mem_Ici.mpr hx)
    (P.f_diff k hk).hasDerivAt
  constructor <;> nlinarith

/-- Second welfare theorem: the certified Cass optimum with competitive prices is a
competitive equilibrium. -/
theorem second_welfare_theorem (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) :
    CompetitiveEquilibrium f U (fun t => deriv f (a.capital t))
      (fun t => f (a.capital t) - a.capital t * deriv f (a.capital t)) d m a := by
  refine ⟨hc.capital_pos, fun _ _ => rfl, fun _ _ => rfl, hc.investment_nonneg, hc.welfare, ?_⟩
  intro b hb0 ε hε
  set p : ℝ → ℝ := fun t => discount d t * q t
  -- the boundary term `B = p (k_a - k_b)` and its derivative
  set B : ℝ → ℝ := fun t => p t * (a.capital t - b.capital t)
  have hp : ∀ t, 0 ≤ t → HasDerivAt p
      (m * p t - discount d t * deriv U (a.consumption t) * deriv f (a.capital t)) t :=
    fun t ht => hasDerivAt_discounted_costate (hc.costate t ht)
  set B' : ℝ → ℝ := fun t =>
    (m * p t - discount d t * deriv U (a.consumption t) * deriv f (a.capital t)) *
      (a.capital t - b.capital t) +
    p t * ((a.investment t - m * a.capital t) - (b.investment t - m * b.capital t))
  have hB : ∀ t, 0 ≤ t → HasDerivAt B (B' t) t := fun t ht =>
    (hp t ht).mul ((a.dynamics t ht).sub (b.dynamics t ht))
  have hpc : ContinuousOn p (Ici 0) := fun t ht => (hp t ht).continuousAt.continuousWithinAt
  have hkac := a.capital_continuous
  have hkbc : ContinuousOn b.capital (Ici 0) := fun t ht =>
    (b.dynamics t ht).continuousAt.continuousWithinAt
  have hRc : ContinuousOn (fun t => deriv f (a.capital t)) (Ici 0) :=
    P.f_prime_cont.comp hkac hc.capital_pos
  have hmuc : ContinuousOn (fun t => deriv U (a.consumption t)) (Ici 0) :=
    P.U_prime_cont.comp a.consumption_continuous a.consumption_pos
  have hB'c : ContinuousOn B' (Ici 0) :=
    (((continuousOn_const.mul hpc).sub (((discount_continuous d).continuousOn.mul hmuc).mul
      hRc)).mul (hkac.sub hkbc)).add (hpc.mul ((a.investment_continuous.sub
      (continuousOn_const.mul hkac)).sub (b.investment_continuous.sub
      (continuousOn_const.mul hkbc))))
  have hUa : ContinuousOn (fun t => discount d t * U (a.consumption t)) (Ici 0) :=
    (discount_continuous d).continuousOn.mul (P.U_cont.comp a.consumption_continuous
      a.consumption_pos)
  have hUb : ContinuousOn (fun t => discount d t * U (b.consumption t)) (Ici 0) :=
    (discount_continuous d).continuousOn.mul (P.U_cont.comp b.consumption_continuous
      b.consumption_pos)
  -- pointwise comparison
  have hpoint : ∀ t, 0 ≤ t →
      0 ≤ discount d t * U (a.consumption t) - discount d t * U (b.consumption t) + B' t := by
    intro t ht
    have hca := a.consumption_pos t ht
    have hcb := b.consumption_pos t ht
    have hU := concave_support P.U_conc.concaveOn hca hcb (P.U_diff _ hca).hasDerivAt
    have hra := a.resource t ht
    have hbb := b.budget t ht
    have hw := hc.wedge t ht
    have hs := hc.slack t ht
    have hzb := b.investment_nonneg t ht
    have hdisc := discount_pos d t
    -- `c_a - c_b = R (k_a - k_b) - (z_a - z_b)` by the Euler identity
    have hcdiff : a.consumption t - b.consumption t =
        deriv f (a.capital t) * (a.capital t - b.capital t) -
          (a.investment t - b.investment t) := by
      linarith
    have hkey : B' t = discount d t * (-(deriv U (a.consumption t) * deriv f (a.capital t) *
        (a.capital t - b.capital t)) + q t * (a.investment t - b.investment t)) := by
      simp only [B', p]
      ring
    rw [hkey]
    have hslack' :
        0 ≤ (q t - deriv U (a.consumption t)) * (a.investment t - b.investment t) := by
      have : (q t - deriv U (a.consumption t)) * (a.investment t - b.investment t) =
          -((q t - deriv U (a.consumption t)) * b.investment t) := by linarith
      rw [this]
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hzb)
    have h1 : deriv U (a.consumption t) * (b.consumption t - a.consumption t) =
        -(deriv U (a.consumption t) * (deriv f (a.capital t) * (a.capital t - b.capital t) -
          (a.investment t - b.investment t))) := by
      rw [show b.consumption t - a.consumption t = -(a.consumption t - b.consumption t) by ring,
        hcdiff]
      ring
    have hmain : 0 ≤ U (a.consumption t) - U (b.consumption t) +
        (-(deriv U (a.consumption t) * deriv f (a.capital t) * (a.capital t - b.capital t)) +
          q t * (a.investment t - b.investment t)) := by
      linarith
    have := mul_nonneg hdisc.le hmain
    linarith
  -- the finite-horizon comparison
  have hfinite : ∀ T, 0 ≤ T → welfare U (discount d) b.consumption T -
      welfare U (discount d) a.consumption T ≤ p T * a.capital T := by
    intro T hT
    have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
    have hai := (hUa.mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
    have hbi := (hUb.mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
    have hBi := (hB'c.mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
    have hFTC : (∫ t in (0 : ℝ)..T, B' t) = B T - B 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => by
        rw [uIcc_of_le hT] at ht; exact hB t ht.1) hBi
    have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..T,
        (discount d t * U (a.consumption t) - discount d t * U (b.consumption t)) + B' t :=
      intervalIntegral.integral_nonneg hT (fun t ht => hpoint t ht.1)
    rw [intervalIntegral.integral_add (hai.sub hbi) hBi, intervalIntegral.integral_sub hai hbi,
      hFTC] at hnonneg
    have hB0 : B 0 = 0 := by simp only [B, hb0, sub_self, mul_zero]
    have hBT : B T ≤ p T * a.capital T := by
      have := mul_nonneg (mul_nonneg (discount_pos d T).le (hc.price_nonneg T hT))
        (b.capital_nonneg T hT)
      simp only [B, p] at this ⊢
      nlinarith
    change welfare U (discount d) a.consumption T - welfare U (discount d) b.consumption T +
      (B T - B 0) ≥ 0 at hnonneg
    linarith
  -- the discounted value of the planner's capital vanishes
  obtain ⟨K, hK, hcap⟩ := P.exists_capacity (a.capital 0)
  have hvanish : Tendsto (fun T => p T * a.capital T) atTop (𝓝 0) :=
    Terminal.terminal_tendsto_zero_of_bounded_capital (k₁ := fun _ => 0) hc.transversality
      (fun t ht => ⟨a.capital_nonneg t ht, a.capital_le_capacity hcap hK t ht⟩)
      (fun _ _ => ⟨le_rfl, le_trans (a.capital_nonneg 0 le_rfl) hK⟩) |>.congr
      (fun T => by simp only [sub_zero]; rfl)
  filter_upwards [eventually_ge_atTop (0 : ℝ), hvanish.eventually (gt_mem_nhds hε)] with T hT hv
  exact (hfinite T hT).trans_lt hv

/-- First welfare theorem: a competitive-equilibrium allocation is Cass optimal. -/
theorem first_welfare_theorem (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {R w : ℝ → ℝ} (he : CompetitiveEquilibrium f U R w d m a) {J : ℝ}
    (hJ : HasWelfare U (discount d) a.consumption J) : IsCassOptimal U d a J := by
  refine ⟨he.investment_nonneg, hJ, fun b hb hinit Jb hJb => ?_⟩
  -- the planner's competitor is affordable to the household, with more consumption
  have hRc : ContinuousOn R (Ici 0) := (P.f_prime_cont.comp a.capital_continuous
    he.capital_pos).congr (fun t ht => he.rental t ht)
  have hwc : ContinuousOn w (Ici 0) := ((P.f_cont.comp a.capital_continuous he.capital_pos).sub
    (a.capital_continuous.mul (P.f_prime_cont.comp a.capital_continuous he.capital_pos))).congr
    (fun t ht => he.wage t ht)
  have hkbc : ContinuousOn b.capital (Ici 0) := b.capital_continuous
  have hafford : ∀ t, 0 ≤ t → b.consumption t ≤ R t * b.capital t + w t - b.investment t := by
    intro t ht
    have hs := concave_support P.f_conc.concaveOn (mem_Ici.mpr (he.capital_pos t ht).le)
      (b.capital_nonneg t ht) (P.f_diff _ (he.capital_pos t ht)).hasDerivAt
    have hr := b.resource t ht
    rw [he.rental t ht, he.wage t ht]
    nlinarith
  let b' : HouseholdPlan R w m := {
    capital := b.capital
    consumption := fun t => R t * b.capital t + w t - b.investment t
    investment := b.investment
    capital_nonneg := b.capital_nonneg
    consumption_pos := fun t ht => (b.consumption_pos t ht).trans_le (hafford t ht)
    consumption_continuous := ((hRc.mul hkbc).add hwc).sub b.investment_continuous
    investment_continuous := b.investment_continuous
    investment_nonneg := hb
    budget := fun t _ => by ring
    dynamics := b.dynamics }
  have hdom := he.household_optimal b' hinit.symm
  -- the household's welfare dominates the planner competitor's at every horizon
  have hle : ∀ T, 0 ≤ T → welfare U (discount d) b.consumption T ≤
      welfare U (discount d) b'.consumption T := by
    intro T hT
    have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
    apply intervalIntegral.integral_mono_on hT
    · exact (((discount_continuous d).continuousOn.mul (P.U_cont.comp b.consumption_continuous
        b.consumption_pos)).mono hsub).intervalIntegrable_of_Icc hT
    · exact (((discount_continuous d).continuousOn.mul (P.U_cont.comp
        b'.consumption_continuous b'.consumption_pos)).mono hsub).intervalIntegrable_of_Icc hT
    · intro t ht
      exact mul_le_mul_of_nonneg_left (P.U_strictMono.monotoneOn (b.consumption_pos t ht.1)
        (b'.consumption_pos t ht.1) (hafford t ht.1)) (discount_pos d t).le
  have hdomb : AsymptoticallyDominates U (discount d) a.consumption b.consumption := by
    intro ε hε
    filter_upwards [hdom ε hε, eventually_ge_atTop (0 : ℝ)] with T hT hT0
    linarith [hle T hT0]
  exact hdomb.finite_welfare_le hJ hJb

/-- Every competitive-equilibrium allocation is the unique Cass optimum. -/
theorem equilibrium_eq_optimum (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {R w : ℝ → ℝ} (he : CompetitiveEquilibrium f U R w d m a) :
    ∀ t, 0 ≤ t → a.capital t = (optimalPath P (he.capital_pos 0 le_rfl)).capital t ∧
      a.consumption t = (optimalPath P (he.capital_pos 0 le_rfl)).consumption t := by
  obtain ⟨J, hJ⟩ := he.welfare
  obtain ⟨qo, ho0, hoc⟩ := optimalPath_spec P (he.capital_pos 0 le_rfl)
  obtain ⟨Jo, hJo⟩ := hoc.welfare
  intro t ht
  have h := (hoc.eq_of_isCassOptimal P hJo (first_welfare_theorem P he hJ) ho0).2 t ht
  exact ⟨h.1, h.2.1⟩

end RamseyCassKoopmans

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# The discrete-time Ramsey–Cass–Koopmans model: feasibility and existence

Capital per worker obeys `k(t+1) = F(k(t)) - c(t)` with gross resources
`F(k) = f(k) + (1 - δ) k`, and a path is feasible when `0 ≤ k(t+1) ≤ F(k(t))`.
Welfare is `∑ βᵗ u(c(t))` with `0 < β < 1`.

Utility is continuous at zero consumption (`u` is continuous on `[0, ∞)`), so
welfare is a convergent series on the compact set of feasible paths; logarithmic
utility is not covered. Feasible paths are bounded (`Feasible.le_bound`), the
feasible set is compact in the product topology, and welfare is continuous on it,
so an optimal path exists (`exists_optimal`).
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.DiscreteTime

/-- Primitive assumptions of the discrete-time model. -/
structure Primitives (f u : ℝ → ℝ) (β δ : ℝ) : Prop where
  β_pos : 0 < β
  β_lt_one : β < 1
  δ_pos : 0 < δ
  δ_le_one : δ ≤ 1
  f_cont : ContinuousOn f (Ici 0)
  f_zero : f 0 = 0
  f_conc : StrictConcaveOn ℝ (Ici 0) f
  f_diff : ∀ k, 0 < k → DifferentiableAt ℝ f k
  f_prime_pos : ∀ k, 0 < k → 0 < deriv f k
  f_prime_cont : ContinuousOn (deriv f) (Ioi 0)
  f_inada0 : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop
  f_inadaTop : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))
  u_cont : ContinuousOn u (Ici 0)
  u_conc : StrictConcaveOn ℝ (Ici 0) u
  u_diff : ∀ c, 0 < c → DifferentiableAt ℝ u c
  u_prime_pos : ∀ c, 0 < c → 0 < deriv u c
  u_prime_cont : ContinuousOn (deriv u) (Ioi 0)
  u_inada0 : Tendsto (deriv u) (𝓝[>] (0 : ℝ)) atTop

variable {f u : ℝ → ℝ} {β δ : ℝ}

/-- Gross resources: output plus undepreciated capital. -/
def resources (f : ℝ → ℝ) (δ k : ℝ) : ℝ := f k + (1 - δ) * k

/-- A feasible capital path from `k₀`. -/
def Feasible (f : ℝ → ℝ) (δ k₀ : ℝ) (k : ℕ → ℝ) : Prop :=
  k 0 = k₀ ∧ ∀ t, 0 ≤ k (t + 1) ∧ k (t + 1) ≤ resources f δ (k t)

/-- Consumption along a capital path. -/
def consumption (f : ℝ → ℝ) (δ : ℝ) (k : ℕ → ℝ) (t : ℕ) : ℝ :=
  resources f δ (k t) - k (t + 1)

/-- Discounted lifetime welfare. -/
noncomputable def welfare (f u : ℝ → ℝ) (β δ : ℝ) (k : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * u (consumption f δ k t)

theorem Primitives.f_strictMono (P : Primitives f u β δ) : StrictMonoOn f (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) P.f_cont
    (fun k hk => by rw [interior_Ici] at hk; exact P.f_prime_pos k hk)

theorem Primitives.u_strictMono (P : Primitives f u β δ) : StrictMonoOn u (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) P.u_cont
    (fun c hc => by rw [interior_Ici] at hc; exact P.u_prime_pos c hc)

theorem Primitives.resources_strictMono (P : Primitives f u β δ) :
    StrictMonoOn (resources f δ) (Ici 0) := by
  intro a ha b hb hab
  have h1 := P.f_strictMono ha hb hab
  have h2 := mul_le_mul_of_nonneg_left hab.le (sub_nonneg.mpr P.δ_le_one)
  simp only [resources]
  linarith

theorem Primitives.resources_cont (P : Primitives f u β δ) :
    ContinuousOn (resources f δ) (Ici 0) :=
  P.f_cont.add (continuousOn_const.mul continuousOn_id)

theorem resources_zero (P : Primitives f u β δ) : resources f δ 0 = 0 := by
  simp [resources, P.f_zero]

theorem Primitives.resources_nonneg (P : Primitives f u β δ) {k : ℝ} (hk : 0 ≤ k) :
    0 ≤ resources f δ k := by
  rw [← resources_zero P]
  exact P.resources_strictMono.monotoneOn (mem_Ici.mpr le_rfl) hk hk

/-- A capacity beyond which resources do not exceed capital. -/
theorem Primitives.exists_capacity (P : Primitives f u β δ) :
    ∃ K, 0 < K ∧ ∀ k, K ≤ k → resources f δ k ≤ k := by
  obtain ⟨K, hK1, hK⟩ := exists_capacity_of_marginal_tendsto_zero f (k0 := 1) P.δ_pos
    P.f_conc.concaveOn P.f_diff (fun k hk => (P.f_prime_pos k hk).le) P.f_inadaTop
  refine ⟨K, lt_of_lt_of_le one_pos hK1, fun k hk => ?_⟩
  have := hK k hk
  simp only [resources]
  linarith

/-- The capital bound used for paths from `k₀`. -/
noncomputable def bound (P : Primitives f u β δ) (k₀ : ℝ) : ℝ :=
  max k₀ (Classical.choose P.exists_capacity)

theorem bound_spec (P : Primitives f u β δ) (k₀ : ℝ) :
    k₀ ≤ bound P k₀ ∧ 0 < bound P k₀ ∧ resources f δ (bound P k₀) ≤ bound P k₀ := by
  obtain ⟨hK, hcap⟩ := Classical.choose_spec P.exists_capacity
  exact ⟨le_max_left _ _, lt_of_lt_of_le hK (le_max_right _ _),
    hcap _ (le_max_right _ _)⟩

theorem Feasible.nonneg {k₀ : ℝ} {k : ℕ → ℝ} (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) (t : ℕ) :
    0 ≤ k t := by
  cases t with
  | zero => rw [hk.1]; exact hk₀
  | succ t => exact (hk.2 t).1

/-- Every feasible path stays below the bound. -/
theorem Feasible.le_bound (P : Primitives f u β δ) {k₀ : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) (t : ℕ) : k t ≤ bound P k₀ := by
  obtain ⟨h1, h2, h3⟩ := bound_spec P k₀
  induction t with
  | zero => rw [hk.1]; exact h1
  | succ t ih =>
    exact (hk.2 t).2.trans ((P.resources_strictMono.monotoneOn (hk.nonneg hk₀ t)
      h2.le ih).trans h3)

theorem Feasible.consumption_mem (P : Primitives f u β δ) {k₀ : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) (t : ℕ) :
    consumption f δ k t ∈ Icc 0 (bound P k₀) := by
  obtain ⟨-, h2, h3⟩ := bound_spec P k₀
  refine ⟨sub_nonneg.mpr (hk.2 t).2, ?_⟩
  have := (P.resources_strictMono.monotoneOn (hk.nonneg hk₀ t) h2.le
    (hk.le_bound P hk₀ t)).trans h3
  have := (hk.2 t).1
  simp only [consumption]
  linarith

/-- A uniform bound on utility over the consumption range of paths from `k₀`. -/
theorem exists_utility_bound (P : Primitives f u β δ) (k₀ : ℝ) :
    ∃ M, ∀ c ∈ Icc 0 (bound P k₀), |u c| ≤ M := by
  obtain ⟨x, _, hx⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (bound_spec P k₀).2.1.le) ((P.u_cont.mono Icc_subset_Ici_self).norm)
  exact ⟨‖u x‖, fun c hc => hx hc⟩

theorem Feasible.summable (P : Primitives f u β δ) {k₀ : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) :
    Summable (fun t => β ^ t * u (consumption f δ k t)) := by
  obtain ⟨M, hM⟩ := exists_utility_bound P k₀
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one P.β_pos.le P.β_lt_one).mul_right M) (fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos P.β_pos t)]
  exact mul_le_mul_of_nonneg_left (hM _ (hk.consumption_mem P hk₀ t)) (pow_pos P.β_pos t).le

/-- The path that consumes everything after the first period is feasible. -/
theorem feasible_consume_all (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    Feasible f δ k₀ (fun t => if t = 0 then k₀ else 0) := by
  refine ⟨rfl, fun t => ⟨le_rfl, ?_⟩⟩
  cases t with
  | zero => exact P.resources_nonneg hk₀
  | succ t => simp [resources_zero P]

/-- The feasible set from `k₀` as a subset of the sequence space. -/
def feasibleSet (f : ℝ → ℝ) (δ k₀ : ℝ) : Set (ℕ → ℝ) := {k | Feasible f δ k₀ k}

theorem isCompact_feasibleSet (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    IsCompact (feasibleSet f δ k₀) := by
  -- the continuous extension of `f` to the whole line
  set fe : ℝ → ℝ := fun x => f (max x 0)
  have hfe : Continuous fe := P.f_cont.comp_continuous (continuous_id.max continuous_const)
    (fun x => le_max_right x 0)
  have heq : feasibleSet f δ k₀ = {k | k 0 = k₀} ∩ ⋂ t, ({k : ℕ → ℝ | 0 ≤ k (t + 1)} ∩
      {k | k (t + 1) ≤ fe (k t) + (1 - δ) * k t}) := by
    ext k
    simp only [feasibleSet, Feasible, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨h0, h⟩
      refine ⟨h0, fun t => ⟨(h t).1, ?_⟩⟩
      have hnn : 0 ≤ k t := Feasible.nonneg ⟨h0, h⟩ hk₀ t
      simp only [fe, max_eq_left hnn]
      exact (h t).2
    · rintro ⟨h0, h⟩
      have hnn : ∀ t, 0 ≤ k t := by
        intro t
        cases t with
        | zero => rw [h0]; exact hk₀
        | succ t => exact (h t).1
      refine ⟨h0, fun t => ⟨(h t).1, ?_⟩⟩
      have := (h t).2
      simp only [fe, max_eq_left (hnn t)] at this
      exact this
  have hclosed : IsClosed (feasibleSet f δ k₀) := by
    rw [heq]
    refine (isClosed_eq (continuous_apply 0) continuous_const).inter (isClosed_iInter fun t => ?_)
    exact (isClosed_le continuous_const (continuous_apply (t + 1))).inter
      (isClosed_le (continuous_apply (t + 1)) ((hfe.comp (continuous_apply t)).add
        (continuous_const.mul (continuous_apply t))))
  have hbox : feasibleSet f δ k₀ ⊆ Set.pi univ (fun _ => Icc 0 (bound P k₀)) := by
    intro k hk _ _
    exact ⟨Feasible.nonneg hk hk₀ _, Feasible.le_bound P hk hk₀ _⟩
  exact (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset hclosed hbox

theorem continuousOn_welfare (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    ContinuousOn (welfare f u β δ) (feasibleSet f δ k₀) := by
  obtain ⟨M, hM⟩ := exists_utility_bound P k₀
  apply continuousOn_tsum (u := fun t => β ^ t * M)
  · intro t
    apply continuousOn_const.mul
    apply P.u_cont.comp
    · apply ContinuousOn.sub _ (continuous_apply (t + 1)).continuousOn
      exact (P.resources_cont.comp (continuous_apply t).continuousOn
        (fun k hk => Feasible.nonneg hk hk₀ t))
    · exact fun k hk => (Feasible.consumption_mem P hk hk₀ t).1
  · exact (summable_geometric_of_lt_one P.β_pos.le P.β_lt_one).mul_right M
  · intro t k hk
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos P.β_pos t)]
    exact mul_le_mul_of_nonneg_left (hM _ (Feasible.consumption_mem P hk hk₀ t))
      (pow_pos P.β_pos t).le

/-- An optimal path exists from every nonnegative stock. -/
theorem exists_optimal (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    ∃ k, Feasible f δ k₀ k ∧
      ∀ k', Feasible f δ k₀ k' → welfare f u β δ k' ≤ welfare f u β δ k := by
  obtain ⟨k, hk, hmax⟩ := (isCompact_feasibleSet P hk₀).exists_isMaxOn
    ⟨fun t => if t = 0 then k₀ else 0, (feasible_consume_all P hk₀ : _)⟩
    (continuousOn_welfare P hk₀)
  exact ⟨k, hk, fun k' hk' => hmax hk'⟩

/-- The optimal path from `k₀ ≥ 0` (chosen). -/
noncomputable def optimalPath (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) : ℕ → ℝ :=
  Classical.choose (exists_optimal P hk₀)

theorem optimalPath_spec (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    Feasible f δ k₀ (optimalPath P hk₀) ∧ ∀ k', Feasible f δ k₀ k' →
      welfare f u β δ k' ≤ welfare f u β δ (optimalPath P hk₀) :=
  Classical.choose_spec (exists_optimal P hk₀)

/-- The value function. -/
noncomputable def value (P : Primitives f u β δ) (k₀ : ℝ) : ℝ :=
  if hk₀ : 0 ≤ k₀ then welfare f u β δ (optimalPath P hk₀) else 0

theorem value_eq (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    value P k₀ = welfare f u β δ (optimalPath P hk₀) := by
  simp only [value, hk₀, ↓reduceDIte]

theorem welfare_le_value (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) : welfare f u β δ k ≤ value P k₀ := by
  rw [value_eq P hk₀]
  exact (optimalPath_spec P hk₀).2 k hk

end RamseyCassKoopmans.DiscreteTime

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# The principle of optimality, uniqueness, and the shape of the value function

* `welfare_eq_head_add`: `W(k) = u(c₀) + β W(tail k)`.
* `tail_optimal`, `bellman`: the tail of an optimal path is optimal from the stock
  it reaches, and `V(k₀) = max_{0 ≤ y ≤ F(k₀)} u(F(k₀) - y) + β V(y)`.
* `optimal_unique`: the optimal path is unique (strict concavity of `u`).
* `value_strictMono`, `value_strictConcave`: `V` is strictly increasing and strictly
  concave.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.DiscreteTime

variable {f u : ℝ → ℝ} {β δ : ℝ}

/-- The path from date one on. -/
def tail (k : ℕ → ℝ) : ℕ → ℝ := fun t => k (t + 1)

/-- Prepend a stock to a path. -/
def prepend (k₀ : ℝ) (k : ℕ → ℝ) : ℕ → ℝ := fun t => if t = 0 then k₀ else k (t - 1)

theorem Feasible.tail {k₀ : ℝ} {k : ℕ → ℝ} (hk : Feasible f δ k₀ k) :
    Feasible f δ (k 1) (DiscreteTime.tail k) :=
  ⟨rfl, fun t => hk.2 (t + 1)⟩

theorem Feasible.prepend {k₀ y : ℝ} {k : ℕ → ℝ} (hk : Feasible f δ y k) (hy0 : 0 ≤ y)
    (hy : y ≤ resources f δ k₀) : Feasible f δ k₀ (DiscreteTime.prepend k₀ k) := by
  refine ⟨rfl, fun t => ?_⟩
  rcases t with _ | t
  · have h1 : DiscreteTime.prepend k₀ k (0 + 1) = y := by simp [DiscreteTime.prepend, hk.1]
    have h0 : DiscreteTime.prepend k₀ k 0 = k₀ := by simp [DiscreteTime.prepend]
    rw [h1, h0]
    exact ⟨hy0, hy⟩
  · have h1 : DiscreteTime.prepend k₀ k (t + 1 + 1) = k (t + 1) := by
      simp [DiscreteTime.prepend]
    have h0 : DiscreteTime.prepend k₀ k (t + 1) = k t := by simp [DiscreteTime.prepend]
    rw [h1, h0]
    exact hk.2 t

theorem consumption_tail (k : ℕ → ℝ) (t : ℕ) :
    consumption f δ (tail k) t = consumption f δ k (t + 1) := rfl

theorem welfare_eq_head_add (P : Primitives f u β δ) {k₀ : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) :
    welfare f u β δ k = u (consumption f δ k 0) + β * welfare f u β δ (tail k) := by
  unfold welfare
  rw [(hk.summable P hk₀).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, pow_succ, consumption_tail]
  congr 1
  congr 1
  funext t
  ring

theorem consumption_prepend_zero (k₀ : ℝ) (k : ℕ → ℝ) :
    consumption f δ (prepend k₀ k) 0 = resources f δ k₀ - k 0 := by
  simp [consumption, prepend]

theorem tail_prepend (k₀ : ℝ) (k : ℕ → ℝ) : tail (prepend k₀ k) = k := by
  funext t
  simp [tail, prepend]

theorem welfare_prepend (P : Primitives f u β δ) {k₀ y : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ y k) (hy0 : 0 ≤ y) (hy : y ≤ resources f δ k₀) (hk₀ : 0 ≤ k₀) :
    welfare f u β δ (prepend k₀ k) = u (resources f δ k₀ - y) + β * welfare f u β δ k := by
  rw [welfare_eq_head_add P (hk.prepend hy0 hy) hk₀, consumption_prepend_zero, tail_prepend, hk.1]

/-- The tail of an optimal path is optimal. -/
theorem tail_optimal (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k)
    (hopt : ∀ k', Feasible f δ k₀ k' → welfare f u β δ k' ≤ welfare f u β δ k) :
    welfare f u β δ (tail k) = value P (k 1) := by
  have hk1 : 0 ≤ k 1 := (hk.2 0).1
  apply le_antisymm (welfare_le_value P hk1 hk.tail)
  by_contra hlt
  push Not at hlt
  obtain ⟨hopt1, _⟩ := optimalPath_spec P hk1
  have hbetter := hopt _ (hopt1.prepend hk1 (by rw [← hk.1]; exact (hk.2 0).2))
  rw [welfare_prepend P hopt1 hk1 (by rw [← hk.1]; exact (hk.2 0).2) hk₀,
    welfare_eq_head_add P hk hk₀, ← value_eq P hk1] at hbetter
  have hc0 : consumption f δ k 0 = resources f δ k₀ - k 1 := by
    simp [consumption, hk.1]
  rw [hc0] at hbetter
  have := mul_lt_mul_of_pos_left hlt P.β_pos
  linarith

/-- The Bellman equation along the optimal path, and the Bellman inequality for
every feasible choice of next period's capital. -/
theorem bellman (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    value P k₀ = u (resources f δ k₀ - optimalPath P hk₀ 1) +
        β * value P (optimalPath P hk₀ 1) ∧
      ∀ y, 0 ≤ y → y ≤ resources f δ k₀ →
        u (resources f δ k₀ - y) + β * value P y ≤ value P k₀ := by
  obtain ⟨hk, hopt⟩ := optimalPath_spec P hk₀
  refine ⟨?_, fun y hy0 hy => ?_⟩
  · rw [value_eq P hk₀, welfare_eq_head_add P hk hk₀, tail_optimal P hk₀ hk hopt]
    simp [consumption, hk.1]
  · obtain ⟨hy', _⟩ := optimalPath_spec P hy0
    have := welfare_le_value P hk₀ (hy'.prepend hy0 hy)
    rwa [welfare_prepend P hy' hy0 hy hk₀, ← value_eq P hy0] at this

/-- Concavity of resources: mixed resources dominate the mixture, strictly at
distinct stocks. -/
theorem resources_mix (P : Primitives f u β δ) {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    θ * resources f δ a + (1 - θ) * resources f δ b ≤ resources f δ (θ * a + (1 - θ) * b) ∧
      (a ≠ b → θ * resources f δ a + (1 - θ) * resources f δ b <
        resources f δ (θ * a + (1 - θ) * b)) := by
  have hc := P.f_conc.concaveOn.2 ha hb hθ.le (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hc
  refine ⟨by simp only [resources]; nlinarith, fun hne => ?_⟩
  have hs := P.f_conc.2 ha hb hne hθ (by linarith : (0 : ℝ) < 1 - θ) (by ring)
  simp only [smul_eq_mul] at hs
  simp only [resources]
  nlinarith

/-- The mixture of two feasible paths is feasible, with consumption at least the
mixture of consumptions. -/
theorem Feasible.mix (P : Primitives f u β δ) {k₀ k₀' θ : ℝ} {k k' : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk' : Feasible f δ k₀' k') (hk₀ : 0 ≤ k₀) (hk₀' : 0 ≤ k₀')
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    Feasible f δ (θ * k₀ + (1 - θ) * k₀') (fun t => θ * k t + (1 - θ) * k' t) ∧
      ∀ t, θ * consumption f δ k t + (1 - θ) * consumption f δ k' t ≤
        consumption f δ (fun t => θ * k t + (1 - θ) * k' t) t := by
  have hmix := fun t => (resources_mix P (hk.nonneg hk₀ t) (hk'.nonneg hk₀' t) hθ hθ1).1
  refine ⟨⟨by simp only [hk.1, hk'.1], fun t => ⟨?_, ?_⟩⟩, fun t => ?_⟩
  · have := mul_nonneg hθ.le (hk.2 t).1
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ) (hk'.2 t).1
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (hk.2 t).2 hθ.le
    have h2 := mul_le_mul_of_nonneg_left (hk'.2 t).2 (by linarith : (0 : ℝ) ≤ 1 - θ)
    linarith [hmix t]
  · simp only [consumption]
    linarith [hmix t]

/-- Termwise comparison of discounted utility for a mixture. -/
theorem utility_mix (P : Primitives f u β δ) {c c' c'' θ : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hθ : 0 < θ) (hθ1 : θ < 1) (hle : θ * c + (1 - θ) * c' ≤ c'') :
    θ * u c + (1 - θ) * u c' ≤ u c'' ∧
      (c ≠ c' → θ * u c + (1 - θ) * u c' < u c'') := by
  have hmixnn : 0 ≤ θ * c + (1 - θ) * c' := by nlinarith
  have hmono := P.u_strictMono.monotoneOn hmixnn (hmixnn.trans hle) hle
  have hconc := P.u_conc.concaveOn.2 hc hc' hθ.le (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hconc
  refine ⟨hconc.trans hmono, fun hne => ?_⟩
  have hs := P.u_conc.2 hc hc' hne hθ (by linarith : (0 : ℝ) < 1 - θ) (by ring)
  simp only [smul_eq_mul] at hs
  exact hs.trans_le hmono

/-- The mixture's welfare dominates the mixture of welfares. -/
theorem welfare_mix (P : Primitives f u β δ) {k₀ k₀' θ : ℝ} {k k' : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk' : Feasible f δ k₀' k') (hk₀ : 0 ≤ k₀) (hk₀' : 0 ≤ k₀')
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    θ * welfare f u β δ k + (1 - θ) * welfare f u β δ k' ≤
        welfare f u β δ (fun t => θ * k t + (1 - θ) * k' t) ∧
      ((∃ t, consumption f δ k t ≠ consumption f δ k' t ∨
          θ * consumption f δ k t + (1 - θ) * consumption f δ k' t <
            consumption f δ (fun t => θ * k t + (1 - θ) * k' t) t) →
        θ * welfare f u β δ k + (1 - θ) * welfare f u β δ k' <
          welfare f u β δ (fun t => θ * k t + (1 - θ) * k' t)) := by
  obtain ⟨hmixf, hcons⟩ := hk.mix P hk' hk₀ hk₀' hθ hθ1
  have hmix0 : 0 ≤ θ * k₀ + (1 - θ) * k₀' := by nlinarith
  have hs := hk.summable P hk₀
  have hs' := hk'.summable P hk₀'
  have hsm := hmixf.summable P hmix0
  have hlhs : θ * welfare f u β δ k + (1 - θ) * welfare f u β δ k' =
      ∑' t, (θ * (β ^ t * u (consumption f δ k t)) +
        (1 - θ) * (β ^ t * u (consumption f δ k' t))) := by
    unfold welfare
    rw [(hs.mul_left θ).tsum_add (hs'.mul_left (1 - θ)), tsum_mul_left, tsum_mul_left]
  have hterm : ∀ t, θ * (β ^ t * u (consumption f δ k t)) +
      (1 - θ) * (β ^ t * u (consumption f δ k' t)) ≤
        β ^ t * u (consumption f δ (fun t => θ * k t + (1 - θ) * k' t) t) := by
    intro t
    have h := (utility_mix P (hk.consumption_mem P hk₀ t).1 (hk'.consumption_mem P hk₀' t).1 hθ
      hθ1 (hcons t)).1
    have := mul_le_mul_of_nonneg_left h (pow_pos P.β_pos t).le
    linarith
  have hsum := (hs.mul_left θ).add (hs'.mul_left (1 - θ))
  refine ⟨?_, fun ⟨t, ht⟩ => ?_⟩
  · rw [hlhs]
    exact hsum.tsum_le_tsum hterm hsm
  · rw [hlhs]
    refine hsum.tsum_lt_tsum (i := t) hterm ?_ hsm
    have hct := (hk.consumption_mem P hk₀ t).1
    have hct' := (hk'.consumption_mem P hk₀' t).1
    have hstrict : θ * u (consumption f δ k t) + (1 - θ) * u (consumption f δ k' t) <
        u (consumption f δ (fun t => θ * k t + (1 - θ) * k' t) t) := by
      rcases ht with hne | hlt
      · exact (utility_mix P hct hct' hθ hθ1 (hcons t)).2 hne
      · have hmixc : 0 ≤ θ * consumption f δ k t + (1 - θ) * consumption f δ k' t := by
          nlinarith
        have h1 := (utility_mix P hct hct' hθ hθ1 le_rfl).1
        exact h1.trans_lt (P.u_strictMono hmixc (hmixc.trans hlt.le) hlt)
    have := mul_lt_mul_of_pos_left hstrict (pow_pos P.β_pos t)
    linarith

/-- The optimal path is unique. -/
theorem optimal_unique (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k)
    (hopt : ∀ k', Feasible f δ k₀ k' → welfare f u β δ k' ≤ welfare f u β δ k) :
    k = optimalPath P hk₀ := by
  obtain ⟨ho, hoopt⟩ := optimalPath_spec P hk₀
  set o := optimalPath P hk₀
  by_contra hne
  -- two distinct feasible paths from the same stock differ in some consumption
  have hcne : ∃ t, consumption f δ k t ≠ consumption f δ o t := by
    by_contra hall
    push Not at hall
    apply hne
    funext t
    induction t with
    | zero => rw [hk.1, ho.1]
    | succ t ih =>
      have := hall t
      simp only [consumption, ih] at this
      linarith
  have hθ : (0 : ℝ) < 1 / 2 := by norm_num
  have hθ1 : (1 : ℝ) / 2 < 1 := by norm_num
  obtain ⟨hmixf, -⟩ := hk.mix P ho hk₀ hk₀ hθ hθ1
  have hstrict := (welfare_mix P hk ho hk₀ hk₀ hθ hθ1).2
    (by obtain ⟨t, ht⟩ := hcne; exact ⟨t, Or.inl ht⟩)
  have hmix0 : 1 / 2 * k₀ + (1 - 1 / 2) * k₀ = k₀ := by ring
  rw [hmix0] at hmixf
  have h1 := hopt _ hmixf
  have h2 := hoopt k hk
  have h3 := hopt o ho
  linarith

/-- The value function is strictly increasing. -/
theorem value_strictMono (P : Primitives f u β δ) : StrictMonoOn (value P) (Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  have hb' : (0 : ℝ) ≤ b := hb
  obtain ⟨hk, hopt⟩ := optimalPath_spec P ha'
  have hk1 : 0 ≤ optimalPath P ha' 1 := (hk.2 0).1
  have hFa : optimalPath P ha' 1 ≤ resources f δ a :=
    (hk.2 0).2.trans_eq (congrArg (resources f δ) hk.1)
  have hFab := P.resources_strictMono ha hb hab
  obtain ⟨hb1, _⟩ := bellman P hb'
  have hbell := (bellman P hb').2 (optimalPath P ha' 1) hk1 (hFa.trans hFab.le)
  rw [(bellman P ha').1]
  have hc : 0 ≤ resources f δ a - optimalPath P ha' 1 := sub_nonneg.mpr hFa
  have hu := P.u_strictMono hc (by linarith : (0 : ℝ) ≤ resources f δ b - optimalPath P ha' 1)
    (by linarith)
  linarith

/-- The value function is strictly concave. -/
theorem value_strictConcave (P : Primitives f u β δ) : StrictConcaveOn ℝ (Ici 0) (value P) := by
  refine ⟨convex_Ici 0, fun a ha b hb hne θ θ' hθ hθ' hsum => ?_⟩
  have ha' : (0 : ℝ) ≤ a := ha
  have hb' : (0 : ℝ) ≤ b := hb
  have hθ'' : θ' = 1 - θ := by linarith
  subst hθ''
  have hθ1 : θ < 1 := by linarith
  obtain ⟨hka, _⟩ := optimalPath_spec P ha'
  obtain ⟨hkb, _⟩ := optimalPath_spec P hb'
  obtain ⟨hmixf, -⟩ := hka.mix P hkb ha' hb' hθ hθ1
  have hstrict := (welfare_mix P hka hkb ha' hb' hθ hθ1).2 ⟨0, Or.inr (by
    have hne' : optimalPath P ha' 0 ≠ optimalPath P hb' 0 := by rw [hka.1, hkb.1]; exact hne
    have h := (resources_mix P (hka.nonneg ha' 0) (hkb.nonneg hb' 0) hθ hθ1).2 hne'
    simp only [consumption]
    linarith)⟩
  have hmix0 : 0 ≤ θ * a + (1 - θ) * b := by nlinarith
  have hle := welfare_le_value P hmix0 hmixf
  simp only [smul_eq_mul]
  rw [value_eq P ha', value_eq P hb']
  linarith

end RamseyCassKoopmans.DiscreteTime

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# Interiority and the Euler equation

* `IsOptimal.shift`: every tail of an optimal path is optimal from the stock reached,
  and `IsOptimal.bellman_eq` gives the Bellman equation along the path.
* `interior_choice`: by the Inada conditions a maximizer of `u(F(x) - y) + β V(y)` over
  `0 ≤ y ≤ F(x)` is interior: saving and consumption are both strictly positive.
* `IsOptimal.capital_pos`, `IsOptimal.consumption_pos`: an optimal path from positive
  capital keeps capital and consumption strictly positive.
* `IsOptimal.euler`: `u'(c t) = β u'(c (t+1)) F'(k (t+1))`, `F' = f' + 1 - δ`.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.DiscreteTime

variable {f u : ℝ → ℝ} {β δ : ℝ}

/-- A feasible path attaining the maximal welfare from `x`. -/
def IsOptimal (f u : ℝ → ℝ) (β δ x : ℝ) (k : ℕ → ℝ) : Prop :=
  Feasible f δ x k ∧ ∀ k', Feasible f δ x k' → welfare f u β δ k' ≤ welfare f u β δ k

theorem isOptimal_optimalPath (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) :
    IsOptimal f u β δ x (optimalPath P hx) := optimalPath_spec P hx

theorem IsOptimal.welfare_eq (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) : welfare f u β δ k = value P x := by
  apply le_antisymm (welfare_le_value P hx hk.1)
  rw [value_eq P hx]
  exact hk.2 _ (optimalPath_spec P hx).1

theorem IsOptimal.tail (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) : IsOptimal f u β δ (k 1) (DiscreteTime.tail k) := by
  refine ⟨hk.1.tail, fun k' hk' => ?_⟩
  rw [tail_optimal P hx hk.1 hk.2]
  exact welfare_le_value P (hk.1.2 0).1 hk'

theorem IsOptimal.shift (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    IsOptimal f u β δ (k t) (fun s => k (t + s)) := by
  induction t with
  | zero => simpa only [zero_add, hk.1.1] using hk
  | succ t ih =>
    have h := ih.tail P (hk.1.nonneg hx t)
    have heq : DiscreteTime.tail (fun s => k (t + s)) = fun s => k (t + 1 + s) := by
      funext s
      simp only [DiscreteTime.tail]
      congr 1
      ring
    rw [heq] at h
    simpa only [add_zero] using h

/-- The Bellman equation along an optimal path. -/
theorem IsOptimal.bellman_eq (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    value P (k t) = u (resources f δ (k t) - k (t + 1)) + β * value P (k (t + 1)) := by
  have hs := hk.shift P hx t
  have hkt := hk.1.nonneg hx t
  rw [← hs.welfare_eq P hkt, welfare_eq_head_add P hs.1 hkt, tail_optimal P hkt hs.1 hs.2]
  simp only [consumption, add_zero]

theorem value_zero (P : Primitives f u β δ) : value P 0 = u 0 + β * value P 0 := by
  obtain ⟨hk, -⟩ := optimalPath_spec P (le_refl (0 : ℝ))
  have h1 : optimalPath P (le_refl (0 : ℝ)) 1 = 0 := by
    have := hk.2 0
    rw [hk.1, resources_zero P] at this
    linarith [this.1, this.2]
  have := (bellman P (le_refl (0 : ℝ))).1
  rwa [h1, resources_zero P, sub_zero] at this

theorem Primitives.u_prime_anti (P : Primitives f u β δ) : StrictAntiOn (deriv u) (Ioi 0) :=
  (P.u_conc.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv P.u_diff

/-- A maximizer of `u(F(x) - y) + β V(y)` is interior. -/
theorem interior_choice (P : Primitives f u β δ) {x y : ℝ} (hx : 0 < x) (hy0 : 0 ≤ y)
    (hyF : y ≤ resources f δ x)
    (hmax : ∀ z, 0 ≤ z → z ≤ resources f δ x →
      u (resources f δ x - z) + β * value P z ≤ u (resources f δ x - y) + β * value P y) :
    0 < y ∧ y < resources f δ x := by
  have hFx : 0 < resources f δ x := by
    have h := P.resources_strictMono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx
    rwa [resources_zero P] at h
  have hVmono := value_strictMono P
  have hVconc := value_strictConcave P
  constructor
  · -- saving is positive
    by_contra hle
    push Not at hle
    have hy : y = 0 := le_antisymm hle hy0
    subst hy
    set a := resources f δ x / 2 with ha
    have hapos : 0 < a := half_pos hFx
    have hua : 0 < deriv u a := P.u_prime_pos a hapos
    -- small `ε` with `F(ε) ≤ a` and `β f'(ε) > 1`
    have hFcont : Tendsto (resources f δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (P.resources_cont (0 : ℝ) (mem_Ici.mpr le_rfl)).tendsto
      rw [resources_zero P] at this
      exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    obtain ⟨ε, hε⟩ := ((eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0).and
      ((hFcont.eventually (gt_mem_nhds hapos)).and
      ((P.f_inada0.eventually (eventually_gt_atTop (1 / β))).and
      (Ioo_mem_nhdsGT hapos : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo 0 a)))).exists
    obtain ⟨hεpos, hFε, hfε, hεa⟩ := hε
    have hεpos' : (0 : ℝ) < ε := hεpos
    have hεF : ε ≤ resources f δ x := by linarith [hεa.2]
    have hcmp := hmax ε hεpos'.le hεF
    -- `u(F x) - u(F x - ε) ≤ u'(a) ε`
    have hu1 : u (resources f δ x) - u (resources f δ x - ε) ≤ deriv u a * ε := by
      have hpos : 0 < resources f δ x - ε := by linarith [hεa.2]
      have hs := concave_support P.u_conc.concaveOn (mem_Ici.mpr hpos.le) (mem_Ici.mpr hFx.le)
        (P.u_diff _ hpos).hasDerivAt
      have hmono : deriv u (resources f δ x - ε) ≤ deriv u a :=
        P.u_prime_anti.antitoneOn hapos hpos (by linarith [hεa.2])
      have : u (resources f δ x) - u (resources f δ x - ε) ≤
          deriv u (resources f δ x - ε) * ε := by
        have := hs
        rw [show resources f δ x - (resources f δ x - ε) = ε by ring] at this
        exact this
      exact this.trans (mul_le_mul_of_nonneg_right hmono hεpos'.le)
    -- `V(ε) - V(0) ≥ u(F ε) - u(0) ≥ u'(a) f'(ε) ε`
    have hFεpos : 0 < resources f δ ε := by
      have h := P.resources_strictMono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hεpos'.le) hεpos'
      rwa [resources_zero P] at h
    have hV1 : u (resources f δ ε) - u 0 ≤ value P ε - value P 0 := by
      have hb := (bellman P hεpos'.le).2 0 le_rfl hFεpos.le
      rw [sub_zero] at hb
      have hz := value_zero P
      have : value P 0 * (1 - β) = u 0 := by linarith
      have hV0 : value P 0 = u 0 + β * value P 0 := hz
      nlinarith [P.β_pos, P.β_lt_one]
    have hu2 : deriv u a * (deriv f ε * ε) ≤ u (resources f δ ε) - u 0 := by
      have hs := concave_support P.u_conc.concaveOn (mem_Ici.mpr hFεpos.le) (mem_Ici.mpr le_rfl)
        (P.u_diff _ hFεpos).hasDerivAt
      have hmono : deriv u a ≤ deriv u (resources f δ ε) :=
        P.u_prime_anti.antitoneOn hFεpos hapos hFε.le
      have hfε' : deriv f ε * ε ≤ resources f δ ε := by
        have hs' := concave_support P.f_conc.concaveOn (mem_Ici.mpr hεpos'.le) (mem_Ici.mpr le_rfl)
          (P.f_diff _ hεpos').hasDerivAt
        rw [P.f_zero] at hs'
        have := mul_nonneg (sub_nonneg.mpr P.δ_le_one) hεpos'.le
        simp only [resources]
        linarith
      have hfpos : 0 ≤ deriv f ε * ε := mul_nonneg (P.f_prime_pos ε hεpos').le hεpos'.le
      have h1 : deriv u a * (deriv f ε * ε) ≤ deriv u (resources f δ ε) * resources f δ ε :=
        mul_le_mul hmono hfε' hfpos (P.u_prime_pos _ hFεpos).le
      linarith
    have hbf : 1 < β * deriv f ε := by
      have := (div_lt_iff₀' P.β_pos).mp hfε
      linarith
    have hgain : deriv u a * ε < β * (deriv u a * (deriv f ε * ε)) := by
      have := mul_lt_mul_of_pos_left hbf (mul_pos hua hεpos')
      nlinarith
    simp only [sub_zero] at hcmp
    have := mul_le_mul_of_nonneg_left (hu2.trans hV1) P.β_pos.le
    linarith
  · -- consumption is positive
    by_contra hle
    push Not at hle
    have hy : y = resources f δ x := le_antisymm hyF hle
    subst hy
    set Y := resources f δ x
    set S := 2 * (value P Y - value P 0) / Y
    obtain ⟨ε, hε⟩ := ((eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0).and
      ((P.u_inada0.eventually (eventually_gt_atTop (β * S))).and
      (Ioo_mem_nhdsGT (half_pos hFx) : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo 0 (Y / 2)))).exists
    obtain ⟨hεpos, huε, hεY⟩ := hε
    have hεpos' : (0 : ℝ) < ε := hεpos
    have hYε : Y / 2 < Y - ε := by linarith [hεY.2]
    have hcmp := hmax (Y - ε) (by linarith) (by linarith)
    rw [sub_self, show Y - (Y - ε) = ε by ring] at hcmp
    -- `u(ε) - u(0) ≥ u'(ε) ε`
    have hu : deriv u ε * ε ≤ u ε - u 0 := by
      have hs := concave_support P.u_conc.concaveOn (mem_Ici.mpr hεpos'.le) (mem_Ici.mpr le_rfl)
        (P.u_diff _ hεpos').hasDerivAt
      linarith
    -- `V(Y) - V(Y - ε) ≤ S ε` by concavity and monotonicity
    have hV : value P Y - value P (Y - ε) ≤ S * ε := by
      have hslope := hVconc.concaveOn.slope_anti_adjacent (x := 0) (y := Y - ε) (z := Y)
        (mem_Ici.mpr le_rfl) (mem_Ici.mpr hFx.le) (by linarith) (by linarith)
      rw [show Y - (Y - ε) = ε by ring, div_le_div_iff₀ hεpos' (by linarith : (0 : ℝ) < Y - ε - 0),
        sub_zero] at hslope
      have hmono : value P (Y - ε) ≤ value P Y :=
        hVmono.monotoneOn (mem_Ici.mpr (by linarith)) (mem_Ici.mpr hFx.le) (by linarith)
      have hV0 : value P 0 ≤ value P (Y - ε) :=
        hVmono.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith)) (by linarith)
      have hS : (value P (Y - ε) - value P 0) / (Y - ε) ≤ S := by
        rw [div_le_iff₀ (by linarith)]
        simp only [S]
        rw [div_mul_eq_mul_div, le_div_iff₀ hFx]
        nlinarith
      have h2 : (value P Y - value P (Y - ε)) * (Y - ε) ≤
          (value P (Y - ε) - value P 0) * ε := hslope
      have h3 := (div_le_iff₀ (by linarith : (0 : ℝ) < Y - ε)).mp hS
      nlinarith
    have hgain : β * S * ε < deriv u ε * ε := mul_lt_mul_of_pos_right huε hεpos'
    have := mul_le_mul_of_nonneg_left hV P.β_pos.le
    linarith

theorem Primitives.resources_pos (P : Primitives f u β δ) {k : ℝ} (hk : 0 < k) :
    0 < resources f δ k := by
  have h := P.resources_strictMono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hk.le) hk
  rwa [resources_zero P] at h

/-- An optimal path from positive capital keeps capital strictly positive and
consumption strictly positive. -/
theorem IsOptimal.interior (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    0 < k t ∧ 0 < k (t + 1) ∧ 0 < consumption f δ k t := by
  have hpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => rw [hk.1.1]; exact hx
    | succ t ih =>
      have hbell := hk.bellman_eq P hx.le t
      exact (interior_choice P ih (hk.1.2 t).1 (hk.1.2 t).2 (fun z hz0 hzF => by
        rw [← hbell]; exact (bellman P (hk.1.nonneg hx.le t)).2 z hz0 hzF)).1
  refine ⟨hpos t, hpos (t + 1), ?_⟩
  have hbell := hk.bellman_eq P hx.le t
  have h := (interior_choice P (hpos t) (hk.1.2 t).1 (hk.1.2 t).2 (fun z hz0 hzF => by
    rw [← hbell]; exact (bellman P (hk.1.nonneg hx.le t)).2 z hz0 hzF)).2
  simp only [consumption]
  linarith

theorem hasDerivAt_resources (P : Primitives f u β δ) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (resources f δ) (deriv f k + (1 - δ)) k := by
  have h1 : HasDerivAt (fun y => f y + (1 - δ) * y) (deriv f k + (1 - δ) * 1) k :=
    (P.f_diff k hk).hasDerivAt.add ((hasDerivAt_id' k).const_mul (1 - δ))
  rw [mul_one] at h1
  exact h1

/-- The Euler equation along an optimal path. -/
theorem IsOptimal.euler (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    deriv u (consumption f δ k t) =
      β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ)) := by
  obtain ⟨hkt, hkt1, hct⟩ := hk.interior P hx t
  obtain ⟨-, -, hct1⟩ := hk.interior P hx (t + 1)
  set ψ : ℝ → ℝ := fun y => u (resources f δ (k t) - y) +
    β * (u (resources f δ y - k (t + 2)) + β * value P (k (t + 2)))
  have hct' : 0 < resources f δ (k t) - k (t + 1) := hct
  have hct1' : 0 < resources f δ (k (t + 1)) - k (t + 2) := hct1
  -- `ψ` has a local maximum at `k (t + 1)`
  have hloc : IsLocalMax ψ (k (t + 1)) := by
    have hFc : ContinuousAt (resources f δ) (k (t + 1)) :=
      (hasDerivAt_resources P hkt1).continuousAt
    have hnear : ∀ᶠ y in 𝓝 (k (t + 1)), 0 < y ∧ y < resources f δ (k t) ∧
        k (t + 2) < resources f δ y := by
      refine (lt_mem_nhds hkt1).and
        ((gt_mem_nhds (by linarith : k (t + 1) < resources f δ (k t))).and ?_)
      exact hFc.eventually (lt_mem_nhds (by linarith : k (t + 2) < resources f δ (k (t + 1))))
    filter_upwards [hnear] with y hy
    obtain ⟨hypos, hyF, hy2⟩ := hy
    have hbt := hk.bellman_eq P hx.le t
    have hbt1 := hk.bellman_eq P hx.le (t + 1)
    have hin1 := (bellman P hypos.le).2 (k (t + 2)) (hk.1.2 (t + 1)).1 hy2.le
    have hin0 := (bellman P (hk.1.nonneg hx.le t)).2 y hypos.le hyF.le
    have := mul_le_mul_of_nonneg_left hin1 P.β_pos.le
    simp only [ψ]
    rw [show t + 1 + 1 = t + 2 by ring] at hbt1
    have hbt1' : β * value P (k (t + 1)) = β * (u (resources f δ (k (t + 1)) - k (t + 2)) +
        β * value P (k (t + 2))) := by rw [hbt1]
    linarith
  -- its derivative at `k (t + 1)`
  have hd1 : HasDerivAt (fun y => u (resources f δ (k t) - y))
      (deriv u (resources f δ (k t) - k (t + 1)) * (-1)) (k (t + 1)) :=
    (P.u_diff _ hct').hasDerivAt.comp (k (t + 1)) ((hasDerivAt_id (k (t + 1))).const_sub _)
  have hd2 : HasDerivAt (fun y => u (resources f δ y - k (t + 2)))
      (deriv u (resources f δ (k (t + 1)) - k (t + 2)) * (deriv f (k (t + 1)) + (1 - δ)))
      (k (t + 1)) :=
    (P.u_diff _ hct1').hasDerivAt.comp (k (t + 1)) ((hasDerivAt_resources P hkt1).sub_const _)
  have hd := hd1.add ((hd2.add_const (β * value P (k (t + 2)))).const_mul β)
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hc0 : consumption f δ k t = resources f δ (k t) - k (t + 1) := rfl
  have hc1 : consumption f δ k (t + 1) = resources f δ (k (t + 1)) - k (t + 2) := rfl
  rw [hc0, hc1]
  linarith

end RamseyCassKoopmans.DiscreteTime

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# The policy function and global dynamics of the discrete Ramsey–Cass model

* `policy`: next period's capital `g(x)` on the optimal path from `x`;
  `IsOptimal.succ_eq_policy`: every optimal path follows `k(t+1) = g(k(t))`.
* `policy_strictMono`: `g` is strictly increasing (increasing differences of
  `u(F(x) - y)` in `(x, y)`; strictness from the Euler equation).
* `existsUnique_steady`, `steady`: the unique positive `k*` with
  `β (f'(k*) + 1 - δ) = 1`.
* `IsOptimal.tendsto`: every optimal path from positive capital converges to `k*`;
  `IsOptimal.dynamics_below`, `IsOptimal.dynamics_above`: strictly monotonically,
  with consumption moving in the same direction, and never crossing `k*`.
* `consumptionPolicy_strictMono`, `IsOptimal.capital_lt`, `IsOptimal.consumption_lt`,
  `IsOptimal.absolute_convergence`: consumption is strictly increasing in capital,
  optimal paths of identical economies never cross, and they converge to each other.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.DiscreteTime

variable {f u : ℝ → ℝ} {β δ : ℝ}

/-- Shifting an interval right lowers the increment of a strictly concave function. -/
theorem shift_increment_lt (P : Primitives f u β δ) {a b Δ : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hΔ : 0 < Δ) : u (b + Δ) - u (a + Δ) < u b - u a := by
  have hs1 := P.u_conc.secant_strict_mono (a := a) (x := b) (y := b + Δ) (mem_Ici.mpr ha)
    (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) (ne_of_gt hab)
    (by linarith) (by linarith)
  have hs2 := P.u_conc.secant_strict_mono (a := b + Δ) (x := a) (y := a + Δ)
    (mem_Ici.mpr (by linarith)) (mem_Ici.mpr ha) (mem_Ici.mpr (by linarith)) (by linarith)
    (by linarith) (by linarith)
  have hL : 0 < b - a := sub_pos.mpr hab
  have e1 : (u (a + Δ) - u (b + Δ)) / (a + Δ - (b + Δ)) = (u (b + Δ) - u (a + Δ)) / (b - a) := by
    rw [show a + Δ - (b + Δ) = -(b - a) by ring, div_neg, ← neg_div]
    ring_nf
  have e2 : (u a - u (b + Δ)) / (a - (b + Δ)) = (u (b + Δ) - u a) / (b + Δ - a) := by
    rw [show a - (b + Δ) = -(b + Δ - a) by ring, div_neg, ← neg_div]
    ring_nf
  rw [e1, e2] at hs2
  have h := hs2.trans hs1
  rwa [div_lt_div_iff_of_pos_right hL] at h

/-- Next period's capital chosen from `x`. -/
noncomputable def policy (P : Primitives f u β δ) (x : ℝ) : ℝ :=
  if hx : 0 ≤ x then optimalPath P hx 1 else 0

theorem policy_eq (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) :
    policy P x = optimalPath P hx 1 := by
  simp only [policy, hx, ↓reduceDIte]

/-- Every optimal path follows the policy. -/
theorem IsOptimal.succ_eq_policy (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) : k (t + 1) = policy P (k t) := by
  have hkt := hk.1.nonneg hx t
  have hs := hk.shift P hx t
  have heq := optimal_unique P hkt hs.1 hs.2
  rw [policy_eq P hkt]
  exact congrFun heq 1

/-- The Bellman equation at the policy, with its feasibility. -/
theorem bellman_policy (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) :
    value P x = u (resources f δ x - policy P x) + β * value P (policy P x) ∧
      0 ≤ policy P x ∧ policy P x ≤ resources f δ x := by
  obtain ⟨hk, -⟩ := optimalPath_spec P hx
  rw [policy_eq P hx]
  exact ⟨(bellman P hx).1, (hk.2 0).1, (hk.2 0).2.trans_eq (congrArg (resources f δ) hk.1)⟩

/-- From `x > 0`, next capital is interior and the Euler equation holds at date zero. -/
theorem policy_interior (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) :
    0 < policy P x ∧ policy P x < resources f δ x ∧
      deriv u (resources f δ x - policy P x) =
        β * deriv u (resources f δ (policy P x) - policy P (policy P x)) *
          (deriv f (policy P x) + (1 - δ)) := by
  have hk := isOptimal_optimalPath P hx.le
  obtain ⟨-, h1, hc⟩ := hk.interior P hx 0
  have he := hk.euler P hx 0
  have hs0 := hk.succ_eq_policy P hx.le 0
  have hs1 := hk.succ_eq_policy P hx.le 1
  have h0 : optimalPath P hx.le 0 = x := hk.1.1
  simp only [consumption, zero_add] at hc he h1 hs0 hs1
  rw [h0] at hs0 hc he
  rw [hs0] at h1 hc he hs1
  rw [hs1] at he
  exact ⟨h1, by linarith, he⟩

/-- The policy is strictly increasing. -/
theorem policy_strictMono (P : Primitives f u β δ) : StrictMonoOn (policy P) (Ioi 0) := by
  intro x hx x' hx' hxx
  have hx0 : (0 : ℝ) < x := hx
  have hx0' : (0 : ℝ) < x' := hx'
  obtain ⟨-, hy0, hyF⟩ := bellman_policy P hx0.le
  obtain ⟨-, hy0', hyF'⟩ := bellman_policy P hx0'.le
  have hFF := P.resources_strictMono (mem_Ici.mpr hx0.le) (mem_Ici.mpr hx0'.le) hxx
  have hweak : policy P x ≤ policy P x' := by
    by_contra hlt
    push Not at hlt
    have h1 := (bellman P hx0.le).2 (policy P x') hy0' (hlt.le.trans hyF)
    have h2 := (bellman P hx0'.le).2 (policy P x) hy0 (hyF.trans hFF.le)
    have hb1 := (bellman_policy P hx0.le).1
    have hb2 := (bellman_policy P hx0'.le).1
    have hinc := shift_increment_lt P (a := resources f δ x - policy P x)
      (b := resources f δ x - policy P x') (Δ := resources f δ x' - resources f δ x)
      (sub_nonneg.mpr hyF) (by linarith) (by linarith)
    rw [show resources f δ x - policy P x' + (resources f δ x' - resources f δ x) =
        resources f δ x' - policy P x' by ring,
      show resources f δ x - policy P x + (resources f δ x' - resources f δ x) =
        resources f δ x' - policy P x by ring] at hinc
    linarith
  rcases lt_or_eq_of_le hweak with hlt | heq
  · exact hlt
  · -- equal choices contradict the two Euler equations
    exfalso
    obtain ⟨hp, hpF, he⟩ := policy_interior P hx0
    obtain ⟨-, hpF', he'⟩ := policy_interior P hx0'
    rw [← heq] at he' hpF'
    have hu : deriv u (resources f δ x - policy P x) = deriv u (resources f δ x' - policy P x) := by
      rw [he, he']
    have hc : 0 < resources f δ x - policy P x := by linarith
    have hc' : 0 < resources f δ x' - policy P x := by linarith
    have := P.u_prime_anti.injOn hc hc' hu
    linarith

theorem Primitives.target_pos (P : Primitives f u β δ) : 0 < 1 / β - (1 - δ) := by
  have h1 : 1 < 1 / β := by rw [lt_div_iff₀ P.β_pos]; linarith [P.β_lt_one]
  linarith [P.δ_pos]

theorem Primitives.existsUnique_steady (P : Primitives f u β δ) :
    ∃! k : ℝ, 0 < k ∧ deriv f k = 1 / β - (1 - δ) :=
  existsUnique_positive_root_of_inada (deriv f) _ P.target_pos P.f_prime_cont
    (production_deriv_strictAnti f P.f_conc P.f_diff) P.f_inada0 P.f_inadaTop

/-- The steady state: `β (f'(k*) + 1 - δ) = 1`. -/
noncomputable def steady (P : Primitives f u β δ) : ℝ :=
  Classical.choose P.existsUnique_steady.exists

theorem steady_spec (P : Primitives f u β δ) :
    0 < steady P ∧ deriv f (steady P) = 1 / β - (1 - δ) :=
  Classical.choose_spec P.existsUnique_steady.exists

theorem steady_euler (P : Primitives f u β δ) : β * (deriv f (steady P) + (1 - δ)) = 1 := by
  rw [(steady_spec P).2]
  field_simp [P.β_pos.ne']
  ring

/-- Steady-state consumption `c* = F(k*) - k*` is positive. -/
theorem steady_consumption_pos (P : Primitives f u β δ) :
    0 < resources f δ (steady P) - steady P := by
  obtain ⟨hk, hd⟩ := steady_spec P
  have hgap := marginal_product_times_capital_lt_output f _ P.f_conc P.f_zero hk (P.f_diff _ hk)
  rw [hd] at hgap
  have h1 : 1 < 1 / β := by rw [lt_div_iff₀ P.β_pos]; linarith [P.β_lt_one]
  have : (1 - (1 - δ)) * steady P < (1 / β - (1 - δ)) * steady P :=
    mul_lt_mul_of_pos_right (by linarith) hk
  simp only [resources]
  nlinarith

theorem hasDerivAt_resources_pos (P : Primitives f u β δ) {k : ℝ} (hk : 0 < k) :
    0 < deriv f k + (1 - δ) := by
  have := P.f_prime_pos k hk
  linarith [P.δ_le_one]

/-- An optimal path is monotone. -/
theorem IsOptimal.monotone_or_antitone (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : IsOptimal f u β δ x k) :
    (k 0 ≤ k 1 → Monotone k) ∧ (k 1 ≤ k 0 → Antitone k) := by
  have hpos : ∀ t, 0 < k t := fun t => (hk.interior P hx t).1
  have hsucc := hk.succ_eq_policy P hx.le
  constructor
  · intro h01
    apply monotone_nat_of_le_succ
    intro t
    induction t with
    | zero => exact h01
    | succ t ih =>
      calc k (t + 1) = policy P (k t) := hsucc t
        _ ≤ policy P (k (t + 1)) := (policy_strictMono P).monotoneOn (hpos t) (hpos (t + 1)) ih
        _ = k (t + 1 + 1) := (hsucc (t + 1)).symm
  · intro h10
    apply antitone_nat_of_succ_le
    intro t
    induction t with
    | zero => exact h10
    | succ t ih =>
      calc k (t + 1 + 1) = policy P (k (t + 1)) := hsucc (t + 1)
        _ ≤ policy P (k t) := (policy_strictMono P).monotoneOn (hpos (t + 1)) (hpos t) ih
        _ = k (t + 1) := (hsucc t).symm

/-- Every optimal path from positive capital converges to the steady state. -/
theorem IsOptimal.tendsto (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) : Tendsto k atTop (𝓝 (steady P)) := by
  have hpos : ∀ t, 0 < k t := fun t => (hk.interior P hx t).1
  have hcpos : ∀ t, 0 < consumption f δ k t := fun t => (hk.interior P hx t).2.2
  have hbd : ∀ t, k t ≤ bound P x := fun t => hk.1.le_bound P hx.le t
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  -- the limit
  obtain ⟨L, hL⟩ : ∃ L, Tendsto k atTop (𝓝 L) := by
    rcases le_total (k 0) (k 1) with h | h
    · exact ⟨_, tendsto_atTop_ciSup (hmono h) ⟨bound P x, by rintro _ ⟨t, rfl⟩; exact hbd t⟩⟩
    · exact ⟨_, tendsto_atTop_ciInf (hanti h) ⟨0, by rintro _ ⟨t, rfl⟩; exact (hpos t).le⟩⟩
  have hL0 : 0 ≤ L := ge_of_tendsto' hL (fun t => (hpos t).le)
  have hshift : Tendsto (fun t => k (t + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
  have hFcont : ContinuousWithinAt (resources f δ) (Ici 0) L := P.resources_cont L hL0
  have hFk : Tendsto (fun t => resources f δ (k t)) atTop (𝓝 (resources f δ L)) :=
    hFcont.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hL, Eventually.of_forall
      (fun t => mem_Ici.mpr (hpos t).le)⟩)
  have hc : Tendsto (consumption f δ k) atTop (𝓝 (resources f δ L - L)) := hFk.sub hshift
  have hLF : L ≤ resources f δ L := by
    have h := le_of_tendsto_of_tendsto hshift hFk (Eventually.of_forall (fun t => (hk.1.2 t).2))
    exact h
  obtain ⟨hks, hkd⟩ := steady_spec P
  have hr := P.target_pos
  -- case `L = 0` is impossible
  rcases hL0.eq_or_lt with hL00 | hLpos
  · exfalso
    subst hL00
    have hk0 : Tendsto (fun t => k (t + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hshift, Eventually.of_forall (fun t => hpos (t + 1))⟩
    have hbig := (P.f_inada0.comp hk0).eventually (eventually_gt_atTop (1 / β - (1 - δ)))
    obtain ⟨T, hT⟩ := eventually_atTop.mp hbig
    -- consumption rises from `T` on
    have hrise : ∀ t, T ≤ t → consumption f δ k t < consumption f δ k (t + 1) := by
      intro t ht
      have he := hk.euler P hx t
      have hg : 1 < β * (deriv f (k (t + 1)) + (1 - δ)) := by
        have h := hT t ht
        simp only [Function.comp_apply] at h
        have := mul_lt_mul_of_pos_left h P.β_pos
        rw [mul_sub, mul_div_cancel₀ _ P.β_pos.ne'] at this
        nlinarith
      by_contra hle
      push Not at hle
      have hu := P.u_prime_anti.antitoneOn (hcpos (t + 1)) (hcpos t) hle
      have hup := P.u_prime_pos _ (hcpos (t + 1))
      have : deriv u (consumption f δ k (t + 1)) <
          β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ)) := by
        nlinarith
      linarith
    have hge : ∀ n, consumption f δ k T ≤ consumption f δ k (T + n) := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih => exact ih.trans (hrise (T + n) (by omega)).le
    rw [resources_zero P, sub_zero] at hc
    have hev := (hc.eventually (gt_mem_nhds (hcpos T)))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    have := hN (T + N) (by omega)
    have := hge N
    linarith
  -- case `F(L) = L`: consumption vanishes, contradicted by jumping to `k*`
  rcases lt_or_eq_of_le hLF with hFL | hFL
  · -- `F(L) > L`: the Euler equation in the limit pins down `L = k*`
    have hcL : 0 < resources f δ L - L := sub_pos.mpr hFL
    have huc : ContinuousAt (deriv u) (resources f δ L - L) :=
      P.u_prime_cont.continuousAt (Ioi_mem_nhds hcL)
    have hfc : ContinuousAt (deriv f) L := P.f_prime_cont.continuousAt (Ioi_mem_nhds hLpos)
    have hlhs := huc.tendsto.comp hc
    have hrhs := ((huc.tendsto.comp (hc.comp (tendsto_add_atTop_nat 1))).const_mul β).mul
      ((hfc.tendsto.comp hshift).add_const (1 - δ))
    have heq : deriv u (resources f δ L - L) =
        β * deriv u (resources f δ L - L) * (deriv f L + (1 - δ)) :=
      tendsto_nhds_unique hlhs (hrhs.congr (fun t => by
        simp only [Function.comp_apply]
        exact (hk.euler P hx t).symm))
    have hup := P.u_prime_pos _ hcL
    have hβ : β * (deriv f L + (1 - δ)) = 1 := by
      have : deriv u (resources f δ L - L) * (β * (deriv f L + (1 - δ)) - 1) = 0 := by
        linear_combination -heq
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ne_of_gt hup)
      · linarith
    have hfL : deriv f L = 1 / β - (1 - δ) := by
      field_simp [P.β_pos.ne']
      linarith
    have := P.existsUnique_steady.unique ⟨hLpos, hfL⟩ ⟨hks, hkd⟩
    rw [this] at hL
    exact hL
  · exfalso
    -- consumption tends to zero and `L > k*`
    rw [← hFL, sub_self] at hc
    have hLks : steady P < L := by
      have hfL : f L = δ * L := by simp only [resources] at hFL; linarith
      have hgap := marginal_product_times_capital_lt_output f L P.f_conc P.f_zero hLpos
        (P.f_diff L hLpos)
      rw [hfL] at hgap
      have hdL : deriv f L < δ := by nlinarith
      by_contra hle
      push Not at hle
      have := (production_deriv_strictAnti f P.f_conc P.f_diff).antitoneOn hLpos hks hle
      rw [hkd] at this
      have h1 : 1 < 1 / β := by rw [lt_div_iff₀ P.β_pos]; linarith [P.β_lt_one]
      linarith
    have hcs0 := steady_consumption_pos P
    set cs := resources f δ (steady P) - steady P with hcs_def
    have hcs : 0 < cs := hcs0
    obtain ⟨T, hT⟩ := eventually_atTop.mp ((hL.eventually (lt_mem_nhds hLks)).and
      (hc.eventually (gt_mem_nhds (half_pos hcs))))
    -- the alternative path from `k T`: move to `k*` and stay there
    set z : ℕ → ℝ := fun s => if s = 0 then k T else steady P
    have hFmono : resources f δ (steady P) ≤ resources f δ (k T) :=
      P.resources_strictMono.monotoneOn (mem_Ici.mpr hks.le) (mem_Ici.mpr (hpos T).le)
        (hT T le_rfl).1.le
    have hFT : steady P < resources f δ (k T) := by linarith
    have hz : Feasible f δ (k T) z := by
      refine ⟨rfl, fun s => ⟨?_, ?_⟩⟩
      · simp only [z, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]; exact hks.le
      · rcases s with _ | s
        · simp only [z, zero_add, one_ne_zero, ↓reduceIte]; exact hFT.le
        · simp only [z, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]; linarith
    have hzc : ∀ s, cs ≤ consumption f δ z s := by
      intro s
      rcases s with _ | s
      · simp only [consumption, z, zero_add, one_ne_zero, ↓reduceIte]
        linarith
      · simp only [consumption, z, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        exact le_rfl
    have hsT := hk.shift P hx.le T
    have hle := hsT.2 z hz
    -- compare welfare termwise
    have hshc : ∀ s, consumption f δ (fun s => k (T + s)) s ≤ cs / 2 := by
      intro s
      have := (hT (T + s) (by omega)).2
      exact this.le
    have hshnn : ∀ s, 0 ≤ consumption f δ (fun s => k (T + s)) s :=
      fun s => (hsT.1.consumption_mem P (hpos T).le s).1
    have hgeo := summable_geometric_of_lt_one P.β_pos.le P.β_lt_one
    have h1 : welfare f u β δ (fun s => k (T + s)) ≤ ∑' s, β ^ s * u (cs / 2) :=
      (hsT.1.summable P (hpos T).le).tsum_le_tsum (fun s => mul_le_mul_of_nonneg_left
        (P.u_strictMono.monotoneOn (hshnn s) (mem_Ici.mpr (half_pos hcs).le) (hshc s))
        (pow_pos P.β_pos s).le) (hgeo.mul_right _)
    have h2 : ∑' s, β ^ s * u (cs / 2) < ∑' s, β ^ s * u cs :=
      (hgeo.mul_right _).tsum_lt_tsum (i := 0) (fun s => mul_le_mul_of_nonneg_left
        (P.u_strictMono.monotoneOn (mem_Ici.mpr (half_pos hcs).le) (mem_Ici.mpr hcs.le)
          (half_le_self hcs.le)) (pow_pos P.β_pos s).le)
        (by
          simp only [pow_zero, one_mul]
          exact P.u_strictMono (mem_Ici.mpr (half_pos hcs).le) (mem_Ici.mpr hcs.le)
            (half_lt_self hcs))
        (hgeo.mul_right _)
    have h3 : ∑' s, β ^ s * u cs ≤ welfare f u β δ z :=
      (hgeo.mul_right _).tsum_le_tsum (fun s => mul_le_mul_of_nonneg_left
        (P.u_strictMono.monotoneOn (mem_Ici.mpr hcs.le)
          (mem_Ici.mpr (hcs.le.trans (hzc s))) (hzc s)) (pow_pos P.β_pos s).le)
        (hz.summable P (hpos T).le)
    linarith

/-- Consumption converges to `c* = F(k*) - k*`. -/
theorem IsOptimal.consumption_tendsto (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : IsOptimal f u β δ x k) :
    Tendsto (consumption f δ k) atTop (𝓝 (resources f δ (steady P) - steady P)) := by
  have hL := hk.tendsto P hx
  have hks := (steady_spec P).1
  have hFk : Tendsto (fun t => resources f δ (k t)) atTop (𝓝 (resources f δ (steady P))) :=
    (P.resources_cont _ (mem_Ici.mpr hks.le)).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hL, Eventually.of_forall (fun t => mem_Ici.mpr (hk.interior P hx t).1.le)⟩)
  exact hFk.sub (hL.comp (tendsto_add_atTop_nat 1))

/-- Below the steady state an optimal path rises strictly toward `k*`, with rising
consumption. -/
theorem IsOptimal.dynamics_below (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (hlt : x < steady P) :
    StrictMono k ∧ (∀ t, k t < steady P) ∧ StrictMono (consumption f δ k) := by
  have hpos : ∀ t, 0 < k t := fun t => (hk.interior P hx t).1
  have hL := hk.tendsto P hx
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  have hsucc := hk.succ_eq_policy P hx.le
  have h01 : k 0 < k 1 := by
    by_contra hle
    push Not at hle
    have hlim := le_of_tendsto' hL (fun t => (hanti hle) (Nat.zero_le t))
    rw [hk.1.1] at hlim
    linarith
  have hsm : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro t
    induction t with
    | zero => exact h01
    | succ t ih =>
      calc k (t + 1) = policy P (k t) := hsucc t
        _ < policy P (k (t + 1)) := policy_strictMono P (hpos t) (hpos (t + 1)) ih
        _ = k (t + 1 + 1) := (hsucc (t + 1)).symm
  have hbelow : ∀ t, k t < steady P := fun t =>
    (hsm (Nat.lt_succ_self t)).trans_le (ge_of_tendsto hL (eventually_atTop.mpr
      ⟨t + 1, fun s hs => hsm.monotone hs⟩))
  refine ⟨hsm, hbelow, strictMono_nat_of_lt_succ (fun t => ?_)⟩
  have he := hk.euler P hx t
  have hks := steady_spec P
  have hfd : deriv f (steady P) < deriv f (k (t + 1)) :=
    (production_deriv_strictAnti f P.f_conc P.f_diff) (hpos (t + 1)) hks.1 (hbelow (t + 1))
  have hg : 1 < β * (deriv f (k (t + 1)) + (1 - δ)) := by
    have := steady_euler P
    nlinarith [P.β_pos]
  have hcpos := fun t => (hk.interior P hx t).2.2
  by_contra hle
  push Not at hle
  have hu := P.u_prime_anti.antitoneOn (hcpos (t + 1)) (hcpos t) hle
  have hup := P.u_prime_pos _ (hcpos (t + 1))
  nlinarith

/-- Above the steady state an optimal path falls strictly toward `k*`, with falling
consumption. -/
theorem IsOptimal.dynamics_above (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (hgt : steady P < x) :
    StrictAnti k ∧ (∀ t, steady P < k t) ∧ StrictAnti (consumption f δ k) := by
  have hpos : ∀ t, 0 < k t := fun t => (hk.interior P hx t).1
  have hL := hk.tendsto P hx
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  have hsucc := hk.succ_eq_policy P hx.le
  have h10 : k 1 < k 0 := by
    by_contra hle
    push Not at hle
    have hlim := ge_of_tendsto' hL (fun t => (hmono hle) (Nat.zero_le t))
    rw [hk.1.1] at hlim
    linarith
  have hsa : StrictAnti k := by
    apply strictAnti_nat_of_succ_lt
    intro t
    induction t with
    | zero => exact h10
    | succ t ih =>
      calc k (t + 1 + 1) = policy P (k (t + 1)) := hsucc (t + 1)
        _ < policy P (k t) := policy_strictMono P (hpos (t + 1)) (hpos t) ih
        _ = k (t + 1) := (hsucc t).symm
  have habove : ∀ t, steady P < k t := fun t =>
    lt_of_le_of_lt (le_of_tendsto hL (eventually_atTop.mpr
      ⟨t + 1, fun s hs => hsa.antitone hs⟩)) (hsa (Nat.lt_succ_self t))
  refine ⟨hsa, habove, strictAnti_nat_of_succ_lt (fun t => ?_)⟩
  have he := hk.euler P hx t
  have hks := steady_spec P
  have hfd : deriv f (k (t + 1)) < deriv f (steady P) :=
    (production_deriv_strictAnti f P.f_conc P.f_diff) hks.1 (hpos (t + 1)) (habove (t + 1))
  have hg : β * (deriv f (k (t + 1)) + (1 - δ)) < 1 := by
    have := steady_euler P
    nlinarith [P.β_pos]
  have hcpos := fun t => (hk.interior P hx t).2.2
  by_contra hle
  push Not at hle
  have hu := P.u_prime_anti.antitoneOn (hcpos t) (hcpos (t + 1)) hle
  have hup := P.u_prime_pos _ (hcpos (t + 1))
  have hFp := hasDerivAt_resources_pos P (hpos (t + 1))
  nlinarith

/-- Optimal paths of identical economies never cross. -/
theorem IsOptimal.capital_lt (P : Primitives f u β δ) {x x' : ℝ} (hx : 0 < x)
    {k k' : ℕ → ℝ} (hk : IsOptimal f u β δ x k) (hk' : IsOptimal f u β δ x' k') (hxx : x < x')
    (t : ℕ) : k t < k' t := by
  have hx' : 0 < x' := hx.trans hxx
  induction t with
  | zero => rw [hk.1.1, hk'.1.1]; exact hxx
  | succ t ih =>
    rw [hk.succ_eq_policy P hx.le t, hk'.succ_eq_policy P hx'.le t]
    exact policy_strictMono P (hk.interior P hx t).1 (hk'.interior P hx' t).1 ih

/-- Consumption as a function of capital. -/
noncomputable def consumptionPolicy (P : Primitives f u β δ) (x : ℝ) : ℝ :=
  resources f δ x - policy P x

theorem IsOptimal.consumption_eq (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    consumption f δ k t = consumptionPolicy P (k t) := by
  simp only [consumption, consumptionPolicy, hk.succ_eq_policy P hx t]

/-- Consumption is strictly increasing in capital. -/
theorem consumptionPolicy_strictMono (P : Primitives f u β δ) :
    StrictMonoOn (consumptionPolicy P) (Ioi 0) := by
  intro x hx x' hx' hxx
  have hx0 : (0 : ℝ) < x := hx
  have hx0' : (0 : ℝ) < x' := hx'
  set k := optimalPath P hx0.le
  set k' := optimalPath P hx0'.le
  have hk := isOptimal_optimalPath P hx0.le
  have hk' := isOptimal_optimalPath P hx0'.le
  have hc0 : consumption f δ k 0 = consumptionPolicy P x := by
    rw [hk.consumption_eq P hx0.le 0, hk.1.1]
  have hc0' : consumption f δ k' 0 = consumptionPolicy P x' := by
    rw [hk'.consumption_eq P hx0'.le 0, hk'.1.1]
  rw [← hc0, ← hc0']
  by_contra hle
  push Not at hle
  have hcp := fun t => (hk.interior P hx0 t).2.2
  have hcp' := fun t => (hk'.interior P hx0' t).2.2
  have hkp := fun t => (hk.interior P hx0 t).1
  have hkp' := fun t => (hk'.interior P hx0' t).1
  -- the marginal-utility ratio `R t = u'(c'_t)/u'(c_t)` rises strictly
  set R : ℕ → ℝ := fun t => deriv u (consumption f δ k' t) / deriv u (consumption f δ k t)
  have hup := fun t => P.u_prime_pos _ (hcp t)
  have hup' := fun t => P.u_prime_pos _ (hcp' t)
  have hstep : ∀ t, R t < R (t + 1) := by
    intro t
    have he := hk.euler P hx0 t
    have he' := hk'.euler P hx0' t
    have hlt := hk.capital_lt P hx0 hk' hxx (t + 1)
    have hfd : deriv f (k' (t + 1)) < deriv f (k (t + 1)) :=
      (production_deriv_strictAnti f P.f_conc P.f_diff) (hkp (t + 1)) (hkp' (t + 1)) hlt
    have hF := hasDerivAt_resources_pos P (hkp' (t + 1))
    simp only [R]
    rw [div_lt_div_iff₀ (hup t) (hup (t + 1)), he, he']
    have := mul_pos (mul_pos P.β_pos (hup' (t + 1))) (hup (t + 1))
    nlinarith
  have hR0 : 1 ≤ R 0 := by
    simp only [R]
    rw [le_div_iff₀ (hup 0), one_mul]
    exact P.u_prime_anti.antitoneOn (hcp' 0) (hcp 0) hle
  have hR1 : ∀ t, R 1 ≤ R (t + 1) := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih => exact ih.trans (hstep (t + 1)).le
  -- but `R t → 1`
  have hcs := steady_consumption_pos P
  have huc : ContinuousAt (deriv u) (resources f δ (steady P) - steady P) :=
    P.u_prime_cont.continuousAt (Ioi_mem_nhds hcs)
  have hlim : Tendsto R atTop (𝓝 1) := by
    have h := (huc.tendsto.comp (hk'.consumption_tendsto P hx0')).div
      (huc.tendsto.comp (hk.consumption_tendsto P hx0)) (ne_of_gt (P.u_prime_pos _ hcs))
    rw [div_self (ne_of_gt (P.u_prime_pos _ hcs))] at h
    exact h
  have hge : R 1 ≤ 1 := ge_of_tendsto' (hlim.comp (tendsto_add_atTop_nat 1))
    (fun t => hR1 t)
  have := hstep 0
  linarith

/-- The poorer economy consumes strictly less at every date. -/
theorem IsOptimal.consumption_lt (P : Primitives f u β δ) {x x' : ℝ} (hx : 0 < x)
    {k k' : ℕ → ℝ} (hk : IsOptimal f u β δ x k) (hk' : IsOptimal f u β δ x' k') (hxx : x < x')
    (t : ℕ) : consumption f δ k t < consumption f δ k' t := by
  have hx' : 0 < x' := hx.trans hxx
  rw [hk.consumption_eq P hx.le t, hk'.consumption_eq P hx'.le t]
  exact consumptionPolicy_strictMono P (hk.interior P hx t).1 (hk'.interior P hx' t).1
    (hk.capital_lt P hx hk' hxx t)

/-- Absolute convergence of identical economies. -/
theorem IsOptimal.absolute_convergence (P : Primitives f u β δ) {x x' : ℝ} (hx : 0 < x)
    (hx' : 0 < x') {k k' : ℕ → ℝ} (hk : IsOptimal f u β δ x k)
    (hk' : IsOptimal f u β δ x' k') :
    Tendsto (fun t => k' t - k t) atTop (𝓝 0) ∧
      Tendsto (fun t => consumption f δ k' t - consumption f δ k t) atTop (𝓝 0) := by
  constructor
  · simpa only [sub_self] using (hk'.tendsto P hx').sub (hk.tendsto P hx)
  · simpa only [sub_self] using (hk'.consumption_tendsto P hx').sub (hk.consumption_tendsto P hx)

end RamseyCassKoopmans.DiscreteTime

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# The envelope theorem and steady-state comparative statics in discrete time

* `value_hasDerivAt`: `V'(x) = u'(c₀) (f'(x) + 1 - δ)` at every `x > 0`, where
  `c₀ = F(x) - g(x)`. As in continuous time the proof is the Clausen–Strub sandwich
  (`clausen_strub_sandwich`): the lower support is `u(F(z) - g(x)) + β V(g(x))`
  (keep next period's capital), and the upper support is the tangent line, which
  bounds `V` from above by concavity (`concave_le_tangent_of_lower_support`).
* `steady_strictMono_patience`, `steady_strictAnti_depreciation`: the steady state
  rises with patience `β` and falls with depreciation `δ`.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.DiscreteTime

variable {f u : ℝ → ℝ} {β δ : ℝ}

/-- A concave function with a lower support touching it at an interior point, and
differentiable there, lies below the support's tangent line. -/
theorem concave_le_tangent_of_lower_support {V L : ℝ → ℝ} {x D : ℝ}
    (hV : ConcaveOn ℝ (Ici 0) V) (hx : 0 < x) (hL : HasDerivAt L D x)
    (hLV : ∀ᶠ z in 𝓝 x, L z ≤ V z) (hLx : L x = V x) {z : ℝ} (hz : 0 ≤ z) :
    V z ≤ V x + D * (z - x) := by
  rw [hasDerivAt_iff_tendsto_slope, ← nhdsLT_sup_nhdsGT, tendsto_sup] at hL
  rcases lt_trichotomy z x with hzx | hzx | hzx
  · -- slopes to the right of `x` are at most the slope over `[z, x]`
    have hbound : D ≤ (V x - V z) / (x - z) := by
      refine le_of_tendsto hL.2 ?_
      filter_upwards [nhdsWithin_le_nhds hLV, self_mem_nhdsWithin] with w hw hwx
      have hwx' : x < w := hwx
      have hslope := hV.slope_anti_adjacent (x := z) (y := x) (z := w) (mem_Ici.mpr hz)
        (mem_Ici.mpr (hx.le.trans hwx'.le)) hzx hwx'
      rw [slope_def_field]
      calc (L w - L x) / (w - x) ≤ (V w - V x) / (w - x) :=
            div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hwx'.le)
        _ ≤ (V x - V z) / (x - z) := hslope
    rw [le_div_iff₀ (sub_pos.mpr hzx)] at hbound
    linarith
  · rw [hzx]; simp
  · -- slopes to the left of `x` are at least the slope over `[x, z]`
    have hbound : (V z - V x) / (z - x) ≤ D := by
      refine ge_of_tendsto hL.1 ?_
      filter_upwards [nhdsWithin_le_nhds hLV, self_mem_nhdsWithin,
        nhdsWithin_le_nhds (lt_mem_nhds hx)] with w hw hwx hw0
      have hwx' : w < x := hwx
      have hslope := hV.slope_anti_adjacent (x := w) (y := x) (z := z) (mem_Ici.mpr hw0.le)
        (mem_Ici.mpr hz) hwx' hzx
      rw [slope_def_field]
      calc (V z - V x) / (z - x) ≤ (V x - V w) / (x - w) := hslope
        _ ≤ (L x - L w) / (x - w) :=
            div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hwx'.le)
        _ = (L w - L x) / (w - x) := by
            rw [show L x - L w = -(L w - L x) by ring, show x - w = -(w - x) by ring,
              neg_div_neg_eq]
    rw [div_le_iff₀ (sub_pos.mpr hzx)] at hbound
    linarith

/-- The envelope theorem: `V'(x) = u'(c₀) (f'(x) + 1 - δ)`. -/
theorem value_hasDerivAt (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (value P) (deriv u (resources f δ x - policy P x) * (deriv f x + (1 - δ))) x := by
  obtain ⟨hy, hyF, -⟩ := policy_interior P hx
  set y := policy P x
  have hc : 0 < resources f δ x - y := by linarith
  set D := deriv u (resources f δ x - y) * (deriv f x + (1 - δ))
  set L : ℝ → ℝ := fun z => u (resources f δ z - y) + β * value P y
  have hL : HasDerivAt L D x := by
    exact ((P.u_diff _ hc).hasDerivAt.comp x
      ((hasDerivAt_resources P hx).sub_const y)).add_const (β * value P y)
  have hLx : L x = value P x := (bellman_policy P hx.le).1.symm
  have hLV : ∀ᶠ z in 𝓝 x, L z ≤ value P z := by
    have hFc : ContinuousAt (resources f δ) x := (hasDerivAt_resources P hx).continuousAt
    filter_upwards [lt_mem_nhds hx, hFc.eventually (lt_mem_nhds hyF)] with z hz hzF
    exact (bellman P hz.le).2 y hy.le hzF.le
  have hH : HasDerivAt (fun z => value P x + D * (z - x)) D x := by
    have := ((hasDerivAt_id x).sub_const x).const_mul D |>.const_add (value P x)
    simpa only [id, mul_one] using this
  refine clausen_strub_sandwich hL hH hLV ?_ hLx (by ring)
  filter_upwards [lt_mem_nhds hx] with z hz
  exact concave_le_tangent_of_lower_support (value_strictConcave P).concaveOn hx hL hLV hLx hz.le

/-- A more patient economy has a larger steady state. -/
theorem steady_strictMono_patience {β' : ℝ} (P : Primitives f u β δ)
    (P' : Primitives f u β' δ) (hββ : β < β') : steady P < steady P' := by
  obtain ⟨hk, hd⟩ := steady_spec P
  obtain ⟨hk', hd'⟩ := steady_spec P'
  by_contra hle
  push Not at hle
  have hanti := (production_deriv_strictAnti f P.f_conc P.f_diff).antitoneOn hk' hk hle
  rw [hd, hd'] at hanti
  have : 1 / β' < 1 / β := one_div_lt_one_div_of_lt P.β_pos hββ
  linarith

/-- Faster depreciation lowers the steady state. -/
theorem steady_strictAnti_depreciation {δ' : ℝ} (P : Primitives f u β δ)
    (P' : Primitives f u β δ') (hδδ : δ < δ') : steady P' < steady P := by
  obtain ⟨hk, hd⟩ := steady_spec P
  obtain ⟨hk', hd'⟩ := steady_spec P'
  by_contra hle
  push Not at hle
  have hanti := (production_deriv_strictAnti f P.f_conc P.f_diff).antitoneOn hk hk' hle
  rw [hd, hd'] at hanti
  linarith

end RamseyCassKoopmans.DiscreteTime

#print axioms RamseyCassKoopmans.FeasiblePath
#print axioms RamseyCassKoopmans.FeasiblePath.mk
#print axioms RamseyCassKoopmans.FeasiblePath.capital
#print axioms RamseyCassKoopmans.FeasiblePath.consumption
#print axioms RamseyCassKoopmans.FeasiblePath.investment
#print axioms RamseyCassKoopmans.FeasiblePath.capital_nonneg
#print axioms RamseyCassKoopmans.FeasiblePath.consumption_pos
#print axioms RamseyCassKoopmans.FeasiblePath.consumption_continuous
#print axioms RamseyCassKoopmans.FeasiblePath.investment_continuous
#print axioms RamseyCassKoopmans.FeasiblePath.resource
#print axioms RamseyCassKoopmans.FeasiblePath.dynamics
#print axioms RamseyCassKoopmans.FeasiblePath.NonnegativeInvestment
#print axioms RamseyCassKoopmans.FeasiblePath.capital_continuous
#print axioms RamseyCassKoopmans.discount
#print axioms RamseyCassKoopmans.discount_pos
#print axioms RamseyCassKoopmans.discount_continuous
#print axioms RamseyCassKoopmans.hasDerivAt_discount
#print axioms RamseyCassKoopmans.welfare
#print axioms RamseyCassKoopmans.HasWelfare
#print axioms RamseyCassKoopmans.boundary
#print axioms RamseyCassKoopmans.hasDerivAt_discounted_costate
#print axioms RamseyCassKoopmans.discounted_costate_normalization
#print axioms RamseyCassKoopmans.present_value_boundary_derivative
#print axioms RamseyCassKoopmans.cass_pointwise_welfare_identity
#print axioms RamseyCassKoopmans.present_value_welfare_identity
#print axioms RamseyCassKoopmans.present_value_comparison_nonneg
#print axioms RamseyCassKoopmans.corner_does_not_imply_euler_equality
#print axioms RamseyCassKoopmans.interior_implies_euler_equality
#print axioms RamseyCassKoopmans.complementarity_welfare_term
#print axioms RamseyCassKoopmans.nonnegative_welfare_remainders
#print axioms RamseyCassKoopmans.correct_terminal_bound
#print axioms RamseyCassKoopmans.reversed_terminal_bound_is_invalid
#print axioms RamseyCassKoopmans.population_weighted_stationary_rate
#print axioms RamseyCassKoopmans.concave_support
#print axioms RamseyCassKoopmans.strict_concave_support
#print axioms RamseyCassKoopmans.concavity_remainder_nonneg
#print axioms RamseyCassKoopmans.concavity_remainder_pos
#print axioms RamseyCassKoopmans.concavity_remainder_eq_zero_iff
#print axioms RamseyCassKoopmans.Terminal.terminal_tendsto_zero_of_bounded_capital
#print axioms RamseyCassKoopmans.Terminal.discount_factor_tendsto_zero
#print axioms RamseyCassKoopmans.Terminal.discounted_price_tendsto_zero
#print axioms RamseyCassKoopmans.Terminal.discounted_terminal_tendsto_zero
#print axioms RamseyCassKoopmans.Terminal.discounted_price_tendsto_zero_of_consumption_limit
#print axioms RamseyCassKoopmans.Terminal.capital_le_capacity
#print axioms RamseyCassKoopmans.Terminal.discounted_terminal_tendsto_zero_of_feasible_paths
#print axioms RamseyCassKoopmans.existsUnique_positive_root_of_bracket
#print axioms RamseyCassKoopmans.exists_positive_bracket_of_inada
#print axioms RamseyCassKoopmans.existsUnique_positive_root_of_inada
#print axioms RamseyCassKoopmans.production_deriv_strictAnti
#print axioms RamseyCassKoopmans.existsUnique_stationary_capital_of_bracket
#print axioms RamseyCassKoopmans.existsUnique_stationary_capital_of_inada
#print axioms RamseyCassKoopmans.marginal_product_times_capital_lt_output
#print axioms RamseyCassKoopmans.stationary_consumption_pos
#print axioms RamseyCassKoopmans.existsUnique_positive_stationary_pair_of_bracket
#print axioms RamseyCassKoopmans.existsUnique_positive_stationary_pair_of_inada
#print axioms RamseyCassKoopmans.golden_rule_strictly_maximizes_consumption
#print axioms RamseyCassKoopmans.stationary_capital_lt_golden_rule
#print axioms RamseyCassKoopmans.stationary_capital_lt_golden_rule_of_strictConcave
#print axioms RamseyCassKoopmans.stationary_investment_pos
#print axioms RamseyCassKoopmans.stationary_resource_and_capital
#print axioms RamseyCassKoopmans.interior_euler_stationary_iff
#print axioms RamseyCassKoopmans.stationaryPath
#print axioms RamseyCassKoopmans.stationaryPath_nonnegativeInvestment
#print axioms RamseyCassKoopmans.welfare_constant_consumption
#print axioms RamseyCassKoopmans.hasWelfare_constant_consumption
#print axioms RamseyCassKoopmans.stationaryPath_hasWelfare
#print axioms RamseyCassKoopmans.SupportingPrices
#print axioms RamseyCassKoopmans.SupportingPrices.mk
#print axioms RamseyCassKoopmans.SupportingPrices.price
#print axioms RamseyCassKoopmans.SupportingPrices.marginalUtility
#print axioms RamseyCassKoopmans.SupportingPrices.marginalProduct
#print axioms RamseyCassKoopmans.SupportingPrices.weight_nonneg
#print axioms RamseyCassKoopmans.SupportingPrices.weight_continuous
#print axioms RamseyCassKoopmans.SupportingPrices.utility_continuous
#print axioms RamseyCassKoopmans.SupportingPrices.marginalUtility_continuous
#print axioms RamseyCassKoopmans.SupportingPrices.marginalProduct_continuous
#print axioms RamseyCassKoopmans.SupportingPrices.marginalUtility_nonneg
#print axioms RamseyCassKoopmans.SupportingPrices.utility_support
#print axioms RamseyCassKoopmans.SupportingPrices.production_support
#print axioms RamseyCassKoopmans.SupportingPrices.costate
#print axioms RamseyCassKoopmans.SupportingPrices.price_continuous
#print axioms RamseyCassKoopmans.AllocationComparison
#print axioms RamseyCassKoopmans.allocation_of_cass
#print axioms RamseyCassKoopmans.allocation_of_interior
#print axioms RamseyCassKoopmans.boundaryRate
#print axioms RamseyCassKoopmans.hasDerivAt_boundary
#print axioms RamseyCassKoopmans.boundaryRate_continuous
#print axioms RamseyCassKoopmans.welfare_integrand_continuous
#print axioms RamseyCassKoopmans.pointwise_comparison
#print axioms RamseyCassKoopmans.finite_horizon_comparison
#print axioms RamseyCassKoopmans.infinite_horizon_optimality
#print axioms RamseyCassKoopmans.infinite_horizon_optimality_of_bounded_capital
#print axioms RamseyCassKoopmans.cassSupportingPrices
#print axioms RamseyCassKoopmans.FeasiblePath.resource_derivative
#print axioms RamseyCassKoopmans.FeasiblePath.capital_le_capacity
#print axioms RamseyCassKoopmans.cass_candidate_dominates
#print axioms RamseyCassKoopmans.IsCassOptimal
#print axioms RamseyCassKoopmans.cass_certificate_is_optimal
#print axioms RamseyCassKoopmans.stationarySupportingPrices
#print axioms RamseyCassKoopmans.stationaryPath_optimality
#print axioms RamseyCassKoopmans.exists_capacity_of_marginal_product_tendsto_zero
#print axioms RamseyCassKoopmans.exists_stationary_optimal_path_of_inada
#print axioms RamseyCassKoopmans.euler_implies_current_value_costate
#print axioms RamseyCassKoopmans.convergent_euler_candidate_optimal
#print axioms RamseyCassKoopmans.positive_limit_of_integral_nonneg_of_pos
#print axioms RamseyCassKoopmans.comparisonSurplus
#print axioms RamseyCassKoopmans.comparisonSurplus_continuous
#print axioms RamseyCassKoopmans.comparisonSurplus_pos_of_consumption_ne
#print axioms RamseyCassKoopmans.integral_comparisonSurplus
#print axioms RamseyCassKoopmans.tendsto_integral_comparisonSurplus
#print axioms RamseyCassKoopmans.strict_welfare_separation
#print axioms RamseyCassKoopmans.consumption_eq_of_welfare_eq
#print axioms RamseyCassKoopmans.comparisonSurplus_pos_of_capital_ne
#print axioms RamseyCassKoopmans.strict_welfare_separation_of_capital_ne
#print axioms RamseyCassKoopmans.capital_eq_of_welfare_eq
#print axioms RamseyCassKoopmans.path_eq_of_welfare_eq
#print axioms RamseyCassKoopmans.Examples.production
#print axioms RamseyCassKoopmans.Examples.sqrt_quarter
#print axioms RamseyCassKoopmans.Examples.production_quarter
#print axioms RamseyCassKoopmans.Examples.production_concave
#print axioms RamseyCassKoopmans.Examples.production_hasDerivAt_quarter
#print axioms RamseyCassKoopmans.Examples.production_capacity
#print axioms RamseyCassKoopmans.Examples.log_continuous_positive
#print axioms RamseyCassKoopmans.Examples.log_hasDerivAt_three_quarters
#print axioms RamseyCassKoopmans.Examples.logSqrtPath
#print axioms RamseyCassKoopmans.Examples.logSqrtPath_values
#print axioms RamseyCassKoopmans.Examples.logSqrtPath_nonnegativeInvestment
#print axioms RamseyCassKoopmans.Examples.logSqrtPath_hasWelfare
#print axioms RamseyCassKoopmans.Examples.logSqrtPath_optimal
#print axioms RamseyCassKoopmans.ClosedForm.utility
#print axioms RamseyCassKoopmans.ClosedForm.state
#print axioms RamseyCassKoopmans.ClosedForm.capital
#print axioms RamseyCassKoopmans.ClosedForm.consumption
#print axioms RamseyCassKoopmans.ClosedForm.investment
#print axioms RamseyCassKoopmans.ClosedForm.state_zero
#print axioms RamseyCassKoopmans.ClosedForm.discount_le_one
#print axioms RamseyCassKoopmans.ClosedForm.state_pos
#print axioms RamseyCassKoopmans.ClosedForm.state_le_max
#print axioms RamseyCassKoopmans.ClosedForm.hasDerivAt_state
#print axioms RamseyCassKoopmans.ClosedForm.state_continuous
#print axioms RamseyCassKoopmans.ClosedForm.state_tendsto
#print axioms RamseyCassKoopmans.ClosedForm.hasDerivAt_capital
#print axioms RamseyCassKoopmans.ClosedForm.capital_tendsto
#print axioms RamseyCassKoopmans.ClosedForm.consumption_tendsto
#print axioms RamseyCassKoopmans.ClosedForm.sqrt_capital
#print axioms RamseyCassKoopmans.ClosedForm.sqrt_consumption
#print axioms RamseyCassKoopmans.ClosedForm.path
#print axioms RamseyCassKoopmans.ClosedForm.path_initial
#print axioms RamseyCassKoopmans.ClosedForm.path_nonnegativeInvestment
#print axioms RamseyCassKoopmans.ClosedForm.utility_continuous
#print axioms RamseyCassKoopmans.ClosedForm.utility_strictConcave
#print axioms RamseyCassKoopmans.ClosedForm.hasDerivAt_utility
#print axioms RamseyCassKoopmans.ClosedForm.hasDerivAt_utility_consumption
#print axioms RamseyCassKoopmans.ClosedForm.hasDerivAt_production_capital
#print axioms RamseyCassKoopmans.ClosedForm.shadow
#print axioms RamseyCassKoopmans.ClosedForm.shadow_continuousOn
#print axioms RamseyCassKoopmans.ClosedForm.hasDerivAt_shadow
#print axioms RamseyCassKoopmans.ClosedForm.supportingPrices
#print axioms RamseyCassKoopmans.ClosedForm.shadow_tendsto
#print axioms RamseyCassKoopmans.ClosedForm.welfare_integrand
#print axioms RamseyCassKoopmans.ClosedForm.integral_discount
#print axioms RamseyCassKoopmans.ClosedForm.welfare_path
#print axioms RamseyCassKoopmans.ClosedForm.path_hasWelfare
#print axioms RamseyCassKoopmans.ClosedForm.state_strictMono
#print axioms RamseyCassKoopmans.ClosedForm.state_strictAnti
#print axioms RamseyCassKoopmans.ClosedForm.capital_strictMonoOn
#print axioms RamseyCassKoopmans.ClosedForm.capital_strictAntiOn
#print axioms RamseyCassKoopmans.ClosedForm.consumption_strictMonoOn
#print axioms RamseyCassKoopmans.ClosedForm.consumption_strictAntiOn
#print axioms RamseyCassKoopmans.ClosedForm.path_optimal
#print axioms RamseyCassKoopmans.ClosedForm.exists_optimal_convergent_path
#print axioms RamseyCassKoopmans.ClosedForm.path_isCassOptimal
#print axioms RamseyCassKoopmans.joinAt
#print axioms RamseyCassKoopmans.joinAt_left
#print axioms RamseyCassKoopmans.joinAt_right
#print axioms RamseyCassKoopmans.continuous_joinAt
#print axioms RamseyCassKoopmans.hasDerivAt_joinAt_switch
#print axioms RamseyCassKoopmans.hasDerivAt_joinAt
#print axioms RamseyCassKoopmans.strictAnti_joinAt
#print axioms RamseyCassKoopmans.tendsto_joinAt_atTop
#print axioms RamseyCassKoopmans.ClosedForm.Corner.r
#print axioms RamseyCassKoopmans.ClosedForm.Corner.inverseFactor
#print axioms RamseyCassKoopmans.ClosedForm.Corner.preCapital
#print axioms RamseyCassKoopmans.ClosedForm.Corner.preConsumption
#print axioms RamseyCassKoopmans.ClosedForm.Corner.preShadow
#print axioms RamseyCassKoopmans.ClosedForm.Corner.preMu
#print axioms RamseyCassKoopmans.ClosedForm.Corner.preMp
#print axioms RamseyCassKoopmans.ClosedForm.Corner.r_pos
#print axioms RamseyCassKoopmans.ClosedForm.Corner.inverseFactor_pos
#print axioms RamseyCassKoopmans.ClosedForm.Corner.r_switch
#print axioms RamseyCassKoopmans.ClosedForm.Corner.inverseFactor_switch
#print axioms RamseyCassKoopmans.ClosedForm.Corner.r_eq_inv_inverseFactor
#print axioms RamseyCassKoopmans.ClosedForm.Corner.hasDerivAt_r
#print axioms RamseyCassKoopmans.ClosedForm.Corner.hasDerivAt_inverseFactor
#print axioms RamseyCassKoopmans.ClosedForm.Corner.r_continuous
#print axioms RamseyCassKoopmans.ClosedForm.Corner.inverseFactor_continuous
#print axioms RamseyCassKoopmans.ClosedForm.Corner.hasDerivAt_preCapital
#print axioms RamseyCassKoopmans.ClosedForm.Corner.hasDerivAt_preConsumption
#print axioms RamseyCassKoopmans.ClosedForm.Corner.hasDerivAt_preShadow
#print axioms RamseyCassKoopmans.ClosedForm.Corner.preCapital_pos
#print axioms RamseyCassKoopmans.ClosedForm.Corner.preConsumption_pos
#print axioms RamseyCassKoopmans.ClosedForm.Corner.sqrt_preCapital
#print axioms RamseyCassKoopmans.ClosedForm.Corner.sqrt_preConsumption
#print axioms RamseyCassKoopmans.ClosedForm.Corner.pre_resource
#print axioms RamseyCassKoopmans.ClosedForm.Corner.pre_utility_derivative
#print axioms RamseyCassKoopmans.ClosedForm.Corner.pre_production_derivative
#print axioms RamseyCassKoopmans.ClosedForm.Corner.preShadow_pos
#print axioms RamseyCassKoopmans.ClosedForm.Corner.preShadow_le_preMu
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedCapital
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedConsumption
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedInvestment
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedShadow
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedMu
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedMp
#print axioms RamseyCassKoopmans.ClosedForm.Corner.tail_state_pos
#print axioms RamseyCassKoopmans.ClosedForm.Corner.tail_shadow_hasDerivAt
#print axioms RamseyCassKoopmans.ClosedForm.Corner.tail_shadow_continuous
#print axioms RamseyCassKoopmans.ClosedForm.Corner.capital_match
#print axioms RamseyCassKoopmans.ClosedForm.Corner.consumption_match
#print axioms RamseyCassKoopmans.ClosedForm.Corner.investment_match
#print axioms RamseyCassKoopmans.ClosedForm.Corner.shadow_match
#print axioms RamseyCassKoopmans.ClosedForm.Corner.mu_match
#print axioms RamseyCassKoopmans.ClosedForm.Corner.mp_match
#print axioms RamseyCassKoopmans.ClosedForm.Corner.hasDerivAt_joinedCapital
#print axioms RamseyCassKoopmans.ClosedForm.Corner.hasDerivAt_joinedShadow
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedConsumption_continuous
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedInvestment_continuous
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedMu_continuous
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedMp_continuous
#print axioms RamseyCassKoopmans.ClosedForm.Corner.cornerPath
#print axioms RamseyCassKoopmans.ClosedForm.Corner.cornerPath_nonnegativeInvestment
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedMu_pos
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedShadow_nonneg
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedShadow_le_joinedMu
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joined_complementarity
#print axioms RamseyCassKoopmans.discount_shift
#print axioms RamseyCassKoopmans.welfare_of_tail_eq
#print axioms RamseyCassKoopmans.hasWelfare_of_tail_eq
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joined_utility_derivative
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joined_production_derivative
#print axioms RamseyCassKoopmans.ClosedForm.Corner.cornerPrices
#print axioms RamseyCassKoopmans.ClosedForm.Corner.corner_allocation
#print axioms RamseyCassKoopmans.ClosedForm.Corner.shift_tendsto
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedCapital_tendsto
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedConsumption_tendsto
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedShadow_tendsto
#print axioms RamseyCassKoopmans.ClosedForm.Corner.cornerValue
#print axioms RamseyCassKoopmans.ClosedForm.Corner.cornerPath_hasWelfare
#print axioms RamseyCassKoopmans.ClosedForm.Corner.cornerPath_isCassOptimal
#print axioms RamseyCassKoopmans.ClosedForm.Corner.cornerPath_initial
#print axioms RamseyCassKoopmans.ClosedForm.Corner.cornerPath_initial_from_stock
#print axioms RamseyCassKoopmans.ClosedForm.Corner.pre_welfare_integrand
#print axioms RamseyCassKoopmans.ClosedForm.Corner.welfare_prefix
#print axioms RamseyCassKoopmans.ClosedForm.Corner.cornerValue_eq
#print axioms RamseyCassKoopmans.ClosedForm.terminal_for_paths
#print axioms RamseyCassKoopmans.ClosedForm.utility_strictConcave_positive
#print axioms RamseyCassKoopmans.ClosedForm.production_strictConcave
#print axioms RamseyCassKoopmans.ClosedForm.path_unique
#print axioms RamseyCassKoopmans.ClosedForm.Corner.preCapital_strictAnti
#print axioms RamseyCassKoopmans.ClosedForm.Corner.preConsumption_strictAnti
#print axioms RamseyCassKoopmans.ClosedForm.Corner.tailCapital_strictAnti
#print axioms RamseyCassKoopmans.ClosedForm.Corner.tailConsumption_strictAnti
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedCapital_strictAnti
#print axioms RamseyCassKoopmans.ClosedForm.Corner.joinedConsumption_strictAnti
#print axioms RamseyCassKoopmans.ClosedForm.Corner.cornerPath_unique
#print axioms RamseyCassKoopmans.ClosedForm.exists_unique_cass_optimal_convergent_path
#print axioms RamseyCassKoopmans.exists_hasWelfare_of_nonneg_bounded
#print axioms RamseyCassKoopmans.ClosedForm.cass_path_hasWelfare
#print axioms RamseyCassKoopmans.ClosedForm.MonotoneTransition
#print axioms RamseyCassKoopmans.ClosedForm.path_monotoneTransition
#print axioms RamseyCassKoopmans.ClosedForm.Corner.cornerPath_monotoneTransition
#print axioms RamseyCassKoopmans.ClosedForm.optimalPath
#print axioms RamseyCassKoopmans.ClosedForm.optimalValue
#print axioms RamseyCassKoopmans.ClosedForm.optimalPath_initial
#print axioms RamseyCassKoopmans.ClosedForm.optimalPath_isCassOptimal
#print axioms RamseyCassKoopmans.ClosedForm.optimalPath_converges
#print axioms RamseyCassKoopmans.ClosedForm.optimalPath_monotone
#print axioms RamseyCassKoopmans.ClosedForm.optimalPath_unique
#print axioms RamseyCassKoopmans.ClosedForm.cass_dynamic_theorem
#print axioms RamseyCassKoopmans.ClosedForm.every_optimum_eq
#print axioms RamseyCassKoopmans.ClosedForm.every_optimum_converges
#print axioms RamseyCassKoopmans.ODE.exists_global_solution
#print axioms RamseyCassKoopmans.ODE.flow_lipschitz_initial
#print axioms RamseyCassKoopmans.ODE.exists_global_flow
#print axioms RamseyCassKoopmans.ODE.flow_add
#print axioms RamseyCassKoopmans.ODE.eventually_lt_right_of_deriv_neg
#print axioms RamseyCassKoopmans.ODE.eventually_below_right
#print axioms RamseyCassKoopmans.ODE.pair_le_barrier
#print axioms RamseyCassKoopmans.ODE.Cooperative
#print axioms RamseyCassKoopmans.ODE.hasDerivAt_fst
#print axioms RamseyCassKoopmans.ODE.hasDerivAt_snd
#print axioms RamseyCassKoopmans.ODE.Cooperative.fst_le_boundary
#print axioms RamseyCassKoopmans.ODE.Cooperative.snd_le_boundary
#print axioms RamseyCassKoopmans.ODE.solution_le_supersolution
#print axioms RamseyCassKoopmans.ODE.solution_le_equilibrium
#print axioms RamseyCassKoopmans.ODE.Cooperative.fst_le_gap
#print axioms RamseyCassKoopmans.ODE.Cooperative.snd_le_gap
#print axioms RamseyCassKoopmans.ODE.strict_neg_of_deriv_le_mul
#print axioms RamseyCassKoopmans.ODE.solution_lt_equilibrium
#print axioms RamseyCassKoopmans.ODE.reflected
#print axioms RamseyCassKoopmans.ODE.Cooperative.reflected
#print axioms RamseyCassKoopmans.ODE.lipschitz_reflected
#print axioms RamseyCassKoopmans.ODE.solution_gt_equilibrium
#print axioms RamseyCassKoopmans.ODE.solution_ge_subsolution
#print axioms RamseyCassKoopmans.ODE.linear_lower_bound_on
#print axioms RamseyCassKoopmans.ODE.linear_upper_bound_on
#print axioms RamseyCassKoopmans.ODE.linear_lower_bound
#print axioms RamseyCassKoopmans.ODE.linear_upper_bound
#print axioms RamseyCassKoopmans.ODE.not_bounded_below_of_negative_drift
#print axioms RamseyCassKoopmans.ODE.not_bounded_above_of_positive_drift
#print axioms RamseyCassKoopmans.ODE.derivative_limit_zero
#print axioms RamseyCassKoopmans.ODE.limit_is_equilibrium
#print axioms RamseyCassKoopmans.ODE.exists_limit_of_monotone_bounded
#print axioms RamseyCassKoopmans.ODE.exists_limit_of_antitone_bounded
#print axioms RamseyCassKoopmans.ODE.exponential_lower_bound
#print axioms RamseyCassKoopmans.exists_capacity_of_marginal_tendsto_zero
#print axioms RamseyCassKoopmans.cass_certificate_unique
#print axioms RamseyCassKoopmans.clip
#print axioms RamseyCassKoopmans.clip_mem
#print axioms RamseyCassKoopmans.clip_eq
#print axioms RamseyCassKoopmans.monotone_clip
#print axioms RamseyCassKoopmans.lipschitz_clip
#print axioms RamseyCassKoopmans.strong_decrease_of_deriv_bound
#print axioms RamseyCassKoopmans.exists_compact_demand
#print axioms RamseyCassKoopmans.exists_uniform_negative_deriv
#print axioms RamseyCassKoopmans.exists_compact_demand_of_deriv
#print axioms RamseyCassKoopmans.BoundedLip
#print axioms RamseyCassKoopmans.BoundedLip.const
#print axioms RamseyCassKoopmans.BoundedLip.sub
#print axioms RamseyCassKoopmans.BoundedLip.mul
#print axioms RamseyCassKoopmans.BoundedLip.min_function
#print axioms RamseyCassKoopmans.BoundedLip.max_function
#print axioms RamseyCassKoopmans.BoundedLip.comp
#print axioms RamseyCassKoopmans.BoundedLip.prodMk
#print axioms RamseyCassKoopmans.boundedLip_clip
#print axioms RamseyCassKoopmans.boundedLip_comp_clip
#print axioms RamseyCassKoopmans.ODE.hits
#print axioms RamseyCassKoopmans.ODE.isOpen_hits
#print axioms RamseyCassKoopmans.ODE.disjoint_hits
#print axioms RamseyCassKoopmans.ODE.exists_avoiding_exits
#print axioms RamseyCassKoopmans.ODE.lowerQuadrant
#print axioms RamseyCassKoopmans.ODE.upperQuadrant
#print axioms RamseyCassKoopmans.ODE.isOpen_lowerQuadrant
#print axioms RamseyCassKoopmans.ODE.isOpen_upperQuadrant
#print axioms RamseyCassKoopmans.ODE.disjoint_quadrants
#print axioms RamseyCassKoopmans.ODE.exists_solution_avoiding_quadrants
#print axioms RamseyCassKoopmans.ODE.enters_lower_at_boundary
#print axioms RamseyCassKoopmans.ODE.enters_upper_at_boundary
#print axioms RamseyCassKoopmans.cassConsumption
#print axioms RamseyCassKoopmans.cassInvestment
#print axioms RamseyCassKoopmans.cassField
#print axioms RamseyCassKoopmans.cassExtension
#print axioms RamseyCassKoopmans.cass_consumption_pos
#print axioms RamseyCassKoopmans.cass_investment_nonneg
#print axioms RamseyCassKoopmans.cass_resource
#print axioms RamseyCassKoopmans.marginal_utility_min
#print axioms RamseyCassKoopmans.cass_marginal_utility
#print axioms RamseyCassKoopmans.cass_wedge_and_slack
#print axioms RamseyCassKoopmans.cass_field_costate
#print axioms RamseyCassKoopmans.cass_extension_eq
#print axioms RamseyCassKoopmans.cass_extension_cooperative
#print axioms RamseyCassKoopmans.cass_extension_boundedLip
#print axioms RamseyCassKoopmans.ODE.Avoids
#print axioms RamseyCassKoopmans.ODE.trajectory_shift
#print axioms RamseyCassKoopmans.ODE.avoids_shift
#print axioms RamseyCassKoopmans.ODE.never_reaches_equilibrium
#print axioms RamseyCassKoopmans.ODE.enters_lower_at_first_boundary
#print axioms RamseyCassKoopmans.ODE.enters_upper_at_first_boundary
#print axioms RamseyCassKoopmans.ODE.avoids_first_ne
#print axioms RamseyCassKoopmans.ODE.first_stays_below
#print axioms RamseyCassKoopmans.ODE.first_stays_above
#print axioms RamseyCassKoopmans.ODE.lower_branch_velocity
#print axioms RamseyCassKoopmans.ODE.lower_branch_monotone
#print axioms RamseyCassKoopmans.ODE.upper_branch_velocity
#print axioms RamseyCassKoopmans.ODE.upper_branch_monotone
#print axioms RamseyCassKoopmans.ODE.lower_branch_limit
#print axioms RamseyCassKoopmans.ODE.upper_branch_limit
#print axioms RamseyCassKoopmans.CassPhase
#print axioms RamseyCassKoopmans.CassPhase.mk
#print axioms RamseyCassKoopmans.CassPhase.f
#print axioms RamseyCassKoopmans.CassPhase.mp
#print axioms RamseyCassKoopmans.CassPhase.μ
#print axioms RamseyCassKoopmans.CassPhase.C
#print axioms RamseyCassKoopmans.CassPhase.d
#print axioms RamseyCassKoopmans.CassPhase.m
#print axioms RamseyCassKoopmans.CassPhase.kl
#print axioms RamseyCassKoopmans.CassPhase.ku
#print axioms RamseyCassKoopmans.CassPhase.ks
#print axioms RamseyCassKoopmans.CassPhase.ca
#print axioms RamseyCassKoopmans.CassPhase.cb
#print axioms RamseyCassKoopmans.CassPhase.qs
#print axioms RamseyCassKoopmans.CassPhase.Q
#print axioms RamseyCassKoopmans.CassPhase.d_pos
#print axioms RamseyCassKoopmans.CassPhase.m_pos
#print axioms RamseyCassKoopmans.CassPhase.kl_pos
#print axioms RamseyCassKoopmans.CassPhase.kl_lt
#print axioms RamseyCassKoopmans.CassPhase.ku_gt
#print axioms RamseyCassKoopmans.CassPhase.ca_pos
#print axioms RamseyCassKoopmans.CassPhase.ca_le_cb
#print axioms RamseyCassKoopmans.CassPhase.f_mem
#print axioms RamseyCassKoopmans.CassPhase.f_mono
#print axioms RamseyCassKoopmans.CassPhase.mp_pos
#print axioms RamseyCassKoopmans.CassPhase.mp_anti
#print axioms RamseyCassKoopmans.CassPhase.mp_star
#print axioms RamseyCassKoopmans.CassPhase.μ_pos
#print axioms RamseyCassKoopmans.CassPhase.μ_anti
#print axioms RamseyCassKoopmans.CassPhase.C_mem
#print axioms RamseyCassKoopmans.CassPhase.C_anti
#print axioms RamseyCassKoopmans.CassPhase.inverse
#print axioms RamseyCassKoopmans.CassPhase.Q_eq
#print axioms RamseyCassKoopmans.CassPhase.qs_pos
#print axioms RamseyCassKoopmans.CassPhase.qs_lt
#print axioms RamseyCassKoopmans.CassPhase.ca_lt_surplus
#print axioms RamseyCassKoopmans.CassPhase.qs_eq
#print axioms RamseyCassKoopmans.CassPhase.stock
#print axioms RamseyCassKoopmans.CassPhase.price
#print axioms RamseyCassKoopmans.CassPhase.point
#print axioms RamseyCassKoopmans.CassPhase.field
#print axioms RamseyCassKoopmans.CassPhase.stock_mem
#print axioms RamseyCassKoopmans.CassPhase.price_mem
#print axioms RamseyCassKoopmans.CassPhase.stock_pos
#print axioms RamseyCassKoopmans.CassPhase.output_pos
#print axioms RamseyCassKoopmans.CassPhase.demand_pos
#print axioms RamseyCassKoopmans.CassPhase.marginal
#print axioms RamseyCassKoopmans.CassPhase.cooperative
#print axioms RamseyCassKoopmans.CassPhase.stock_lt_star
#print axioms RamseyCassKoopmans.CassPhase.stock_gt_star
#print axioms RamseyCassKoopmans.CassPhase.stock_ge_star
#print axioms RamseyCassKoopmans.CassPhase.price_ge_star
#print axioms RamseyCassKoopmans.CassPhase.price_mono
#print axioms RamseyCassKoopmans.CassPhase.stock_mono
#print axioms RamseyCassKoopmans.CassPhase.mp_above_target
#print axioms RamseyCassKoopmans.CassPhase.mp_below_target
#print axioms RamseyCassKoopmans.CassPhase.lower_price_drift
#print axioms RamseyCassKoopmans.CassPhase.lower_price_negative
#print axioms RamseyCassKoopmans.CassPhase.interior_price
#print axioms RamseyCassKoopmans.CassPhase.interior_field_price
#print axioms RamseyCassKoopmans.CassPhase.upper_cross
#print axioms RamseyCassKoopmans.CassPhase.investment_mono
#print axioms RamseyCassKoopmans.CassPhase.upper_price_drift
#print axioms RamseyCassKoopmans.CassPhase.upper_corner_drift
#print axioms RamseyCassKoopmans.CassPhase.steady
#print axioms RamseyCassKoopmans.CassPhase.surplus
#print axioms RamseyCassKoopmans.CassPhase.ks_pos
#print axioms RamseyCassKoopmans.CassPhase.surplus_pos
#print axioms RamseyCassKoopmans.CassPhase.surplus_lt_output
#print axioms RamseyCassKoopmans.CassPhase.surplus_lt_cb
#print axioms RamseyCassKoopmans.CassPhase.bottom_price_lt
#print axioms RamseyCassKoopmans.CassPhase.stock_steady
#print axioms RamseyCassKoopmans.CassPhase.price_steady
#print axioms RamseyCassKoopmans.CassPhase.price_lt_steady
#print axioms RamseyCassKoopmans.CassPhase.price_gt_steady
#print axioms RamseyCassKoopmans.CassPhase.inverse_price
#print axioms RamseyCassKoopmans.CassPhase.demand_at_steady
#print axioms RamseyCassKoopmans.CassPhase.demand_gt_surplus
#print axioms RamseyCassKoopmans.CassPhase.demand_lt_surplus
#print axioms RamseyCassKoopmans.CassPhase.field_steady
#print axioms RamseyCassKoopmans.CassPhase.field_first_axis
#print axioms RamseyCassKoopmans.CassPhase.field_zero_unique
#print axioms RamseyCassKoopmans.ODE.coordinate_bounds
#print axioms RamseyCassKoopmans.ODE.exists_low_endpoint
#print axioms RamseyCassKoopmans.ODE.exists_high_endpoint
#print axioms RamseyCassKoopmans.CassPhase.demand_at_zero
#print axioms RamseyCassKoopmans.CassPhase.demand_at_top
#print axioms RamseyCassKoopmans.CassPhase.low_capital_drift
#print axioms RamseyCassKoopmans.CassPhase.high_capital_drift
#print axioms RamseyCassKoopmans.CassPhase.exists_avoiding_solution
#print axioms RamseyCassKoopmans.CassPhase.lower_avoiding_converges
#print axioms RamseyCassKoopmans.CassPhase.upper_avoiding_converges
#print axioms RamseyCassKoopmans.CassPhase.nonpositive_price_velocity
#print axioms RamseyCassKoopmans.CassPhase.upper_clips_inactive
#print axioms RamseyCassKoopmans.CassPhase.lower_exponential_price
#print axioms RamseyCassKoopmans.CassPhase.lower_initial_price_lt_top
#print axioms RamseyCassKoopmans.CassPhase.lower_clips_inactive
#print axioms RamseyCassKoopmans.CassPhase.demand_inverse
#print axioms RamseyCassKoopmans.CassPhase.finite_price_capital_drift
#print axioms RamseyCassKoopmans.CassPhase.exists_convergent_trajectory
#print axioms RamseyCassKoopmans.CassConstructionData
#print axioms RamseyCassKoopmans.CassConstructionData.mk
#print axioms RamseyCassKoopmans.CassConstructionData.phase
#print axioms RamseyCassKoopmans.CassConstructionData.production_eq
#print axioms RamseyCassKoopmans.CassConstructionData.marginalProduct_eq
#print axioms RamseyCassKoopmans.CassConstructionData.marginalUtility_eq
#print axioms RamseyCassKoopmans.CassConstructionData.discount_eq
#print axioms RamseyCassKoopmans.CassConstructionData.dilution_eq
#print axioms RamseyCassKoopmans.CassConstructionData.steady_eq
#print axioms RamseyCassKoopmans.CassConstructionData.bounded
#print axioms RamseyCassKoopmans.CassConstructionData.demand_bounded
#print axioms RamseyCassKoopmans.CassConstructionData.production_bounded
#print axioms RamseyCassKoopmans.CassConstructionData.net_mono
#print axioms RamseyCassKoopmans.CassConstructionData.c
#print axioms RamseyCassKoopmans.CassConstructionData.T
#print axioms RamseyCassKoopmans.CassConstructionData.consumption_mem
#print axioms RamseyCassKoopmans.CassConstructionData.net_gap
#print axioms RamseyCassKoopmans.CassConstructionData.time_nonneg
#print axioms RamseyCassKoopmans.CassConstructionData.price_large
#print axioms RamseyCassKoopmans.CassConstructionData.time_large
#print axioms RamseyCassKoopmans.CassConstructionData.initial_mem
#print axioms RamseyCassKoopmans.exists_cass_finite_data
#print axioms RamseyCassKoopmans.exists_cass_data_of_inada
#print axioms RamseyCassKoopmans.CassPhase.consumption_continuous
#print axioms RamseyCassKoopmans.CassPhase.investment_continuous
#print axioms RamseyCassKoopmans.CassPhase.consumption_mem
#print axioms RamseyCassKoopmans.CassPhase.consumption_steady
#print axioms RamseyCassKoopmans.CassPhase.feasiblePath
#print axioms RamseyCassKoopmans.CassPhase.path_capital_pos
#print axioms RamseyCassKoopmans.CassPhase.path_costate
#print axioms RamseyCassKoopmans.CassPhase.path_wedge_slack
#print axioms RamseyCassKoopmans.CassPhase.consumption_converges
#print axioms RamseyCassKoopmans.exists_hasWelfare_of_abs_bounded
#print axioms RamseyCassKoopmans.exists_hasWelfare_of_compact_consumption
#print axioms RamseyCassKoopmans.CassPhase.positive_investment_of_nondecreasing_capital
#print axioms RamseyCassKoopmans.CassPhase.production_strictMono
#print axioms RamseyCassKoopmans.CassPhase.consumption_lt_of_coordinates
#print axioms RamseyCassKoopmans.CassPhase.consumption_strictMono
#print axioms RamseyCassKoopmans.CassPhase.consumption_strictAnti
#print axioms RamseyCassKoopmans.CassPhase.investment_converges
#print axioms RamseyCassKoopmans.CassPhase.eventually_positive_investment
#print axioms RamseyCassKoopmans.CassPhase.saving_rate_converges
#print axioms RamseyCassKoopmans.AsymptoticallyDominates
#print axioms RamseyCassKoopmans.asymptotic_dominance_of_terminal_limit
#print axioms RamseyCassKoopmans.AsymptoticallyDominates.finite_welfare_le
#print axioms RamseyCassKoopmans.CassPhase.constructed_optimal
#print axioms RamseyCassKoopmans.CassPhase.constructed_unique
#print axioms RamseyCassKoopmans.CassPhase.constructed_dominates
#print axioms RamseyCassKoopmans.CassConstructionData.exists_optimal
#print axioms RamseyCassKoopmans.cass_general_dynamic
#print axioms RamseyCassKoopmans.ODE.exponential_upper_bound_on
#print axioms RamseyCassKoopmans.ODE.tendsto_zero_of_negative_logarithmic_derivative
#print axioms RamseyCassKoopmans.currentHamiltonian
#print axioms RamseyCassKoopmans.hasDerivAt_currentHamiltonian
#print axioms RamseyCassKoopmans.hasDerivAt_discountedHamiltonian
#print axioms RamseyCassKoopmans.hasWelfare_of_primitive
#print axioms RamseyCassKoopmans.KoopmansBoundary.production
#print axioms RamseyCassKoopmans.KoopmansBoundary.marginalProduct
#print axioms RamseyCassKoopmans.KoopmansBoundary.utility
#print axioms RamseyCassKoopmans.KoopmansBoundary.marginalUtility
#print axioms RamseyCassKoopmans.KoopmansBoundary.production_formula
#print axioms RamseyCassKoopmans.KoopmansBoundary.production_deriv
#print axioms RamseyCassKoopmans.KoopmansBoundary.marginalProduct_deriv
#print axioms RamseyCassKoopmans.KoopmansBoundary.utility_deriv
#print axioms RamseyCassKoopmans.KoopmansBoundary.marginalUtility_deriv
#print axioms RamseyCassKoopmans.KoopmansBoundary.deriv_production
#print axioms RamseyCassKoopmans.KoopmansBoundary.deriv_utility
#print axioms RamseyCassKoopmans.KoopmansBoundary.production_continuous
#print axioms RamseyCassKoopmans.KoopmansBoundary.utility_continuous
#print axioms RamseyCassKoopmans.KoopmansBoundary.production_second
#print axioms RamseyCassKoopmans.KoopmansBoundary.utility_second
#print axioms RamseyCassKoopmans.KoopmansBoundary.production_strictConcave
#print axioms RamseyCassKoopmans.KoopmansBoundary.utility_strictConcave
#print axioms RamseyCassKoopmans.KoopmansBoundary.marginalProduct_pos
#print axioms RamseyCassKoopmans.KoopmansBoundary.marginalUtility_pos
#print axioms RamseyCassKoopmans.KoopmansBoundary.production_stationary
#print axioms RamseyCassKoopmans.KoopmansBoundary.capacity_for_each_dilution
#print axioms RamseyCassKoopmans.KoopmansBoundary.displayed_assumptions
#print axioms RamseyCassKoopmans.KoopmansBoundary.marginalProduct_limit
#print axioms RamseyCassKoopmans.KoopmansBoundary.marginalUtility_limit
#print axioms RamseyCassKoopmans.KoopmansBoundary.utility_at_zero
#print axioms RamseyCassKoopmans.KoopmansBoundary.hamiltonian_at_capacity
#print axioms RamseyCassKoopmans.KoopmansBoundary.reciprocal_bound
#print axioms RamseyCassKoopmans.KoopmansBoundary.production_capacity
#print axioms RamseyCassKoopmans.KoopmansBoundary.competitorCapital
#print axioms RamseyCassKoopmans.KoopmansBoundary.competitorConsumption
#print axioms RamseyCassKoopmans.KoopmansBoundary.competitorCapital_ge_one
#print axioms RamseyCassKoopmans.KoopmansBoundary.competitorCapital_deriv
#print axioms RamseyCassKoopmans.KoopmansBoundary.competitorConsumption_bounds
#print axioms RamseyCassKoopmans.KoopmansBoundary.competitorConsumption_continuous
#print axioms RamseyCassKoopmans.KoopmansBoundary.competitor
#print axioms RamseyCassKoopmans.KoopmansBoundary.competitor_initial
#print axioms RamseyCassKoopmans.KoopmansBoundary.competitor_felicity_bounds
#print axioms RamseyCassKoopmans.KoopmansBoundary.competitor_welfare
#print axioms RamseyCassKoopmans.KoopmansBoundary.production_prime_continuous
#print axioms RamseyCassKoopmans.KoopmansBoundary.utility_prime_continuous
#print axioms RamseyCassKoopmans.KoopmansBoundary.production_prime_limit
#print axioms RamseyCassKoopmans.KoopmansBoundary.capital_positive
#print axioms RamseyCassKoopmans.KoopmansBoundary.no_convergent_euler_path
#print axioms RamseyCassKoopmans.CassPrimitives
#print axioms RamseyCassKoopmans.CassPrimitives.mk
#print axioms RamseyCassKoopmans.CassPrimitives.d_pos
#print axioms RamseyCassKoopmans.CassPrimitives.m_pos
#print axioms RamseyCassKoopmans.CassPrimitives.f_conc
#print axioms RamseyCassKoopmans.CassPrimitives.f_zero
#print axioms RamseyCassKoopmans.CassPrimitives.f_diff
#print axioms RamseyCassKoopmans.CassPrimitives.f_prime_cont
#print axioms RamseyCassKoopmans.CassPrimitives.f_prime_pos
#print axioms RamseyCassKoopmans.CassPrimitives.f_second
#print axioms RamseyCassKoopmans.CassPrimitives.f_second_cont
#print axioms RamseyCassKoopmans.CassPrimitives.f_inada0
#print axioms RamseyCassKoopmans.CassPrimitives.f_inadaTop
#print axioms RamseyCassKoopmans.CassPrimitives.U_conc
#print axioms RamseyCassKoopmans.CassPrimitives.U_diff
#print axioms RamseyCassKoopmans.CassPrimitives.U_prime_pos
#print axioms RamseyCassKoopmans.CassPrimitives.U_second
#print axioms RamseyCassKoopmans.CassPrimitives.U_second_cont
#print axioms RamseyCassKoopmans.CassPrimitives.U_second_neg
#print axioms RamseyCassKoopmans.CassPrimitives.U_inada0
#print axioms RamseyCassKoopmans.CassPrimitives.U_cont
#print axioms RamseyCassKoopmans.CassPrimitives.U_prime_cont
#print axioms RamseyCassKoopmans.CassPrimitives.existsUnique_steady
#print axioms RamseyCassKoopmans.cassSteady
#print axioms RamseyCassKoopmans.cassSteady_spec
#print axioms RamseyCassKoopmans.cassSteady_eq
#print axioms RamseyCassKoopmans.CassPrimitives.exists_capacity
#print axioms RamseyCassKoopmans.CassCertificate
#print axioms RamseyCassKoopmans.CassCertificate.mk
#print axioms RamseyCassKoopmans.CassCertificate.capital_pos
#print axioms RamseyCassKoopmans.CassCertificate.investment_nonneg
#print axioms RamseyCassKoopmans.CassCertificate.price_nonneg
#print axioms RamseyCassKoopmans.CassCertificate.costate
#print axioms RamseyCassKoopmans.CassCertificate.wedge
#print axioms RamseyCassKoopmans.CassCertificate.slack
#print axioms RamseyCassKoopmans.CassCertificate.transversality
#print axioms RamseyCassKoopmans.CassCertificate.welfare
#print axioms RamseyCassKoopmans.exists_certified
#print axioms RamseyCassKoopmans.CassCertificate.isCassOptimal
#print axioms RamseyCassKoopmans.CassCertificate.eq_of_isCassOptimal
#print axioms RamseyCassKoopmans.CassCertificate.eq
#print axioms RamseyCassKoopmans.FeasiblePath.shift
#print axioms RamseyCassKoopmans.FeasiblePath.shift_capital
#print axioms RamseyCassKoopmans.FeasiblePath.shift_consumption
#print axioms RamseyCassKoopmans.FeasiblePath.shift_investment
#print axioms RamseyCassKoopmans.hasWelfare_shift
#print axioms RamseyCassKoopmans.CassCertificate.shift
#print axioms RamseyCassKoopmans.CassCertificate.dynamics
#print axioms RamseyCassKoopmans.CassCertificate.capital_bounds
#print axioms RamseyCassKoopmans.cassSteadyConsumption
#print axioms RamseyCassKoopmans.optimalPath
#print axioms RamseyCassKoopmans.optimalPath_spec
#print axioms RamseyCassKoopmans.policy
#print axioms RamseyCassKoopmans.consumption_eq_policy
#print axioms RamseyCassKoopmans.tail_eq_optimalPath
#print axioms RamseyCassKoopmans.policy_steady
#print axioms RamseyCassKoopmans.exists_hit_of_lt
#print axioms RamseyCassKoopmans.exists_hit_of_gt
#print axioms RamseyCassKoopmans.exists_shift_of_between
#print axioms RamseyCassKoopmans.capital_lt_of_lt
#print axioms RamseyCassKoopmans.policy_strictMono
#print axioms RamseyCassKoopmans.consumption_lt_of_lt
#print axioms RamseyCassKoopmans.absolute_convergence
#print axioms RamseyCassKoopmans.hasDerivAt_of_comp_eq
#print axioms RamseyCassKoopmans.tendsto_div_of_deriv_tendsto
#print axioms RamseyCassKoopmans.riccati_algebra
#print axioms RamseyCassKoopmans.riccati_tendsto
#print axioms RamseyCassKoopmans.cassCurvature
#print axioms RamseyCassKoopmans.cassSpeed
#print axioms RamseyCassKoopmans.cassSteadyConsumption_pos
#print axioms RamseyCassKoopmans.cassCurvature_pos
#print axioms RamseyCassKoopmans.cassSpeed_pos
#print axioms RamseyCassKoopmans.stable_root_eq
#print axioms RamseyCassKoopmans.CassCertificate.eventually_positive_investment
#print axioms RamseyCassKoopmans.FeasiblePath.hasDerivAt_capital'
#print axioms RamseyCassKoopmans.CassCertificate.gap_sign
#print axioms RamseyCassKoopmans.CassCertificate.hasDerivAt_consumption
#print axioms RamseyCassKoopmans.slope_tendsto
#print axioms RamseyCassKoopmans.speed_tendsto
#print axioms RamseyCassKoopmans.capital_rate
#print axioms RamseyCassKoopmans.consumption_rate
#print axioms RamseyCassKoopmans.policy_hasDerivAt
#print axioms RamseyCassKoopmans.CassPrimitives.existsUnique_marginal
#print axioms RamseyCassKoopmans.marginalInverse
#print axioms RamseyCassKoopmans.marginalInverse_spec
#print axioms RamseyCassKoopmans.marginalInverse_eq
#print axioms RamseyCassKoopmans.marginalInverse_deriv
#print axioms RamseyCassKoopmans.cassSteady_eq_marginalInverse
#print axioms RamseyCassKoopmans.marginalInverse_strictAnti
#print axioms RamseyCassKoopmans.marginalInverse_hasDerivAt
#print axioms RamseyCassKoopmans.steady_hasDerivAt_discount
#print axioms RamseyCassKoopmans.steady_hasDerivAt_dilution
#print axioms RamseyCassKoopmans.steadyConsumption_hasDerivAt_discount
#print axioms RamseyCassKoopmans.steadyConsumption_hasDerivAt_dilution
#print axioms RamseyCassKoopmans.steady_strictAnti_discount
#print axioms RamseyCassKoopmans.steady_strictAnti_dilution'
#print axioms RamseyCassKoopmans.steady_productivity
#print axioms RamseyCassKoopmans.steady_strictMono_productivity
#print axioms RamseyCassKoopmans.gap_exp_hasDerivAt
#print axioms RamseyCassKoopmans.patience_rise
#print axioms RamseyCassKoopmans.impatience_rise
#print axioms RamseyCassKoopmans.exists_pos_bounds
#print axioms RamseyCassKoopmans.CassPrimitives.f_cont
#print axioms RamseyCassKoopmans.CassPrimitives.f_strictMono
#print axioms RamseyCassKoopmans.CassPrimitives.U_strictMono
#print axioms RamseyCassKoopmans.CassPrimitives.exists_welfare
#print axioms RamseyCassKoopmans.optimalPath_welfare
#print axioms RamseyCassKoopmans.value
#print axioms RamseyCassKoopmans.value_spec
#print axioms RamseyCassKoopmans.value_ge
#print axioms RamseyCassKoopmans.value_eq
#print axioms RamseyCassKoopmans.finite_horizon_comparison'
#print axioms RamseyCassKoopmans.value_le_supergradient
#print axioms RamseyCassKoopmans.FeasiblePath.mimic
#print axioms RamseyCassKoopmans.value_strictMono
#print axioms RamseyCassKoopmans.FeasiblePath.mix
#print axioms RamseyCassKoopmans.value_strictConcave
#print axioms RamseyCassKoopmans.clausen_strub_sandwich
#print axioms RamseyCassKoopmans.mimicConsumption
#print axioms RamseyCassKoopmans.integral_exp_neg_le
#print axioms RamseyCassKoopmans.value_hasDerivAt
#print axioms RamseyCassKoopmans.value_deriv_eq_marginal_utility
#print axioms RamseyCassKoopmans.HouseholdPlan
#print axioms RamseyCassKoopmans.HouseholdPlan.mk
#print axioms RamseyCassKoopmans.HouseholdPlan.capital
#print axioms RamseyCassKoopmans.HouseholdPlan.consumption
#print axioms RamseyCassKoopmans.HouseholdPlan.investment
#print axioms RamseyCassKoopmans.HouseholdPlan.capital_nonneg
#print axioms RamseyCassKoopmans.HouseholdPlan.consumption_pos
#print axioms RamseyCassKoopmans.HouseholdPlan.consumption_continuous
#print axioms RamseyCassKoopmans.HouseholdPlan.investment_continuous
#print axioms RamseyCassKoopmans.HouseholdPlan.investment_nonneg
#print axioms RamseyCassKoopmans.HouseholdPlan.budget
#print axioms RamseyCassKoopmans.HouseholdPlan.dynamics
#print axioms RamseyCassKoopmans.CompetitiveEquilibrium
#print axioms RamseyCassKoopmans.CompetitiveEquilibrium.mk
#print axioms RamseyCassKoopmans.CompetitiveEquilibrium.capital_pos
#print axioms RamseyCassKoopmans.CompetitiveEquilibrium.rental
#print axioms RamseyCassKoopmans.CompetitiveEquilibrium.wage
#print axioms RamseyCassKoopmans.CompetitiveEquilibrium.investment_nonneg
#print axioms RamseyCassKoopmans.CompetitiveEquilibrium.welfare
#print axioms RamseyCassKoopmans.CompetitiveEquilibrium.household_optimal
#print axioms RamseyCassKoopmans.firm_optimal
#print axioms RamseyCassKoopmans.second_welfare_theorem
#print axioms RamseyCassKoopmans.first_welfare_theorem
#print axioms RamseyCassKoopmans.equilibrium_eq_optimum
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.mk
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.β_pos
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.β_lt_one
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.δ_pos
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.δ_le_one
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.f_cont
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.f_zero
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.f_conc
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.f_diff
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.f_prime_pos
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.f_prime_cont
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.f_inada0
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.f_inadaTop
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.u_cont
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.u_conc
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.u_diff
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.u_prime_pos
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.u_prime_cont
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.u_inada0
#print axioms RamseyCassKoopmans.DiscreteTime.resources
#print axioms RamseyCassKoopmans.DiscreteTime.Feasible
#print axioms RamseyCassKoopmans.DiscreteTime.consumption
#print axioms RamseyCassKoopmans.DiscreteTime.welfare
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.f_strictMono
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.u_strictMono
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.resources_strictMono
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.resources_cont
#print axioms RamseyCassKoopmans.DiscreteTime.resources_zero
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.resources_nonneg
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.exists_capacity
#print axioms RamseyCassKoopmans.DiscreteTime.bound
#print axioms RamseyCassKoopmans.DiscreteTime.bound_spec
#print axioms RamseyCassKoopmans.DiscreteTime.Feasible.nonneg
#print axioms RamseyCassKoopmans.DiscreteTime.Feasible.le_bound
#print axioms RamseyCassKoopmans.DiscreteTime.Feasible.consumption_mem
#print axioms RamseyCassKoopmans.DiscreteTime.exists_utility_bound
#print axioms RamseyCassKoopmans.DiscreteTime.Feasible.summable
#print axioms RamseyCassKoopmans.DiscreteTime.feasible_consume_all
#print axioms RamseyCassKoopmans.DiscreteTime.feasibleSet
#print axioms RamseyCassKoopmans.DiscreteTime.isCompact_feasibleSet
#print axioms RamseyCassKoopmans.DiscreteTime.continuousOn_welfare
#print axioms RamseyCassKoopmans.DiscreteTime.exists_optimal
#print axioms RamseyCassKoopmans.DiscreteTime.optimalPath
#print axioms RamseyCassKoopmans.DiscreteTime.optimalPath_spec
#print axioms RamseyCassKoopmans.DiscreteTime.value
#print axioms RamseyCassKoopmans.DiscreteTime.value_eq
#print axioms RamseyCassKoopmans.DiscreteTime.welfare_le_value
#print axioms RamseyCassKoopmans.DiscreteTime.tail
#print axioms RamseyCassKoopmans.DiscreteTime.prepend
#print axioms RamseyCassKoopmans.DiscreteTime.Feasible.tail
#print axioms RamseyCassKoopmans.DiscreteTime.Feasible.prepend
#print axioms RamseyCassKoopmans.DiscreteTime.consumption_tail
#print axioms RamseyCassKoopmans.DiscreteTime.welfare_eq_head_add
#print axioms RamseyCassKoopmans.DiscreteTime.consumption_prepend_zero
#print axioms RamseyCassKoopmans.DiscreteTime.tail_prepend
#print axioms RamseyCassKoopmans.DiscreteTime.welfare_prepend
#print axioms RamseyCassKoopmans.DiscreteTime.tail_optimal
#print axioms RamseyCassKoopmans.DiscreteTime.bellman
#print axioms RamseyCassKoopmans.DiscreteTime.resources_mix
#print axioms RamseyCassKoopmans.DiscreteTime.Feasible.mix
#print axioms RamseyCassKoopmans.DiscreteTime.utility_mix
#print axioms RamseyCassKoopmans.DiscreteTime.welfare_mix
#print axioms RamseyCassKoopmans.DiscreteTime.optimal_unique
#print axioms RamseyCassKoopmans.DiscreteTime.value_strictMono
#print axioms RamseyCassKoopmans.DiscreteTime.value_strictConcave
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal
#print axioms RamseyCassKoopmans.DiscreteTime.isOptimal_optimalPath
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.welfare_eq
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.tail
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.shift
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.bellman_eq
#print axioms RamseyCassKoopmans.DiscreteTime.value_zero
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.u_prime_anti
#print axioms RamseyCassKoopmans.DiscreteTime.interior_choice
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.resources_pos
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.interior
#print axioms RamseyCassKoopmans.DiscreteTime.hasDerivAt_resources
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.euler
#print axioms RamseyCassKoopmans.DiscreteTime.shift_increment_lt
#print axioms RamseyCassKoopmans.DiscreteTime.policy
#print axioms RamseyCassKoopmans.DiscreteTime.policy_eq
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.succ_eq_policy
#print axioms RamseyCassKoopmans.DiscreteTime.bellman_policy
#print axioms RamseyCassKoopmans.DiscreteTime.policy_interior
#print axioms RamseyCassKoopmans.DiscreteTime.policy_strictMono
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.target_pos
#print axioms RamseyCassKoopmans.DiscreteTime.Primitives.existsUnique_steady
#print axioms RamseyCassKoopmans.DiscreteTime.steady
#print axioms RamseyCassKoopmans.DiscreteTime.steady_spec
#print axioms RamseyCassKoopmans.DiscreteTime.steady_euler
#print axioms RamseyCassKoopmans.DiscreteTime.steady_consumption_pos
#print axioms RamseyCassKoopmans.DiscreteTime.hasDerivAt_resources_pos
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.monotone_or_antitone
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.tendsto
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.consumption_tendsto
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.dynamics_below
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.dynamics_above
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.capital_lt
#print axioms RamseyCassKoopmans.DiscreteTime.consumptionPolicy
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.consumption_eq
#print axioms RamseyCassKoopmans.DiscreteTime.consumptionPolicy_strictMono
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.consumption_lt
#print axioms RamseyCassKoopmans.DiscreteTime.IsOptimal.absolute_convergence
#print axioms RamseyCassKoopmans.DiscreteTime.concave_le_tangent_of_lower_support
#print axioms RamseyCassKoopmans.DiscreteTime.value_hasDerivAt
#print axioms RamseyCassKoopmans.DiscreteTime.steady_strictMono_patience
#print axioms RamseyCassKoopmans.DiscreteTime.steady_strictAnti_depreciation
