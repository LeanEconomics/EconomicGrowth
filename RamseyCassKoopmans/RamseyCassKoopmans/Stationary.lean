import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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
