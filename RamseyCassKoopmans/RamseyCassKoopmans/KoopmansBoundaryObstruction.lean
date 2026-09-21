import RamseyCassKoopmans.KoopmansBoundaryCompetitor
import RamseyCassKoopmans.PairBarrier
import RamseyCassKoopmans.ExponentialDecay

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
