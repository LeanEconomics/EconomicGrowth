import RamseyCassKoopmans.Cass
import RamseyCassKoopmans.StationaryOptimality

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
