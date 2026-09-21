import RamseyCassKoopmans.StationaryPath
import RamseyCassKoopmans.Verification
import RamseyCassKoopmans.Concavity
import RamseyCassKoopmans.Stationary

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
