import RamseyCassKoopmans.CornerOptimality
import Mathlib.Analysis.Calculus.Deriv.MeanValue

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
