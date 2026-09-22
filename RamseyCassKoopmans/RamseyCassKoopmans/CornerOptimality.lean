import RamseyCassKoopmans.CornerPath
import RamseyCassKoopmans.TailWelfare

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
