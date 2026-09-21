import RamseyCassKoopmans.KoopmansBoundaryEconomy

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
