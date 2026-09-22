import RamseyCassKoopmans.Cass
import RamseyCassKoopmans.Examples
import RamseyCassKoopmans.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Inv

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
