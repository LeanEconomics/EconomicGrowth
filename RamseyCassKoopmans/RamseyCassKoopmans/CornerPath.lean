import RamseyCassKoopmans.CornerDynamics

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
  norm_num [preCapital, R, capital, state, discount]

theorem consumption_match (τ : ℝ) : preConsumption τ τ = consumption (2 / 3) (τ - τ) := by
  norm_num [preConsumption, R, consumption, state, discount]

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
  · exact continuous_const.mul ((R_continuous τ).pow 2)
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
    · simp only [joinedConsumption, joinedInvestment, joinedCapital, joinAt, ite_eq_left ht, add_zero]
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
