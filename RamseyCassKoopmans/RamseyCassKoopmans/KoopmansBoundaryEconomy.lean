import RamseyCassKoopmans.Hamiltonian
import RamseyCassKoopmans.SignedWelfare
import Mathlib.Analysis.Convex.Deriv

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
