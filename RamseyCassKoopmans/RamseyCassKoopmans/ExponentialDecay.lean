import RamseyCassKoopmans.AsymptoticODE
import RamseyCassKoopmans.Terminal

/-! # Price decay from an eventually negative logarithmic derivative -/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.ODE

theorem exponential_upper_bound_on {f df : ℝ → ℝ} {A T K : ℝ} (hAT : A ≤ T)
    (hf : ∀ t ∈ Icc A T, HasDerivAt f (df t) t)
    (hb : ∀ t ∈ Icc A T, df t ≤ K * f t) :
    f T ≤ f A * Real.exp (K * (T - A)) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (a := A) (b := T) (δ := f A) (K := K) (ε := 0)
    (HasDerivAt.continuousOn hf)
    (fun t ht r hr => by
      simpa only [slope_def_field, div_eq_mul_inv, mul_comm] using
        ((hf t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt).liminf_right_slope_le hr)
    le_rfl (fun t ht => by simpa using hb t ⟨ht.1, ht.2.le⟩) T ⟨hAT, le_rfl⟩
  rwa [gronwallBound_ε0] at h

theorem tendsto_zero_of_negative_logarithmic_derivative {f a : ℝ → ℝ} {L : ℝ}
    (hf : ∀ t, 0 ≤ t → HasDerivAt f (a t * f t) t)
    (hn : ∀ t, 0 ≤ t → 0 ≤ f t) (ha : Tendsto a atTop (𝓝 L)) (hL : L < 0) :
    Tendsto f atTop (𝓝 0) := by
  obtain ⟨A, hA⟩ := eventually_atTop.mp (ha.eventually (gt_mem_nhds (show L < L / 2 by linarith)))
  let B := max 0 A
  have hB : 0 ≤ B := le_max_left _ _
  have hbound : ∀ T, B ≤ T → f T ≤ f B * Real.exp ((L / 2) * (T - B)) := by
    intro T hT
    apply exponential_upper_bound_on hT (fun t ht => hf t (hB.trans ht.1))
    intro t ht
    exact mul_le_mul_of_nonneg_right (hA t ((le_max_right _ _).trans ht.1)).le
      (hn t (hB.trans ht.1))
  have hl : Tendsto (fun T => f B * Real.exp ((L / 2) * (T - B))) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      ((tendsto_atTop_add_const_right atTop (-B) tendsto_id).const_mul_atTop_of_neg
        (show L / 2 < 0 by linarith))
    simpa only [sub_eq_add_neg, mul_zero, Function.comp_def, id_eq] using he.const_mul (f B)
  apply squeeze_zero'
    ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht => hn t ht))
    ((eventually_ge_atTop B).mono (fun t ht => hbound t ht)) hl

end RamseyCassKoopmans.ODE
