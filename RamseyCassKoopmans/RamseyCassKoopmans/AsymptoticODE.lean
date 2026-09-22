import RamseyCassKoopmans.CooperativeFlow
import Mathlib.Topology.Order.MonotoneConvergence

/-! # Drift bounds and limits of autonomous trajectories -/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.ODE

theorem linear_lower_bound_on {f df : ℝ → ℝ} {A T c : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hAT : A ≤ T)
    (hb : ∀ t ∈ Icc A T, c ≤ df t) : c * (T - A) ≤ f T - f A := by
  exact (convex_Icc A T).mul_sub_le_image_sub_of_le_deriv
    (HasDerivAt.continuousOn (fun t _ => hf t))
    (fun t _ => (hf t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hf t).deriv]; exact hb t (interior_subset ht))
    A ⟨le_rfl, hAT⟩ T ⟨hAT, le_rfl⟩ hAT

theorem linear_upper_bound_on {f df : ℝ → ℝ} {A T c : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hAT : A ≤ T)
    (hb : ∀ t ∈ Icc A T, df t ≤ c) : f T - f A ≤ c * (T - A) := by
  have h := linear_lower_bound_on (fun t => (hf t).neg) hAT
    (c := -c) (fun t ht => neg_le_neg (hb t ht))
  change -c * (T - A) ≤ -f T - -f A at h
  linarith

theorem linear_lower_bound {f df : ℝ → ℝ} {A T c : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hAT : A ≤ T)
    (hb : ∀ t, A ≤ t → c ≤ df t) : c * (T - A) ≤ f T - f A := by
  apply (convex_Ici A).mul_sub_le_image_sub_of_le_deriv
    (HasDerivAt.continuousOn (fun t _ => hf t))
    (fun t _ => (hf t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hf t).deriv]; exact hb t (interior_subset ht))
    A (mem_Ici.mpr le_rfl) T (mem_Ici.mpr hAT) hAT

theorem linear_upper_bound {f df : ℝ → ℝ} {A T c : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hAT : A ≤ T)
    (hb : ∀ t, A ≤ t → df t ≤ c) : f T - f A ≤ c * (T - A) := by
  have h := linear_lower_bound (fun t => (hf t).neg) hAT
    (c := -c) (fun t ht => neg_le_neg (hb t ht))
  change -c * (T - A) ≤ -f T - -f A at h
  linarith

theorem not_bounded_below_of_negative_drift {f df : ℝ → ℝ} {ε B : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hε : 0 < ε)
    (hd : ∀ t, 0 ≤ t → df t ≤ -ε)
    (hb : ∀ t, 0 ≤ t → B ≤ f t) : False := by
  let T := max 0 ((f 0 - B + 1) / ε)
  have hT : 0 ≤ T := le_max_left _ _
  have htime : f 0 - B + 1 ≤ ε * T := by
    have h := le_max_right 0 ((f 0 - B + 1) / ε)
    exact (div_le_iff₀ hε).mp h |>.trans_eq (mul_comm _ _)
  have hbound := linear_upper_bound hf hT hd
  have hbelow := hb T hT
  simp only [sub_zero] at hbound
  nlinarith

theorem not_bounded_above_of_positive_drift {f df : ℝ → ℝ} {ε B : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hε : 0 < ε)
    (hd : ∀ t, 0 ≤ t → ε ≤ df t)
    (hb : ∀ t, 0 ≤ t → f t ≤ B) : False :=
  not_bounded_below_of_negative_drift (fun t => (hf t).neg) hε
    (fun t ht => neg_le_neg (hd t ht)) (fun t ht => neg_le_neg (hb t ht))

/-- A convergent differentiable function cannot have a nonzero limiting
derivative. The proof uses an eventual uniform drift bound and the mean value
theorem, rather than exchanging a derivative and a limit. -/
theorem derivative_limit_zero {f df : ℝ → ℝ} {l v : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t)
    (hlim : Tendsto f atTop (𝓝 l)) (hdlim : Tendsto df atTop (𝓝 v)) : v = 0 := by
  have hposImpossible : ∀ {f df : ℝ → ℝ} {l v : ℝ},
      (∀ t, HasDerivAt f (df t) t) → Tendsto f atTop (𝓝 l) →
      Tendsto df atTop (𝓝 v) → 0 < v → False := by
    intro f df l v hf hl hd hv
    obtain ⟨A, hA⟩ := eventually_atTop.mp
      ((hl.eventually (gt_mem_nhds (show l < l + 1 by linarith))).and
        (hd.eventually (lt_mem_nhds (show v / 2 < v by linarith))))
    have hs : ∀ t, HasDerivAt (fun u => f (u + A)) (df (t + A)) t := by
      intro t
      convert (hf (t + A)).comp t ((hasDerivAt_id t).add_const A) using 1
      · rfl
      · ring
    exact not_bounded_above_of_positive_drift hs (show 0 < v / 2 by linarith)
      (fun t ht => (hA (t + A) (by linarith)).2.le)
      (fun t ht => (hA (t + A) (by linarith)).1.le)
  rcases lt_trichotomy v 0 with hv | hv | hv
  · exact False.elim (hposImpossible (fun t => (hf t).neg) hlim.neg hdlim.neg (neg_pos.mpr hv))
  · exact hv
  · exact False.elim (hposImpossible hf hlim hdlim hv)

theorem limit_is_equilibrium {v : ℝ × ℝ → ℝ × ℝ} (hc : Continuous v)
    {γ : ℝ → ℝ × ℝ} {a : ℝ × ℝ}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (ha : Tendsto γ atTop (𝓝 a)) : v a = 0 := by
  have hv := hc.continuousAt.tendsto.comp ha
  apply Prod.ext
  · exact derivative_limit_zero (fun t => hasDerivAt_fst (hγ t))
      (continuous_fst.tendsto a |>.comp ha) (continuous_fst.tendsto (v a) |>.comp hv)
  · exact derivative_limit_zero (fun t => hasDerivAt_snd (hγ t))
      (continuous_snd.tendsto a |>.comp ha) (continuous_snd.tendsto (v a) |>.comp hv)

theorem exists_limit_of_monotone_bounded {f : ℝ → ℝ} {B : ℝ}
    (hm : MonotoneOn f (Ici 0)) (hb : ∀ t, 0 ≤ t → f t ≤ B) :
    ∃ l, Tendsto f atTop (𝓝 l) := by
  let g := fun t => f (max 0 t)
  have hmono : Monotone g := fun s t hst =>
    hm (mem_Ici.mpr (le_max_left _ _)) (mem_Ici.mpr (le_max_left _ _))
      (max_le_max_left _ hst)
  have hbound : BddAbove (range g) := ⟨B, by
    rintro _ ⟨t, rfl⟩
    exact hb _ (le_max_left _ _)⟩
  refine ⟨⨆ t, g t, (tendsto_atTop_ciSup hmono hbound).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact congrArg f (max_eq_right ht)

theorem exists_limit_of_antitone_bounded {f : ℝ → ℝ} {B : ℝ}
    (hm : AntitoneOn f (Ici 0)) (hb : ∀ t, 0 ≤ t → B ≤ f t) :
    ∃ l, Tendsto f atTop (𝓝 l) := by
  obtain ⟨l, hl⟩ := exists_limit_of_monotone_bounded
    (f := fun t => -f t) (fun _ hx _ hy hxy => neg_le_neg (hm hx hy hxy))
    (fun t ht => neg_le_neg (hb t ht))
  exact ⟨-l, by simpa only [neg_neg] using hl.neg⟩

theorem exponential_lower_bound {f df : ℝ → ℝ} {A : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t)
    (hb : ∀ t, 0 ≤ t → -A * f t ≤ df t) :
    ∀ T, 0 ≤ T → f 0 * Real.exp (-A * T) ≤ f T := by
  intro T hT
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (a := 0) (b := T) (δ := -f 0) (K := -A) (ε := 0)
    (HasDerivAt.continuousOn (fun t _ => (hf t).neg))
    (fun t _ r hr => by
      simpa only [slope_def_field, div_eq_mul_inv, mul_comm] using
        ((hf t).neg).hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl (fun t ht => by
      have hh := hb t ht.1
      change -df t ≤ -A * -f t + 0
      linarith) T ⟨hT, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at h
  change -f T ≤ -f 0 * Real.exp (-A * T) at h
  nlinarith

end RamseyCassKoopmans.ODE
