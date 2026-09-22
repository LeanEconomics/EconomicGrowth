import RamseyCassKoopmans.Model
import Mathlib.Topology.Order.OrderClosed

/-! # Joining economic regimes at a switching time
Original work under the Unlicense. Values and derivatives must agree at the
switch; the result does not silently assume differentiability of a branch join.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

noncomputable def joinAt (τ : ℝ) (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ τ then f t else g t

theorem joinAt_left {τ t : ℝ} (f g : ℝ → ℝ) (ht : t ≤ τ) :
    joinAt τ f g t = f t := ite_eq_left ht

theorem joinAt_right {τ t : ℝ} (f g : ℝ → ℝ) (ht : τ < t) :
    joinAt τ f g t = g t := ite_eq_right (not_le.mpr ht)

theorem continuous_joinAt {τ : ℝ} {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hmatch : f τ = g τ) :
    Continuous (joinAt τ f g) := by
  apply hf.if_le hg continuous_id continuous_const
  intro t ht
  change t = τ at ht
  subst t
  exact hmatch

theorem hasDerivAt_joinAt_switch {τ v : ℝ} {f g : ℝ → ℝ}
    (hf : HasDerivAt f v τ) (hg : HasDerivAt g v τ) (hmatch : f τ = g τ) :
    HasDerivAt (joinAt τ f g) v τ := by
  have hleft : HasDerivWithinAt (joinAt τ f g) v (Iic τ) τ :=
    hf.hasDerivWithinAt.congr (fun t ht => ite_eq_left ht) (ite_eq_left le_rfl)
  have hright : HasDerivWithinAt (joinAt τ f g) v (Ici τ) τ := by
    apply hg.hasDerivWithinAt.congr
    · intro t ht
      rcases eq_or_lt_of_le (show τ ≤ t from ht) with heq | hlt
      · subst t
        exact (ite_eq_left le_rfl).trans hmatch
      · exact ite_eq_right (not_le.mpr hlt)
    · exact (ite_eq_left le_rfl).trans hmatch
  have h := hleft.union hright
  rw [Iic_union_Ici] at h
  exact h.hasDerivAt Filter.univ_mem

theorem hasDerivAt_joinAt {τ t vf vg : ℝ} {f g : ℝ → ℝ}
    (hf : HasDerivAt f vf t) (hg : HasDerivAt g vg t)
    (hmatch : f τ = g τ) (hderiv : t = τ → vf = vg) :
    HasDerivAt (joinAt τ f g) (if t ≤ τ then vf else vg) t := by
  rcases lt_trichotomy t τ with hlt | heq | hgt
  · rw [ite_eq_left hlt.le]
    apply hf.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hlt] with s hs
    exact ite_eq_left hs.le
  · subst t
    rw [ite_eq_left le_rfl]
    exact hasDerivAt_joinAt_switch hf (hg.congr_deriv (hderiv rfl).symm) hmatch
  · rw [ite_eq_right (not_le.mpr hgt)]
    apply hg.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hgt] with s hs
    exact ite_eq_right (not_le.mpr hs)

theorem strictAnti_joinAt {τ : ℝ} {f g : ℝ → ℝ}
    (hf : StrictAnti f) (hg : StrictAnti g) (hmatch : f τ = g τ) :
    StrictAnti (joinAt τ f g) := by
  intro s t hst
  by_cases ht : t ≤ τ
  · rw [joinAt_left f g ht, joinAt_left f g (hst.le.trans ht)]
    exact hf hst
  · rw [joinAt_right f g (lt_of_not_ge ht)]
    by_cases hs : s ≤ τ
    · rw [joinAt_left f g hs]
      calc
        g t < g τ := hg (lt_of_not_ge ht)
        _ = f τ := hmatch.symm
        _ ≤ f s := hf.antitone hs
    · rw [joinAt_right f g (lt_of_not_ge hs)]
      exact hg hst

theorem tendsto_joinAt_atTop {τ L : ℝ} {f g : ℝ → ℝ}
    (hg : Tendsto g atTop (𝓝 L)) : Tendsto (joinAt τ f g) atTop (𝓝 L) := by
  apply hg.congr'
  filter_upwards [eventually_gt_atTop τ] with t ht
  exact (joinAt_right f g ht).symm

end RamseyCassKoopmans
