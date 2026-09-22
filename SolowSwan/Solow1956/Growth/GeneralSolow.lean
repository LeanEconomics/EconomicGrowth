/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/
import Solow1956.Growth.Neoclassical
import Solow1956.Analysis.ScalarFlow
import Mathlib.Topology.Order.Lattice

/-! # Acemoglu's general continuous-time Solow dynamics -/

open Set Filter Topology
open scoped NNReal

namespace Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- Nonnegative solutions from positive initial capital stay strictly positive.
The inequality follows from nonnegative gross investment and an integrating
factor; local Lipschitz continuity at zero is not assumed. -/
theorem capital_lower_bound (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k : ℝ → ℝ} (hk : ∀ t, 0 ≤ t → 0 ≤ k t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt k (rate f s m (k t)) t)
    {t : ℝ} (ht : 0 ≤ t) : k 0 * Real.exp (-m * t) ≤ k t := by
  have hg := le_gronwallBound_of_liminf_deriv_right_le
    (a := 0) (b := t) (δ := -k 0) (K := -m) (ε := 0)
    (HasDerivAt.continuousOn (fun u hu => (hd u hu.1).neg))
    (fun u hu r hr => by
      simpa only [slope_def_field, div_eq_mul_inv, mul_comm] using
        (hd u hu.1).neg.hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl (fun u hu => by
      have hgross := mul_nonneg hs (h.output_nonneg (hk u hu.1))
      change -rate f s m (k u) ≤ -m * -k u + 0
      dsimp [rate]; linarith) t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at hg
  change -k t ≤ -k 0 * Real.exp (-m * t) at hg
  nlinarith

theorem capital_positive (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k : ℝ → ℝ} (h0 : 0 < k 0) (hk : ∀ t, 0 ≤ t → 0 ≤ k t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt k (rate f s m (k t)) t)
    {t : ℝ} (ht : 0 ≤ t) : 0 < k t :=
  (mul_pos h0 (Real.exp_pos _)).trans_le (capital_lower_bound h hs hk hd ht)

/-- Uniqueness holds among all nonnegative classical future solutions. -/
theorem path_unique (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k l : ℝ → ℝ} (h0 : 0 < k 0) (heq : k 0 = l 0)
    (hk : ∀ t, 0 ≤ t → 0 ≤ k t) (hl : ∀ t, 0 ≤ t → 0 ≤ l t)
    (hkd : ∀ t, 0 ≤ t → HasDerivAt k (rate f s m (k t)) t)
    (hld : ∀ t, 0 ≤ t → HasDerivAt l (rate f s m (l t)) t) :
    EqOn k l (Ici 0) := by
  intro T hT
  change 0 ≤ T at hT
  have hkp : ∀ t, 0 ≤ t → 0 < k t := fun t ht => capital_positive h hs h0 hk hkd ht
  have hlp : ∀ t, 0 ≤ t → 0 < l t := fun t ht =>
    capital_positive h hs (heq ▸ h0) hl hld ht
  have hkc : ContinuousOn k (Icc 0 T) := HasDerivAt.continuousOn (fun t ht => hkd t ht.1)
  have hlc : ContinuousOn l (Icc 0 T) := HasDerivAt.continuousOn (fun t ht => hld t ht.1)
  obtain ⟨ta, hta, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT) (hkc.inf hlc)
  obtain ⟨tb, htb, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) (hkc.sup hlc)
  let a := min (k ta) (l ta)
  let b := max (k tb) (l tb)
  have ha : 0 < a := lt_min (hkp ta hta.1) (hlp ta hta.1)
  have hkm : ∀ t ∈ Icc 0 T, k t ∈ Icc a b := fun t ht =>
    ⟨(hmin ht).trans (min_le_left _ _), (le_max_left _ _).trans (hmax ht)⟩
  have hlm : ∀ t ∈ Icc 0 T, l t ∈ Icc a b := fun t ht =>
    ⟨(hmin ht).trans (min_le_right _ _), (le_max_right _ _).trans (hmax ht)⟩
  have hab : a ≤ b := (hkm 0 ⟨le_rfl, hT⟩).1.trans (hkm 0 ⟨le_rfl, hT⟩).2
  have hdc : ContinuousOn (deriv (rate f s m)) (Icc a b) :=
    (rate_derivative_continuous h s m).mono (fun _ hx => ha.trans_le hx.1)
  obtain ⟨z, hz, hzmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hdc.norm
  have hLip : LipschitzOnWith ‖deriv (rate f s m) z‖₊ (rate f s m) (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le
      (fun k hk => (rate_hasDerivAt h s m (ha.trans_le hk.1)).differentiableAt)
      (fun k hk => hzmax hk)
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => rate f s m) (s := fun _ => Icc a b)
    (fun _ _ => hLip) hkc (fun t ht => (hkd t ht.1).hasDerivWithinAt)
    (fun t ht => hkm t (Ico_subset_Icc_self ht))
    hlc (fun t ht => (hld t ht.1).hasDerivWithinAt)
    (fun t ht => hlm t (Ico_subset_Icc_self ht)) heq ⟨hT, le_rfl⟩

/-- Propositions 2.7 and 2.9, with constructive existence and uniqueness made
explicit. Saving is positive and effective depreciation/dilution is positive.
The usual upper bound `s < 1` is needed for positive consumption, not for this
capital dynamics theorem. -/
theorem general_solow (h : Technology f) {s m k0 : ℝ}
    (hs : 0 < s) (hm : 0 < m) (hk0 : 0 < k0) :
    ∃ ks : ℝ, 0 < ks ∧ rate f s m ks = 0 ∧
      (∀ k, 0 < k → rate f s m k = 0 → k = ks) ∧
      ∃ k : ℝ → ℝ, k 0 = k0 ∧
        (∀ t, 0 ≤ t → 0 < k t ∧ HasDerivAt k (rate f s m (k t)) t) ∧
        (k0 < ks → StrictMonoOn k (Ici 0) ∧ ∀ t, 0 ≤ t → k t < ks) ∧
        (ks < k0 → StrictAntiOn k (Ici 0) ∧ ∀ t, 0 ≤ t → ks < k t) ∧
        (k0 = ks → ∀ t, 0 ≤ t → k t = ks) ∧
        (∀ t, 0 ≤ t → min k0 ks ≤ k t ∧ k t ≤ max k0 ks) ∧
        Tendsto k atTop (𝓝 ks) ∧
        (∀ l : ℝ → ℝ, l 0 = k0 → (∀ t, 0 ≤ t → 0 ≤ l t) →
          (∀ t, 0 ≤ t → HasDerivAt l (rate f s m (l t)) t) → EqOn l k (Ici 0)) := by
  obtain ⟨ks, ⟨hks, heq⟩, hu⟩ := existsUnique_steadyState h hs hm
  obtain ⟨k, h0, hk, hlow, hhigh, hconstant, hbound, hlim⟩ :=
    ODE.exists_attracting_scalar_path
      (fun x hx => (rate_hasDerivAt h s m hx).differentiableAt)
      (rate_derivative_continuous h s m) hks heq hk0
      (fun x hx hlt => rate_pos_below h hs hx hlt heq)
      (fun x hlt => rate_neg_above h hs hks hlt heq)
  refine ⟨ks, hks, heq, fun x hx he => hu x ⟨hx, he⟩,
    k, h0, hk, hlow, hhigh, hconstant, hbound, hlim, ?_⟩
  intro l hl0 hl hld
  exact path_unique h hs.le (hl0 ▸ hk0) (hl0.trans h0.symm) hl
    (fun t ht => (hk t ht).1.le) hld (fun t ht => (hk t ht).2)

/-- Output and consumption converge along any positive path converging to the
positive steady stock; positive consumption requires `s < 1`. -/
theorem output_consumption_limit (h : Technology f) {s ks : ℝ} {k : ℝ → ℝ}
    (hks : 0 < ks) (hlim : Tendsto k atTop (𝓝 ks)) :
    Tendsto (fun t => f (k t)) atTop (𝓝 (f ks)) ∧
    Tendsto (fun t => (1 - s) * f (k t)) atTop (𝓝 ((1 - s) * f ks)) := by
  have hy := (h.differentiable ks hks).continuousAt.tendsto.comp hlim
  exact ⟨hy, hy.const_mul (1 - s)⟩

end Solow1956.Neoclassical
