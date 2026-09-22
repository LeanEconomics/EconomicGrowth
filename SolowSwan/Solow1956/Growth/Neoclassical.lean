/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Neoclassical production and the general Solow steady state

Source: Acemoglu, Introduction to Modern Economic Growth, Chapter 2,
Assumptions 1–2 and Proposition 2.7. The assumptions below are stated for
the intensive production function. No derivative at zero is required.
-/

open Set Filter Topology

namespace Solow1956.Neoclassical

/-- Intensive-form neoclassical assumptions. Strict concavity and a continuous
first derivative suffice; the source's negative second derivative implies them. -/
structure Technology (f : ℝ → ℝ) : Prop where
  continuous : ContinuousOn f (Ici 0)
  zero : f 0 = 0
  differentiable : ∀ k, 0 < k → DifferentiableAt ℝ f k
  derivative_continuous : ContinuousOn (deriv f) (Ioi 0)
  concave : StrictConcaveOn ℝ (Ici 0) f
  marginal_positive : ∀ k, 0 < k → 0 < deriv f k
  inada_zero : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop
  inada_top : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))

/-- The source's twice-differentiable primitive assumptions imply `Technology`.
Continuity of the first derivative is deduced from its differentiability. -/
theorem technology_of_second_derivative {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ici 0)) (h0 : f 0 = 0)
    (hd : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hd2 : ∀ k, 0 < k → DifferentiableAt ℝ (deriv f) k)
    (hp : ∀ k, 0 < k → 0 < deriv f k)
    (hn : ∀ k, 0 < k → deriv (deriv f) k < 0)
    (hz : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop)
    (ht : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))) : Technology f := by
  refine ⟨hc, h0, hd, fun k hk => (hd2 k hk).continuousAt.continuousWithinAt,
    strictConcaveOn_of_deriv2_neg (convex_Ici 0) hc ?_, hp, hz, ht⟩
  intro k hk
  exact hn k (by simpa only [interior_Ici, mem_Ioi] using hk)

variable {f : ℝ → ℝ}

theorem Technology.marginal_strictAnti (h : Technology f) :
    StrictAntiOn (deriv f) (Ioi 0) :=
  (h.concave.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv h.differentiable

theorem Technology.output_gap (h : Technology f) {k : ℝ} (hk : 0 < k) :
    deriv f k * k < f k := by
  have hs := h.concave.deriv_lt_slope (show (0 : ℝ) ∈ Ici 0 by simp)
    hk.le hk (h.differentiable k hk)
  rw [slope_def_field, h.zero, sub_zero, sub_zero] at hs
  exact (lt_div_iff₀ hk).mp hs

theorem Technology.output_pos (h : Technology f) {k : ℝ} (hk : 0 < k) : 0 < f k :=
  (mul_pos (h.marginal_positive k hk) hk).trans (h.output_gap hk)

theorem Technology.output_nonneg (h : Technology f) {k : ℝ} (hk : 0 ≤ k) : 0 ≤ f k := by
  rcases hk.eq_or_lt with he | he
  · rw [← he, h.zero]
  · exact (h.output_pos he).le

theorem Technology.output_strictMono (h : Technology f) : StrictMonoOn f (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) h.continuous
  intro k hk
  exact h.marginal_positive k (by simpa only [interior_Ici, mem_Ioi] using hk)

/-- Average product is strictly decreasing, a conclusion of concavity. -/
theorem Technology.average_strictAnti (h : Technology f) :
    StrictAntiOn (fun k => f k / k) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun k hk => ((h.differentiable k hk).hasDerivAt.div (hasDerivAt_id k)
      (ne_of_gt hk)).continuousAt.continuousWithinAt)
  intro k hk
  have hk' : 0 < k := by simpa only [interior_Ioi, mem_Ioi] using hk
  rw [((h.differentiable k hk').hasDerivAt.div (hasDerivAt_id k) (ne_of_gt hk')).deriv]
  simp only [mul_one]
  exact div_neg_of_neg_of_pos (sub_neg.mpr (h.output_gap hk')) (sq_pos_of_pos hk')

noncomputable def rate (f : ℝ → ℝ) (s m k : ℝ) : ℝ := s * f k - m * k

theorem rate_zero (h : Technology f) (s m : ℝ) : rate f s m 0 = 0 := by
  simp [rate, h.zero]

theorem rate_hasDerivAt (h : Technology f) (s m : ℝ) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (rate f s m) (s * deriv f k - m) k := by
  change HasDerivAt (fun y => s * f y - m * y) (s * deriv f k - m) k
  convert! ((h.differentiable k hk).hasDerivAt.const_mul s).sub
    ((hasDerivAt_id k).const_mul m) using 1
  simp only [mul_one]

theorem rate_derivative_continuous (h : Technology f) (s m : ℝ) :
    ContinuousOn (deriv (rate f s m)) (Ioi 0) := by
  apply ((h.derivative_continuous.const_mul s).sub
    (continuousOn_const (c := m))).congr
  intro k hk
  exact (rate_hasDerivAt h s m hk).deriv

/-- A tangent at a sufficiently large stock gives a finite upper bracket. -/
theorem Technology.exists_capacity (h : Technology f) {r k0 : ℝ} (hr : 0 < r) :
    ∃ K, k0 ≤ K ∧ ∀ k, K ≤ k → f k ≤ r * k := by
  obtain ⟨a, ha, hma⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (h.inada_top.eventually (gt_mem_nhds (half_pos hr)))).exists
  let K := max k0 (max (a + 1) (2 * |f a| / r))
  refine ⟨K, le_max_left _ _, ?_⟩
  intro k hk
  have hak : a < k := by have := (le_max_left _ _).trans ((le_max_right _ _).trans hk); linarith
  have hratio : 2 * |f a| / r ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hmk := (div_le_iff₀ hr).mp hratio
  have hs := h.concave.concaveOn.slope_le_of_hasDerivAt ha.le (ha.le.trans hak.le)
    hak (h.differentiable a ha).hasDerivAt
  rw [slope_def_field] at hs
  have htan := (div_le_iff₀ (sub_pos.mpr hak)).mp hs
  have hpk := mul_le_mul_of_nonneg_right hma.le (ha.le.trans hak.le)
  have hpa := mul_nonneg (h.marginal_positive a ha).le ha.le
  nlinarith [le_abs_self (f a)]

/-- Acemoglu Proposition 2.7: the positive stationary capital stock exists
uniquely. The stationary zero boundary is not asserted to be unique. -/
theorem existsUnique_steadyState (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    ∃! k : ℝ, 0 < k ∧ rate f s m k = 0 := by
  have hz : ∀ᶠ k : ℝ in 𝓝[>] (0 : ℝ), 0 < k := self_mem_nhdsWithin
  obtain ⟨a, ha, hma⟩ := (hz.and
    (h.inada_zero.eventually_gt_atTop (m / s))).exists
  have hapos : 0 < rate f s m a := by
    have hg := h.output_gap ha
    have hm' := (div_lt_iff₀ hs).mp hma
    have := mul_lt_mul_of_pos_left hg hs
    dsimp [rate]
    nlinarith
  obtain ⟨b, hab, hb⟩ := h.exists_capacity (k0 := a) (div_pos hm hs)
  have hbpos := ha.trans_le hab
  have hbrate : rate f s m b ≤ 0 := by
    have := mul_le_mul_of_nonneg_left (hb b le_rfl) hs.le
    have hc : s * (m / s * b) = m * b := by field_simp
    dsimp [rate]; linarith
  have hc : ContinuousOn (rate f s m) (Icc a b) :=
    (h.continuous.mono (fun _ hx => ha.le.trans hx.1)).const_mul s |>.sub
      (continuousOn_id.const_mul m)
  obtain ⟨k, hk, heq⟩ := intermediate_value_Icc' hab hc ⟨hbrate, hapos.le⟩
  have hkpos := ha.trans_le hk.1
  refine ⟨k, ⟨hkpos, heq⟩, ?_⟩
  intro y hy
  apply h.average_strictAnti.injOn hy.1 hkpos
  have heq' : f k / k = m / s := by
    apply (div_eq_div_iff (ne_of_gt hkpos) (ne_of_gt hs)).mpr
    dsimp [rate] at heq; nlinarith
  have hy' : f y / y = m / s := by
    apply (div_eq_div_iff (ne_of_gt hy.1) (ne_of_gt hs)).mpr
    have := hy.2; dsimp [rate] at this; nlinarith
  exact hy'.trans heq'.symm

theorem rate_pos_below (h : Technology f) {s m ks k : ℝ}
    (hs : 0 < s) (hk : 0 < k) (hkk : k < ks) (hks : rate f s m ks = 0) :
    0 < rate f s m k := by
  have hp := h.average_strictAnti hk (hk.trans hkk) hkk
  have hp' := (div_lt_div_iff₀ (hk.trans hkk) hk).mp hp
  have hm := mul_lt_mul_of_pos_left hp' hs
  dsimp [rate] at *
  nlinarith

theorem rate_neg_above (h : Technology f) {s m ks k : ℝ}
    (hs : 0 < s) (hkspos : 0 < ks) (hkk : ks < k) (hks : rate f s m ks = 0) :
    rate f s m k < 0 := by
  have hp := h.average_strictAnti hkspos (hkspos.trans hkk) hkk
  have hp' := (div_lt_div_iff₀ (hkspos.trans hkk) hkspos).mp hp
  have hm := mul_lt_mul_of_pos_left hp' hs
  dsimp [rate] at *
  nlinarith

end Solow1956.Neoclassical
