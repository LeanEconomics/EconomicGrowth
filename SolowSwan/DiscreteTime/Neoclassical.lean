/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import Solow1956.Growth.SolowComparative

/-!
# The discrete-time Solow map and its steady state

Source: Acemoglu, *Introduction to Modern Economic Growth*, Chapter 2,
equation (2.17) and Proposition 2.2. With saving `s`, depreciation `δ` and gross
growth `γ = (1 + n)(1 + g)` of effective labour, capital per effective worker
obeys

`k(t+1) = (s f(k(t)) + (1 - δ) k(t)) / γ`.

Acemoglu's equation (2.17) is the case `γ = 1`. The map moves capital by
`rate f s m k / γ` with `m = γ - 1 + δ`, so its positive fixed point is the
continuous-time steady state `steadyCapital h s m`: stationary results are shared
by the two models, only the dynamics differ. The restriction `δ ≤ 1` makes the
map increasing, which the global dynamics require.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime

open Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- Discrete-time parameters: positive saving, depreciation at most one, positive
gross growth of effective labour, and positive effective dilution `γ - 1 + δ`. -/
structure Params (s δ γ : ℝ) : Prop where
  saving_pos : 0 < s
  depreciation_le_one : δ ≤ 1
  growth_pos : 0 < γ
  dilution_pos : 0 < γ - 1 + δ

/-- The discrete-time law of motion for capital per effective worker. -/
noncomputable def next (f : ℝ → ℝ) (s δ γ k : ℝ) : ℝ := (s * f k + (1 - δ) * k) / γ

/-- The positive steady state of the map: the continuous steady state with
effective dilution `m = γ - 1 + δ`. -/
noncomputable def steady (h : Technology f) (s δ γ : ℝ) : ℝ := steadyCapital h s (γ - 1 + δ)

/-- The one-period change in capital is the continuous accumulation rate divided by `γ`. -/
theorem next_sub_self {s δ γ : ℝ} (hγ : 0 < γ) (k : ℝ) :
    next f s δ γ k - k = rate f s (γ - 1 + δ) k / γ := by
  unfold next rate
  field_simp
  ring

/-- Acemoglu's case `γ = 1`: `k(t+1) = s f(k(t)) + (1 - δ) k(t)`. -/
theorem next_acemoglu (s δ k : ℝ) : next f s δ 1 k = s * f k + (1 - δ) * k := by
  simp [next]

theorem next_zero (h : Technology f) (s δ γ : ℝ) : next f s δ γ 0 = 0 := by
  simp [next, h.zero]

theorem next_pos (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ) (hk : 0 < k) :
    0 < next f s δ γ k := by
  have h1 := mul_pos P.saving_pos (h.output_pos hk)
  have h2 := mul_nonneg (sub_nonneg.mpr P.depreciation_le_one) hk.le
  exact div_pos (by linarith) P.growth_pos

theorem next_nonneg (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ) (hk : 0 ≤ k) :
    0 ≤ next f s δ γ k := by
  rcases hk.eq_or_lt with he | he
  · rw [← he, next_zero h]
  · exact (next_pos h P he).le

/-- Acemoglu's proof of Proposition 2.5 starts from `g' > 0`: the map is increasing. -/
theorem next_strictMono (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    StrictMonoOn (next f s δ γ) (Ici 0) := by
  intro a ha b hb hab
  have h1 := mul_lt_mul_of_pos_left (h.output_strictMono ha hb hab) P.saving_pos
  have h2 := mul_le_mul_of_nonneg_left hab.le (sub_nonneg.mpr P.depreciation_le_one)
  exact div_lt_div_of_pos_right (by linarith) P.growth_pos

theorem next_continuousOn (h : Technology f) (s δ γ : ℝ) :
    ContinuousOn (next f s δ γ) (Ici 0) :=
  (((h.continuous.const_mul s).add (continuousOn_id.const_mul (1 - δ)))).div_const γ

theorem next_hasDerivAt (h : Technology f) (s δ γ : ℝ) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (next f s δ γ) ((s * deriv f k + (1 - δ)) / γ) k := by
  have h1 : HasDerivAt (fun y => s * f y + (1 - δ) * y) (s * deriv f k + (1 - δ) * 1) k :=
    ((h.differentiable k hk).hasDerivAt.const_mul s).add ((hasDerivAt_id' k).const_mul (1 - δ))
  rw [mul_one] at h1
  exact h1.div_const γ

/-- Positive fixed points of the map are exactly the positive roots of the continuous rate. -/
theorem next_eq_self_iff {s δ γ k : ℝ} (hγ : 0 < γ) :
    next f s δ γ k = k ↔ rate f s (γ - 1 + δ) k = 0 := by
  rw [← sub_eq_zero, next_sub_self hγ, div_eq_zero_iff]
  exact ⟨fun h => h.resolve_right (ne_of_gt hγ), fun h => Or.inl h⟩

/-- Acemoglu Proposition 2.2: a unique positive steady state exists. -/
theorem existsUnique_steadyState (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    ∃! k : ℝ, 0 < k ∧ next f s δ γ k = k := by
  simpa only [next_eq_self_iff P.growth_pos] using
    Neoclassical.existsUnique_steadyState h P.saving_pos P.dilution_pos

theorem steady_spec (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    0 < steady h s δ γ ∧ next f s δ γ (steady h s δ γ) = steady h s δ γ := by
  obtain ⟨hk, he⟩ := steadyCapital_spec h P.saving_pos P.dilution_pos
  exact ⟨hk, (next_eq_self_iff P.growth_pos).mpr he⟩

theorem steady_eq (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ) (hk : 0 < k)
    (he : next f s δ γ k = k) : steady h s δ γ = k :=
  steadyCapital_eq h P.saving_pos P.dilution_pos hk ((next_eq_self_iff P.growth_pos).mp he)

/-- Zero is also a fixed point; Proposition 2.2 ignores it by convention. -/
theorem zero_fixed (h : Technology f) (s δ γ : ℝ) : next f s δ γ 0 = 0 := next_zero h s δ γ

/-- Proposition 2.2 in full: the steady state, its output `y* = f(k*)`, and its
consumption `c* = (1 - s) f(k*) = f(k*) - m k*`. -/
theorem steady_state_equilibrium (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    0 < steady h s δ γ ∧ next f s δ γ (steady h s δ γ) = steady h s δ γ ∧
      s * f (steady h s δ γ) = (γ - 1 + δ) * steady h s δ γ ∧
      (1 - s) * f (steady h s δ γ) = f (steady h s δ γ) - (γ - 1 + δ) * steady h s δ γ := by
  obtain ⟨hk, he⟩ := steady_spec h P
  have hr := (next_eq_self_iff P.growth_pos).mp he
  unfold rate at hr
  exact ⟨hk, he, by linarith, by linarith⟩

theorem next_gt_self (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ)
    (hk : 0 < k) (hlt : k < steady h s δ γ) : k < next f s δ γ k := by
  have hr := rate_pos_below h P.saving_pos hk hlt
    ((next_eq_self_iff P.growth_pos).mp (steady_spec h P).2)
  have := next_sub_self (f := f) (s := s) (δ := δ) P.growth_pos k
  have := div_pos hr P.growth_pos
  linarith

theorem next_lt_self (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ)
    (hgt : steady h s δ γ < k) : next f s δ γ k < k := by
  have hr := rate_neg_above h P.saving_pos (steady_spec h P).1 hgt
    ((next_eq_self_iff P.growth_pos).mp (steady_spec h P).2)
  have := next_sub_self (f := f) (s := s) (δ := δ) P.growth_pos k
  have := div_neg_of_neg_of_pos hr P.growth_pos
  linarith

/-- Local stability, Proposition 2.5: the slope of the map at `k*` lies in `(0, 1)`. -/
theorem slope_at_steady (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    0 < (s * deriv f (steady h s δ γ) + (1 - δ)) / γ ∧
      (s * deriv f (steady h s δ γ) + (1 - δ)) / γ < 1 := by
  obtain ⟨hk, _, hss, _⟩ := steady_state_equilibrium h P
  set ks := steady h s δ γ
  have hmp := mul_pos P.saving_pos (h.marginal_positive ks hk)
  have hgap := mul_lt_mul_of_pos_left (h.output_gap hk) P.saving_pos
  refine ⟨div_pos (by linarith [P.depreciation_le_one]) P.growth_pos,
    (div_lt_one P.growth_pos).mpr ?_⟩
  have : s * deriv f ks < γ - 1 + δ := by
    have h' : s * (deriv f ks * ks) < (γ - 1 + δ) * ks := by linarith
    nlinarith
  linarith

end Solow1956.DiscreteTime
