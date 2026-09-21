import RamseyCassKoopmans.NonescapingDynamics

/-! # Finite shooting endpoints from ordinary velocity bounds

The price starts sufficiently far outside the clipped price interval that it
cannot return to that interval before capital crosses the equilibrium stock.
The bounds and crossing times are explicit; endpoint escape is proved.
-/

open Set
open scoped NNReal

namespace RamseyCassKoopmans.ODE

theorem coordinate_bounds {v : ℝ × ℝ → ℝ × ℝ} {B : ℝ≥0}
    (hb : ∀ x, ‖v x‖ ≤ B) (x : ℝ × ℝ) :
    -(B : ℝ) ≤ (v x).2 ∧ (v x).2 ≤ B := by
  have h : ‖(v x).2‖ ≤ B := (le_max_right ‖(v x).1‖ ‖(v x).2‖).trans (hb x)
  exact abs_le.mp h

theorem exists_low_endpoint {v : ℝ × ℝ → ℝ × ℝ} {B : ℝ≥0}
    (hbound : ∀ x, ‖v x‖ ≤ B) {a : ℝ × ℝ} (ha : 0 < a.2)
    {ε : ℝ} (hε : 0 < ε)
    (hdown : ∀ x : ℝ × ℝ, x.2 ≤ 0 → (v x).1 ≤ -ε) (k0 : ℝ) :
    ∃ l : ℝ, l < 0 ∧ ∀ γ : ℝ → ℝ × ℝ, γ 0 = (k0, l) →
      (∀ t, HasDerivAt γ (v (γ t)) t) → ∃ t, 0 ≤ t ∧ γ t ∈ lowerQuadrant a := by
  let T := (max 0 (k0 - a.1) + 1) / ε
  have hT : 0 < T := div_pos (by linarith [le_max_left (0 : ℝ) (k0 - a.1)]) hε
  have htime : k0 - a.1 < ε * T := by
    have heq : ε * T = max 0 (k0 - a.1) + 1 := by dsimp [T]; field_simp
    rw [heq]
    linarith [le_max_right (0 : ℝ) (k0 - a.1)]
  let l := -(B : ℝ) * T - 1
  have hl : l < 0 := by dsimp [l]; nlinarith [B.coe_nonneg]
  refine ⟨l, hl, ?_⟩
  intro γ h0 hd
  have hq : ∀ t ∈ Icc 0 T, (γ t).2 < 0 := by
    intro t ht
    have h := linear_upper_bound (fun u => hasDerivAt_snd (hd u)) ht.1
      (fun u _ => (coordinate_bounds hbound (γ u)).2)
    rw [h0] at h
    change (γ t).2 - l ≤ (B : ℝ) * (t - 0) at h
    dsimp [l] at h
    nlinarith [mul_le_mul_of_nonneg_left ht.2 B.coe_nonneg]
  have hk := linear_upper_bound_on (fun u => hasDerivAt_fst (hd u)) hT.le
    (fun t ht => hdown (γ t) (hq t ht).le)
  rw [h0] at hk
  change (γ T).1 - k0 ≤ -ε * (T - 0) at hk
  exact ⟨T, hT.le, by constructor; linarith; exact (hq T ⟨hT.le, le_rfl⟩).trans ha⟩

theorem exists_high_endpoint {v : ℝ × ℝ → ℝ × ℝ} {B : ℝ≥0}
    (hbound : ∀ x, ‖v x‖ ≤ B) {a : ℝ × ℝ} {Q ε : ℝ}
    (hQ : a.2 < Q) (hε : 0 < ε)
    (hup : ∀ x : ℝ × ℝ, x.1 ≤ a.1 → Q ≤ x.2 → ε ≤ (v x).1) (k0 : ℝ) :
    ∃ r : ℝ, Q < r ∧ ∀ γ : ℝ → ℝ × ℝ, γ 0 = (k0, r) →
      (∀ t, HasDerivAt γ (v (γ t)) t) → ∃ t, 0 ≤ t ∧ γ t ∈ upperQuadrant a := by
  let T := (max 0 (a.1 - k0) + 1) / ε
  have hT : 0 < T := div_pos (by linarith [le_max_left (0 : ℝ) (a.1 - k0)]) hε
  have htime : a.1 - k0 < ε * T := by
    have heq : ε * T = max 0 (a.1 - k0) + 1 := by dsimp [T]; field_simp
    rw [heq]
    linarith [le_max_right (0 : ℝ) (a.1 - k0)]
  let r := Q + (B : ℝ) * T + 1
  have hr : Q < r := by dsimp [r]; nlinarith [B.coe_nonneg]
  refine ⟨r, hr, ?_⟩
  intro γ h0 hd
  by_contra hn
  push Not at hn
  have hq : ∀ t ∈ Icc 0 T, Q < (γ t).2 := by
    intro t ht
    have h := linear_lower_bound (fun u => hasDerivAt_snd (hd u)) ht.1
      (fun u _ => (coordinate_bounds hbound (γ u)).1)
    rw [h0] at h
    change -(B : ℝ) * (t - 0) ≤ (γ t).2 - r at h
    dsimp [r] at h
    nlinarith [mul_le_mul_of_nonneg_left ht.2 B.coe_nonneg]
  have hk : ∀ t ∈ Icc 0 T, (γ t).1 ≤ a.1 := by
    intro t ht
    by_contra hnk
    exact hn t ht.1 ⟨lt_of_not_ge hnk, hQ.trans (hq t ht)⟩
  have h := linear_lower_bound_on (fun u => hasDerivAt_fst (hd u)) hT.le
    (fun t ht => hup (γ t) (hk t ht) (hq t ht).le)
  rw [h0] at h
  change ε * (T - 0) ≤ (γ T).1 - k0 at h
  have hkT := hk T ⟨hT.le, le_rfl⟩
  linarith

end RamseyCassKoopmans.ODE
