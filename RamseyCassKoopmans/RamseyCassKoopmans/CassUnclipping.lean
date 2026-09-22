import RamseyCassKoopmans.CassShooting

/-! # Removing the auxiliary clipping bounds

For the upper branch, the signs exclude nonpositive prices directly. For the
lower branch, an explicit exponential price bound and a finite capital drift
exclude prices as large as the upper clip. Capital confinement follows from
the proved monotonicity on both branches.
-/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.CassPhase

theorem nonpositive_price_velocity (p : CassPhase) {x : ℝ × ℝ} (hq : x.2 ≤ 0) :
    (p.field x).2 < 0 := by
  have hp : p.price x.2 = 0 := by
    dsimp [price, clip]
    rw [min_eq_right (hq.trans (p.qs_pos.trans p.qs_lt).le), max_eq_left hq]
  change (p.d + p.m) * p.price x.2 -
    max (p.price x.2) (p.μ (p.f (p.stock x.1))) * p.mp (p.stock x.1) < 0
  rw [hp, mul_zero, max_eq_right (p.μ_pos _ (p.output_pos _)).le, zero_sub]
  exact neg_neg_of_pos (mul_pos (p.μ_pos _ (p.output_pos _)) (p.mp_pos _ (p.stock_mem _)))

theorem upper_clips_inactive (p : CassPhase) {K : ℝ≥0}
    (hlip : LipschitzWith K p.field) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hav : ODE.Avoids γ p.steady) (h0 : p.ks < (γ 0).1)
    (hku : (γ 0).1 ≤ p.ku) :
    ∀ t, 0 ≤ t → p.point (γ t) = γ t ∧ 0 < (γ t).2 := by
  obtain ⟨_, ha, _, hside⟩ := p.upper_avoiding_converges hlip hd hav h0
  have hv := ODE.upper_branch_velocity p.cooperative hlip (a := p.steady)
    (fun b hb _ hv => p.upper_cross hb hv)
    (fun b hb _ hv => by
      obtain ⟨ε, hε, he⟩ := p.upper_price_drift hb hv
      exact ⟨ε, hε, fun x hx hqx _ => he x hx hqx⟩)
    (fun b hb _ hv => p.upper_corner_drift hb hv) hd
    (fun t ht => (hside t ht).1) hav
  intro t ht
  have hq : 0 < (γ t).2 := by
    by_contra hn
    have hneg := p.nonpositive_price_velocity (le_of_not_gt hn)
    linarith [(hv t ht).2]
  refine ⟨Prod.ext ?_ ?_, hq⟩
  · exact clip_eq ⟨(p.kl_lt.trans (hside t ht).1).le,
      (ha.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht).trans hku⟩
  · exact clip_eq ⟨hq.le, (hside t ht).2.trans p.qs_lt.le⟩

theorem lower_exponential_price (p : CassPhase) {K : ℝ≥0}
    (hlip : LipschitzWith K p.field) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hav : ODE.Avoids γ p.steady) (h0 : (γ 0).1 < p.ks) :
    ∀ t, 0 ≤ t → (γ 0).2 * Real.exp (-p.mp p.kl * t) ≤ (γ t).2 := by
  obtain ⟨_, _, _, hside⟩ := p.lower_avoiding_converges hlip hd hav h0
  have hv := ODE.lower_branch_velocity p.cooperative hlip (a := p.steady)
    (fun x hx hqx => p.lower_price_negative hx hqx)
    (fun b hb _ => by
      obtain ⟨ε, hε, he⟩ := p.lower_price_drift hb
      exact ⟨ε, hε, fun x hx hqx _ => he x hx hqx⟩) hd
    (fun t ht => (hside t ht).1) hav
  apply ODE.exponential_lower_bound (fun t => ODE.hasDerivAt_snd (hd t))
  intro t ht
  have hz : 0 < cassInvestment p.f p.C (p.point (γ t)) := by
    have hh := (hv t ht).1
    change 0 < cassInvestment p.f p.C (p.point (γ t)) - p.m * p.stock (γ t).1 at hh
    linarith [mul_pos p.m_pos (p.stock_pos (γ t).1)]
  rw [p.interior_field_price hz]
  have hmp : p.mp (p.stock (γ t).1) ≤ p.mp p.kl :=
    p.mp_anti.antitoneOn ⟨le_rfl, (p.kl_lt.trans p.ku_gt).le⟩
      (p.stock_mem _) (p.stock_mem _).1
  have hqpos := p.qs_pos.trans_le (hside t ht).2
  have hpq : p.price (γ t).2 ≤ (γ t).2 := max_le hqpos.le (min_le_right _ _)
  have hprod := mul_le_mul hmp hpq (p.price_mem _).1
    (p.mp_pos _ ⟨le_rfl, (p.kl_lt.trans p.ku_gt).le⟩).le
  have hrate := mul_nonneg (add_pos p.d_pos p.m_pos).le (p.price_mem (γ t).2).1
  nlinarith

/-- A finite, checkable price threshold suffices to remove the upper price
clip. `hpush` is an inequality for points, not a trajectory hypothesis. -/
theorem lower_initial_price_lt_top (p : CassPhase) {K : ℝ≥0}
    (hlip : LipschitzWith K p.field) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hav : ODE.Avoids γ p.steady) (h0 : (γ 0).1 < p.ks)
    {H ε T : ℝ} (hT : 0 ≤ T)
    (hlarge : H * Real.exp (p.mp p.kl * T) ≤ p.Q)
    (htime : p.ks - (γ 0).1 ≤ ε * T)
    (hpush : ∀ x : ℝ × ℝ, (γ 0).1 ≤ x.1 → x.1 ≤ p.ks → H ≤ x.2 → ε ≤ (p.field x).1) :
    (γ 0).2 < p.Q := by
  by_contra hn
  have hQ0 : p.Q ≤ (γ 0).2 := le_of_not_gt hn
  obtain ⟨_, hm, _, hside⟩ := p.lower_avoiding_converges hlip hd hav h0
  have hq0 : 0 < (γ 0).2 := p.qs_pos.trans_le (hside 0 le_rfl).2
  have hq : ∀ t ∈ Icc 0 T, H ≤ (γ t).2 := by
    intro t ht
    have hmp := p.mp_pos p.kl ⟨le_rfl, (p.kl_lt.trans p.ku_gt).le⟩
    have hexp : Real.exp (-p.mp p.kl * T) ≤ Real.exp (-p.mp p.kl * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.2 (neg_nonpos.mpr hmp.le))
    have hmul := mul_le_mul_of_nonneg_right (hlarge.trans hQ0) (Real.exp_pos (-p.mp p.kl * T)).le
    have hid : (H * Real.exp (p.mp p.kl * T)) * Real.exp (-p.mp p.kl * T) = H := by
      rw [mul_assoc, ← Real.exp_add]
      have he : p.mp p.kl * T + -p.mp p.kl * T = 0 := by ring
      rw [he, Real.exp_zero, mul_one]
    rw [hid] at hmul
    exact (hmul.trans (mul_le_mul_of_nonneg_left hexp hq0.le)).trans
      (p.lower_exponential_price hlip hd hav h0 t ht.1)
  have hk := ODE.linear_lower_bound_on (fun t => ODE.hasDerivAt_fst (hd t)) hT
    (fun t ht => hpush (γ t)
      (hm.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht.1) ht.1)
      (hside t ht.1).1.le (hq t ht))
  have hlast := (hside T hT).1
  linarith

theorem lower_clips_inactive (p : CassPhase) {K : ℝ≥0}
    (hlip : LipschitzWith K p.field) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hav : ODE.Avoids γ p.steady) (h0 : (γ 0).1 < p.ks)
    (hkl : p.kl ≤ (γ 0).1) (hq0 : (γ 0).2 ≤ p.Q) :
    ∀ t, 0 ≤ t → p.point (γ t) = γ t ∧ 0 < (γ t).2 := by
  obtain ⟨_, hm, ha, hside⟩ := p.lower_avoiding_converges hlip hd hav h0
  intro t ht
  have hq := p.qs_pos.trans_le (hside t ht).2
  refine ⟨Prod.ext ?_ ?_, hq⟩
  · exact clip_eq ⟨hkl.trans (hm.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht),
      ((hside t ht).1.trans p.ku_gt).le⟩
  · exact clip_eq ⟨hq.le, (ha.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht).trans hq0⟩

end RamseyCassKoopmans.CassPhase
