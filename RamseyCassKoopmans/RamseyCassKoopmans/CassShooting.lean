import RamseyCassKoopmans.CassPhaseEquilibrium
import RamseyCassKoopmans.ShootingEndpoints

/-! # Constructed convergent solutions of the clipped Cass system

Shooting endpoints are derived from bounded velocity and the two extreme-price
capital drifts. Monotonicity, confinement of capital between its initial and
steady stocks, and convergence follow from the constructed solution. Removing
the price clip additionally requires the quantitative price bound.
-/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.CassPhase

theorem demand_at_zero (p : CassPhase) : p.C 0 = p.cb := by
  apply p.μ_anti.injOn (p.ca_pos.trans_le (p.C_mem _).1) (p.ca_pos.trans_le p.ca_le_cb)
  rw [p.inverse, clip, min_eq_right (p.μ_pos p.ca p.ca_pos).le,
    max_eq_left (p.μ_pos p.cb (p.ca_pos.trans_le p.ca_le_cb)).le]

theorem demand_at_top (p : CassPhase) : p.C p.Q = p.ca := by
  apply p.μ_anti.injOn (p.ca_pos.trans_le (p.C_mem _).1) p.ca_pos
  rw [p.inverse, p.Q_eq]
  exact clip_eq ⟨p.μ_anti.antitoneOn p.ca_pos (p.ca_pos.trans_le p.ca_le_cb) p.ca_le_cb, le_rfl⟩

theorem low_capital_drift (p : CassPhase) (x : ℝ × ℝ) (hq : x.2 ≤ 0) :
    (p.field x).1 ≤ -(p.m * p.kl) := by
  have hp : p.price x.2 = 0 := by
    dsimp [price, clip]
    rw [min_eq_right (hq.trans (p.qs_pos.trans p.qs_lt).le), max_eq_left hq]
  change p.f (p.stock x.1) - min (p.C (p.price x.2)) (p.f (p.stock x.1)) -
    p.m * p.stock x.1 ≤ _
  rw [hp, p.demand_at_zero, min_eq_right (p.f_mem _ (p.stock_mem _)).2, sub_self, zero_sub]
  exact neg_le_neg (mul_le_mul_of_nonneg_left (p.stock_mem _).1 p.m_pos.le)

theorem high_capital_drift (p : CassPhase)
    (hnet : MonotoneOn (fun k => p.f k - p.m * k) (Icc p.kl p.ks))
    (x : ℝ × ℝ) (hk : x.1 ≤ p.ks) (hq : p.Q ≤ x.2) :
    p.f p.kl - p.m * p.kl - p.ca ≤ (p.field x).1 := by
  have hp : p.price x.2 = p.Q := by
    dsimp [price, clip]
    rw [min_eq_left hq, max_eq_right (p.qs_pos.trans p.qs_lt).le]
  have hstock : p.stock x.1 ≤ p.ks :=
    max_le p.kl_lt.le ((min_le_right _ _).trans hk)
  have hn := hnet ⟨le_rfl, p.kl_lt.le⟩ ⟨(p.stock_mem _).1, hstock⟩ (p.stock_mem _).1
  change _ ≤ p.f (p.stock x.1) - min (p.C (p.price x.2)) (p.f (p.stock x.1)) -
    p.m * p.stock x.1
  rw [hp, p.demand_at_top, min_eq_left (p.f_mem _ (p.stock_mem _)).1]
  linarith

theorem exists_avoiding_solution (p : CassPhase) (hb : BoundedLip p.field)
    (hnet : MonotoneOn (fun k => p.f k - p.m * k) (Icc p.kl p.ks))
    (hfloor : p.ca < p.f p.kl - p.m * p.kl) (k0 : ℝ) :
    ∃ γ : ℝ → ℝ × ℝ, (γ 0).1 = k0 ∧
      (∀ t, HasDerivAt γ (p.field (γ t)) t) ∧ ODE.Avoids γ p.steady := by
  obtain ⟨K, B, hlip, hbound⟩ := hb
  obtain ⟨l, hl, hleft⟩ := ODE.exists_low_endpoint hbound (a := p.steady) p.qs_pos
    (mul_pos p.m_pos p.kl_pos) p.low_capital_drift k0
  obtain ⟨r, hr, hright⟩ := ODE.exists_high_endpoint hbound (a := p.steady) p.qs_lt
    (sub_pos.mpr hfloor) (p.high_capital_drift hnet) k0
  obtain ⟨q, _, γ, h0, hd, hav⟩ := ODE.exists_solution_avoiding_quadrants
    p.cooperative hlip hbound p.field_steady (fun q => (k0, q))
    (continuous_const.prodMk continuous_id)
    (show l ≤ r from (hl.trans (p.qs_pos.trans (p.qs_lt.trans hr))).le) hleft hright
  exact ⟨γ, congrArg Prod.fst h0, hd, hav⟩

theorem lower_avoiding_converges (p : CassPhase) {K : ℝ≥0}
    (hlip : LipschitzWith K p.field) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hav : ODE.Avoids γ p.steady) (h0 : (γ 0).1 < p.ks) :
    Tendsto γ atTop (𝓝 p.steady) ∧
      StrictMonoOn (fun t => (γ t).1) (Ici 0) ∧
      StrictAntiOn (fun t => (γ t).2) (Ici 0) ∧
      ∀ t, 0 ≤ t → (γ t).1 < p.ks ∧ p.qs ≤ (γ t).2 := by
  have hne : γ 0 ≠ p.steady := by
    intro heq
    have hh := congrArg Prod.fst heq
    change (γ 0).1 = p.ks at hh
    linarith
  have hγcont : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hk := ODE.first_stays_below (a := p.steady) hγcont h0
    (ODE.avoids_first_ne hlip p.field_steady p.field_first_axis hd hne hav)
  have hq : ∀ t, 0 ≤ t → p.qs ≤ (γ t).2 := by
    intro t ht
    by_contra hn
    exact hav t ht (Or.inl ⟨hk t ht, lt_of_not_ge hn⟩)
  have hv := ODE.lower_branch_velocity p.cooperative hlip (a := p.steady)
    (fun x hx hqx => p.lower_price_negative hx hqx)
    (fun b hb _ => by
      obtain ⟨ε, hε, he⟩ := p.lower_price_drift hb
      exact ⟨ε, hε, fun x hx hqx _ => he x hx hqx⟩) hd hk hav
  obtain ⟨hm, ha⟩ := ODE.lower_branch_monotone hd hv
  obtain ⟨b, hb, hzero, _, _⟩ := ODE.lower_branch_limit hlip.continuous hd
    (fun t ht => (hk t ht).le) hq hm.monotoneOn ha.antitoneOn
  rw [p.field_zero_unique hzero] at hb
  exact ⟨hb, hm, ha, fun t ht => ⟨hk t ht, hq t ht⟩⟩

theorem upper_avoiding_converges (p : CassPhase) {K : ℝ≥0}
    (hlip : LipschitzWith K p.field) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hav : ODE.Avoids γ p.steady) (h0 : p.ks < (γ 0).1) :
    Tendsto γ atTop (𝓝 p.steady) ∧
      StrictAntiOn (fun t => (γ t).1) (Ici 0) ∧
      StrictMonoOn (fun t => (γ t).2) (Ici 0) ∧
      ∀ t, 0 ≤ t → p.ks < (γ t).1 ∧ (γ t).2 ≤ p.qs := by
  have hne : γ 0 ≠ p.steady := by
    intro heq
    have hh := congrArg Prod.fst heq
    change (γ 0).1 = p.ks at hh
    linarith
  have hγcont : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  have hk := ODE.first_stays_above (a := p.steady) hγcont h0
    (ODE.avoids_first_ne hlip p.field_steady p.field_first_axis hd hne hav)
  have hq : ∀ t, 0 ≤ t → (γ t).2 ≤ p.qs := by
    intro t ht
    by_contra hn
    exact hav t ht (Or.inr ⟨hk t ht, lt_of_not_ge hn⟩)
  have hv := ODE.upper_branch_velocity p.cooperative hlip (a := p.steady)
    (fun b hb _ hv => p.upper_cross hb hv)
    (fun b hb _ hv => by
      obtain ⟨ε, hε, he⟩ := p.upper_price_drift hb hv
      exact ⟨ε, hε, fun x hx hqx _ => he x hx hqx⟩)
    (fun b hb _ hv => p.upper_corner_drift hb hv) hd hk hav
  obtain ⟨ha, hm⟩ := ODE.upper_branch_monotone hd hv
  obtain ⟨b, hb, hzero, _, _⟩ := ODE.upper_branch_limit hlip.continuous hd
    (fun t ht => (hk t ht).le) hq ha.antitoneOn hm.monotoneOn
  rw [p.field_zero_unique hzero] at hb
  exact ⟨hb, ha, hm, fun t ht => ⟨hk t ht, hq t ht⟩⟩

end RamseyCassKoopmans.CassPhase
