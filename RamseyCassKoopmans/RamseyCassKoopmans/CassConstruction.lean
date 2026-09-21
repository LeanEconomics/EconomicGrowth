import RamseyCassKoopmans.CassUnclipping

/-! # A constructed trajectory for finite, explicitly checkable economic data

The quantitative price bound removes the price clip; monotonicity removes the
capital clip. The resulting global future trajectory satisfies the original
Cass field. Neither a trajectory nor its convergence is an input.
-/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.CassPhase

theorem demand_inverse (p : CassPhase) {c : ℝ} (hc : c ∈ Icc p.ca p.cb) :
    p.C (p.μ c) = c := by
  have hcpos := p.ca_pos.trans_le hc.1
  apply p.μ_anti.injOn (p.ca_pos.trans_le (p.C_mem _).1) hcpos
  rw [p.inverse]
  exact clip_eq ⟨p.μ_anti.antitoneOn hcpos (hcpos.trans_le hc.2) hc.2,
    p.μ_anti.antitoneOn p.ca_pos hcpos hc.1⟩

theorem finite_price_capital_drift (p : CassPhase)
    (hnet : MonotoneOn (fun k => p.f k - p.m * k) (Icc p.kl p.ks))
    {c : ℝ} (hc : c ∈ Icc p.ca p.cb)
    (x : ℝ × ℝ) (hk : x.1 ≤ p.ks) (hq : p.μ c ≤ x.2) :
    p.f p.kl - p.m * p.kl - c ≤ (p.field x).1 := by
  have hcprice : p.μ c ≤ p.Q := by
    rw [p.Q_eq]
    exact p.μ_anti.antitoneOn p.ca_pos (p.ca_pos.trans_le hc.1) hc.1
  have hprice : p.μ c ≤ p.price x.2 :=
    (le_min hcprice hq).trans (le_max_right _ _)
  have hC : p.C (p.price x.2) ≤ c := by
    simpa only [p.demand_inverse hc] using p.C_anti hprice
  have hstock : p.stock x.1 ≤ p.ks := max_le p.kl_lt.le ((min_le_right _ _).trans hk)
  have hn := hnet ⟨le_rfl, p.kl_lt.le⟩ ⟨(p.stock_mem _).1, hstock⟩ (p.stock_mem _).1
  have hcons := (min_le_left (p.C (p.price x.2)) (p.f (p.stock x.1))).trans hC
  change _ ≤ p.f (p.stock x.1) - min (p.C (p.price x.2)) (p.f (p.stock x.1)) -
    p.m * p.stock x.1
  linarith

/-- The original, unclipped capital and shadow-price trajectory is constructed
for any initial stock in the stated box. All extra conditions are finite scalar
inequalities or regularity of ordinary functions. -/
theorem exists_convergent_trajectory (p : CassPhase) (hb : BoundedLip p.field)
    (hnet : MonotoneOn (fun k => p.f k - p.m * k) (Icc p.kl p.ks))
    {c T k0 : ℝ} (hc : c ∈ Icc p.ca p.cb)
    (hgap : c < p.f p.kl - p.m * p.kl) (hT : 0 ≤ T)
    (hlarge : p.μ c * Real.exp (p.mp p.kl * T) ≤ p.Q)
    (htime : p.ks - k0 ≤ (p.f p.kl - p.m * p.kl - c) * T)
    (hk0 : k0 ∈ Icc p.kl p.ku) :
    ∃ γ : ℝ → ℝ × ℝ, (γ 0).1 = k0 ∧
      (∀ t, HasDerivAt γ (p.field (γ t)) t) ∧
      (∀ t, 0 ≤ t → p.point (γ t) = γ t ∧ 0 < (γ t).2) ∧
      Tendsto γ atTop (𝓝 p.steady) ∧
      (k0 < p.ks → StrictMonoOn (fun t => (γ t).1) (Ici 0) ∧
        StrictAntiOn (fun t => (γ t).2) (Ici 0)) ∧
      (p.ks < k0 → StrictAntiOn (fun t => (γ t).1) (Ici 0) ∧
        StrictMonoOn (fun t => (γ t).2) (Ici 0)) ∧
      (k0 = p.ks → ∀ t, γ t = p.steady) := by
  obtain ⟨K, B, hlip, hbound⟩ := hb
  rcases lt_trichotomy k0 p.ks with hbelow | heq | habove
  · obtain ⟨γ, h0, hd, hav⟩ := p.exists_avoiding_solution ⟨K, B, hlip, hbound⟩ hnet (hc.1.trans_lt hgap) k0
    have hk : (γ 0).1 < p.ks := h0 ▸ hbelow
    obtain ⟨hlim, hm, ha, _⟩ := p.lower_avoiding_converges hlip hd hav hk
    have hq0 : (γ 0).2 < p.Q := p.lower_initial_price_lt_top hlip hd hav hk hT hlarge
      (h0 ▸ htime) (fun x _ hx hq => p.finite_price_capital_drift hnet hc x hx hq)
    exact ⟨γ, h0, hd, p.lower_clips_inactive hlip hd hav hk (h0 ▸ hk0.1) hq0.le,
      hlim, (fun _ => ⟨hm, ha⟩), (fun h => False.elim (lt_asymm hbelow h)),
      fun h => False.elim (lt_irrefl _ (h ▸ hbelow))⟩
  · refine ⟨fun _ => p.steady, heq.symm, ?_, ?_, tendsto_const_nhds, ?_, ?_, fun _ _ => rfl⟩
    · intro t
      simpa only [p.field_steady] using hasDerivAt_const t p.steady
    · intro t _
      exact ⟨Prod.ext p.stock_steady p.price_steady, p.qs_pos⟩
    · intro h
      exact False.elim (lt_irrefl _ (heq ▸ h))
    · intro h
      exact False.elim (lt_irrefl _ (heq ▸ h))
  · obtain ⟨γ, h0, hd, hav⟩ := p.exists_avoiding_solution ⟨K, B, hlip, hbound⟩ hnet (hc.1.trans_lt hgap) k0
    have hk : p.ks < (γ 0).1 := h0 ▸ habove
    obtain ⟨hlim, ha, hm, _⟩ := p.upper_avoiding_converges hlip hd hav hk
    exact ⟨γ, h0, hd, p.upper_clips_inactive hlip hd hav hk (h0 ▸ hk0.2),
      hlim, (fun h => False.elim (lt_asymm habove h)), (fun _ => ⟨ha, hm⟩),
      fun h => False.elim (lt_irrefl _ (h ▸ habove))⟩

end RamseyCassKoopmans.CassPhase
