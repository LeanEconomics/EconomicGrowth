import RamseyCassKoopmans.CassPhase

/-! # The equilibrium and the direction of crossing its capital axis -/

open Set

namespace RamseyCassKoopmans.CassPhase

def steady (p : CassPhase) : ℝ × ℝ := (p.ks, p.qs)
def surplus (p : CassPhase) : ℝ := p.f p.ks - p.m * p.ks

theorem ks_pos (p : CassPhase) : 0 < p.ks := p.kl_pos.trans p.kl_lt

theorem surplus_pos (p : CassPhase) : 0 < p.surplus := p.ca_pos.trans p.ca_lt_surplus

theorem surplus_lt_output (p : CassPhase) : p.surplus < p.f p.ks := by
  have hp := mul_pos p.m_pos p.ks_pos
  dsimp [surplus]
  linarith

theorem surplus_lt_cb (p : CassPhase) : p.surplus < p.cb :=
  p.surplus_lt_output.trans_le (p.f_mem _ ⟨p.kl_lt.le, p.ku_gt.le⟩).2

theorem bottom_price_lt (p : CassPhase) : p.μ p.cb < p.qs := by
  rw [p.qs_eq]
  exact p.μ_anti p.surplus_pos (p.surplus_pos.trans p.surplus_lt_cb) p.surplus_lt_cb

theorem stock_steady (p : CassPhase) : p.stock p.ks = p.ks :=
  clip_eq ⟨p.kl_lt.le, p.ku_gt.le⟩

theorem price_steady (p : CassPhase) : p.price p.qs = p.qs :=
  clip_eq ⟨p.qs_pos.le, p.qs_lt.le⟩

theorem price_lt_steady (p : CassPhase) {q : ℝ} (hq : q < p.qs) : p.price q < p.qs :=
  max_lt p.qs_pos ((min_le_right _ _).trans_lt hq)

theorem price_gt_steady (p : CassPhase) {q : ℝ} (hq : p.qs < q) : p.qs < p.price q :=
  (lt_min p.qs_lt hq).trans_le (le_max_right _ _)

theorem inverse_price (p : CassPhase) (q : ℝ) :
    p.μ (p.C (p.price q)) = max (p.μ p.cb) (p.price q) := by
  rw [p.inverse, clip, ← p.Q_eq, min_eq_right (p.price_mem q).2]

theorem demand_at_steady (p : CassPhase) : p.C p.qs = p.surplus := by
  apply p.μ_anti.injOn (p.ca_pos.trans_le (p.C_mem _).1) p.surplus_pos
  have h := p.inverse_price p.qs
  rw [p.price_steady, max_eq_right p.bottom_price_lt.le] at h
  exact h.trans p.qs_eq

theorem demand_gt_surplus (p : CassPhase) {q : ℝ} (hq : q < p.qs) :
    p.surplus < p.C (p.price q) := by
  have hμ : p.μ (p.C (p.price q)) < p.qs := by
    rw [p.inverse_price]
    exact max_lt p.bottom_price_lt (p.price_lt_steady hq)
  by_contra hn
  have h := p.μ_anti.antitoneOn (p.demand_pos q) p.surplus_pos (le_of_not_gt hn)
  rw [surplus, ← p.qs_eq] at h
  linarith

theorem demand_lt_surplus (p : CassPhase) {q : ℝ} (hq : p.qs < q) :
    p.C (p.price q) < p.surplus := by
  have hμ : p.qs < p.μ (p.C (p.price q)) := by
    rw [p.inverse_price]
    exact (p.price_gt_steady hq).trans_le (le_max_right _ _)
  by_contra hn
  have h := p.μ_anti.antitoneOn p.surplus_pos (p.demand_pos q) (le_of_not_gt hn)
  rw [surplus, ← p.qs_eq] at h
  linarith

theorem field_steady (p : CassPhase) : p.field p.steady = 0 := by
  have hcons : cassConsumption p.f p.C (p.point p.steady) = p.surplus := by
    change min (p.C (p.price p.qs)) (p.f (p.stock p.ks)) = _
    rw [p.price_steady, p.stock_steady, p.demand_at_steady, min_eq_left p.surplus_lt_output.le]
  have hmu : p.μ (p.f p.ks) < p.qs := by
    rw [p.qs_eq]
    exact p.μ_anti p.surplus_pos (p.surplus_pos.trans p.surplus_lt_output) p.surplus_lt_output
  apply Prod.ext
  · change p.f (p.stock p.ks) - cassConsumption p.f p.C (p.point p.steady) -
      p.m * p.stock p.ks = 0
    rw [hcons, p.stock_steady]
    dsimp [surplus]
    ring
  · change (p.d + p.m) * p.price p.qs -
      max (p.price p.qs) (p.μ (p.f (p.stock p.ks))) * p.mp (p.stock p.ks) = 0
    rw [p.price_steady, p.stock_steady, p.mp_star, max_eq_left hmu.le]
    ring

theorem field_first_axis (p : CassPhase) (x : ℝ × ℝ) (hk : x.1 = p.ks) :
    (x.2 < p.qs → (p.field x).1 < 0) ∧ (p.qs < x.2 → 0 < (p.field x).1) := by
  have hs : p.stock x.1 = p.ks := hk ▸ p.stock_steady
  constructor
  · intro hq
    have hmin := lt_min (p.demand_gt_surplus hq) p.surplus_lt_output
    change p.f (p.stock x.1) - min (p.C (p.price x.2)) (p.f (p.stock x.1)) -
      p.m * p.stock x.1 < 0
    rw [hs]
    dsimp [surplus] at hmin
    linarith
  · intro hq
    have hlt := p.demand_lt_surplus hq
    change 0 < p.f (p.stock x.1) - min (p.C (p.price x.2)) (p.f (p.stock x.1)) -
      p.m * p.stock x.1
    rw [hs, min_eq_left (hlt.trans p.surplus_lt_output).le]
    dsimp [surplus] at hlt
    linarith

/-- The clipped field has exactly one equilibrium, even outside its clipping
rectangle. Hence a limiting trajectory cannot converge to an artificial root. -/
theorem field_zero_unique (p : CassPhase) {x : ℝ × ℝ} (hv : p.field x = 0) :
    x = p.steady := by
  have h1 := congrArg Prod.fst hv
  have h2 := congrArg Prod.snd hv
  change cassInvestment p.f p.C (p.point x) - p.m * p.stock x.1 = 0 at h1
  change (p.field x).2 = 0 at h2
  have hz : 0 < cassInvestment p.f p.C (p.point x) := by
    have hm := mul_pos p.m_pos (p.stock_pos x.1)
    linarith
  rw [p.interior_field_price hz] at h2
  have hmp : p.mp (p.stock x.1) = p.d + p.m := by
    have hh := (mul_eq_zero.mp h2).resolve_right (ne_of_gt (p.interior_price hz).2)
    linarith
  have hstock : p.stock x.1 = p.ks := p.mp_anti.injOn (p.stock_mem _)
    ⟨p.kl_lt.le, p.ku_gt.le⟩ (hmp.trans p.mp_star.symm)
  have hk : x.1 = p.ks := by
    rcases lt_trichotomy x.1 p.ks with h | h | h
    · exact False.elim (lt_irrefl _ (hstock ▸ p.stock_lt_star h))
    · exact h
    · exact False.elim (lt_irrefl _ (hstock ▸ p.stock_gt_star h))
  have hc : cassConsumption p.f p.C (p.point x) = p.surplus := by
    change p.f (p.stock x.1) - cassConsumption p.f p.C (p.point x) -
      p.m * p.stock x.1 = 0 at h1
    rw [hstock] at h1
    dsimp [surplus]
    linarith
  have hp : p.price x.2 = p.qs := by
    have hh := (p.interior_price hz).1
    rw [hc, surplus, ← p.qs_eq] at hh
    exact hh.symm
  have hq : x.2 = p.qs := by
    rcases lt_trichotomy x.2 p.qs with h | h | h
    · exact False.elim (lt_irrefl _ (hp ▸ p.price_lt_steady h))
    · exact h
    · exact False.elim (lt_irrefl _ (hp ▸ p.price_gt_steady h))
  exact Prod.ext hk hq

end RamseyCassKoopmans.CassPhase
