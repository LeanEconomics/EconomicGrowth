import RamseyCassKoopmans.CassField
import RamseyCassKoopmans.NonescapingDynamics

/-! # Finite economic data for the general Cass shooting argument

This structure records ordinary functions and inequalities on compact intervals.
It contains no trajectory, existence assertion, convergence assumption, or
optimality certificate. Its lemmas establish the phase inequalities needed by
the analytic construction. Marginal product and marginal utility are identified
with actual derivatives when applying this construction to a utility problem.
-/

open Set
open scoped NNReal

namespace RamseyCassKoopmans

structure CassPhase where
  f : ℝ → ℝ
  mp : ℝ → ℝ
  μ : ℝ → ℝ
  C : ℝ → ℝ
  d : ℝ
  m : ℝ
  kl : ℝ
  ku : ℝ
  ks : ℝ
  ca : ℝ
  cb : ℝ
  qs : ℝ
  Q : ℝ
  d_pos : 0 < d
  m_pos : 0 < m
  kl_pos : 0 < kl
  kl_lt : kl < ks
  ku_gt : ks < ku
  ca_pos : 0 < ca
  ca_le_cb : ca ≤ cb
  f_mem : ∀ k ∈ Icc kl ku, f k ∈ Icc ca cb
  f_mono : MonotoneOn f (Icc kl ku)
  mp_pos : ∀ k ∈ Icc kl ku, 0 < mp k
  mp_anti : StrictAntiOn mp (Icc kl ku)
  mp_star : mp ks = d + m
  μ_pos : ∀ c, 0 < c → 0 < μ c
  μ_anti : StrictAntiOn μ (Ioi 0)
  C_mem : ∀ q, C q ∈ Icc ca cb
  C_anti : Antitone C
  inverse : ∀ q, μ (C q) = clip (μ cb) (μ ca) q
  Q_eq : Q = μ ca
  qs_pos : 0 < qs
  qs_lt : qs < Q
  ca_lt_surplus : ca < f ks - m * ks
  qs_eq : qs = μ (f ks - m * ks)

namespace CassPhase

def stock (p : CassPhase) (k : ℝ) : ℝ := clip p.kl p.ku k
def price (p : CassPhase) (q : ℝ) : ℝ := clip 0 p.Q q
def point (p : CassPhase) (x : ℝ × ℝ) : ℝ × ℝ := (p.stock x.1, p.price x.2)
def field (p : CassPhase) : ℝ × ℝ → ℝ × ℝ :=
  cassExtension p.f p.mp p.μ p.C p.d p.m p.kl p.ku 0 p.Q

theorem stock_mem (p : CassPhase) (k : ℝ) : p.stock k ∈ Icc p.kl p.ku :=
  clip_mem (p.kl_lt.trans p.ku_gt).le k

theorem price_mem (p : CassPhase) (q : ℝ) : p.price q ∈ Icc 0 p.Q :=
  clip_mem (p.qs_pos.trans p.qs_lt).le q

theorem stock_pos (p : CassPhase) (k : ℝ) : 0 < p.stock k :=
  p.kl_pos.trans_le (p.stock_mem k).1

theorem output_pos (p : CassPhase) (k : ℝ) : 0 < p.f (p.stock k) :=
  p.ca_pos.trans_le (p.f_mem _ (p.stock_mem k)).1

theorem demand_pos (p : CassPhase) (q : ℝ) : 0 < p.C (p.price q) :=
  p.ca_pos.trans_le (p.C_mem _).1

theorem marginal (p : CassPhase) (x : ℝ × ℝ) :
    p.μ (cassConsumption p.f p.C (p.point x)) =
      max (p.price x.2) (p.μ (p.f (p.stock x.1))) :=
  cass_marginal_utility p.μ_anti.antitoneOn p.ca_pos
    (p.f_mem _ (p.stock_mem _)) (p.C_mem _) (p.inverse _)
    (by rw [← p.Q_eq]; exact (p.price_mem _).2)

theorem cooperative (p : CassPhase) : ODE.Cooperative p.field := by
  apply cass_extension_cooperative (p.kl_lt.trans p.ku_gt).le p.C_anti
  · intro x hx y hy hxy
    exact p.μ_anti.antitoneOn
      (p.ca_pos.trans_le (p.f_mem x hx).1)
      (p.ca_pos.trans_le (p.f_mem y hy).1) (p.f_mono hx hy hxy)
  · exact p.mp_anti.antitoneOn
  · exact fun k hk => (p.μ_pos _ (p.ca_pos.trans_le (p.f_mem k hk).1)).le
  · exact fun k hk => (p.mp_pos k hk).le

theorem stock_lt_star (p : CassPhase) {k : ℝ} (hk : k < p.ks) : p.stock k < p.ks := by
  exact max_lt p.kl_lt ((min_le_right p.ku k).trans_lt hk)

theorem stock_gt_star (p : CassPhase) {k : ℝ} (hk : p.ks < k) : p.ks < p.stock k := by
  exact (lt_min p.ku_gt hk).trans_le (le_max_right _ _)

theorem stock_ge_star (p : CassPhase) {k : ℝ} (hk : p.ks ≤ k) : p.ks ≤ p.stock k := by
  exact (le_min p.ku_gt.le hk).trans (le_max_right _ _)

theorem price_ge_star (p : CassPhase) {q : ℝ} (hq : p.qs ≤ q) : p.qs ≤ p.price q := by
  exact (le_min p.qs_lt.le hq).trans (le_max_right _ _)

theorem price_mono (p : CassPhase) : Monotone p.price := monotone_clip 0 p.Q
theorem stock_mono (p : CassPhase) : Monotone p.stock := monotone_clip p.kl p.ku

theorem mp_above_target (p : CassPhase) {k : ℝ} (hk : k < p.ks) :
    p.d + p.m < p.mp (p.stock k) := by
  rw [← p.mp_star]
  exact p.mp_anti (p.stock_mem k) ⟨p.kl_lt.le, p.ku_gt.le⟩ (p.stock_lt_star hk)

theorem mp_below_target (p : CassPhase) {k : ℝ} (hk : p.ks < k) :
    p.mp (p.stock k) < p.d + p.m := by
  rw [← p.mp_star]
  exact p.mp_anti ⟨p.kl_lt.le, p.ku_gt.le⟩ (p.stock_mem k) (p.stock_gt_star hk)

/-- The price decreases uniformly on every rectangle strictly left of steady
capital and above steady price, including points beyond the artificial clips. -/
theorem lower_price_drift (p : CassPhase) {b : ℝ × ℝ} (hb : b.1 < p.ks) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ × ℝ,
      x.1 ≤ b.1 → p.qs ≤ x.2 → (p.field x).2 ≤ -ε := by
  let ε := (p.mp (p.stock b.1) - (p.d + p.m)) * p.qs
  refine ⟨ε, mul_pos (sub_pos.mpr (p.mp_above_target hb)) p.qs_pos, ?_⟩
  intro x hk hq
  have hmp := p.mp_anti.antitoneOn (p.stock_mem _) (p.stock_mem _) (p.stock_mono hk)
  have hp := p.price_ge_star hq
  have hmpx := p.mp_pos _ (p.stock_mem x.1)
  have hm := mul_le_mul_of_nonneg_right
    (le_max_left (p.price x.2) (p.μ (p.f (p.stock x.1)))) hmpx.le
  have hfactor : (p.mp (p.stock b.1) - (p.d + p.m)) * p.qs ≤
      (p.mp (p.stock x.1) - (p.d + p.m)) * p.price x.2 :=
    mul_le_mul (sub_le_sub_right hmp _) hp p.qs_pos.le
      (by linarith [p.mp_above_target hb])
  change (p.d + p.m) * p.price x.2 -
    max (p.price x.2) (p.μ (p.f (p.stock x.1))) * p.mp (p.stock x.1) ≤ -ε
  dsimp [ε]
  nlinarith

theorem lower_price_negative (p : CassPhase) {x : ℝ × ℝ}
    (hk : x.1 < p.ks) (hq : p.qs ≤ x.2) : (p.field x).2 < 0 := by
  obtain ⟨ε, hε, he⟩ := p.lower_price_drift (b := x) hk
  exact (he x le_rfl hq).trans_lt (neg_neg_of_pos hε)

theorem interior_price (p : CassPhase) {x : ℝ × ℝ}
    (hz : 0 < cassInvestment p.f p.C (p.point x)) :
    p.μ (cassConsumption p.f p.C (p.point x)) = p.price x.2 ∧
      0 < p.price x.2 := by
  have hc : 0 < cassConsumption p.f p.C (p.point x) :=
    cass_consumption_pos (p.output_pos _) (p.demand_pos _)
  have hlt : cassConsumption p.f p.C (p.point x) < p.f (p.stock x.1) :=
    sub_pos.mp hz
  have hμ := p.μ_anti hc (p.output_pos _) hlt
  rw [p.marginal x] at hμ
  have hprice : p.μ (p.f (p.stock x.1)) < p.price x.2 :=
    (lt_max_iff.mp hμ).resolve_right (lt_irrefl _)
  exact ⟨(p.marginal x).trans (max_eq_left hprice.le),
    (p.μ_pos _ (p.output_pos _)).trans hprice⟩

theorem interior_field_price (p : CassPhase) {x : ℝ × ℝ}
    (hz : 0 < cassInvestment p.f p.C (p.point x)) :
    (p.field x).2 = (p.d + p.m - p.mp (p.stock x.1)) * p.price x.2 := by
  have hh := (p.interior_price hz).1
  rw [p.marginal x] at hh
  change (p.d + p.m) * p.price x.2 -
    max (p.price x.2) (p.μ (p.f (p.stock x.1))) * p.mp (p.stock x.1) = _
  rw [hh]
  ring

theorem upper_cross (p : CassPhase) {x : ℝ × ℝ}
    (hk : p.ks < x.1) (hv : 0 ≤ (p.field x).1) : 0 < (p.field x).2 := by
  have hz : 0 < cassInvestment p.f p.C (p.point x) := by
    have hm := mul_pos p.m_pos (p.stock_pos x.1)
    change 0 ≤ cassInvestment p.f p.C (p.point x) - p.m * p.stock x.1 at hv
    linarith
  rw [p.interior_field_price hz]
  exact mul_pos (sub_pos.mpr (p.mp_below_target hk)) (p.interior_price hz).2

theorem investment_mono (p : CassPhase) {x y : ℝ × ℝ}
    (hk : x.1 ≤ y.1) (hq : x.2 ≤ y.2) :
    cassInvestment p.f p.C (p.point x) ≤ cassInvestment p.f p.C (p.point y) := by
  have hf := p.f_mono (p.stock_mem _) (p.stock_mem _) (p.stock_mono hk)
  have hC := p.C_anti (p.price_mono hq)
  change p.f (p.stock x.1) - min (p.C (p.price x.2)) (p.f (p.stock x.1)) ≤
    p.f (p.stock y.1) - min (p.C (p.price y.2)) (p.f (p.stock y.1))
  simp only [min_def]
  split_ifs <;> linarith

theorem upper_price_drift (p : CassPhase) {b : ℝ × ℝ}
    (hb : p.ks < b.1) (hv : 0 ≤ (p.field b).1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ × ℝ,
      b.1 ≤ x.1 → b.2 ≤ x.2 → ε ≤ (p.field x).2 := by
  have hz : 0 < cassInvestment p.f p.C (p.point b) := by
    have hm := mul_pos p.m_pos (p.stock_pos b.1)
    change 0 ≤ cassInvestment p.f p.C (p.point b) - p.m * p.stock b.1 at hv
    linarith
  let ε := (p.d + p.m - p.mp (p.stock b.1)) * p.price b.2
  refine ⟨ε, mul_pos (sub_pos.mpr (p.mp_below_target hb)) (p.interior_price hz).2, ?_⟩
  intro x hk hq
  have hzx := hz.trans_le (p.investment_mono hk hq)
  rw [p.interior_field_price hzx]
  exact mul_le_mul
    (sub_le_sub_left (p.mp_anti.antitoneOn (p.stock_mem _) (p.stock_mem _) (p.stock_mono hk)) _)
    (p.price_mono hq) (p.interior_price hz).2.le
    (sub_pos.mpr (p.mp_below_target (hb.trans_le hk))).le

theorem upper_corner_drift (p : CassPhase) {b : ℝ × ℝ}
    (hb : p.ks < b.1) (hv : (p.field b).2 ≤ 0) :
    (p.field b).1 ≤ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ × ℝ,
      p.ks ≤ x.1 → x.1 ≤ b.1 → x.2 ≤ b.2 → (p.field x).1 ≤ -ε := by
  have hzb : cassInvestment p.f p.C (p.point b) = 0 := by
    by_contra hn
    have hz := lt_of_le_of_ne (cass_investment_nonneg p.f p.C (p.point b)) (Ne.symm hn)
    have hp : 0 < (p.field b).2 := by
      rw [p.interior_field_price hz]
      exact mul_pos (sub_pos.mpr (p.mp_below_target hb)) (p.interior_price hz).2
    linarith
  have hxb : (p.field b).1 = -p.m * p.stock b.1 := by
    change cassInvestment p.f p.C (p.point b) - p.m * p.stock b.1 = _
    rw [hzb]
    ring
  refine ⟨hxb ▸ (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr p.m_pos.le)
    (p.stock_pos b.1).le), p.m * p.ks, mul_pos p.m_pos (p.kl_pos.trans p.kl_lt), ?_⟩
  intro x hstar hk hq
  have hzx : cassInvestment p.f p.C (p.point x) = 0 :=
    le_antisymm (hzb ▸ p.investment_mono hk hq) (cass_investment_nonneg p.f p.C (p.point x))
  change cassInvestment p.f p.C (p.point x) - p.m * p.stock x.1 ≤ -(p.m * p.ks)
  rw [hzx, zero_sub]
  exact neg_le_neg (mul_le_mul_of_nonneg_left (p.stock_ge_star hstar) p.m_pos.le)

end CassPhase
end RamseyCassKoopmans
