/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import RamseyCassKoopmans.CassCertified

/-!
# The Cass policy function, non-crossing paths, and absolute convergence

The optimal consumption policy `policy P k` is initial consumption on the unique
optimum from `k`. By time consistency (`consumption_eq_policy`) every optimal path
satisfies `c(t) = policy P (k(t))`: the saddle path is the graph of the policy.

Below the steady state every optimal path passes through every higher stock, so
all optimal paths from stocks in `(0, k*)` are time translates of one another
(`exists_shift_of_lt`); the same holds above `k*`. Consequences:

* `policy_strictMono`: consumption is strictly increasing in capital;
* `capital_lt_of_lt`, `consumption_lt_of_lt`: optimal paths of identical economies
  never cross, and the poorer economy consumes strictly less at every date;
* `absolute_convergence`: identical economies converge to each other in capital,
  consumption, and the capital ratio.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

/-- The steady-state consumption `c* = f(k*) - m k*`. -/
noncomputable def cassSteadyConsumption (P : CassPrimitives f U d m) : ℝ :=
  f (cassSteady P) - m * cassSteady P

/-- The certified optimum from a positive stock. -/
noncomputable def optimalPath (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k) :
    FeasiblePath f m :=
  Classical.choose (exists_certified P hk)

theorem optimalPath_spec (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k) :
    ∃ q, (optimalPath P hk).capital 0 = k ∧ CassCertificate f U d m (optimalPath P hk) q :=
  Classical.choose_spec (exists_certified P hk)

/-- Optimal consumption as a function of current capital. -/
noncomputable def policy (P : CassPrimitives f U d m) (k : ℝ) : ℝ :=
  if hk : 0 < k then (optimalPath P hk).consumption 0 else 0

/-- Time consistency: along any certified path, consumption is the policy
evaluated at current capital. -/
theorem consumption_eq_policy (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) {t : ℝ} (ht : 0 ≤ t) :
    a.consumption t = policy P (a.capital t) := by
  have hkt := hc.capital_pos t ht
  obtain ⟨qo, ho0, hoc⟩ := optimalPath_spec P hkt
  have hs := hc.shift P ht
  have heq := (hoc.eq P hs (by simp only [FeasiblePath.shift_capital, add_zero]; exact ho0))
    0 le_rfl
  simp only [policy, hkt, ↓reduceDIte]
  simpa only [FeasiblePath.shift_consumption, add_zero] using heq.2.1

/-- Time consistency for the whole tail: from date `T` on, a certified path is the
optimum from the stock reached. -/
theorem tail_eq_optimalPath (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) {T : ℝ} (hT : 0 ≤ T) :
    ∀ t, 0 ≤ t → a.capital (T + t) = (optimalPath P (hc.capital_pos T hT)).capital t ∧
      a.consumption (T + t) = (optimalPath P (hc.capital_pos T hT)).consumption t := by
  obtain ⟨qo, ho0, hoc⟩ := optimalPath_spec P (hc.capital_pos T hT)
  intro t ht
  have heq := hoc.eq P (hc.shift P hT)
    (by simp only [FeasiblePath.shift_capital, add_zero]; exact ho0) t ht
  exact ⟨heq.1, heq.2.1⟩

theorem policy_steady (P : CassPrimitives f U d m) :
    policy P (cassSteady P) = cassSteadyConsumption P := by
  have hks := (cassSteady_spec P).1
  obtain ⟨q, h0, hc⟩ := optimalPath_spec P hks
  have := ((hc.dynamics P).2.2.2.2 h0 0 le_rfl).2
  simp only [policy, hks, ↓reduceDIte]
  exact this

/-- Below the steady state, an optimal path reaches every higher stock below `k*`
at a positive date. -/
theorem exists_hit_of_lt (P : CassPrimitives f U d m) {a : FeasiblePath f m} {q : ℝ → ℝ}
    (hc : CassCertificate f U d m a q) {k1 : ℝ} (h01 : a.capital 0 < k1)
    (h1s : k1 < cassSteady P) : ∃ τ, 0 < τ ∧ a.capital τ = k1 := by
  obtain ⟨hk, -, -, -, -⟩ := hc.dynamics P
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((hk.eventually (lt_mem_nhds h1s)).and
    (eventually_ge_atTop (0 : ℝ)))
  have hT0 := (hT T le_rfl).2
  obtain ⟨τ, hτ, hτeq⟩ := intermediate_value_Icc hT0
    (a.capital_continuous.mono (fun _ hx => hx.1)) ⟨h01.le, (hT T le_rfl).1.le⟩
  refine ⟨τ, lt_of_le_of_ne hτ.1 ?_, hτeq⟩
  rintro rfl
  exact (ne_of_lt h01) hτeq

/-- Above the steady state, an optimal path reaches every lower stock above `k*`. -/
theorem exists_hit_of_gt (P : CassPrimitives f U d m) {a : FeasiblePath f m} {q : ℝ → ℝ}
    (hc : CassCertificate f U d m a q) {k1 : ℝ} (h01 : k1 < a.capital 0)
    (h1s : cassSteady P < k1) : ∃ τ, 0 < τ ∧ a.capital τ = k1 := by
  obtain ⟨hk, -, -, -, -⟩ := hc.dynamics P
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((hk.eventually (gt_mem_nhds h1s)).and
    (eventually_ge_atTop (0 : ℝ)))
  have hT0 := (hT T le_rfl).2
  obtain ⟨τ, hτ, hτeq⟩ := intermediate_value_Icc' hT0
    (a.capital_continuous.mono (fun _ hx => hx.1)) ⟨(hT T le_rfl).1.le, h01.le⟩
  refine ⟨τ, lt_of_le_of_ne hτ.1 ?_, hτeq⟩
  rintro rfl
  exact (ne_of_gt h01) hτeq

/-- On either side of the steady state, optimal paths are time translates: the path
from the stock nearer to `k*` is the tail of the path from the stock farther away. -/
theorem exists_shift_of_between (P : CassPrimitives f U d m) {a b : FeasiblePath f m}
    {qa qb : ℝ → ℝ} (ha : CassCertificate f U d m a qa) (hb : CassCertificate f U d m b qb)
    (hbetween : (a.capital 0 < b.capital 0 ∧ b.capital 0 < cassSteady P) ∨
      (cassSteady P < b.capital 0 ∧ b.capital 0 < a.capital 0)) :
    ∃ τ, 0 < τ ∧ ∀ t, 0 ≤ t → b.capital t = a.capital (τ + t) ∧
      b.consumption t = a.consumption (τ + t) := by
  obtain ⟨τ, hτ, hτeq⟩ : ∃ τ, 0 < τ ∧ a.capital τ = b.capital 0 := by
    rcases hbetween with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact exists_hit_of_lt P ha h1 h2
    · exact exists_hit_of_gt P ha h2 h1
  refine ⟨τ, hτ, fun t ht => ?_⟩
  have heq := ha.shift P hτ.le |>.eq P hb
    (by simp only [FeasiblePath.shift_capital, add_zero]; exact hτeq) t ht
  exact ⟨heq.1, heq.2.1⟩

/-- Optimal paths of identical economies never cross. -/
theorem capital_lt_of_lt (P : CassPrimitives f U d m) {a b : FeasiblePath f m}
    {qa qb : ℝ → ℝ} (ha : CassCertificate f U d m a qa) (hb : CassCertificate f U d m b qb)
    (h0 : a.capital 0 < b.capital 0) {t : ℝ} (ht : 0 ≤ t) : a.capital t < b.capital t := by
  set ks := cassSteady P
  obtain ⟨-, -, habelow, -, haconst⟩ := ha.dynamics P
  obtain ⟨-, -, -, hbabove, hbconst⟩ := hb.dynamics P
  obtain ⟨hab1, -⟩ := ha.capital_bounds P
  obtain ⟨-, hbb2⟩ := hb.capital_bounds P
  rcases lt_trichotomy (b.capital 0) ks with h1 | h1 | h1
  · -- both below: `b` is a tail of `a`
    obtain ⟨τ, hτ, hshift⟩ := exists_shift_of_between P ha hb (Or.inl ⟨h0, h1⟩)
    rw [(hshift t ht).1]
    exact (habelow (h0.trans h1)).1 ht (by simp only [mem_Ici]; linarith) (by linarith)
  · rw [(hbconst h1 t ht).1]
    exact ((hab1 (lt_of_lt_of_eq h0 h1)) t ht).1
  · rcases lt_trichotomy (a.capital 0) ks with h2 | h2 | h2
    · exact ((hab1 h2) t ht).1.trans ((hbb2 h1) t ht).1
    · rw [(haconst h2 t ht).1]
      exact ((hbb2 h1) t ht).1
    · -- both above: `a` is a tail of `b`
      obtain ⟨τ, hτ, hshift⟩ := exists_shift_of_between P hb ha (Or.inr ⟨h2, h0⟩)
      rw [(hshift t ht).1]
      exact (hbabove h1).1 ht (by simp only [mem_Ici]; linarith) (by linarith)

/-- The optimal consumption policy is strictly increasing in capital. -/
theorem policy_strictMono (P : CassPrimitives f U d m) : StrictMonoOn (policy P) (Ioi 0) := by
  intro k0 hk0 k1 hk1 h01
  have hk0' : (0 : ℝ) < k0 := hk0
  have hk1' : (0 : ℝ) < k1 := hk1
  obtain ⟨qa, ha0, ha⟩ := optimalPath_spec P hk0'
  obtain ⟨qb, hb0, hb⟩ := optimalPath_spec P hk1'
  set a := optimalPath P hk0'
  set b := optimalPath P hk1'
  have hpa : policy P k0 = a.consumption 0 := by simp only [policy, hk0', ↓reduceDIte, a]
  have hpb : policy P k1 = b.consumption 0 := by simp only [policy, hk1', ↓reduceDIte, b]
  rw [hpa, hpb]
  set ks := cassSteady P
  obtain ⟨-, -, habelow, -, -⟩ := ha.dynamics P
  obtain ⟨-, -, -, hbabove, hbconst⟩ := hb.dynamics P
  obtain ⟨hab1, -⟩ := ha.capital_bounds P
  obtain ⟨-, hbb2⟩ := hb.capital_bounds P
  have hh0 : a.capital 0 < b.capital 0 := by rw [ha0, hb0]; exact h01
  rcases lt_trichotomy (b.capital 0) ks with h1 | h1 | h1
  · obtain ⟨τ, hτ, hshift⟩ := exists_shift_of_between P ha hb (Or.inl ⟨hh0, h1⟩)
    rw [(hshift 0 le_rfl).2, add_zero]
    exact (habelow (hh0.trans h1)).2 (mem_Ici.mpr le_rfl) hτ.le hτ
  · rw [(hbconst h1 0 le_rfl).2]
    exact ((hab1 (lt_of_lt_of_eq hh0 h1)) 0 le_rfl).2
  · rcases lt_trichotomy (a.capital 0) ks with h2 | h2 | h2
    · exact ((hab1 h2) 0 le_rfl).2.trans ((hbb2 h1) 0 le_rfl).2
    · obtain ⟨-, -, -, -, haconst⟩ := ha.dynamics P
      rw [(haconst h2 0 le_rfl).2]
      exact ((hbb2 h1) 0 le_rfl).2
    · obtain ⟨τ, hτ, hshift⟩ := exists_shift_of_between P hb ha (Or.inr ⟨h2, hh0⟩)
      rw [(hshift 0 le_rfl).2, add_zero]
      exact (hbabove h1).2 (mem_Ici.mpr le_rfl) hτ.le hτ

/-- The poorer economy consumes strictly less at every date. -/
theorem consumption_lt_of_lt (P : CassPrimitives f U d m) {a b : FeasiblePath f m}
    {qa qb : ℝ → ℝ} (ha : CassCertificate f U d m a qa) (hb : CassCertificate f U d m b qb)
    (h0 : a.capital 0 < b.capital 0) {t : ℝ} (ht : 0 ≤ t) :
    a.consumption t < b.consumption t := by
  rw [consumption_eq_policy P ha ht, consumption_eq_policy P hb ht]
  exact policy_strictMono P (ha.capital_pos t ht) (hb.capital_pos t ht)
    (capital_lt_of_lt P ha hb h0 ht)

/-- Absolute convergence: two identical economies converge to each other in capital,
in consumption, and in the capital ratio, whatever their initial stocks. -/
theorem absolute_convergence (P : CassPrimitives f U d m) {a b : FeasiblePath f m}
    {qa qb : ℝ → ℝ} (ha : CassCertificate f U d m a qa) (hb : CassCertificate f U d m b qb) :
    Tendsto (fun t => b.capital t - a.capital t) atTop (𝓝 0) ∧
      Tendsto (fun t => b.consumption t - a.consumption t) atTop (𝓝 0) ∧
      Tendsto (fun t => b.capital t / a.capital t) atTop (𝓝 1) := by
  obtain ⟨hak, hac, -⟩ := ha.dynamics P
  obtain ⟨hbk, hbc, -⟩ := hb.dynamics P
  have hks := (cassSteady_spec P).1
  refine ⟨by simpa only [sub_self] using hbk.sub hak, by simpa only [sub_self] using hbc.sub hac,
    ?_⟩
  have := hbk.div hak (ne_of_gt hks)
  rw [div_self (ne_of_gt hks)] at this
  exact this

end RamseyCassKoopmans
