import RamseyCassKoopmans.CassConstructedPath

/-! # Consumption monotonicity and eventual interior investment

The result retains corners. Strict consumption monotonicity follows from
`U'(c)=max(q,U'(f(k)))`; it does not differentiate consumption at a switch.
Positive steady replacement investment implies that all corners end in finite
time. No assertion of a single crossing is needed for this conclusion.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.CassPhase

theorem positive_investment_of_nondecreasing_capital
    {f : ℝ → ℝ} {m : ℝ} (a : FeasiblePath f m) (hm : 0 < m)
    (hpos : ∀ t, 0 ≤ t → 0 < a.capital t)
    (hk : MonotoneOn a.capital (Ici 0)) : ∀ t, 0 ≤ t → 0 < a.investment t := by
  intro t ht
  by_contra hz
  have hdneg : a.investment t - m * a.capital t < 0 :=
    sub_neg.mpr ((le_of_not_gt hz).trans_lt (mul_pos hm (hpos t ht)))
  have hneg := ODE.eventually_lt_right_of_deriv_neg (a.dynamics t ht) hdneg
  have hright : ∀ᶠ u in 𝓝[>] t, t < u := self_mem_nhdsWithin
  obtain ⟨u, hu, htu⟩ := (hneg.and hright).exists
  exact not_lt_of_ge (hk ht (ht.trans htu.le) htu.le) hu

theorem production_strictMono (p : CassPhase) (hmp : p.mp = deriv p.f)
    (hf : ∀ k, 0 < k → DifferentiableAt ℝ p.f k) :
    StrictMonoOn p.f (Icc p.kl p.ku) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun k hk => (hf k (p.kl_pos.trans_le hk.1)).continuousAt.continuousWithinAt)
  intro k hk
  rw [← hmp]
  exact p.mp_pos k (interior_subset hk)

theorem consumption_lt_of_coordinates (p : CassPhase)
    (hf : StrictMonoOn p.f (Icc p.kl p.ku)) {x y : ℝ × ℝ}
    (hx : p.point x = x) (hy : p.point y = y)
    (hk : x.1 < y.1) (hq : y.2 < x.2) :
    cassConsumption p.f p.C (p.point x) < cassConsumption p.f p.C (p.point y) := by
  have hxk : p.stock x.1 = x.1 := congrArg Prod.fst hx
  have hyk : p.stock y.1 = y.1 := congrArg Prod.fst hy
  have hxq : p.price x.2 = x.2 := congrArg Prod.snd hx
  have hyq : p.price y.2 = y.2 := congrArg Prod.snd hy
  have hfx : 0 < p.f x.1 := hxk ▸ p.output_pos x.1
  have hfy : 0 < p.f y.1 := hyk ▸ p.output_pos y.1
  have hfm := hf (hxk ▸ p.stock_mem x.1) (hyk ▸ p.stock_mem y.1) hk
  have hμ : p.μ (cassConsumption p.f p.C (p.point y)) <
      p.μ (cassConsumption p.f p.C (p.point x)) := by
    rw [p.marginal y, p.marginal x, hxk, hyk, hxq, hyq]
    exact max_lt_max hq (p.μ_anti hfx hfy hfm)
  by_contra h
  have hle := p.μ_anti.antitoneOn (p.ca_pos.trans_le (p.consumption_mem y).1)
    (p.ca_pos.trans_le (p.consumption_mem x).1) (le_of_not_gt h)
  exact not_le_of_gt hμ hle

theorem consumption_strictMono (p : CassPhase)
    (hf : StrictMonoOn p.f (Icc p.kl p.ku)) {γ : ℝ → ℝ × ℝ}
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t)
    (hk : StrictMonoOn (fun t => (γ t).1) (Ici 0))
    (hq : StrictAntiOn (fun t => (γ t).2) (Ici 0)) :
    StrictMonoOn (fun t => cassConsumption p.f p.C (p.point (γ t))) (Ici 0) := by
  intro s hs t ht hst
  exact p.consumption_lt_of_coordinates hf (hclip s hs) (hclip t ht)
    (hk hs ht hst) (hq hs ht hst)

theorem consumption_strictAnti (p : CassPhase)
    (hf : StrictMonoOn p.f (Icc p.kl p.ku)) {γ : ℝ → ℝ × ℝ}
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t)
    (hk : StrictAntiOn (fun t => (γ t).1) (Ici 0))
    (hq : StrictMonoOn (fun t => (γ t).2) (Ici 0)) :
    StrictAntiOn (fun t => cassConsumption p.f p.C (p.point (γ t))) (Ici 0) := by
  intro s hs t ht hst
  exact p.consumption_lt_of_coordinates hf (hclip t ht) (hclip s hs)
    (hk hs ht hst) (hq hs ht hst)

theorem investment_converges (p : CassPhase) (hC : Continuous p.C)
    (hf : Continuous (p.f ∘ clip p.kl p.ku)) {γ : ℝ → ℝ × ℝ}
    (hlim : Tendsto γ atTop (𝓝 p.steady)) :
    Tendsto (fun t => cassInvestment p.f p.C (p.point (γ t))) atTop (𝓝 (p.m * p.ks)) := by
  have h := (p.investment_continuous hC hf).continuousAt.tendsto.comp hlim
  have hsteady : cassInvestment p.f p.C (p.point p.steady) = p.m * p.ks := by
    change p.f (p.stock p.ks) - cassConsumption p.f p.C (p.point p.steady) = _
    rw [p.stock_steady, p.consumption_steady]
    dsimp [surplus]
    ring
  simpa only [hsteady, Function.comp_def] using h

theorem eventually_positive_investment (p : CassPhase) (hC : Continuous p.C)
    (hf : Continuous (p.f ∘ clip p.kl p.ku)) {γ : ℝ → ℝ × ℝ}
    (hlim : Tendsto γ atTop (𝓝 p.steady)) :
    ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → 0 < cassInvestment p.f p.C (p.point (γ t)) := by
  have hz : 0 < p.m * p.ks := mul_pos p.m_pos (p.kl_pos.trans p.kl_lt)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((p.investment_converges hC hf hlim).eventually (lt_mem_nhds hz))
  exact ⟨max 0 T, le_max_left _ _, fun t ht => hT t ((le_max_right _ _).trans ht)⟩

theorem saving_rate_converges (p : CassPhase) (hC : Continuous p.C)
    (hf : Continuous (p.f ∘ clip p.kl p.ku)) {γ : ℝ → ℝ × ℝ}
    (hlim : Tendsto γ atTop (𝓝 p.steady)) :
    Tendsto (fun t => cassInvestment p.f p.C (p.point (γ t)) / p.f (p.stock (γ t).1))
      atTop (𝓝 (p.m * p.ks / p.f p.ks)) ∧
      0 < p.m * p.ks / p.f p.ks ∧ p.m * p.ks / p.f p.ks < 1 := by
  have houtput : 0 < p.f p.ks := p.stock_steady ▸ p.output_pos p.ks
  have hn : 0 < p.m * p.ks := mul_pos p.m_pos (p.kl_pos.trans p.kl_lt)
  have hden : Tendsto (fun t => p.f (p.stock (γ t).1)) atTop (𝓝 (p.f p.ks)) := by
    have hh := (hf.continuousAt.tendsto.comp hlim.fst_nhds)
    change Tendsto (fun t => p.f (p.stock (γ t).1)) atTop (𝓝 (p.f (p.stock p.ks))) at hh
    rwa [p.stock_steady] at hh
  refine ⟨(p.investment_converges hC hf hlim).div hden houtput.ne', div_pos hn houtput, ?_⟩
  apply (div_lt_one houtput).mpr
  linarith [p.ca_lt_surplus, p.ca_pos]

end RamseyCassKoopmans.CassPhase
