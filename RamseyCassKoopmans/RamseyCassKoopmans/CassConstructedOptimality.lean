import RamseyCassKoopmans.CassConstructedPath
import RamseyCassKoopmans.SignedWelfare
import RamseyCassKoopmans.CapacityFromInada
import RamseyCassKoopmans.CassCertificateUniqueness
import RamseyCassKoopmans.CassQualitative
import RamseyCassKoopmans.AsymptoticOptimality

/-! # Optimality of the constructed general Cass path -/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans

theorem CassPhase.constructed_optimal (p : CassPhase) (U : ℝ → ℝ)
    (hmp : p.mp = deriv p.f) (hμ : p.μ = deriv U)
    (hfconc : ConcaveOn ℝ (Ici 0) p.f) (hUconc : ConcaveOn ℝ (Ioi 0) U)
    (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ p.f k)
    (hUdiff : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv p.f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hC : Continuous p.C) (hf : Continuous (p.f ∘ clip p.kl p.ku))
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t)
    (hlim : Tendsto γ atTop (𝓝 p.steady))
    {K : ℝ} (hk0 : (γ 0).1 ≤ K) (hcapacity : ∀ k, K ≤ k → p.f k ≤ p.m * k) :
    ∃ J, IsCassOptimal U p.d (p.feasiblePath γ hC hf hd hclip) J := by
  let a := p.feasiblePath γ hC hf hd hclip
  have hUcont : ContinuousOn U (Ioi 0) :=
    fun c hc => (hUdiff c hc).continuousAt.continuousWithinAt
  obtain ⟨J, hJ⟩ := exists_hasWelfare_of_compact_consumption U a.consumption p.d_pos p.ca_le_cb
    (hUcont.mono (fun _ hx => p.ca_pos.trans_le hx.1)) a.consumption_continuous
    (fun t _ => p.consumption_mem (γ t))
  refine ⟨J, ?_⟩
  have hcostate := p.path_costate hd hclip
  rw [hmp, hμ] at hcostate
  have hwedge := p.path_wedge_slack hclip
  rw [hμ] at hwedge
  apply cass_certificate_is_optimal p.f U (fun t => (γ t).2) p.d p.m K J a
    hfconc hUconc hUcont hfdiff hUdiff hfprime hUprime
    (p.path_capital_pos γ hclip)
  · intro t ht
    have hq := congrArg Prod.snd (hclip t ht)
    exact hq ▸ (p.price_mem (γ t).2).1
  · exact hcostate
  · exact fun t ht => (hwedge t ht).1
  · exact fun t ht => (hwedge t ht).2
  · exact fun t _ => cass_investment_nonneg p.f p.C (p.point (γ t))
  · exact hcapacity
  · exact hk0
  · exact hJ
  · exact Terminal.discounted_price_tendsto_zero p.d_pos hlim.snd_nhds

theorem CassPhase.constructed_unique (p : CassPhase) (U : ℝ → ℝ)
    (hmp : p.mp = deriv p.f) (hμ : p.μ = deriv U)
    (hfconc : StrictConcaveOn ℝ (Ici 0) p.f) (hUconc : StrictConcaveOn ℝ (Ioi 0) U)
    (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ p.f k)
    (hUdiff : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv p.f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hC : Continuous p.C) (hf : Continuous (p.f ∘ clip p.kl p.ku))
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t)
    (hlim : Tendsto γ atTop (𝓝 p.steady))
    {K Ja Jb : ℝ} (hk0 : (γ 0).1 ≤ K) (hcapacity : ∀ k, K ≤ k → p.f k ≤ p.m * k)
    (ha : HasWelfare U (discount p.d) (p.feasiblePath γ hC hf hd hclip).consumption Ja)
    (b : FeasiblePath p.f p.m) (hbinv : b.NonnegativeInvestment)
    (hi : (γ 0).1 = b.capital 0) (hb : HasWelfare U (discount p.d) b.consumption Jb)
    (heq : Jb = Ja) :
    ∀ t, 0 ≤ t → b.capital t = (γ t).1 ∧
      b.consumption t = cassConsumption p.f p.C (p.point (γ t)) ∧
      b.investment t = cassInvestment p.f p.C (p.point (γ t)) := by
  let a := p.feasiblePath γ hC hf hd hclip
  have hUcont : ContinuousOn U (Ioi 0) :=
    fun c hc => (hUdiff c hc).continuousAt.continuousWithinAt
  have hcostate := p.path_costate hd hclip
  rw [hmp, hμ] at hcostate
  have hwedge := p.path_wedge_slack hclip
  rw [hμ] at hwedge
  apply cass_certificate_unique p.f U (fun t => (γ t).2) p.d p.m K Ja Jb a b
    hfconc hUconc hUcont hfdiff hUdiff hfprime hUprime (p.path_capital_pos γ hclip)
  · intro t ht
    rw [← hμ]
    exact p.μ_pos _ (a.consumption_pos t ht)
  · exact hcostate
  · exact fun t ht => (hwedge t ht).1
  · exact fun t ht => (hwedge t ht).2
  · exact hbinv
  · exact hi
  · exact hcapacity
  · exact hk0
  · exact ha
  · exact hb
  · exact Terminal.discounted_price_tendsto_zero p.d_pos hlim.snd_nhds
  · exact heq

/-- Every feasible Cass competitor is compared, without an assumption that its
discounted objective has a finite real limit. -/
theorem CassPhase.constructed_dominates (p : CassPhase) (U : ℝ → ℝ)
    (hmp : p.mp = deriv p.f) (hμ : p.μ = deriv U)
    (hfconc : ConcaveOn ℝ (Ici 0) p.f) (hUconc : ConcaveOn ℝ (Ioi 0) U)
    (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ p.f k)
    (hUdiff : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv p.f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hC : Continuous p.C) (hf : Continuous (p.f ∘ clip p.kl p.ku))
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t)
    (hlim : Tendsto γ atTop (𝓝 p.steady))
    {K : ℝ} (hk0 : (γ 0).1 ≤ K) (hcapacity : ∀ k, K ≤ k → p.f k ≤ p.m * k)
    (b : FeasiblePath p.f p.m) (hb : b.NonnegativeInvestment) (hi : (γ 0).1 = b.capital 0) :
    AsymptoticallyDominates U (discount p.d)
      (p.feasiblePath γ hC hf hd hclip).consumption b.consumption := by
  let a := p.feasiblePath γ hC hf hd hclip
  have hUcont : ContinuousOn U (Ioi 0) :=
    fun c hc => (hUdiff c hc).continuousAt.continuousWithinAt
  have hcostate := p.path_costate hd hclip
  rw [hmp, hμ] at hcostate
  have hmu : ∀ t, 0 ≤ t → 0 ≤ deriv U (a.consumption t) := by
    intro t ht
    rw [← hμ]
    exact (p.μ_pos _ (a.consumption_pos t ht)).le
  let v := cassSupportingPrices p.f U (fun t => (γ t).2) p.d p.m a
    hfconc hUconc hUcont hfdiff hUdiff hfprime hUprime (p.path_capital_pos γ hclip) hmu hcostate
  have hw := p.path_wedge_slack hclip
  rw [hμ] at hw
  have halloc : AllocationComparison v b := by
    apply allocation_of_cass v
    · intro t ht
      exact mul_le_mul_of_nonneg_left (hw t ht).1 (discount_pos p.d t).le
    · intro t ht
      change (discount p.d t * (γ t).2 - discount p.d t * deriv U (a.consumption t)) *
        a.investment t = 0
      rw [← mul_sub, mul_assoc]
      change discount p.d t * (((γ t).2 - deriv U
        (cassConsumption p.f p.C (p.point (γ t)))) * cassInvestment p.f p.C (p.point (γ t))) = 0
      rw [(hw t ht).2, mul_zero]
    · exact hb
  apply asymptotic_dominance_of_terminal_limit v b halloc hi
  exact Terminal.terminal_tendsto_zero_of_bounded_capital
    (Terminal.discounted_price_tendsto_zero p.d_pos hlim.snd_nhds)
    (fun t ht => ⟨a.capital_nonneg t ht, a.capital_le_capacity hcapacity hk0 t ht⟩)
    (fun t ht => ⟨b.capital_nonneg t ht, b.capital_le_capacity hcapacity (hi ▸ hk0) t ht⟩)

theorem CassConstructionData.exists_optimal
    {f U : ℝ → ℝ} {d m k0 ks : ℝ}
    (D : CassConstructionData f (deriv f) (deriv U) d m k0 ks)
    (hfconc : StrictConcaveOn ℝ (Ici 0) f) (hUconc : StrictConcaveOn ℝ (Ioi 0) U)
    (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hUdiff : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    {K : ℝ} (hkK : k0 ≤ K) (hcapacity : ∀ k, K ≤ k → f k ≤ m * k) :
    ∃ a : FeasiblePath f m, ∃ J : ℝ, a.capital 0 = k0 ∧ IsCassOptimal U d a J ∧
      Tendsto a.capital atTop (𝓝 ks) ∧
      Tendsto a.consumption atTop (𝓝 (f ks - m * ks)) ∧
      (k0 < ks → StrictMonoOn a.capital (Ici 0)) ∧
      (ks < k0 → StrictAntiOn a.capital (Ici 0)) ∧
      (k0 < ks → StrictMonoOn a.consumption (Ici 0)) ∧
      (ks < k0 → StrictAntiOn a.consumption (Ici 0)) ∧
      (k0 < ks → ∀ t, 0 ≤ t → 0 < a.investment t) ∧
      (k0 = ks → ∀ t, a.capital t = ks ∧ a.consumption t = f ks - m * ks ∧
        a.investment t = m * ks) ∧
      (∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → 0 < a.investment t) ∧
      (∀ b : FeasiblePath f m, b.NonnegativeInvestment → b.capital 0 = k0 →
        AsymptoticallyDominates U (discount d) a.consumption b.consumption) ∧
      (∀ (b : FeasiblePath f m) (Jb : ℝ), IsCassOptimal U d b Jb → b.capital 0 = k0 →
        Jb = J ∧ ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
          b.consumption t = a.consumption t ∧ b.investment t = a.investment t) := by
  let p := D.phase
  obtain ⟨_, _, hCLip, _⟩ := D.demand_bounded
  obtain ⟨_, _, hFLip, _⟩ := D.production_bounded
  obtain ⟨γ, h0, hd, hclipq, hlim, hbelow, habove, hconstant⟩ := p.exists_convergent_trajectory
    D.bounded D.net_mono D.consumption_mem D.net_gap D.time_nonneg D.price_large
    D.time_large D.initial_mem
  have hclip := fun t ht => (hclipq t ht).1
  have hprod : p.f = f := D.production_eq
  have hmul : p.μ = deriv U := D.marginalUtility_eq
  have hmp : p.mp = deriv p.f := by rw [hprod]; exact D.marginalProduct_eq
  have hdil : p.m = m := D.dilution_eq
  have hdis : p.d = d := D.discount_eq
  have hsteady : p.ks = ks := D.steady_eq
  have hfconc' : StrictConcaveOn ℝ (Ici 0) p.f := hprod ▸ hfconc
  have hfdiff' : ∀ k, 0 < k → DifferentiableAt ℝ p.f k := hprod ▸ hfdiff
  have hfprime' : ContinuousOn (deriv p.f) (Ioi 0) := hprod ▸ hfprime
  have hcapacity' : ∀ k, K ≤ k → p.f k ≤ p.m * k := by simpa only [hprod, hdil] using hcapacity
  obtain ⟨J, hJ⟩ :=
    p.constructed_optimal U hmp hmul hfconc'.concaveOn hUconc.concaveOn
      hfdiff' hUdiff hfprime' hUprime
    hCLip.continuous hFLip.continuous hd hclip hlim (h0 ▸ hkK) hcapacity'
  let a := p.feasiblePath γ hCLip.continuous hFLip.continuous hd hclip
  have hresult : ∃ a : FeasiblePath p.f p.m, ∃ J : ℝ,
      a.capital 0 = k0 ∧ IsCassOptimal U p.d a J ∧
      Tendsto a.capital atTop (𝓝 p.ks) ∧
      Tendsto a.consumption atTop (𝓝 (p.f p.ks - p.m * p.ks)) ∧
      (k0 < p.ks → StrictMonoOn a.capital (Ici 0)) ∧
      (p.ks < k0 → StrictAntiOn a.capital (Ici 0)) ∧
      (k0 < p.ks → StrictMonoOn a.consumption (Ici 0)) ∧
      (p.ks < k0 → StrictAntiOn a.consumption (Ici 0)) ∧
      (k0 < p.ks → ∀ t, 0 ≤ t → 0 < a.investment t) ∧
      (k0 = p.ks → ∀ t, a.capital t = p.ks ∧ a.consumption t = p.f p.ks - p.m * p.ks ∧
        a.investment t = p.m * p.ks) ∧
      (∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → 0 < a.investment t) ∧
      (∀ b : FeasiblePath p.f p.m, b.NonnegativeInvestment → b.capital 0 = k0 →
        AsymptoticallyDominates U (discount p.d) a.consumption b.consumption) ∧
      (∀ (b : FeasiblePath p.f p.m) (Jb : ℝ), IsCassOptimal U p.d b Jb → b.capital 0 = k0 →
        Jb = J ∧ ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
          b.consumption t = a.consumption t ∧ b.investment t = a.investment t) := by
    refine ⟨a, J, h0, hJ, hlim.fst_nhds,
      p.consumption_converges hCLip.continuous hFLip.continuous hlim,
      (fun h => (hbelow h).1), (fun h => (habove h).1),
      (fun h => p.consumption_strictMono (p.production_strictMono hmp hfdiff') hclip
        (hbelow h).1 (hbelow h).2),
      (fun h => p.consumption_strictAnti (p.production_strictMono hmp hfdiff') hclip
        (habove h).1 (habove h).2),
      (fun h => CassPhase.positive_investment_of_nondecreasing_capital a p.m_pos
        (p.path_capital_pos γ hclip) (hbelow h).1.monotoneOn), ?_,
      p.eventually_positive_investment hCLip.continuous hFLip.continuous hlim, ?_, ?_⟩
    · intro heq t
      change (γ t).1 = p.ks ∧ cassConsumption p.f p.C (p.point (γ t)) = p.surplus ∧
        cassInvestment p.f p.C (p.point (γ t)) = p.m * p.ks
      rw [hconstant heq t, p.consumption_steady]
      refine ⟨rfl, rfl, ?_⟩
      change p.f (p.stock p.ks) - cassConsumption p.f p.C (p.point p.steady) = _
      rw [p.stock_steady, p.consumption_steady]
      dsimp [CassPhase.surplus]
      ring
    · intro b hb hi
      exact p.constructed_dominates U hmp hmul hfconc'.concaveOn hUconc.concaveOn hfdiff' hUdiff
        hfprime' hUprime hCLip.continuous hFLip.continuous hd hclip hlim
        (h0 ▸ hkK) hcapacity' b hb (h0.trans hi.symm)
    · intro b Jb hb hi
      have hinit : a.capital 0 = b.capital 0 := h0.trans hi.symm
      have heq : Jb = J := le_antisymm
        (hJ.2.2 b hb.1 hinit Jb hb.2.1) (hb.2.2 a hJ.1 hinit.symm J hJ.2.1)
      exact ⟨heq, p.constructed_unique U hmp hmul hfconc' hUconc hfdiff' hUdiff hfprime' hUprime
        hCLip.continuous hFLip.continuous hd hclip hlim (h0 ▸ hkK) hcapacity'
        hJ.2.1 b hb.1 hinit hb.2.1 heq⟩
  rw [hprod, hdil, hdis, hsteady] at hresult
  exact hresult

end RamseyCassKoopmans
