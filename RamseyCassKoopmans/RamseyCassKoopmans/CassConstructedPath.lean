import RamseyCassKoopmans.CassInadaData
import RamseyCassKoopmans.Cass

/-! # Turning the constructed trajectory into an economic feasible path -/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.CassPhase

theorem consumption_continuous (p : CassPhase) (hC : Continuous p.C)
    (hf : Continuous (p.f ∘ clip p.kl p.ku)) :
    Continuous (fun x : ℝ × ℝ => cassConsumption p.f p.C (p.point x)) :=
  (hC.comp ((lipschitz_clip 0 p.Q).continuous.comp continuous_snd)).min
    (hf.comp continuous_fst)

theorem investment_continuous (p : CassPhase) (hC : Continuous p.C)
    (hf : Continuous (p.f ∘ clip p.kl p.ku)) :
    Continuous (fun x : ℝ × ℝ => cassInvestment p.f p.C (p.point x)) :=
  (hf.comp continuous_fst).sub (p.consumption_continuous hC hf)

theorem consumption_mem (p : CassPhase) (x : ℝ × ℝ) :
    cassConsumption p.f p.C (p.point x) ∈ Icc p.ca p.cb := by
  exact ⟨le_min (p.C_mem _).1 (p.f_mem _ (p.stock_mem _)).1,
    (min_le_left _ _).trans (p.C_mem _).2⟩

theorem consumption_steady (p : CassPhase) :
    cassConsumption p.f p.C (p.point p.steady) = p.surplus := by
  change min (p.C (p.price p.qs)) (p.f (p.stock p.ks)) = _
  rw [p.price_steady, p.stock_steady, p.demand_at_steady, min_eq_left p.surplus_lt_output.le]

noncomputable def feasiblePath (p : CassPhase) (γ : ℝ → ℝ × ℝ)
    (hC : Continuous p.C) (hf : Continuous (p.f ∘ clip p.kl p.ku))
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t) : FeasiblePath p.f p.m where
  capital := fun t => (γ t).1
  consumption := fun t => cassConsumption p.f p.C (p.point (γ t))
  investment := fun t => cassInvestment p.f p.C (p.point (γ t))
  capital_nonneg := fun t ht => by
    have hk := congrArg Prod.fst (hclip t ht)
    exact hk ▸ (p.stock_pos (γ t).1).le
  consumption_pos := fun t _ => p.ca_pos.trans_le (p.consumption_mem (γ t)).1
  consumption_continuous := (p.consumption_continuous hC hf).comp_continuousOn
    (HasDerivAt.continuousOn (fun t _ => hd t))
  investment_continuous := (p.investment_continuous hC hf).comp_continuousOn
    (HasDerivAt.continuousOn (fun t _ => hd t))
  resource := fun t ht => by
    have hr := cass_resource p.f p.C (p.point (γ t))
    rw [hclip t ht] at hr
    simpa only [hclip t ht] using hr
  dynamics := fun t ht => by
    have h := ODE.hasDerivAt_fst (hd t)
    have hk := congrArg Prod.fst (hclip t ht)
    change HasDerivAt (fun t => (γ t).1)
      (cassInvestment p.f p.C (p.point (γ t)) - p.m * p.stock (γ t).1) t at h
    change p.stock (γ t).1 = (γ t).1 at hk
    rw [hk] at h
    exact h

theorem path_capital_pos (p : CassPhase) (γ : ℝ → ℝ × ℝ)
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t) :
    ∀ t, 0 ≤ t → 0 < (γ t).1 := by
  intro t ht
  have hk := congrArg Prod.fst (hclip t ht)
  exact hk ▸ p.stock_pos (γ t).1

theorem path_costate (p : CassPhase) {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (p.field (γ t)) t)
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t) :
    ∀ t, 0 ≤ t → HasDerivAt (fun t => (γ t).2)
      ((p.d + p.m) * (γ t).2 -
        p.μ (cassConsumption p.f p.C (p.point (γ t))) * p.mp (γ t).1) t := by
  intro t ht
  have h := ODE.hasDerivAt_snd (hd t)
  have hk := congrArg Prod.fst (hclip t ht)
  have hq := congrArg Prod.snd (hclip t ht)
  change p.stock (γ t).1 = (γ t).1 at hk
  change p.price (γ t).2 = (γ t).2 at hq
  change HasDerivAt (fun t => (γ t).2)
    ((p.d + p.m) * p.price (γ t).2 -
      max (p.price (γ t).2) (p.μ (p.f (p.stock (γ t).1))) * p.mp (p.stock (γ t).1)) t at h
  rw [← p.marginal (γ t), hk, hq] at h
  exact h

theorem path_wedge_slack (p : CassPhase) {γ : ℝ → ℝ × ℝ}
    (hclip : ∀ t, 0 ≤ t → p.point (γ t) = γ t) :
    ∀ t, 0 ≤ t → (γ t).2 ≤ p.μ (cassConsumption p.f p.C (p.point (γ t))) ∧
      ((γ t).2 - p.μ (cassConsumption p.f p.C (p.point (γ t)))) *
        cassInvestment p.f p.C (p.point (γ t)) = 0 := by
  intro t ht
  have hw := cass_wedge_and_slack (p.marginal (γ t)) p.μ_anti (p.output_pos _) (p.demand_pos _)
  have hq := congrArg Prod.snd (hclip t ht)
  change p.price (γ t).2 = (γ t).2 at hq
  change p.price (γ t).2 ≤ _ ∧ (p.price (γ t).2 - _) * _ = 0 at hw
  rw [hq] at hw
  exact hw

theorem consumption_converges (p : CassPhase) (hC : Continuous p.C)
    (hf : Continuous (p.f ∘ clip p.kl p.ku)) {γ : ℝ → ℝ × ℝ}
    (hlim : Tendsto γ atTop (𝓝 p.steady)) :
    Tendsto (fun t => cassConsumption p.f p.C (p.point (γ t))) atTop (𝓝 p.surplus) := by
  have h := (p.consumption_continuous hC hf).continuousAt.tendsto.comp hlim
  simpa only [p.consumption_steady, Function.comp_def] using h

end RamseyCassKoopmans.CassPhase
