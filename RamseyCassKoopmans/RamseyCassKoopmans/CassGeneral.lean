import RamseyCassKoopmans.CassConstructedOptimality

/-! # The general positive-discount Cass construction

For every positive initial stock, the primitive Inada and curvature assumptions
give a constructed feasible optimal path, convergence of capital and consumption,
strict movement of nonstationary capital toward the steady state, and uniqueness
of every optimum in the stated continuous-control, finite-welfare class.

Neither existence, a selected initial consumption, convergence, transversality,
nor a stable manifold is assumed. The possible zero-investment corner is retained
throughout the construction and the verification certificate.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

theorem cass_general_dynamic (f U : ℝ → ℝ) (d m k0 : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hk0 : 0 < k0)
    (hfconc : StrictConcaveOn ℝ (Ici 0) f) (hfzero : f 0 = 0)
    (hfdiff : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hfprimepos : ∀ k, 0 < k → 0 < deriv f k)
    (hfsecond : ∀ k, 0 < k → DifferentiableAt ℝ (deriv f) k)
    (hfsecondcont : ContinuousOn (deriv (deriv f)) (Ioi 0))
    (hfInada0 : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop)
    (hfInadaTop : Tendsto (deriv f) atTop (𝓝 (0 : ℝ)))
    (hUconc : StrictConcaveOn ℝ (Ioi 0) U)
    (hUdiff : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hUprimepos : ∀ c, 0 < c → 0 < deriv U c)
    (hUsecond : ∀ c, 0 < c → DifferentiableAt ℝ (deriv U) c)
    (hUsecondcont : ContinuousOn (deriv (deriv U)) (Ioi 0))
    (hUsecondneg : ∀ c, 0 < c → deriv (deriv U) c < 0)
    (hUInada0 : Tendsto (deriv U) (𝓝[>] (0 : ℝ)) atTop) :
    ∃ ks : ℝ, 0 < ks ∧ deriv f ks = d + m ∧
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
  obtain ⟨ks, hks, hstationary, ⟨D⟩⟩ := exists_cass_data_of_inada f U d m k0 hd hm hk0
    hfconc hfzero hfdiff hfprime hfprimepos hfsecond hfsecondcont hfInada0 hfInadaTop
    hUconc hUdiff hUprimepos hUsecond hUsecondcont hUsecondneg hUInada0
  obtain ⟨K, hkK, hcapacity⟩ := exists_capacity_of_marginal_tendsto_zero f hm hfconc.concaveOn
    hfdiff (fun k hk => (hfprimepos k hk).le) hfInadaTop
  have hUprime : ContinuousOn (deriv U) (Ioi 0) :=
    fun c hc => (hUsecond c hc).continuousAt.continuousWithinAt
  exact ⟨ks, hks, hstationary, D.exists_optimal hfconc hUconc hfdiff hUdiff hfprime hUprime hkK hcapacity⟩

end RamseyCassKoopmans
