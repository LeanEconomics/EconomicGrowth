import RamseyCassKoopmans.CassFiniteData
import RamseyCassKoopmans.Stationary

/-! # From the primitive growth assumptions to the shooting construction

This file chooses the stationary stock, the capital box, and every finite price
bound from the Inada and curvature assumptions. The only smoothness required is
continuous first and second derivatives on the positive half-line.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

theorem exists_cass_data_of_inada (f U : ℝ → ℝ) (d m k0 : ℝ)
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
      Nonempty (CassConstructionData f (deriv f) (deriv U) d m k0 ks) := by
  obtain ⟨ks, hks, _⟩ := existsUnique_stationary_capital_of_inada f d m
    (add_pos hd hm) hfconc hfdiff hfprime hfInada0 hfInadaTop
  let kl := min k0 ks / 2
  let ku := max k0 ks + 1
  have hkl : 0 < kl := half_pos (lt_min hk0 hks.1)
  have hkl0 : kl < k0 := by
    have hmin := min_le_left k0 ks
    have hp := lt_min hk0 hks.1
    dsimp [kl]
    linarith
  have hlstar : kl < ks := by
    have hmin := min_le_right k0 ks
    have hp := lt_min hk0 hks.1
    dsimp [kl]
    linarith
  have hstaru : ks < ku := by dsimp [ku]; linarith [le_max_right k0 ks]
  have hku0 : k0 < ku := by dsimp [ku]; linarith [le_max_left k0 ks]
  have hsub : Icc kl ku ⊆ Ioi (0 : ℝ) := fun _ hx => hkl.trans_le hx.1
  have hsubnet : Icc kl ks ⊆ Ioi (0 : ℝ) := fun _ hx => hkl.trans_le hx.1
  have hanti := production_deriv_strictAnti f hfconc hfdiff
  have hfcont : ContinuousOn f (Icc kl ku) :=
    fun k hk => (hfdiff k (hsub hk)).continuousAt.continuousWithinAt
  have hfmono : MonotoneOn f (Icc kl ku) := monotoneOn_of_deriv_nonneg (convex_Icc kl ku)
    hfcont (fun k hk => (hfdiff k (hsub (interior_subset hk))).differentiableWithinAt)
    (fun k hk => (hfprimepos k (hsub (interior_subset hk))).le)
  have hnetDeriv : ∀ k ∈ Icc kl ks,
      HasDerivAt (fun x => f x - m * x) (deriv f k - m) k := by
    intro k hk
    convert (hfdiff k (hsubnet hk)).hasDerivAt.sub ((hasDerivAt_id k).const_mul m) using 1
    · rfl
    · ring
  have hnet : MonotoneOn (fun k => f k - m * k) (Icc kl ks) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc kl ks)
      (HasDerivAt.continuousOn hnetDeriv)
      (fun k hk => (hnetDeriv k (interior_subset hk)).differentiableAt.differentiableWithinAt)
    intro k hk
    have hkmem := interior_subset hk
    have hmp := hanti.antitoneOn (hsubnet hkmem) hks.1 hkmem.2
    rw [hks.2] at hmp
    rw [(hnetDeriv k hkmem).deriv]
    linarith
  have hnetpos : 0 < f kl - m * kl := by
    have hgap := marginal_product_times_capital_lt_output f kl hfconc hfzero hkl (hfdiff kl hkl)
    have hmp := hanti hkl hks.1 hlstar
    rw [hks.2] at hmp
    have hprod := mul_pos (show 0 < deriv f kl - m by linarith) hkl
    nlinarith
  have hμanti : StrictAntiOn (deriv U) (Ioi 0) := hUconc.strictAntiOn_deriv hUdiff
  refine ⟨ks, hks.1, hks.2, ?_⟩
  exact exists_cass_finite_data f (deriv f) (deriv U) d m kl ku ks k0 hd hm hkl hlstar hstaru
    ⟨hkl0.le, hku0.le⟩
    (fun k hk => (hfdiff k (hsub hk)).hasDerivAt) (hfprime.mono hsub)
    (fun k hk => hfsecond k (hsub hk)) (hfsecondcont.mono hsub) hfmono
    (hanti.mono hsub) (fun k hk => hfprimepos k (hsub hk)) hks.2 hnet hnetpos
    hUprimepos hμanti hUsecond hUsecondcont hUsecondneg hUInada0

end RamseyCassKoopmans
