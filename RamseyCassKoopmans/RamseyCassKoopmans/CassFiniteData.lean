import RamseyCassKoopmans.CassConstruction

/-! # Choosing the finite data from the Inada condition on marginal utility

The consumption floor and upper price are selected after the finite travel-time
bound is computed. The Inada limit supplies a large enough upper price, so the
quantitative condition used to remove clipping is derived here.
-/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans

structure CassConstructionData (f mp μ : ℝ → ℝ) (d m k0 ks : ℝ) where
  phase : CassPhase
  production_eq : phase.f = f
  marginalProduct_eq : phase.mp = mp
  marginalUtility_eq : phase.μ = μ
  discount_eq : phase.d = d
  dilution_eq : phase.m = m
  steady_eq : phase.ks = ks
  bounded : BoundedLip phase.field
  demand_bounded : BoundedLip phase.C
  production_bounded : BoundedLip (phase.f ∘ clip phase.kl phase.ku)
  net_mono : MonotoneOn (fun k => phase.f k - phase.m * k) (Icc phase.kl phase.ks)
  c : ℝ
  T : ℝ
  consumption_mem : c ∈ Icc phase.ca phase.cb
  net_gap : c < phase.f phase.kl - phase.m * phase.kl
  time_nonneg : 0 ≤ T
  price_large : phase.μ c * Real.exp (phase.mp phase.kl * T) ≤ phase.Q
  time_large : phase.ks - k0 ≤ (phase.f phase.kl - phase.m * phase.kl - c) * T
  initial_mem : k0 ∈ Icc phase.kl phase.ku

/-- No compact inverse, price bound or nonstationary path is assumed. All are
constructed from functions, their ordinary derivatives, and an Inada limit. -/
theorem exists_cass_finite_data (f mp μ : ℝ → ℝ) (d m kl ku ks k0 : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hkl : 0 < kl) (hlstar : kl < ks) (hstaru : ks < ku)
    (hk0 : k0 ∈ Icc kl ku)
    (hfderiv : ∀ k ∈ Icc kl ku, HasDerivAt f (mp k) k)
    (hmpcont : ContinuousOn mp (Icc kl ku))
    (hmpdiff : ∀ k ∈ Icc kl ku, DifferentiableAt ℝ mp k)
    (hmpprime : ContinuousOn (deriv mp) (Icc kl ku))
    (hfmono : MonotoneOn f (Icc kl ku))
    (hmpanti : StrictAntiOn mp (Icc kl ku))
    (hmppos : ∀ k ∈ Icc kl ku, 0 < mp k) (hmpstar : mp ks = d + m)
    (hnet : MonotoneOn (fun k => f k - m * k) (Icc kl ks))
    (hnetpos : 0 < f kl - m * kl)
    (hμpos : ∀ c, 0 < c → 0 < μ c) (hμanti : StrictAntiOn μ (Ioi 0))
    (hμdiff : ∀ c, 0 < c → DifferentiableAt ℝ μ c)
    (hμprime : ContinuousOn (deriv μ) (Ioi 0))
    (hμneg : ∀ c, 0 < c → deriv μ c < 0)
    (hμInada : Tendsto μ (𝓝[>] (0 : ℝ)) atTop) :
    Nonempty (CassConstructionData f mp μ d m k0 ks) := by
  let c := (f kl - m * kl) / 2
  have hcpos : 0 < c := half_pos hnetpos
  have hcnet : c < f kl - m * kl := by dsimp [c]; linarith
  have hkspos := hkl.trans hlstar
  have hnetstar : f kl - m * kl ≤ f ks - m * ks :=
    hnet ⟨le_rfl, hlstar.le⟩ ⟨hlstar.le, le_rfl⟩ hlstar.le
  have hcstar : c < f ks - m * ks := hcnet.trans_le hnetstar
  have hstarpos := hcpos.trans hcstar
  have hnetout : f kl - m * kl < f kl := by nlinarith [mul_pos hm hkl]
  have hflpos := hnetpos.trans hnetout
  have hflu : f kl ≤ f ku :=
    hfmono ⟨le_rfl, (hlstar.trans hstaru).le⟩ ⟨(hlstar.trans hstaru).le, le_rfl⟩
      (hlstar.trans hstaru).le
  let cb := f ku + 1
  have hcbpos : 0 < cb := by dsimp [cb]; linarith
  have hc_cb : c < cb := by dsimp [cb]; linarith
  let T := (ks - kl + 1) / (f kl - m * kl - c)
  have hT : 0 < T := div_pos (by linarith) (sub_pos.mpr hcnet)
  have htime : ks - k0 ≤ (f kl - m * kl - c) * T := by
    have ht : (f kl - m * kl - c) * T = ks - kl + 1 := by
      dsimp [T]
      field_simp [ne_of_gt (sub_pos.mpr hcnet)]
    rw [ht]
    linarith [hk0.1]
  let H := μ c * Real.exp (mp kl * T)
  have hcapos : ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < a := self_mem_nhdsWithin
  have hcnear : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < c :=
    (gt_mem_nhds hcpos).filter_mono nhdsWithin_le_nhds
  obtain ⟨ca, hca, hca_c, hlarge⟩ :=
    (hcapos.and (hcnear.and (hμInada.eventually_ge_atTop H))).exists
  have hcab : ca ≤ cb := (hca_c.trans hc_cb).le
  have hμinterval : Icc ca cb ⊆ Ioi (0 : ℝ) := fun _ hx => hca.trans_le hx.1
  obtain ⟨KC, C, hCmem, hCanti, hCLip, hCinv⟩ := exists_compact_demand_of_deriv hcab
    (fun x hx => hμdiff x (hμinterval hx)) (hμprime.mono hμinterval)
    (fun x hx => hμneg x (hμinterval hx))
  have hCL : BoundedLip C := ⟨KC, ‖cb‖₊, hCLip, fun q => by
    rw [Real.norm_eq_abs, abs_of_pos (hca.trans_le (hCmem q).1)]
    exact (hCmem q).2.trans (le_abs_self cb)⟩
  have hfmem : ∀ k ∈ Icc kl ku, f k ∈ Icc ca cb := by
    intro k hk
    have hlo := hfmono ⟨le_rfl, (hlstar.trans hstaru).le⟩ hk hk.1
    have hhi := hfmono hk ⟨(hlstar.trans hstaru).le, le_rfl⟩ hk.2
    constructor
    · exact (hca_c.trans (hcnet.trans hnetout)).le.trans hlo
    · dsimp [cb]; linarith
  let p : CassPhase := {
    f := f, mp := mp, μ := μ, C := C, d := d, m := m,
    kl := kl, ku := ku, ks := ks, ca := ca, cb := cb,
    qs := μ (f ks - m * ks), Q := μ ca,
    d_pos := hd, m_pos := hm, kl_pos := hkl, kl_lt := hlstar, ku_gt := hstaru,
    ca_pos := hca, ca_le_cb := hcab, f_mem := hfmem, f_mono := hfmono,
    mp_pos := hmppos, mp_anti := hmpanti, mp_star := hmpstar,
    μ_pos := hμpos, μ_anti := hμanti, C_mem := hCmem, C_anti := hCanti,
    inverse := hCinv, Q_eq := rfl, qs_pos := hμpos _ hstarpos,
    qs_lt := hμanti hca hstarpos (hca_c.trans hcstar),
    ca_lt_surplus := hca_c.trans hcstar, qs_eq := rfl }
  have hfprime : ContinuousOn (deriv f) (Icc kl ku) :=
    hmpcont.congr (fun k hk => (hfderiv k hk).deriv)
  have hFL : BoundedLip (f ∘ clip kl ku) := boundedLip_comp_clip (hlstar.trans hstaru).le
    (fun k hk => (hfderiv k hk).differentiableAt) hfprime
  have hPL : BoundedLip (mp ∘ clip kl ku) :=
    boundedLip_comp_clip (hlstar.trans hstaru).le hmpdiff hmpprime
  have hμL : BoundedLip (μ ∘ clip ca cb) := boundedLip_comp_clip hcab
    (fun x hx => hμdiff x (hμinterval hx)) (hμprime.mono hμinterval)
  have hHL : BoundedLip ((fun k => μ (f k)) ∘ clip kl ku) := by
    obtain ⟨KF, MF, hFLip, hFbound⟩ := hFL
    have hcomp := hμL.comp hFLip
    have heq : (μ ∘ clip ca cb) ∘ (f ∘ clip kl ku) = (fun k => μ (f k)) ∘ clip kl ku := by
      funext x
      simp only [Function.comp_apply, clip_eq (hfmem _ (clip_mem (hlstar.trans hstaru).le x))]
    exact heq ▸ hcomp
  have hpBound : BoundedLip p.field := cass_extension_boundedLip (hlstar.trans hstaru).le
    (hμpos ca hca).le hFL hPL hHL hCL
  exact ⟨{
    phase := p, production_eq := rfl, marginalProduct_eq := rfl,
    marginalUtility_eq := rfl, discount_eq := rfl, dilution_eq := rfl, steady_eq := rfl,
    bounded := hpBound, demand_bounded := hCL, production_bounded := hFL,
    net_mono := hnet, c := c, T := T,
    consumption_mem := ⟨hca_c.le, hc_cb.le⟩, net_gap := hcnet, time_nonneg := hT.le,
    price_large := hlarge, time_large := htime, initial_mem := hk0 }⟩

end RamseyCassKoopmans
