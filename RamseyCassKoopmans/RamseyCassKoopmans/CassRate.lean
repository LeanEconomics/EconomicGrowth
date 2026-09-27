/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import RamseyCassKoopmans.CassPolicy
import RamseyCassKoopmans.RiccatiRate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The exact local speed of convergence of the Cass optimum

Let `A = f''(k*) U'(c*) / U''(c*) > 0` and `β* = (√(d² + 4A) - d) / 2`, the stable
root of the linearized saddle. Assuming `f''(k*) < 0`:

* `slope_tendsto`: along every nonstationary optimum,
  `(c(t) - c*) / (k(t) - k*) → d + β*`. The slope obeys a Riccati equation whose
  other solutions blow up or turn negative (`riccati_tendsto`), so the optimum is
  forced onto the stable direction; no stable-manifold theorem is assumed.
* `speed_tendsto`: the instantaneous proportional speed `k̇ / (k - k*) → -β*`;
* `capital_rate`, `consumption_rate`: `log |k(t) - k*| / t → -β*` and
  `log |c(t) - c*| / t → -β*`;
* `policy_hasDerivAt`: the policy function is differentiable at `k*` with slope
  `d + β*`, the slope of the stable eigenvector.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

/-- `A = f''(k*) U'(c*) / U''(c*)`. -/
noncomputable def cassCurvature (P : CassPrimitives f U d m) : ℝ :=
  deriv (deriv f) (cassSteady P) * deriv U (cassSteadyConsumption P) /
    deriv (deriv U) (cassSteadyConsumption P)

/-- The stable root `β* = (√(d² + 4A) - d) / 2` of the linearized Cass system. -/
noncomputable def cassSpeed (P : CassPrimitives f U d m) : ℝ :=
  (Real.sqrt (d ^ 2 + 4 * cassCurvature P) - d) / 2

theorem cassSteadyConsumption_pos (P : CassPrimitives f U d m) :
    0 < cassSteadyConsumption P :=
  stationary_consumption_pos f (cassSteady P) d m P.f_conc P.f_zero (cassSteady_spec P).1
    (P.f_diff _ (cassSteady_spec P).1) P.d_pos.le (cassSteady_spec P).2

theorem cassCurvature_pos (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) : 0 < cassCurvature P := by
  have hc := cassSteadyConsumption_pos P
  exact div_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hf2 (P.U_prime_pos _ hc))
    (P.U_second_neg _ hc)

theorem cassSpeed_pos (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) : 0 < cassSpeed P := by
  have hA := cassCurvature_pos P hf2
  have hd := P.d_pos
  have : d < Real.sqrt (d ^ 2 + 4 * cassCurvature P) :=
    (Real.lt_sqrt hd.le).mpr (by linarith)
  unfold cassSpeed
  linarith

theorem stable_root_eq (P : CassPrimitives f U d m) :
    (d + Real.sqrt (d ^ 2 + 4 * cassCurvature P)) / 2 = d + cassSpeed P := by
  unfold cassSpeed
  ring

/-- Eventually the optimum invests strictly: transferred from the construction. -/
theorem CassCertificate.eventually_positive_investment (P : CassPrimitives f U d m)
    {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) :
    ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → 0 < a.investment t := by
  obtain ⟨ks, hks, hstat, b, Jb, hb0, hbopt, -, -, -, -, -, -, -, -, ⟨T, hT, hTpos⟩, -, -⟩ :=
    cass_general_dynamic f U d m (a.capital 0) P.d_pos P.m_pos (hc.capital_pos 0 le_rfl)
      P.f_conc P.f_zero P.f_diff P.f_prime_cont P.f_prime_pos P.f_second P.f_second_cont
      P.f_inada0 P.f_inadaTop P.U_conc P.U_diff P.U_prime_pos P.U_second P.U_second_cont
      P.U_second_neg P.U_inada0
  obtain ⟨Ja, hJa⟩ := hc.welfare
  have heq := (hc.eq_of_isCassOptimal P hJa hbopt hb0.symm).2
  exact ⟨T, hT, fun t ht => by
    rw [← (heq t (hT.trans ht)).2.2]
    exact hTpos t ht⟩

/-- The capital equation `k̇ = f(k) - m k - c`. -/
theorem FeasiblePath.hasDerivAt_capital' (a : FeasiblePath f m) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt a.capital (f (a.capital t) - m * a.capital t - a.consumption t) t := by
  have h := a.dynamics t ht
  have hr := a.resource t ht
  convert h using 1
  linarith

/-- Along a nonstationary optimum the capital and consumption gaps share a sign. -/
theorem CassCertificate.gap_sign (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) (hne : a.capital 0 ≠ cassSteady P)
    {t : ℝ} (ht : 0 ≤ t) :
    a.capital t - cassSteady P ≠ 0 ∧
      0 < (a.consumption t - cassSteadyConsumption P) / (a.capital t - cassSteady P) := by
  obtain ⟨hb1, hb2⟩ := hc.capital_bounds P
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨hk, hcn⟩ := hb1 h t ht
    refine ⟨sub_ne_zero.mpr (ne_of_lt hk), div_pos_of_neg_of_neg ?_ (sub_neg.mpr hk)⟩
    exact sub_neg.mpr hcn
  · obtain ⟨hk, hcn⟩ := hb2 h t ht
    exact ⟨sub_ne_zero.mpr (ne_of_gt hk), div_pos (sub_pos.mpr hcn) (sub_pos.mpr hk)⟩

/-- In the interior phase consumption obeys `ċ = -(U'/U'')(c) (f'(k) - (d + m))`. -/
theorem CassCertificate.hasDerivAt_consumption (P : CassPrimitives f U d m)
    {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q)
    (hne : a.capital 0 ≠ cassSteady P) {T0 : ℝ} (hT0 : 0 ≤ T0)
    (hint : ∀ t, T0 ≤ t → 0 < a.investment t) {t : ℝ} (ht : T0 < t) :
    HasDerivAt a.consumption
      (-(deriv U (a.consumption t)) / deriv (deriv U) (a.consumption t) *
        (deriv f (a.capital t) - (d + m))) t := by
  have ht0 : 0 ≤ t := hT0.trans ht.le
  have hct := a.consumption_pos t ht0
  have hqeq : ∀ s, T0 ≤ s → q s = deriv U (a.consumption s) := by
    intro s hs
    have h := hc.slack s (hT0.trans hs)
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · exact absurd h (ne_of_gt (hint s hs))
  obtain ⟨-, -, hbelow, habove, -⟩ := hc.dynamics P
  have hinjOn : InjOn a.consumption (Ici 0) := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hbelow h).2.injOn
    · exact (habove h).2.injOn
  have hd := hasDerivAt_of_comp_eq (g := a.consumption) (μ := deriv U) (q := q)
    ((a.consumption_continuous t ht0).continuousAt (Ici_mem_nhds (hT0.trans_lt ht)))
    (P.U_second _ hct).hasDerivAt (ne_of_lt (P.U_second_neg _ hct)) (hc.costate t ht0)
    (by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact (hqeq s hs.le).symm)
    (by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (hT0.trans_lt ht)),
        self_mem_nhdsWithin] with s hs hst
      exact fun h => hst (hinjOn (mem_Ici.mpr (le_of_lt hs)) (mem_Ici.mpr ht0) h))
  refine hd.congr_deriv ?_
  rw [hqeq t ht.le]
  have hne' := ne_of_lt (P.U_second_neg _ hct)
  field_simp
  ring

/-- Along every nonstationary optimum the slope `(c - c*)/(k - k*)` converges to the
stable eigenvector slope `d + β*`. -/
theorem slope_tendsto (P : CassPrimitives f U d m) (hf2 : deriv (deriv f) (cassSteady P) < 0)
    {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q)
    (hne : a.capital 0 ≠ cassSteady P) :
    Tendsto (fun t => (a.consumption t - cassSteadyConsumption P) / (a.capital t - cassSteady P))
      atTop (𝓝 (d + cassSpeed P)) := by
  set ks := cassSteady P with hks_def
  set cs := cassSteadyConsumption P with hcs_def
  have hks := (cassSteady_spec P).1
  have hfks : deriv f ks = d + m := (cassSteady_spec P).2
  have hcs : 0 < cs := cassSteadyConsumption_pos P
  obtain ⟨T0, hT0, hint⟩ := hc.eventually_positive_investment P
  obtain ⟨hk, hcon, -⟩ := hc.dynamics P
  set u : ℝ → ℝ := fun t => a.capital t - ks
  set v : ℝ → ℝ := fun t => a.consumption t - cs
  set D : ℝ → ℝ := fun t => (f (a.capital t) - f ks) / (a.capital t - ks) - m
  set σ : ℝ → ℝ := fun c => -(deriv U c) / deriv (deriv U) c
  set B : ℝ → ℝ := fun t =>
    σ (a.consumption t) * ((deriv f (a.capital t) - deriv f ks) / (a.capital t - ks))
  have hS : ∀ t, T0 + 1 ≤ t → HasDerivAt (fun s => v s / u s)
      ((v t / u t) ^ 2 - D t * (v t / u t) + B t) t := by
    intro t ht
    have htT : T0 < t := by linarith
    have ht0 : 0 ≤ t := by linarith
    obtain ⟨hu0, -⟩ := hc.gap_sign P hne ht0
    have hkd := a.hasDerivAt_capital' ht0
    have hcd := hc.hasDerivAt_consumption P hne hT0 hint htT
    have hu : a.capital t - ks ≠ 0 := hu0
    have hμ2 : deriv (deriv U) (a.consumption t) ≠ 0 :=
      ne_of_lt (P.U_second_neg _ (a.consumption_pos t ht0))
    have hdiv := (hcd.sub_const cs).div (hkd.sub_const ks) hu
    refine hdiv.congr_deriv (riccati_algebra hu ?_ ?_)
    · have hcsdef : cs = f ks - m * ks := rfl
      simp only [D]
      rw [hcsdef]
      field_simp
      ring
    · simp only [B, σ]
      rw [hfks]
      field_simp
  have hpos : ∀ t, T0 + 1 ≤ t → 0 < v t / u t := fun t ht =>
    (hc.gap_sign P hne (by linarith)).2
  -- the capital path approaches `k*` from one side
  have hkne : Tendsto a.capital atTop (𝓝[≠] ks) :=
    tendsto_nhdsWithin_iff.mpr ⟨hk, by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact sub_ne_zero.mp (hc.gap_sign P hne ht).1⟩
  have hD : Tendsto D atTop (𝓝 d) := by
    have h := (hasDerivAt_iff_tendsto_slope.mp (P.f_diff ks hks).hasDerivAt).comp hkne
    have h2 := h.sub_const m
    rw [hfks, show d + m - m = d by ring] at h2
    refine h2.congr (fun t => ?_)
    simp only [Function.comp_apply, D, slope_def_field]
  have hB : Tendsto B atTop (𝓝 (-cassCurvature P)) := by
    have hslope := (hasDerivAt_iff_tendsto_slope.mp (P.f_second ks hks).hasDerivAt).comp hkne
    have hμ : ContinuousAt (deriv U) cs := (P.U_second cs hcs).continuousAt
    have hμ' : ContinuousAt (deriv (deriv U)) cs :=
      P.U_second_cont.continuousAt (Ioi_mem_nhds hcs)
    have hσ : Tendsto (fun t => σ (a.consumption t)) atTop (𝓝 (σ cs)) :=
      (hμ.tendsto.comp hcon).neg.div (hμ'.tendsto.comp hcon) (ne_of_lt (P.U_second_neg cs hcs))
    have h := hσ.mul hslope
    have heq : σ cs * deriv (deriv f) ks = -cassCurvature P := by
      simp only [σ, cassCurvature]
      ring
    rw [heq] at h
    refine h.congr (fun t => ?_)
    simp only [Function.comp_apply, B, slope_def_field]
  have := riccati_tendsto P.d_pos (cassCurvature_pos P hf2) hS hpos hD hB
  rwa [stable_root_eq] at this

/-- The instantaneous proportional speed of convergence tends to `β*`:
`k̇ / (k - k*) → -β*`. -/
theorem speed_tendsto (P : CassPrimitives f U d m) (hf2 : deriv (deriv f) (cassSteady P) < 0)
    {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q)
    (hne : a.capital 0 ≠ cassSteady P) :
    Tendsto (fun t => (f (a.capital t) - m * a.capital t - a.consumption t) /
      (a.capital t - cassSteady P)) atTop (𝓝 (-cassSpeed P)) := by
  set ks := cassSteady P
  have hks := (cassSteady_spec P).1
  have hfks : deriv f ks = d + m := (cassSteady_spec P).2
  obtain ⟨hk, -, -⟩ := hc.dynamics P
  have hkne : Tendsto a.capital atTop (𝓝[≠] ks) :=
    tendsto_nhdsWithin_iff.mpr ⟨hk, by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact sub_ne_zero.mp (hc.gap_sign P hne ht).1⟩
  have hD := ((hasDerivAt_iff_tendsto_slope.mp (P.f_diff ks hks).hasDerivAt).comp hkne).sub_const m
  have h := hD.sub (slope_tendsto P hf2 hc hne)
  rw [hfks, show d + m - m - (d + cassSpeed P) = -cassSpeed P by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  have hu : a.capital t - ks ≠ 0 := (hc.gap_sign P hne ht).1
  have hu2 : a.capital t - cassSteady P ≠ 0 := hu
  have hcs : cassSteadyConsumption P = f ks - m * ks := rfl
  simp only [Function.comp_apply, slope_def_field]
  rw [hcs]
  field_simp
  ring

/-- Capital converges at exactly the rate `β*`: `log |k(t) - k*| / t → -β*`. -/
theorem capital_rate (P : CassPrimitives f U d m) (hf2 : deriv (deriv f) (cassSteady P) < 0)
    {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q)
    (hne : a.capital 0 ≠ cassSteady P) :
    Tendsto (fun t => Real.log |a.capital t - cassSteady P| / t) atTop
      (𝓝 (-cassSpeed P)) := by
  have hφ : ∀ t, 0 ≤ t → HasDerivAt (fun s => Real.log (a.capital s - cassSteady P))
      ((f (a.capital t) - m * a.capital t - a.consumption t) / (a.capital t - cassSteady P)) t :=
    fun t ht => ((a.hasDerivAt_capital' ht).sub_const _).log (hc.gap_sign P hne ht).1
  simpa only [Real.log_abs] using tendsto_div_of_deriv_tendsto hφ (speed_tendsto P hf2 hc hne)

/-- Consumption converges at the same rate: `log |c(t) - c*| / t → -β*`. -/
theorem consumption_rate (P : CassPrimitives f U d m) (hf2 : deriv (deriv f) (cassSteady P) < 0)
    {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q)
    (hne : a.capital 0 ≠ cassSteady P) :
    Tendsto (fun t => Real.log |a.consumption t - cassSteadyConsumption P| / t) atTop
      (𝓝 (-cassSpeed P)) := by
  set S := fun t => (a.consumption t - cassSteadyConsumption P) / (a.capital t - cassSteady P)
  have hSlim := slope_tendsto P hf2 hc hne
  have hx : 0 < d + cassSpeed P := add_pos P.d_pos (cassSpeed_pos P hf2)
  have hlogS : Tendsto (fun t => Real.log (S t) / t) atTop (𝓝 0) :=
    ((Real.continuousAt_log (ne_of_gt hx)).tendsto.comp hSlim).div_atTop tendsto_id
  have h := hlogS.add (capital_rate P hf2 hc hne)
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  obtain ⟨hu, hSpos⟩ := hc.gap_sign P hne ht
  have hv : a.consumption t - cassSteadyConsumption P =
      S t * (a.capital t - cassSteady P) := by
    simp only [S]
    field_simp
  rw [hv, abs_mul, abs_of_pos hSpos, Real.log_mul (ne_of_gt hSpos) (abs_ne_zero.mpr hu),
    add_div]

/-- The policy function is differentiable at the steady state, with the slope of the
stable eigenvector. -/
theorem policy_hasDerivAt (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) :
    HasDerivAt (policy P) (d + cassSpeed P) (cassSteady P) := by
  set ks := cassSteady P
  have hks := (cassSteady_spec P).1
  rw [hasDerivAt_iff_tendsto_slope, ← nhdsLT_sup_nhdsGT, tendsto_sup]
  -- the slope of the policy at a stock reached by a path equals the path slope there
  have hslope : ∀ {a : FeasiblePath f m} {q : ℝ → ℝ}, CassCertificate f U d m a q →
      ∀ t, 0 ≤ t → a.capital t ≠ ks →
        slope (policy P) ks (a.capital t) =
          (a.consumption t - cassSteadyConsumption P) / (a.capital t - ks) := by
    intro a q hc t ht _
    rw [slope_def_field, ← consumption_eq_policy P hc ht, policy_steady]
  constructor
  · -- from below, along the optimum from `k*/2`
    have hk0 : 0 < ks / 2 := half_pos hks
    obtain ⟨q, h0, hc⟩ := optimalPath_spec P hk0
    set a := optimalPath P hk0
    have hne : a.capital 0 ≠ ks := by rw [h0]; linarith
    have hlt : a.capital 0 < ks := by rw [h0]; linarith
    obtain ⟨hk, -, -⟩ := hc.dynamics P
    have hS := slope_tendsto P hf2 hc hne
    rw [Metric.tendsto_nhds] at hS ⊢
    intro ε hε
    obtain ⟨T, hT⟩ := eventually_atTop.mp ((hS ε hε).and (eventually_ge_atTop (0 : ℝ)))
    have hTlt : a.capital T < ks := ((hc.capital_bounds P).1 hlt T (hT T le_rfl).2).1
    filter_upwards [Ioo_mem_nhdsLT hTlt] with k hk'
    obtain ⟨T', hT'⟩ := eventually_atTop.mp ((hk.eventually (lt_mem_nhds hk'.2)).and
      (eventually_ge_atTop T))
    obtain ⟨t, htmem, htk⟩ := intermediate_value_Icc (hT' T' le_rfl).2
      (a.capital_continuous.mono (fun s hs => (hT T le_rfl).2.trans hs.1))
      ⟨hk'.1.le, (hT' T' le_rfl).1.le⟩
    have ht0 : 0 ≤ t := (hT T le_rfl).2.trans htmem.1
    rw [← htk, hslope hc t ht0 (by rw [htk]; exact ne_of_lt hk'.2)]
    exact (hT t htmem.1).1
  · -- from above, along the optimum from `2 k*`
    have hk0 : 0 < 2 * ks := by linarith
    obtain ⟨q, h0, hc⟩ := optimalPath_spec P hk0
    set a := optimalPath P hk0
    have hne : a.capital 0 ≠ ks := by rw [h0]; linarith
    have hgt : ks < a.capital 0 := by rw [h0]; linarith
    obtain ⟨hk, -, -⟩ := hc.dynamics P
    have hS := slope_tendsto P hf2 hc hne
    rw [Metric.tendsto_nhds] at hS ⊢
    intro ε hε
    obtain ⟨T, hT⟩ := eventually_atTop.mp ((hS ε hε).and (eventually_ge_atTop (0 : ℝ)))
    have hTgt : ks < a.capital T := ((hc.capital_bounds P).2 hgt T (hT T le_rfl).2).1
    filter_upwards [Ioo_mem_nhdsGT hTgt] with k hk'
    obtain ⟨T', hT'⟩ := eventually_atTop.mp ((hk.eventually (gt_mem_nhds hk'.1)).and
      (eventually_ge_atTop T))
    obtain ⟨t, htmem, htk⟩ := intermediate_value_Icc' (hT' T' le_rfl).2
      (a.capital_continuous.mono (fun s hs => (hT T le_rfl).2.trans hs.1))
      ⟨(hT' T' le_rfl).1.le, hk'.2.le⟩
    have ht0 : 0 ≤ t := (hT T le_rfl).2.trans htmem.1
    rw [← htk, hslope hc t ht0 (by rw [htk]; exact ne_of_gt hk'.1)]
    exact (hT t htmem.1).1

end RamseyCassKoopmans
