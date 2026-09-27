/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import RamseyCassKoopmans.CassValue

/-!
# The envelope theorem for the Cass value function

`value_hasDerivAt`: for a certified optimum `(a, q)` from `k₀`,
`V'(k₀) = q(0)`, the initial current-value costate; when the optimum invests at
time zero this is `U'(c(0))` (`value_deriv_eq_marginal_utility`).

The proof follows Clausen and Strub (2020), *Reverse calculus and nested
optimization*, J. Econ. Theory 187: a function squeezed between a lower and an
upper support function that touch it at `k₀` and share a derivative there is
differentiable with that derivative (`clausen_strub_sandwich`). The upper support
is the affine supergradient bound `V(k₀) + q(0)(k - k₀)`. The lower support is the
welfare `L(k)` of the path that copies the optimum's investment from `k`; its
derivative at `k₀` is identified from the costate identity
`q(0) = ∫₀^∞ e^{-(d+m)t} U'(c) f'(k) dt` and uniform continuity of `U'` and `f'`.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

/-- Clausen–Strub sandwich: a function lying between two functions that touch it at
`x₀` and are differentiable there with a common derivative `D` has derivative `D`. -/
theorem clausen_strub_sandwich {V L H : ℝ → ℝ} {x₀ D : ℝ}
    (hL : HasDerivAt L D x₀) (hH : HasDerivAt H D x₀)
    (hLV : ∀ᶠ x in 𝓝 x₀, L x ≤ V x) (hVH : ∀ᶠ x in 𝓝 x₀, V x ≤ H x)
    (hLx : L x₀ = V x₀) (hHx : H x₀ = V x₀) : HasDerivAt V D x₀ := by
  rw [hasDerivAt_iff_tendsto_slope] at hL hH ⊢
  rw [← nhdsLT_sup_nhdsGT, tendsto_sup] at hL hH ⊢
  constructor
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hH.1 hL.1 ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds hVH, self_mem_nhdsWithin] with x hx hlt
      rw [slope_def_field, slope_def_field, ← hHx]
      exact div_le_div_of_nonpos_of_le (sub_nonpos.mpr (le_of_lt hlt)) (by linarith)
    · filter_upwards [nhdsWithin_le_nhds hLV, self_mem_nhdsWithin] with x hx hlt
      rw [slope_def_field, slope_def_field, ← hLx]
      exact div_le_div_of_nonpos_of_le (sub_nonpos.mpr (le_of_lt hlt)) (by linarith)
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL.2 hH.2 ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds hLV, self_mem_nhdsWithin] with x hx hgt
      rw [slope_def_field, slope_def_field, ← hLx]
      exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr (le_of_lt hgt))
    · filter_upwards [nhdsWithin_le_nhds hVH, self_mem_nhdsWithin] with x hx hgt
      rw [slope_def_field, slope_def_field, ← hHx]
      exact div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr (le_of_lt hgt))

/-- Consumption of the path copying `a`'s investment from stock `a.capital 0 + Δ`. -/
noncomputable def mimicConsumption (a : FeasiblePath f m) (Δ t : ℝ) : ℝ :=
  f (a.capital t + Δ * Real.exp (-m * t)) - a.investment t

theorem integral_exp_neg_le {r : ℝ} (hr : 0 < r) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, Real.exp (-r * t) ≤ 1 / r := by
  have hd : ∀ t, HasDerivAt (fun s => -Real.exp (-r * s) / r) (Real.exp (-r * t)) t := by
    intro t
    have := (((hasDerivAt_id t).const_mul (-r)).exp.neg).div_const r
    refine this.congr_deriv ?_
    simp only [id]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (Continuous.intervalIntegrable (by fun_prop) 0 T)]
  have := Real.exp_pos (-r * T)
  simp only [mul_zero, Real.exp_zero]
  rw [div_sub_div_same, show -Real.exp (-r * T) - -1 = 1 - Real.exp (-r * T) by ring]
  exact div_le_div_of_nonneg_right (by linarith) hr.le

set_option maxHeartbeats 1000000 in
-- The envelope proof assembles many local estimates in one context; the fresh-source
-- audit, which elaborates every module in a single file, needs the larger budget.
/-- The envelope theorem: `V'(k₀) = q(0)`. -/
theorem value_hasDerivAt (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) :
    HasDerivAt (value P) (q 0) (a.capital 0) := by
  classical
  set k0 := a.capital 0 with hk0_def
  have hk0 : 0 < k0 := hc.capital_pos 0 le_rfl
  obtain ⟨Ja, hJa⟩ := hc.welfare
  have hVa : value P k0 = Ja := value_eq P hc hJa
  have hm := P.m_pos
  have hdm : 0 < d + m := add_pos P.d_pos hm
  -- compact bounds for the optimum
  obtain ⟨hk, hcon, -⟩ := hc.dynamics P
  obtain ⟨kmin, kmax, hkmin, -, hkbd⟩ := exists_pos_bounds a.capital_continuous
    hc.capital_pos (cassSteady_spec P).1 hk
  obtain ⟨cmin, cmax, hcmin, -, hcbd⟩ := exists_pos_bounds a.consumption_continuous
    a.consumption_pos (cassSteadyConsumption_pos P) hcon
  set k1 := kmin / 2 with hk1_def
  have hk1 : 0 < k1 := half_pos hkmin
  set Mf := deriv f k1
  have hMf : 0 < Mf := P.f_prime_pos k1 hk1
  have hfanti := production_deriv_strictAnti f P.f_conc P.f_diff
  -- output is Lipschitz with constant `Mf` above `k1`
  have hlip : ∀ x y, k1 ≤ x → k1 ≤ y → |f y - f x| ≤ Mf * |y - x| := by
    intro x y hx hy
    have hx0 : 0 < x := hk1.trans_le hx
    have hy0 : 0 < y := hk1.trans_le hy
    have h1 := concave_support P.f_conc.concaveOn (mem_Ici.mpr hx0.le) (mem_Ici.mpr hy0.le)
      (P.f_diff x hx0).hasDerivAt
    have h2 := concave_support P.f_conc.concaveOn (mem_Ici.mpr hy0.le) (mem_Ici.mpr hx0.le)
      (P.f_diff y hy0).hasDerivAt
    have hfx : 0 < deriv f x ∧ deriv f x ≤ Mf :=
      ⟨P.f_prime_pos x hx0, hfanti.antitoneOn hk1 hx0 hx⟩
    have hfy : 0 < deriv f y ∧ deriv f y ≤ Mf :=
      ⟨P.f_prime_pos y hy0, hfanti.antitoneOn hk1 hy0 hy⟩
    rw [abs_le]
    rcases le_total x y with hxy | hxy
    · rw [abs_of_nonneg (sub_nonneg.mpr hxy)]
      constructor <;> nlinarith
    · rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      constructor <;> nlinarith
  set δ0 := min (kmin / 2) (min 1 (cmin / (2 * Mf)))
  have hδ0 : 0 < δ0 := lt_min hk1 (lt_min one_pos (div_pos hcmin (by linarith)))
  set cmax' := f (kmax + 1)
  -- the mimic path is admissible for `|Δ| < δ0`
  have hexp : ∀ t, 0 ≤ t → 0 < Real.exp (-m * t) ∧ Real.exp (-m * t) ≤ 1 := fun t ht =>
    ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by nlinarith)⟩
  have hkb : ∀ Δ, |Δ| < δ0 → ∀ t, 0 ≤ t →
      k1 ≤ a.capital t + Δ * Real.exp (-m * t) ∧ a.capital t + Δ * Real.exp (-m * t) ≤ kmax + 1 ∧
        |a.capital t + Δ * Real.exp (-m * t) - a.capital t| ≤ |Δ| := by
    intro Δ hΔ t ht
    obtain ⟨he0, he1⟩ := hexp t ht
    have habs : |Δ * Real.exp (-m * t)| ≤ |Δ| := by
      rw [abs_mul, abs_of_pos he0]
      exact mul_le_of_le_one_right (abs_nonneg _) he1
    have hΔk : |Δ| < kmin / 2 := hΔ.trans_le (min_le_left _ _)
    have hΔ1 : |Δ| < 1 := hΔ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    obtain ⟨hlo, hhi⟩ := hkbd t ht
    have := neg_abs_le (Δ * Real.exp (-m * t))
    have := le_abs_self (Δ * Real.exp (-m * t))
    refine ⟨by linarith, by linarith, ?_⟩
    rw [show a.capital t + Δ * Real.exp (-m * t) - a.capital t = Δ * Real.exp (-m * t) by ring]
    exact habs
  have hcb : ∀ Δ, |Δ| < δ0 → ∀ t, 0 ≤ t →
      cmin / 2 ≤ mimicConsumption a Δ t ∧ mimicConsumption a Δ t ≤ cmax' ∧
        |mimicConsumption a Δ t - a.consumption t| ≤ Mf * |Δ| := by
    intro Δ hΔ t ht
    obtain ⟨hb1, hb2, hb3⟩ := hkb Δ hΔ t ht
    have hdiff : |mimicConsumption a Δ t - a.consumption t| ≤ Mf * |Δ| := by
      have hr := a.resource t ht
      have heq : mimicConsumption a Δ t - a.consumption t =
          f (a.capital t + Δ * Real.exp (-m * t)) - f (a.capital t) := by
        simp only [mimicConsumption]
        linarith
      rw [heq]
      exact (hlip _ _ (by linarith [(hkbd t ht).1]) hb1).trans
        (mul_le_mul_of_nonneg_left hb3 hMf.le)
    have hΔc : Mf * |Δ| ≤ cmin / 2 := by
      have h := hΔ.le.trans ((min_le_right _ _).trans (min_le_right _ _))
      rw [le_div_iff₀ (by linarith)] at h
      linarith
    refine ⟨?_, ?_, hdiff⟩
    · have := (abs_le.mp hdiff).1
      linarith [(hcbd t ht).1]
    · have hz := hc.investment_nonneg t ht
      have hmono := P.f_strictMono.monotoneOn (hk1.trans_le hb1)
        (show (0 : ℝ) < kmax + 1 by linarith [(hkbd t ht).1, (hkbd t ht).2]) hb2
      simp only [mimicConsumption]
      linarith
  have hcbpos : ∀ Δ, |Δ| < δ0 → ∀ t, 0 ≤ t → 0 < mimicConsumption a Δ t := fun Δ hΔ t ht =>
    (half_pos hcmin).trans_le (hcb Δ hΔ t ht).1
  let b : ∀ Δ, |Δ| < δ0 → FeasiblePath f m := fun Δ hΔ => a.mimic P Δ
    (fun t ht => hk1.trans_le (hkb Δ hΔ t ht).1) (hcbpos Δ hΔ)
  have hbcons : ∀ Δ hΔ, (b Δ hΔ).consumption = mimicConsumption a Δ := fun _ _ => rfl
  have hb0 : ∀ Δ hΔ, (b Δ hΔ).capital 0 = k0 + Δ := fun Δ hΔ => by
    change a.capital 0 + Δ * Real.exp (-m * 0) = k0 + Δ
    rw [mul_zero, Real.exp_zero, mul_one]
  have hbwel : ∀ Δ, |Δ| < δ0 → ∃ J, HasWelfare U (discount d) (mimicConsumption a Δ) J :=
    fun Δ hΔ => P.exists_welfare (b Δ hΔ).consumption_continuous (half_pos hcmin)
      ((hcb Δ hΔ 0 le_rfl).1.trans (hcb Δ hΔ 0 le_rfl).2.1)
      (fun t ht => ⟨(hcb Δ hΔ t ht).1, (hcb Δ hΔ t ht).2.1⟩)
  -- the lower support function
  let L : ℝ → ℝ := fun k => if h : ∃ J, HasWelfare U (discount d) (mimicConsumption a (k - k0)) J
    then Classical.choose h else value P k
  have hLspec : ∀ k, |k - k0| < δ0 →
      HasWelfare U (discount d) (mimicConsumption a (k - k0)) (L k) := fun k hk => by
    simp only [L, hbwel (k - k0) hk, ↓reduceDIte]
    exact Classical.choose_spec (hbwel (k - k0) hk)
  have hmim0 : ∀ t, 0 ≤ t → mimicConsumption a 0 t = a.consumption t := fun t ht => by
    simp only [mimicConsumption, zero_mul, add_zero]
    linarith [a.resource t ht]
  have hwcongr : ∀ {c1 c2 : ℝ → ℝ}, (∀ t, 0 ≤ t → c1 t = c2 t) → ∀ T, 0 ≤ T →
      welfare U (discount d) c1 T = welfare U (discount d) c2 T := by
    intro c1 c2 h T hT
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    simp only [h t ht.1]
  have hL0 : L k0 = value P k0 := by
    have h1 := hLspec k0 (by rw [sub_self, abs_zero]; exact hδ0)
    rw [sub_self] at h1
    have h2 : HasWelfare U (discount d) (mimicConsumption a 0) Ja :=
      hJa.congr' (by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        exact (hwcongr hmim0 T hT).symm)
    rw [hVa]
    exact tendsto_nhds_unique h1 h2
  -- the integrand of the derivative estimate
  set g : ℝ → ℝ → ℝ := fun Δ t => Real.exp (-(d + m) * t) *
    (deriv U (mimicConsumption a Δ t) * deriv f (a.capital t + Δ * Real.exp (-m * t)))
  have hgcont : ∀ Δ, |Δ| < δ0 → ContinuousOn (g Δ) (Ici 0) := fun Δ hΔ => by
    have hkc : ContinuousOn (fun t => a.capital t + Δ * Real.exp (-m * t)) (Ici 0) :=
      a.capital_continuous.add (continuousOn_const.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
      ((P.U_prime_cont.comp (b Δ hΔ).consumption_continuous (hcbpos Δ hΔ)).mul
        (P.f_prime_cont.comp hkc (fun t ht => hk1.trans_le (hkb Δ hΔ t ht).1)))
  -- the costate identity: `∫₀^T g 0 → q(0)`
  have hq0 : Tendsto (fun T => ∫ t in (0 : ℝ)..T, g 0 t) atTop (𝓝 (q 0)) := by
    have hQ : ∀ t, 0 ≤ t → HasDerivAt (fun s => Real.exp (-(d + m) * s) * q s) (-(g 0 t)) t := by
      intro t ht
      have he := ((hasDerivAt_id t).const_mul (-(d + m))).exp
      refine (he.mul (hc.costate t ht)).congr_deriv ?_
      simp only [g, id, zero_mul, add_zero, hmim0 t ht]
      ring
    have hFTC : ∀ T, 0 ≤ T → ∫ t in (0 : ℝ)..T, g 0 t =
        q 0 - Real.exp (-(d + m) * T) * q T := by
      intro T hT
      have hint : IntervalIntegrable (fun t => -(g 0 t)) volume 0 T :=
        ((hgcont 0 (by rw [abs_zero]; exact hδ0)).neg.mono
          (fun _ ht => ht.1)).intervalIntegrable_of_Icc hT
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => by
        rw [uIcc_of_le hT] at ht; exact hQ t ht.1) hint
      rw [intervalIntegral.integral_neg] at h
      simp only [mul_zero, Real.exp_zero, one_mul] at h
      linarith
    have hdecay : Tendsto (fun T => Real.exp (-(d + m) * T) * q T) atTop (𝓝 0) := by
      have h := hc.transversality.mul (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop hm))
      rw [zero_mul] at h
      refine h.congr (fun T => ?_)
      simp only [Function.comp_apply, discount, id]
      rw [mul_comm, ← mul_assoc, ← Real.exp_add]
      ring_nf
    have := (hdecay.const_sub (q 0))
    rw [sub_zero] at this
    exact this.congr' (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact (hFTC T hT).symm)
  -- pointwise welfare gain bound
  have hpoint : ∀ Δ, |Δ| < δ0 → ∀ t, 0 ≤ t →
      Δ * g Δ t ≤ discount d t * U (mimicConsumption a Δ t) -
        discount d t * U (mimicConsumption a 0 t) := by
    intro Δ hΔ t ht
    have hca := a.consumption_pos t ht
    have hcΔ := hcbpos Δ hΔ t ht
    obtain ⟨hkΔ, -, -⟩ := hkb Δ hΔ t ht
    have hkΔpos : 0 < a.capital t + Δ * Real.exp (-m * t) := hk1.trans_le hkΔ
    have hU := concave_support P.U_conc.concaveOn hcΔ hca (P.U_diff _ hcΔ).hasDerivAt
    have hf := concave_support P.f_conc.concaveOn (mem_Ici.mpr hkΔpos.le)
      (mem_Ici.mpr (hc.capital_pos t ht).le) (P.f_diff _ hkΔpos).hasDerivAt
    have hr := a.resource t ht
    have hUp := (P.U_prime_pos _ hcΔ).le
    rw [hmim0 t ht]
    have hcdiff : mimicConsumption a Δ t - a.consumption t =
        f (a.capital t + Δ * Real.exp (-m * t)) - f (a.capital t) := by
      simp only [mimicConsumption]; linarith
    have hstep : deriv U (mimicConsumption a Δ t) *
        (deriv f (a.capital t + Δ * Real.exp (-m * t)) * (Δ * Real.exp (-m * t))) ≤
        U (mimicConsumption a Δ t) - U (a.consumption t) := by
      have h1 : deriv f (a.capital t + Δ * Real.exp (-m * t)) * (Δ * Real.exp (-m * t)) ≤
          mimicConsumption a Δ t - a.consumption t := by
        rw [hcdiff]
        have : a.capital t - (a.capital t + Δ * Real.exp (-m * t)) = -(Δ * Real.exp (-m * t)) :=
          by ring
        rw [this] at hf
        linarith
      have h2 := mul_le_mul_of_nonneg_left h1 hUp
      linarith
    have hdisc : discount d t * Real.exp (-m * t) = Real.exp (-(d + m) * t) := by
      simp only [discount, ← Real.exp_add]
      ring_nf
    have := mul_le_mul_of_nonneg_left hstep (discount_pos d t).le
    calc Δ * g Δ t = discount d t * (deriv U (mimicConsumption a Δ t) *
          (deriv f (a.capital t + Δ * Real.exp (-m * t)) * (Δ * Real.exp (-m * t)))) := by
          simp only [g]
          rw [← hdisc]
          ring
      _ ≤ discount d t * (U (mimicConsumption a Δ t) - U (a.consumption t)) := this
      _ = _ := by ring
  -- uniform continuity of the integrand in `Δ`
  set MU := deriv U (cmin / 2)
  have hMU : 0 < MU := P.U_prime_pos _ (half_pos hcmin)
  have hUanti := P.U_conc.strictAntiOn_deriv P.U_diff
  have hucf := isCompact_Icc.uniformContinuousOn_of_continuous
    (P.f_prime_cont.mono (fun x hx => hk1.trans_le hx.1) :
      ContinuousOn (deriv f) (Icc k1 (kmax + 1)))
  have hucU := isCompact_Icc.uniformContinuousOn_of_continuous
    (P.U_prime_cont.mono (fun x hx => (half_pos hcmin).trans_le hx.1) :
      ContinuousOn (deriv U) (Icc (cmin / 2) cmax'))
  rw [Metric.uniformContinuousOn_iff] at hucf hucU
  have hcamem : ∀ t, 0 ≤ t → a.consumption t ∈ Icc (cmin / 2) cmax' := fun t ht => by
    have := hcb 0 (by rw [abs_zero]; exact hδ0) t ht
    rw [hmim0 t ht] at this
    exact ⟨this.1, this.2.1⟩
  have huniform : ∀ ε, 0 < ε → ∃ δ, 0 < δ ∧ δ ≤ δ0 ∧ ∀ Δ, |Δ| < δ → ∀ t, 0 ≤ t →
      |g Δ t - g 0 t| ≤ ε * Real.exp (-(d + m) * t) := by
    intro ε hε
    obtain ⟨δf, hδf, hf⟩ := hucf (ε / (2 * (MU + 1))) (by positivity)
    obtain ⟨δU, hδU, hU⟩ := hucU (ε / (2 * (Mf + 1))) (by positivity)
    refine ⟨min δ0 (min δf (δU / (Mf + 1))), lt_min hδ0 (lt_min hδf (by positivity)),
      min_le_left _ _, fun Δ hΔ t ht => ?_⟩
    have hΔ0 : |Δ| < δ0 := hΔ.trans_le (min_le_left _ _)
    have hΔf : |Δ| < δf := hΔ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hΔU : |Δ| < δU / (Mf + 1) := hΔ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    obtain ⟨hkΔ1, hkΔ2, hkΔ3⟩ := hkb Δ hΔ0 t ht
    obtain ⟨hcΔ1, hcΔ2, hcΔ3⟩ := hcb Δ hΔ0 t ht
    have hkamem : a.capital t ∈ Icc k1 (kmax + 1) :=
      ⟨by linarith [(hkbd t ht).1], by linarith [(hkbd t ht).2]⟩
    have hdf : |deriv f (a.capital t + Δ * Real.exp (-m * t)) - deriv f (a.capital t)| <
        ε / (2 * (MU + 1)) := by
      have := hf _ ⟨hkΔ1, hkΔ2⟩ _ hkamem (by rw [Real.dist_eq]; exact hkΔ3.trans_lt hΔf)
      rwa [Real.dist_eq] at this
    have hdU : |deriv U (mimicConsumption a Δ t) - deriv U (a.consumption t)| <
        ε / (2 * (Mf + 1)) := by
      have hlt : Mf * |Δ| < δU := by
        have := (lt_div_iff₀ (by linarith : (0 : ℝ) < Mf + 1)).mp hΔU
        nlinarith [abs_nonneg Δ]
      have := hU _ ⟨hcΔ1, hcΔ2⟩ _ (hcamem t ht) (by rw [Real.dist_eq]; exact hcΔ3.trans_lt hlt)
      rwa [Real.dist_eq] at this
    have hUb : 0 < deriv U (mimicConsumption a Δ t) ∧ deriv U (mimicConsumption a Δ t) ≤ MU :=
      ⟨P.U_prime_pos _ (hcbpos Δ hΔ0 t ht),
        hUanti.antitoneOn (half_pos hcmin) (hcbpos Δ hΔ0 t ht) hcΔ1⟩
    have hfb : 0 < deriv f (a.capital t) ∧ deriv f (a.capital t) ≤ Mf :=
      ⟨P.f_prime_pos _ (hc.capital_pos t ht), hfanti.antitoneOn hk1 (hc.capital_pos t ht)
        hkamem.1⟩
    have hdiff : g Δ t - g 0 t = Real.exp (-(d + m) * t) *
        (deriv U (mimicConsumption a Δ t) *
          (deriv f (a.capital t + Δ * Real.exp (-m * t)) - deriv f (a.capital t)) +
        deriv f (a.capital t) *
          (deriv U (mimicConsumption a Δ t) - deriv U (a.consumption t))) := by
      simp only [g, zero_mul, add_zero, hmim0 t ht]
      ring
    rw [hdiff, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm ε]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have h1 : |deriv U (mimicConsumption a Δ t) *
        (deriv f (a.capital t + Δ * Real.exp (-m * t)) - deriv f (a.capital t))| ≤ ε / 2 := by
      rw [abs_mul, abs_of_pos hUb.1]
      have := mul_le_mul hUb.2 hdf.le (abs_nonneg _) hMU.le
      have h2 : MU * (ε / (2 * (MU + 1))) ≤ ε / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    have h2 : |deriv f (a.capital t) *
        (deriv U (mimicConsumption a Δ t) - deriv U (a.consumption t))| ≤ ε / 2 := by
      rw [abs_mul, abs_of_pos hfb.1]
      have := mul_le_mul hfb.2 hdU.le (abs_nonneg _) hMf.le
      have h3 : Mf * (ε / (2 * (Mf + 1))) ≤ ε / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add h1 h2
      _ = ε := by ring
  -- the lower support has derivative `q(0)` at `k0`
  have hLV : ∀ k, |k - k0| < δ0 → L k ≤ value P k := fun k hk => by
    have hkpos : 0 < k := by
      have := (abs_lt.mp hk).1
      have : δ0 ≤ kmin / 2 := min_le_left _ _
      linarith [(hkbd 0 le_rfl).1]
    exact value_ge P hkpos (b := b (k - k0) hk) hc.investment_nonneg
      ((hb0 (k - k0) hk).trans (by ring)) (hLspec k hk)
  have hnearδ0 : ∀ᶠ k in 𝓝 k0, |k - k0| < δ0 := by
    have := Metric.ball_mem_nhds k0 hδ0
    filter_upwards [this] with k hk
    rwa [Metric.mem_ball, Real.dist_eq] at hk
  have hLder : HasDerivAt L (q 0) k0 := by
    rw [hasDerivAt_iff_isLittleO]
    refine Asymptotics.IsLittleO.of_bound (fun ε hε => ?_)
    obtain ⟨δ, hδ, hδδ0, hunif⟩ := huniform (ε * (d + m)) (by positivity)
    have hnear : ∀ᶠ k in 𝓝 k0, |k - k0| < δ := by
      filter_upwards [Metric.ball_mem_nhds k0 hδ] with k hk
      rwa [Metric.mem_ball, Real.dist_eq] at hk
    filter_upwards [hnear] with k hk
    set Δ := k - k0
    have hΔ0 : |Δ| < δ0 := hk.trans_le hδδ0
    -- upper bound from `L ≤ V ≤ V(k0) + q(0)(k - k0)`
    have hup : L k - L k0 ≤ q 0 * Δ := by
      have h1 := hLV k hΔ0
      have hkpos : 0 < k := by
        have := (abs_lt.mp hΔ0).1
        have : δ0 ≤ kmin / 2 := min_le_left _ _
        linarith [(hkbd 0 le_rfl).1]
      have h2 := value_le_supergradient P hc hkpos
      rw [hL0]
      linarith
    -- lower bound from the pointwise gain and the costate identity
    have hlow : q 0 * Δ - ε * |Δ| ≤ L k - L k0 := by
      have hWk := hLspec k hΔ0
      have hW0 := hLspec k0 (by rw [sub_self, abs_zero]; exact hδ0)
      rw [sub_self] at hW0
      have hlimit : Tendsto (fun T => Δ * ∫ t in (0 : ℝ)..T, g 0 t) atTop (𝓝 (Δ * q 0)) :=
        hq0.const_mul Δ
      have hle : Δ * q 0 - ε * |Δ| ≤ L k - L k0 := by
        apply le_of_tendsto_of_tendsto (hlimit.sub_const (ε * |Δ|)) (hWk.sub hW0)
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
        have hIΔ : IntervalIntegrable (g Δ) volume 0 T :=
          ((hgcont Δ hΔ0).mono hsub).intervalIntegrable_of_Icc hT
        have hI0 : IntervalIntegrable (g 0) volume 0 T :=
          ((hgcont 0 (by rw [abs_zero]; exact hδ0)).mono hsub).intervalIntegrable_of_Icc hT
        have hUc : ∀ e : ℝ, |e| < δ0 → IntervalIntegrable
            (fun t => discount d t * U (mimicConsumption a e t)) volume 0 T := fun e he =>
          (((discount_continuous d).continuousOn.mul (P.U_cont.comp
            (b e he).consumption_continuous (hcbpos e he))).mono hsub).intervalIntegrable_of_Icc hT
        -- `Δ ∫ g Δ ≤ W_Δ(T) - W_0(T)`
        have hgain : Δ * ∫ t in (0 : ℝ)..T, g Δ t ≤
            welfare U (discount d) (mimicConsumption a Δ) T -
              welfare U (discount d) (mimicConsumption a 0) T := by
          simp only [welfare]
          rw [← intervalIntegral.integral_sub (hUc Δ hΔ0) (hUc 0 (by rw [abs_zero]; exact hδ0)),
            ← intervalIntegral.integral_const_mul]
          exact intervalIntegral.integral_mono_on hT (hIΔ.const_mul Δ)
            ((hUc Δ hΔ0).sub (hUc 0 (by rw [abs_zero]; exact hδ0)))
            (fun t ht => hpoint Δ hΔ0 t ht.1)
        -- `|∫ g Δ - ∫ g 0| ≤ ε`
        have hclose : |(∫ t in (0 : ℝ)..T, g Δ t) - ∫ t in (0 : ℝ)..T, g 0 t| ≤ ε := by
          rw [← intervalIntegral.integral_sub hIΔ hI0]
          have hexpI : IntervalIntegrable (fun t => ε * (d + m) * Real.exp (-(d + m) * t))
              volume 0 T := Continuous.intervalIntegrable (by fun_prop) 0 T
          calc |∫ t in (0 : ℝ)..T, g Δ t - g 0 t|
              ≤ ∫ t in (0 : ℝ)..T, ε * (d + m) * Real.exp (-(d + m) * t) := by
                rw [abs_le]
                constructor
                · have hexpN : IntervalIntegrable
                      (fun t => -(ε * (d + m) * Real.exp (-(d + m) * t))) volume 0 T := hexpI.neg
                  have h := intervalIntegral.integral_mono_on hT hexpN (hIΔ.sub hI0)
                    (fun t ht => show -(ε * (d + m) * Real.exp (-(d + m) * t)) ≤ g Δ t - g 0 t
                      from (abs_le.mp (hunif Δ hk t ht.1)).1)
                  rw [intervalIntegral.integral_neg] at h
                  exact h
                · exact intervalIntegral.integral_mono_on hT (hIΔ.sub hI0) hexpI
                    (fun t ht => (abs_le.mp (hunif Δ hk t ht.1)).2)
            _ = ε * (d + m) * ∫ t in (0 : ℝ)..T, Real.exp (-(d + m) * t) :=
                intervalIntegral.integral_const_mul _ _
            _ ≤ ε * (d + m) * (1 / (d + m)) :=
                mul_le_mul_of_nonneg_left (integral_exp_neg_le hdm T) (by positivity)
            _ = ε := by field_simp
        have hmul : |Δ * (∫ t in (0 : ℝ)..T, g Δ t) - Δ * ∫ t in (0 : ℝ)..T, g 0 t| ≤
            ε * |Δ| := by
          rw [← mul_sub, abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right hclose (abs_nonneg _)
        have := (abs_le.mp hmul).1
        linarith
      linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul, abs_le]
    constructor <;> nlinarith [abs_nonneg Δ]
  -- the sandwich
  have hH : HasDerivAt (fun k => value P k0 + q 0 * (k - k0)) (q 0) k0 := by
    have := ((hasDerivAt_id k0).sub_const k0).const_mul (q 0) |>.const_add (value P k0)
    simpa only [id, mul_one] using this
  refine clausen_strub_sandwich hLder hH ?_ ?_ hL0 (by ring)
  · filter_upwards [hnearδ0] with k hk
    exact hLV k hk
  · filter_upwards [hnearδ0] with k hk
    have hkpos : 0 < k := by
      have := (abs_lt.mp hk).1
      have : δ0 ≤ kmin / 2 := min_le_left _ _
      linarith [(hkbd 0 le_rfl).1]
    exact value_le_supergradient P hc hkpos

/-- When the optimum invests at time zero, `V'(k₀) = U'(c(0))`. -/
theorem value_deriv_eq_marginal_utility (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) (hz : 0 < a.investment 0) :
    HasDerivAt (value P) (deriv U (a.consumption 0)) (a.capital 0) := by
  have h := hc.slack 0 le_rfl
  have hq : q 0 = deriv U (a.consumption 0) := by
    rcases mul_eq_zero.mp h with h | h
    · linarith
    · exact absurd h (ne_of_gt hz)
  rw [← hq]
  exact value_hasDerivAt P hc

end RamseyCassKoopmans
