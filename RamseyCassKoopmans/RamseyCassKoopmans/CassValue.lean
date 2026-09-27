/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import RamseyCassKoopmans.CassComparative

/-!
# The Cass value function: monotonicity, strict concavity, and a supergradient

`value P k` is the optimal lifetime welfare from capital `k`. We prove:

* `value_spec`, `value_ge`: it is attained by the certified optimum and bounds the
  welfare of every Cass-feasible path from `k`;
* `value_strictMono`: it is strictly increasing. From a higher stock, copying the
  lower optimum's investment leaves strictly more output to consume;
* `value_strictConcave`: it is strictly concave. A mixture of two optimal paths is
  feasible, and strict concavity of `f` gives it strictly more consumption;
* `value_le_supergradient`: the initial current-value costate is a supergradient,
  `V(k₁) ≤ V(k₀) + q(0) (k₁ - k₀)`, from the verification comparison with unequal
  initial stocks (`finite_horizon_comparison'`).

The envelope theorem `V'(k₀) = q(0)` is in `CassEnvelope`.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

/-- A continuous positive function on `[0, ∞)` with a positive limit lies in a
compact subinterval of `(0, ∞)`. -/
theorem exists_pos_bounds {c : ℝ → ℝ} (hc : ContinuousOn c (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < c t) {L : ℝ} (hL : 0 < L) (hlim : Tendsto c atTop (𝓝 L)) :
    ∃ lo hi, 0 < lo ∧ lo ≤ hi ∧ ∀ t, 0 ≤ t → lo ≤ c t ∧ c t ≤ hi := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp ((hlim.eventually (lt_mem_nhds (half_lt_self hL))).and
    ((hlim.eventually (gt_mem_nhds (lt_add_one L)))))
  set T' := max T 0
  have hT' : 0 ≤ T' := le_max_right _ _
  obtain ⟨x, hx, hxmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT')
    (hc.mono (fun _ ht => ht.1))
  obtain ⟨y, hy, hymax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT')
    (hc.mono (fun _ ht => ht.1))
  have hxpos := hpos x hx.1
  refine ⟨min (L / 2) (c x), max (L + 1) (c y), lt_min (half_pos hL) hxpos,
    (min_le_left _ _).trans (by linarith [le_max_left (L + 1) (c y)]), fun t ht => ?_⟩
  rcases le_total t T' with htT | htT
  · exact ⟨(min_le_right _ _).trans (hxmin ⟨ht, htT⟩),
      (hymax ⟨ht, htT⟩).trans (le_max_right _ _)⟩
  · have h := hT t ((le_max_left _ _).trans htT)
    exact ⟨(min_le_left _ _).trans h.1.le, h.2.le.trans (le_max_left _ _)⟩

theorem CassPrimitives.f_cont (P : CassPrimitives f U d m) : ContinuousOn f (Ioi 0) :=
  fun k hk => (P.f_diff k hk).continuousAt.continuousWithinAt

theorem CassPrimitives.f_strictMono (P : CassPrimitives f U d m) : StrictMonoOn f (Ioi 0) :=
  strictMonoOn_of_deriv_pos (convex_Ioi 0) P.f_cont
    (fun k hk => by rw [interior_Ioi] at hk; exact P.f_prime_pos k hk)

theorem CassPrimitives.U_strictMono (P : CassPrimitives f U d m) : StrictMonoOn U (Ioi 0) :=
  strictMonoOn_of_deriv_pos (convex_Ioi 0) P.U_cont
    (fun c hc => by rw [interior_Ioi] at hc; exact P.U_prime_pos c hc)

/-- Welfare exists for a path whose consumption stays in a compact positive interval. -/
theorem CassPrimitives.exists_welfare (P : CassPrimitives f U d m) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Ici 0)) {lo hi : ℝ} (hlo : 0 < lo) (hlh : lo ≤ hi)
    (hb : ∀ t, 0 ≤ t → lo ≤ c t ∧ c t ≤ hi) : ∃ J, HasWelfare U (discount d) c J :=
  exists_hasWelfare_of_compact_consumption U c P.d_pos hlh
    (P.U_cont.mono (fun _ hx => hlo.trans_le hx.1)) hc (fun t ht => ⟨(hb t ht).1, (hb t ht).2⟩)

/-- The certified optimum's welfare exists. -/
theorem optimalPath_welfare (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k) :
    ∃ J, HasWelfare U (discount d) (optimalPath P hk).consumption J := by
  obtain ⟨q, -, hc⟩ := optimalPath_spec P hk
  exact hc.welfare

/-- Optimal lifetime welfare from capital `k`. -/
noncomputable def value (P : CassPrimitives f U d m) (k : ℝ) : ℝ :=
  if hk : 0 < k then Classical.choose (optimalPath_welfare P hk) else 0

theorem value_spec (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k) :
    HasWelfare U (discount d) (optimalPath P hk).consumption (value P k) := by
  simp only [value, hk, ↓reduceDIte]
  exact Classical.choose_spec (optimalPath_welfare P hk)

/-- The value bounds the welfare of every Cass-feasible path from `k`. -/
theorem value_ge (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k) {b : FeasiblePath f m}
    (hb : b.NonnegativeInvestment) (hb0 : b.capital 0 = k) {J : ℝ}
    (hJ : HasWelfare U (discount d) b.consumption J) : J ≤ value P k := by
  obtain ⟨q, h0, hc⟩ := optimalPath_spec P hk
  exact (hc.isCassOptimal P (value_spec P hk)).2.2 b hb (h0.trans hb0.symm) J hJ

/-- A certified path from `k` attains the value. -/
theorem value_eq (P : CassPrimitives f U d m) {a : FeasiblePath f m} {q : ℝ → ℝ}
    (hc : CassCertificate f U d m a q) {J : ℝ} (hJ : HasWelfare U (discount d) a.consumption J) :
    value P (a.capital 0) = J := by
  have hk := hc.capital_pos 0 le_rfl
  obtain ⟨qo, h0, hoc⟩ := optimalPath_spec P hk
  exact ((hc.eq_of_isCassOptimal P hJ (hoc.isCassOptimal P (value_spec P hk)) h0.symm).1)

/-- The finite-horizon comparison with unequal initial stocks: the boundary term at
time zero is retained. -/
theorem finite_horizon_comparison' {w : ℝ → ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) {T : ℝ} (hT : 0 ≤ T) :
    welfare U w b.consumption T - welfare U w a.consumption T ≤
      boundary v.price a.capital b.capital T - boundary v.price a.capital b.capital 0 := by
  have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
  have haint :=
    ((welfare_integrand_continuous v a).mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
  have hbint :=
    ((welfare_integrand_continuous v b).mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
  have hBint := ((boundaryRate_continuous v b).mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
  have hFTC : (∫ t in (0 : ℝ)..T, boundaryRate v b t) =
      boundary v.price a.capital b.capital T - boundary v.price a.capital b.capital 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hBint
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact hasDerivAt_boundary v b ht.1
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..T,
      (w t * U (a.consumption t) - w t * U (b.consumption t)) + boundaryRate v b t := by
    apply intervalIntegral.integral_nonneg hT
    intro t ht
    simpa only [mul_sub] using pointwise_comparison v b halloc ht.1
  rw [intervalIntegral.integral_add (haint.sub hbint) hBint,
    intervalIntegral.integral_sub haint hbint, hFTC] at hnonneg
  change welfare U w a.consumption T - welfare U w b.consumption T +
    (boundary v.price a.capital b.capital T - boundary v.price a.capital b.capital 0) ≥ 0
    at hnonneg
  linarith

/-- The initial current-value costate is a supergradient of the value function. -/
theorem value_le_supergradient (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) {k1 : ℝ} (hk1 : 0 < k1) :
    value P k1 ≤ value P (a.capital 0) + q 0 * (k1 - a.capital 0) := by
  obtain ⟨Ja, hJa⟩ := hc.welfare
  rw [value_eq P hc hJa]
  obtain ⟨qb, hb0, hbc⟩ := optimalPath_spec P hk1
  set b := optimalPath P hk1
  have hJb := value_spec P hk1
  let v := cassSupportingPrices f U q d m a P.f_conc.concaveOn P.U_conc.concaveOn P.U_cont
    P.f_diff P.U_diff P.f_prime_cont P.U_prime_cont hc.capital_pos
    (fun t ht => (P.U_prime_pos _ (a.consumption_pos t ht)).le) hc.costate
  have halloc : AllocationComparison v b := by
    apply allocation_of_cass v
    · intro t ht
      exact mul_le_mul_of_nonneg_left (hc.wedge t ht) (discount_pos d t).le
    · intro t ht
      change (discount d t * q t - discount d t * deriv U (a.consumption t)) *
        a.investment t = 0
      calc
        _ = discount d t * ((q t - deriv U (a.consumption t)) * a.investment t) := by ring
        _ = 0 := by rw [hc.slack t ht, mul_zero]
    · exact hbc.investment_nonneg
  obtain ⟨K, hK, hcap⟩ := P.exists_capacity (max (a.capital 0) k1)
  have hterm : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0) :=
    Terminal.terminal_tendsto_zero_of_bounded_capital hc.transversality
      (fun t ht => ⟨a.capital_nonneg t ht,
        a.capital_le_capacity hcap ((le_max_left _ _).trans hK) t ht⟩)
      (fun t ht => ⟨b.capital_nonneg t ht,
        b.capital_le_capacity hcap (hb0 ▸ (le_max_right _ _).trans hK) t ht⟩)
  have hle : value P k1 - Ja ≤ 0 - boundary v.price a.capital b.capital 0 :=
    le_of_tendsto_of_tendsto (hJb.sub hJa) (hterm.sub_const _)
      (by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        exact finite_horizon_comparison' v b halloc hT)
  have hB0 : boundary v.price a.capital b.capital 0 = q 0 * (a.capital 0 - k1) := by
    simp only [boundary, v, cassSupportingPrices, discount, mul_zero, Real.exp_zero, one_mul, hb0]
  rw [hB0] at hle
  linarith

/-- The path that copies `a`'s investment from a different initial stock. -/
noncomputable def FeasiblePath.mimic (P : CassPrimitives f U d m) (a : FeasiblePath f m)
    (Δ : ℝ) (hk : ∀ t, 0 ≤ t → 0 < a.capital t + Δ * Real.exp (-m * t))
    (hc : ∀ t, 0 ≤ t → 0 < f (a.capital t + Δ * Real.exp (-m * t)) - a.investment t) :
    FeasiblePath f m where
  capital := fun t => a.capital t + Δ * Real.exp (-m * t)
  consumption := fun t => f (a.capital t + Δ * Real.exp (-m * t)) - a.investment t
  investment := a.investment
  capital_nonneg := fun t ht => (hk t ht).le
  consumption_pos := hc
  consumption_continuous := by
    apply ContinuousOn.sub _ a.investment_continuous
    exact P.f_cont.comp (a.capital_continuous.add (continuousOn_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn))
      (fun t ht => hk t ht)
  investment_continuous := a.investment_continuous
  resource := fun t _ => by ring
  dynamics := fun t ht => by
    have he : HasDerivAt (fun s => Δ * Real.exp (-m * s)) (Δ * (Real.exp (-m * t) * (-m))) t := by
      have := ((hasDerivAt_id t).const_mul (-m)).exp.const_mul Δ
      simpa only [id, mul_one] using this
    refine ((a.dynamics t ht).add he).congr_deriv ?_
    ring

/-- The value function is strictly increasing. -/
theorem value_strictMono (P : CassPrimitives f U d m) : StrictMonoOn (value P) (Ioi 0) := by
  intro k0 hk0 k1 hk1 h01
  have hk0' : (0 : ℝ) < k0 := hk0
  obtain ⟨q, ha0, hc⟩ := optimalPath_spec P hk0'
  set a := optimalPath P hk0'
  set Δ := k1 - k0
  have hΔ : 0 < Δ := sub_pos.mpr h01
  have hkb : ∀ t, 0 ≤ t → a.capital t < a.capital t + Δ * Real.exp (-m * t) := fun t _ => by
    have := mul_pos hΔ (Real.exp_pos (-m * t))
    linarith
  have hcb : ∀ t, 0 ≤ t → a.consumption t <
      f (a.capital t + Δ * Real.exp (-m * t)) - a.investment t := fun t ht => by
    have hf := P.f_strictMono (hc.capital_pos t ht) ((hc.capital_pos t ht).trans (hkb t ht))
      (hkb t ht)
    have hr := a.resource t ht
    linarith
  let b := a.mimic P Δ (fun t ht => (hc.capital_pos t ht).trans (hkb t ht))
    (fun t ht => (a.consumption_pos t ht).trans (hcb t ht))
  have hb0 : b.capital 0 = k1 := by
    change a.capital 0 + Δ * Real.exp (-m * 0) = k1
    rw [ha0, mul_zero, Real.exp_zero, mul_one]
    ring
  -- `b`'s consumption is bounded between `a`'s lower bound and output at a capacity
  obtain ⟨hk, hcon, -⟩ := hc.dynamics P
  obtain ⟨lo, hi, hlo, hlh, hbd⟩ := exists_pos_bounds a.consumption_continuous
    a.consumption_pos (cassSteadyConsumption_pos P) hcon
  obtain ⟨K, hK, hcap⟩ := P.exists_capacity (a.capital 0)
  have hkK : ∀ t, 0 ≤ t → a.capital t ≤ K := a.capital_le_capacity hcap hK
  have hbub : ∀ t, 0 ≤ t → b.consumption t ≤ f (K + Δ) := fun t ht => by
    change f (a.capital t + Δ * Real.exp (-m * t)) - a.investment t ≤ f (K + Δ)
    have hz := hc.investment_nonneg t ht
    have hle : a.capital t + Δ * Real.exp (-m * t) ≤ K + Δ := by
      have := mul_le_of_le_one_right hΔ.le (Real.exp_le_one_iff.mpr
        (by nlinarith [P.m_pos, ht] : -m * t ≤ 0))
      linarith [hkK t ht]
    have hmono := P.f_strictMono.monotoneOn ((hc.capital_pos t ht).trans (hkb t ht))
      (show (0 : ℝ) < K + Δ by linarith [hc.capital_pos t ht, hkK t ht]) hle
    linarith
  obtain ⟨Jb, hJb⟩ := P.exists_welfare b.consumption_continuous hlo
    (show lo ≤ f (K + Δ) from ((hbd 0 le_rfl).1.trans (hcb 0 le_rfl).le).trans (hbub 0 le_rfl))
    (fun t ht => ⟨((hbd t ht).1.trans (hcb t ht).le), hbub t ht⟩)
  have hvb := value_ge P hk1 (b := b) hc.investment_nonneg hb0 hJb
  have hva := value_spec P hk0'
  -- strictly positive welfare gain
  have hgain : 0 < Jb - value P k0 := by
    apply positive_limit_of_integral_nonneg_of_pos (F := fun t =>
      discount d t * U (b.consumption t) - discount d t * U (a.consumption t)) (t₀ := 0)
    · exact ((discount_continuous d).continuousOn.mul (P.U_cont.comp b.consumption_continuous
        b.consumption_pos)).sub ((discount_continuous d).continuousOn.mul
        (P.U_cont.comp a.consumption_continuous a.consumption_pos))
    · intro t ht
      have := P.U_strictMono (a.consumption_pos t ht) (b.consumption_pos t ht) (hcb t ht)
      nlinarith [discount_pos d t]
    · exact le_rfl
    · have := P.U_strictMono (a.consumption_pos 0 le_rfl) (b.consumption_pos 0 le_rfl)
        (hcb 0 le_rfl)
      nlinarith [discount_pos d 0]
    · refine (hJb.sub hva).congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
      have h1 : IntervalIntegrable (fun t => discount d t * U (b.consumption t)) volume 0 T :=
        (((discount_continuous d).continuousOn.mul (P.U_cont.comp
        b.consumption_continuous b.consumption_pos)).mono hsub).intervalIntegrable_of_Icc hT
      have h2 : IntervalIntegrable (fun t => discount d t * U (a.consumption t)) volume 0 T :=
        (((discount_continuous d).continuousOn.mul (P.U_cont.comp
        a.consumption_continuous a.consumption_pos)).mono hsub).intervalIntegrable_of_Icc hT
      simp only [welfare]
      exact (intervalIntegral.integral_sub h1 h2).symm
  linarith

/-- The mixture of two paths: capital and investment are averaged, and consumption
takes the output at averaged capital net of averaged investment. -/
noncomputable def FeasiblePath.mix (P : CassPrimitives f U d m) (a b : FeasiblePath f m)
    (θ : ℝ)
    (hk : ∀ t, 0 ≤ t → 0 < θ * a.capital t + (1 - θ) * b.capital t)
    (hc : ∀ t, 0 ≤ t → 0 < f (θ * a.capital t + (1 - θ) * b.capital t) -
      (θ * a.investment t + (1 - θ) * b.investment t)) : FeasiblePath f m where
  capital := fun t => θ * a.capital t + (1 - θ) * b.capital t
  consumption := fun t => f (θ * a.capital t + (1 - θ) * b.capital t) -
    (θ * a.investment t + (1 - θ) * b.investment t)
  investment := fun t => θ * a.investment t + (1 - θ) * b.investment t
  capital_nonneg := fun t ht => (hk t ht).le
  consumption_pos := hc
  consumption_continuous := by
    apply ContinuousOn.sub _ ((continuousOn_const.mul a.investment_continuous).add
      (continuousOn_const.mul b.investment_continuous))
    exact P.f_cont.comp ((continuousOn_const.mul a.capital_continuous).add
      (continuousOn_const.mul b.capital_continuous)) (fun t ht => hk t ht)
  investment_continuous := (continuousOn_const.mul a.investment_continuous).add
      (continuousOn_const.mul b.investment_continuous)
  resource := fun t _ => by ring
  dynamics := fun t ht => by
    refine (((a.dynamics t ht).const_mul θ).add
      ((b.dynamics t ht).const_mul (1 - θ))).congr_deriv ?_
    ring

/-- The value function is strictly concave. -/
theorem value_strictConcave (P : CassPrimitives f U d m) :
    StrictConcaveOn ℝ (Ioi 0) (value P) := by
  refine ⟨convex_Ioi 0, fun k0 hk0 k1 hk1 hne θ θ' hθ hθ' hsum => ?_⟩
  have hk0' : (0 : ℝ) < k0 := hk0
  have hk1' : (0 : ℝ) < k1 := hk1
  obtain ⟨qa, ha0, hca⟩ := optimalPath_spec P hk0'
  obtain ⟨qb, hb0, hcb⟩ := optimalPath_spec P hk1'
  set a := optimalPath P hk0'
  set b := optimalPath P hk1'
  have hθ'' : θ' = 1 - θ := by linarith
  subst hθ''
  have hkm : ∀ t, 0 ≤ t → 0 < θ * a.capital t + (1 - θ) * b.capital t := fun t ht => by
    have := mul_pos hθ (hca.capital_pos t ht)
    have := mul_pos hθ' (hcb.capital_pos t ht)
    linarith
  -- concavity of `f`: mixed output is at least the mixture of outputs
  have hfmix : ∀ t, 0 ≤ t → θ * f (a.capital t) + (1 - θ) * f (b.capital t) ≤
      f (θ * a.capital t + (1 - θ) * b.capital t) := fun t ht =>
    P.f_conc.concaveOn.2 (a.capital_nonneg t ht) (b.capital_nonneg t ht) hθ.le hθ'.le
      (by ring)
  have hcm : ∀ t, 0 ≤ t → θ * a.consumption t + (1 - θ) * b.consumption t ≤
      f (θ * a.capital t + (1 - θ) * b.capital t) -
        (θ * a.investment t + (1 - θ) * b.investment t) := fun t ht => by
    have := hfmix t ht
    have ha := a.resource t ht
    have hb := b.resource t ht
    nlinarith
  have hcpos : ∀ t, 0 ≤ t → 0 < θ * a.consumption t + (1 - θ) * b.consumption t :=
    fun t ht => by
      have := mul_pos hθ (a.consumption_pos t ht)
      have := mul_pos hθ' (b.consumption_pos t ht)
      linarith
  let c := a.mix P b θ hkm (fun t ht => (hcpos t ht).trans_le (hcm t ht))
  have hc0 : c.capital 0 = θ • k0 + (1 - θ) • k1 := by
    change θ * a.capital 0 + (1 - θ) * b.capital 0 = _
    rw [ha0, hb0, smul_eq_mul, smul_eq_mul]
  -- bounds for the welfare of the mixture
  obtain ⟨-, hacon, -⟩ := hca.dynamics P
  obtain ⟨-, hbcon, -⟩ := hcb.dynamics P
  obtain ⟨loa, hia, hloa, -, hbda⟩ := exists_pos_bounds a.consumption_continuous
    a.consumption_pos (cassSteadyConsumption_pos P) hacon
  obtain ⟨lob, hib, hlob, -, hbdb⟩ := exists_pos_bounds b.consumption_continuous
    b.consumption_pos (cassSteadyConsumption_pos P) hbcon
  obtain ⟨K, hK, hcap⟩ := P.exists_capacity (max k0 k1)
  have hkKa := a.capital_le_capacity hcap (ha0 ▸ (le_max_left _ _).trans hK)
  have hkKb := b.capital_le_capacity hcap (hb0 ▸ (le_max_right _ _).trans hK)
  set lo := min loa lob
  have hlo : 0 < lo := lt_min hloa hlob
  have hclo : ∀ t, 0 ≤ t → lo ≤ c.consumption t := fun t ht => by
    have h1 := (hbda t ht).1
    have h2 := (hbdb t ht).1
    have h3 : lo ≤ θ * a.consumption t + (1 - θ) * b.consumption t := by
      have := mul_le_mul_of_nonneg_left ((min_le_left loa lob).trans h1) hθ.le
      have := mul_le_mul_of_nonneg_left ((min_le_right loa lob).trans h2) hθ'.le
      nlinarith
    exact h3.trans (hcm t ht)
  have hchi : ∀ t, 0 ≤ t → c.consumption t ≤ f K := fun t ht => by
    change f (θ * a.capital t + (1 - θ) * b.capital t) -
      (θ * a.investment t + (1 - θ) * b.investment t) ≤ f K
    have hz : 0 ≤ θ * a.investment t + (1 - θ) * b.investment t := by
      have := mul_nonneg hθ.le (hca.investment_nonneg t ht)
      have := mul_nonneg hθ'.le (hcb.investment_nonneg t ht)
      linarith
    have hkle : θ * a.capital t + (1 - θ) * b.capital t ≤ K := by
      have := mul_le_mul_of_nonneg_left (hkKa t ht) hθ.le
      have := mul_le_mul_of_nonneg_left (hkKb t ht) hθ'.le
      nlinarith
    have := P.f_strictMono.monotoneOn (hkm t ht) ((hkm t ht).trans_le hkle) hkle
    linarith
  obtain ⟨Jc, hJc⟩ := P.exists_welfare c.consumption_continuous hlo
    ((hclo 0 le_rfl).trans (hchi 0 le_rfl)) (fun t ht => ⟨hclo t ht, hchi t ht⟩)
  have hcinv : c.NonnegativeInvestment := fun t ht => by
    have := mul_nonneg hθ.le (hca.investment_nonneg t ht)
    have := mul_nonneg hθ'.le (hcb.investment_nonneg t ht)
    change 0 ≤ θ * a.investment t + (1 - θ) * b.investment t
    linarith
  have hvc := value_ge P (show 0 < θ • k0 + (1 - θ) • k1 from hc0 ▸ hkm 0 le_rfl) hcinv hc0 hJc
  have hva := value_spec P hk0'
  have hvb := value_spec P hk1'
  -- the strict gain at time zero from strict concavity of `f`
  have hstrict0 : θ * a.consumption 0 + (1 - θ) * b.consumption 0 < c.consumption 0 := by
    have hne' : a.capital 0 ≠ b.capital 0 := by rw [ha0, hb0]; exact hne
    have hf := P.f_conc.2 (a.capital_nonneg 0 le_rfl) (b.capital_nonneg 0 le_rfl) hne' hθ hθ'
      (by ring)
    simp only [smul_eq_mul] at hf
    have ha := a.resource 0 le_rfl
    have hb := b.resource 0 le_rfl
    change _ < f (θ * a.capital 0 + (1 - θ) * b.capital 0) -
      (θ * a.investment 0 + (1 - θ) * b.investment 0)
    nlinarith
  have hUmix : ∀ t, 0 ≤ t → θ * U (a.consumption t) + (1 - θ) * U (b.consumption t) ≤
      U (c.consumption t) := fun t ht => by
    have h1 := P.U_conc.concaveOn.2 (a.consumption_pos t ht) (b.consumption_pos t ht) hθ.le
      hθ'.le (by ring)
    simp only [smul_eq_mul] at h1
    have h2 := P.U_strictMono.monotoneOn (hcpos t ht) (c.consumption_pos t ht) (hcm t ht)
    linarith
  have hgain : 0 < Jc - (θ * value P k0 + (1 - θ) * value P k1) := by
    apply positive_limit_of_integral_nonneg_of_pos (F := fun t =>
      discount d t * U (c.consumption t) - (θ * (discount d t * U (a.consumption t)) +
        (1 - θ) * (discount d t * U (b.consumption t)))) (t₀ := 0)
    · have hU : ∀ e : FeasiblePath f m,
          ContinuousOn (fun t => discount d t * U (e.consumption t)) (Ici 0) := fun e =>
        (discount_continuous d).continuousOn.mul (P.U_cont.comp e.consumption_continuous
          e.consumption_pos)
      exact (hU c).sub (((hU a).const_smul θ).add ((hU b).const_smul (1 - θ)))
    · intro t ht
      have := hUmix t ht
      nlinarith [discount_pos d t]
    · exact le_rfl
    · have h1 := P.U_conc.concaveOn.2 (a.consumption_pos 0 le_rfl) (b.consumption_pos 0 le_rfl)
        hθ.le hθ'.le (by ring)
      simp only [smul_eq_mul] at h1
      have h2 := P.U_strictMono (hcpos 0 le_rfl) (c.consumption_pos 0 le_rfl) hstrict0
      nlinarith [discount_pos d 0]
    · refine (hJc.sub ((hva.const_mul θ).add (hvb.const_mul (1 - θ)))).congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
      have hI : ∀ e : FeasiblePath f m, IntervalIntegrable
          (fun t => discount d t * U (e.consumption t)) volume 0 T := fun e =>
        (((discount_continuous d).continuousOn.mul (P.U_cont.comp e.consumption_continuous
          e.consumption_pos)).mono hsub).intervalIntegrable_of_Icc hT
      simp only [welfare]
      rw [intervalIntegral.integral_sub (hI c) (((hI a).const_mul θ).add
        ((hI b).const_mul (1 - θ))), intervalIntegral.integral_add ((hI a).const_mul θ)
        ((hI b).const_mul (1 - θ)), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
  simp only [smul_eq_mul] at hvc ⊢
  linarith

end RamseyCassKoopmans
