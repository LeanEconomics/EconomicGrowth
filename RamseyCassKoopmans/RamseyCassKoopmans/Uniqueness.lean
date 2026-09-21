import RamseyCassKoopmans.Verification
import RamseyCassKoopmans.Concavity

/-!
# Strict welfare separation and consumption uniqueness

With strictly concave utility and positive welfare weights, a feasible competitor
whose consumption differs at even one nonnegative time has strictly lower finite
limiting welfare than a supplied certified candidate. Continuity of controls is
essential here: it turns a strict pointwise gap into a positive integral.

This is uniqueness conditional on a supplied candidate and the stated terminal
comparison; it does not construct an optimal trajectory.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

/-- A continuous nonnegative function that is positive at one nonnegative time
has a strictly positive limiting cumulative integral, whenever that limit exists.
The proof uses a positive finite integral and monotonicity thereafter. -/
theorem positive_limit_of_integral_nonneg_of_pos
    {F : ℝ → ℝ} {L t₀ : ℝ}
    (hcont : ContinuousOn F (Ici 0))
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ F t)
    (ht₀ : 0 ≤ t₀) (hpos : 0 < F t₀)
    (hlim : Tendsto (fun T => ∫ t in (0 : ℝ)..T, F t) atTop (𝓝 L)) :
    0 < L := by
  have hT₀ : 0 < t₀ + 1 := by linarith
  have hpositive : 0 < ∫ t in (0 : ℝ)..(t₀ + 1), F t := by
    apply intervalIntegral.integral_pos hT₀
      (hcont.mono (fun _ ht => ht.1))
    · intro t ht
      exact hnonneg t ht.1.le
    · exact ⟨t₀, ⟨ht₀, by linarith⟩, hpos⟩
  have hle : (∫ t in (0 : ℝ)..(t₀ + 1), F t) ≤ L := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [eventually_ge_atTop (t₀ + 1)] with T hT
    have hTpos : 0 ≤ T := hT₀.le.trans hT
    apply intervalIntegral.integral_mono_interval le_rfl hT₀.le hT
    · exact (ae_restrict_mem measurableSet_Ioc).mono (fun t ht => hnonneg t ht.1.le)
    · exact (hcont.mono (fun _ ht => ht.1)).intervalIntegrable_of_Icc hTpos
  exact hpositive.trans_le hle

/-- The nonnegative instantaneous comparison surplus: weighted utility
advantage plus the derivative of the terminal-capital value gap. -/
noncomputable def comparisonSurplus {f U w : ℝ → ℝ} {m : ℝ}
    {a : FeasiblePath f m} (v : SupportingPrices f U w m a)
    (b : FeasiblePath f m) (t : ℝ) : ℝ :=
    w t * (U (a.consumption t) - U (b.consumption t)) + boundaryRate v b t

theorem comparisonSurplus_continuous {f U w : ℝ → ℝ} {m : ℝ}
    {a : FeasiblePath f m} (v : SupportingPrices f U w m a)
    (b : FeasiblePath f m) : ContinuousOn (comparisonSurplus v b) (Ici 0) := by
  exact (v.weight_continuous.mul
    ((v.utility_continuous.comp a.consumption_continuous
      (fun t ht => a.consumption_pos t ht)).sub
        (v.utility_continuous.comp b.consumption_continuous
          (fun t ht => b.consumption_pos t ht)))).add (boundaryRate_continuous v b)

/-- Strict utility concavity contributes a strict surplus whenever candidate
and competitor consumption differ. Production and allocation terms remain
nonnegative, including Cass's zero-investment corner. -/
theorem comparisonSurplus_pos_of_consumption_ne
    {f U w : ℝ → ℝ} {m t : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (ht : 0 ≤ t)
    (hstrict : StrictConcaveOn ℝ (Ioi 0) U)
    (hderiv : HasDerivAt U (v.marginalUtility t) (a.consumption t))
    (hw : 0 < w t) (hne : b.consumption t ≠ a.consumption t) :
    0 < comparisonSurplus v b t := by
  have hu := concavity_remainder_pos hstrict
    (a.consumption_pos t ht) (b.consumption_pos t ht) hderiv hne
  have hf : 0 ≤ f (a.capital t) - f (b.capital t) -
      v.marginalProduct t * (a.capital t - b.capital t) := by
    nlinarith [v.production_support t ht (b.capital t) (b.capital_nonneg t ht)]
  unfold comparisonSurplus boundaryRate
  rw [present_value_welfare_identity
    (U (a.consumption t)) (U (b.consumption t))
    (f (a.capital t)) (f (b.capital t))
    (a.consumption t) (b.consumption t) (a.investment t) (b.investment t)
    (a.capital t) (b.capital t) (v.marginalProduct t) (v.marginalUtility t)
    (v.price t) m (w t)
    (m * v.price t - w t * v.marginalUtility t * v.marginalProduct t)
    (a.resource t ht) (b.resource t ht) rfl]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg (mul_pos hw hu)
      (mul_nonneg (mul_nonneg hw.le (v.marginalUtility_nonneg t ht)) hf)) (halloc t ht)

/-- Fundamental theorem of calculus gives an exact finite-horizon surplus
identity. In particular, the terminal value is retained with its correct sign. -/
theorem integral_comparisonSurplus
    {f U w : ℝ → ℝ} {m T : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (hinit : a.capital 0 = b.capital 0) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, comparisonSurplus v b t) =
      welfare U w a.consumption T - welfare U w b.consumption T +
        boundary v.price a.capital b.capital T := by
  have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
  have haint := ((welfare_integrand_continuous v a).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hT
  have hbint := ((welfare_integrand_continuous v b).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hT
  have hBint := ((boundaryRate_continuous v b).mono hsub).intervalIntegrable_of_Icc
    (μ := volume) hT
  have hFTC : (∫ t in (0 : ℝ)..T, boundaryRate v b t) =
      boundary v.price a.capital b.capital T - boundary v.price a.capital b.capital 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hBint
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact hasDerivAt_boundary v b ht.1
  simp only [comparisonSurplus, mul_sub]
  rw [intervalIntegral.integral_add (haint.sub hbint) hBint,
    intervalIntegral.integral_sub haint hbint, hFTC]
  simp [welfare, boundary, hinit]

/-- Convergence of finite welfare and the terminal gap implies convergence of
the cumulative comparison surplus to the candidate's welfare advantage. -/
theorem tendsto_integral_comparisonSurplus
    {f U w : ℝ → ℝ} {m Ja Jb : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0)) :
    Tendsto (fun T => ∫ t in (0 : ℝ)..T, comparisonSurplus v b t)
      atTop (𝓝 (Ja - Jb)) := by
  have hlim := (ha.sub hb).add hterminal
  simp only [add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact (integral_comparisonSurplus v b hinit hT).symm

/-- A feasible competitor whose consumption differs at any nonnegative time
has strictly lower finite limiting welfare than the certified candidate. -/
theorem strict_welfare_separation
    {f U w : ℝ → ℝ} {m Ja Jb t₀ : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0))
    (hstrict : StrictConcaveOn ℝ (Ioi 0) U)
    (ht₀ : 0 ≤ t₀)
    (hderiv : HasDerivAt U (v.marginalUtility t₀) (a.consumption t₀))
    (hw : 0 < w t₀) (hne : b.consumption t₀ ≠ a.consumption t₀) :
    Jb < Ja := by
  have hpos : 0 < Ja - Jb := positive_limit_of_integral_nonneg_of_pos
    (comparisonSurplus_continuous v b)
    (fun t ht => pointwise_comparison v b halloc ht) ht₀
    (comparisonSurplus_pos_of_consumption_ne v b halloc ht₀ hstrict hderiv hw hne)
    (tendsto_integral_comparisonSurplus v b hinit ha hb hterminal)
  linarith

/-- Equal finite welfare forces equality of consumption at every nonnegative
time. Continuous controls make pointwise equality appropriate, rather than
merely equality almost everywhere. -/
theorem consumption_eq_of_welfare_eq
    {f U w : ℝ → ℝ} {m Ja Jb : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0))
    (hstrict : StrictConcaveOn ℝ (Ioi 0) U)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt U (v.marginalUtility t) (a.consumption t))
    (hw : ∀ t, 0 ≤ t → 0 < w t) (heq : Jb = Ja) :
    ∀ t, 0 ≤ t → b.consumption t = a.consumption t := by
  intro t ht
  by_contra hne
  have hlt := strict_welfare_separation v b halloc hinit ha hb hterminal hstrict ht
    (hderiv t ht) (hw t ht) hne
  linarith

/-- Strictly concave production gives a strictly positive surplus at a capital
discrepancy, provided the utility marginal value and welfare weight are positive. -/
theorem comparisonSurplus_pos_of_capital_ne
    {f U w : ℝ → ℝ} {m t : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (ht : 0 ≤ t)
    (hstrict : StrictConcaveOn ℝ (Ici 0) f)
    (hderiv : HasDerivAt f (v.marginalProduct t) (a.capital t))
    (hw : 0 < w t) (hmu : 0 < v.marginalUtility t)
    (hne : b.capital t ≠ a.capital t) : 0 < comparisonSurplus v b t := by
  have hf := concavity_remainder_pos hstrict
    (a.capital_nonneg t ht) (b.capital_nonneg t ht) hderiv hne
  have hu : 0 ≤ U (a.consumption t) - U (b.consumption t) -
      v.marginalUtility t * (a.consumption t - b.consumption t) := by
    nlinarith [v.utility_support t ht (b.consumption t) (b.consumption_pos t ht)]
  unfold comparisonSurplus boundaryRate
  rw [present_value_welfare_identity
    (U (a.consumption t)) (U (b.consumption t))
    (f (a.capital t)) (f (b.capital t))
    (a.consumption t) (b.consumption t) (a.investment t) (b.investment t)
    (a.capital t) (b.capital t) (v.marginalProduct t) (v.marginalUtility t)
    (v.price t) m (w t)
    (m * v.price t - w t * v.marginalUtility t * v.marginalProduct t)
    (a.resource t ht) (b.resource t ht) rfl]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_nonneg_of_pos (mul_nonneg hw.le hu) (mul_pos (mul_pos hw hmu) hf))
      (halloc t ht)

/-- A capital discrepancy likewise forces strictly lower competitor welfare
when production is strictly concave and marginal utility is strictly positive. -/
theorem strict_welfare_separation_of_capital_ne
    {f U w : ℝ → ℝ} {m Ja Jb t₀ : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0))
    (hstrict : StrictConcaveOn ℝ (Ici 0) f)
    (ht₀ : 0 ≤ t₀)
    (hderiv : HasDerivAt f (v.marginalProduct t₀) (a.capital t₀))
    (hw : 0 < w t₀) (hmu : 0 < v.marginalUtility t₀)
    (hne : b.capital t₀ ≠ a.capital t₀) : Jb < Ja := by
  have hpos : 0 < Ja - Jb := positive_limit_of_integral_nonneg_of_pos
    (comparisonSurplus_continuous v b)
    (fun t ht => pointwise_comparison v b halloc ht) ht₀
    (comparisonSurplus_pos_of_capital_ne v b halloc ht₀ hstrict hderiv hw hmu hne)
    (tendsto_integral_comparisonSurplus v b hinit ha hb hterminal)
  linarith

/-- Equal welfare forces capital equality under strict technology concavity,
actual marginal-product prices and positive marginal utility. -/
theorem capital_eq_of_welfare_eq
    {f U w : ℝ → ℝ} {m Ja Jb : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0))
    (hstrict : StrictConcaveOn ℝ (Ici 0) f)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt f (v.marginalProduct t) (a.capital t))
    (hw : ∀ t, 0 ≤ t → 0 < w t)
    (hmu : ∀ t, 0 ≤ t → 0 < v.marginalUtility t) (heq : Jb = Ja) :
    ∀ t, 0 ≤ t → b.capital t = a.capital t := by
  intro t ht
  by_contra hne
  have hlt := strict_welfare_separation_of_capital_ne v b halloc hinit ha hb hterminal
    hstrict ht (hderiv t ht) (hw t ht) (hmu t ht) hne
  linarith

/-- Under strict utility and technology concavity, equal finite welfare implies
equality of capital, consumption and investment on the economic time domain.
The proof includes the investment identity via feasibility; no uniqueness of an
unconstructed ODE solution is assumed. -/
theorem path_eq_of_welfare_eq
    {f U w : ℝ → ℝ} {m Ja Jb : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0))
    (hstrictU : StrictConcaveOn ℝ (Ioi 0) U)
    (hstrictF : StrictConcaveOn ℝ (Ici 0) f)
    (hderivU : ∀ t, 0 ≤ t → HasDerivAt U (v.marginalUtility t) (a.consumption t))
    (hderivF : ∀ t, 0 ≤ t → HasDerivAt f (v.marginalProduct t) (a.capital t))
    (hw : ∀ t, 0 ≤ t → 0 < w t)
    (hmu : ∀ t, 0 ≤ t → 0 < v.marginalUtility t) (heq : Jb = Ja) :
    ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
      b.consumption t = a.consumption t ∧ b.investment t = a.investment t := by
  intro t ht
  have hk := capital_eq_of_welfare_eq v b halloc hinit ha hb hterminal
    hstrictF hderivF hw hmu heq t ht
  have hc := consumption_eq_of_welfare_eq v b halloc hinit ha hb hterminal
    hstrictU hderivU hw heq t ht
  refine ⟨hk, hc, ?_⟩
  have hresourceA := a.resource t ht
  have hresourceB := b.resource t ht
  rw [hk, hc] at hresourceB
  linarith

end RamseyCassKoopmans
