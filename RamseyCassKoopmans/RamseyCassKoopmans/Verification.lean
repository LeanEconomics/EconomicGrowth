import RamseyCassKoopmans.Model
import RamseyCassKoopmans.Algebra
import RamseyCassKoopmans.Terminal

/-!
# Optimality verification

The finite-horizon comparison retains terminal capital. Optimality is then
proved for finite limiting welfare values, with the boundary limit explicit.
The hypotheses certify a supplied candidate; they do not assert that one exists.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

/-- Supporting prices and tangent bounds along a candidate path. The supporting
bounds can be derived from concavity and differentiability. Time regularity is
explicit. The price is in present value, so the discount weight occurs in the
costate equation. -/
structure SupportingPrices (f U w : ℝ → ℝ) (m : ℝ) (a : FeasiblePath f m) where
  price : ℝ → ℝ
  marginalUtility : ℝ → ℝ
  marginalProduct : ℝ → ℝ
  weight_nonneg : ∀ t, 0 ≤ t → 0 ≤ w t
  weight_continuous : ContinuousOn w (Ici 0)
  utility_continuous : ContinuousOn U (Ioi 0)
  marginalUtility_continuous : ContinuousOn marginalUtility (Ici 0)
  marginalProduct_continuous : ContinuousOn marginalProduct (Ici 0)
  marginalUtility_nonneg : ∀ t, 0 ≤ t → 0 ≤ marginalUtility t
  utility_support : ∀ t, 0 ≤ t → ∀ c, 0 < c →
    U c - U (a.consumption t) ≤ marginalUtility t * (c - a.consumption t)
  production_support : ∀ t, 0 ≤ t → ∀ k, 0 ≤ k →
    f k - f (a.capital t) ≤ marginalProduct t * (k - a.capital t)
  costate : ∀ t, 0 ≤ t → HasDerivAt price
    (m * price t - w t * marginalUtility t * marginalProduct t) t

theorem SupportingPrices.price_continuous {f U w : ℝ → ℝ} {m : ℝ}
    {a : FeasiblePath f m} (v : SupportingPrices f U w m a) :
    ContinuousOn v.price (Ici 0) := by
  intro t ht
  exact (v.costate t ht).continuousAt.continuousWithinAt

/-- The allocation comparison holds for Cass by complementary slackness, and
for Koopmans's interior allocation because the price wedge is zero. -/
def AllocationComparison {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m) : Prop :=
  ∀ t, 0 ≤ t →
    0 ≤ (v.price t - w t * v.marginalUtility t) * (a.investment t - b.investment t)

theorem allocation_of_cass {f U w : ℝ → ℝ} {m : ℝ} {a b : FeasiblePath f m}
    (v : SupportingPrices f U w m a)
    (hwedge : ∀ t, 0 ≤ t → v.price t ≤ w t * v.marginalUtility t)
    (hslack : ∀ t, 0 ≤ t →
      (v.price t - w t * v.marginalUtility t) * a.investment t = 0)
    (hb : b.NonnegativeInvestment) : AllocationComparison v b := by
  intro t ht
  exact complementarity_welfare_term (w t * v.marginalUtility t) (v.price t)
    (a.investment t) (b.investment t) (hwedge t ht) (hslack t ht) (hb t ht)

theorem allocation_of_interior {f U w : ℝ → ℝ} {m : ℝ} {a b : FeasiblePath f m}
    (v : SupportingPrices f U w m a)
    (hprice : ∀ t, 0 ≤ t → v.price t = w t * v.marginalUtility t) :
    AllocationComparison v b := by
  intro t ht
  simp [hprice t ht]

def boundaryRate {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m) (t : ℝ) : ℝ :=
  (m * v.price t - w t * v.marginalUtility t * v.marginalProduct t) *
      (a.capital t - b.capital t) +
    v.price t * ((a.investment t - m * a.capital t) -
      (b.investment t - m * b.capital t))

theorem hasDerivAt_boundary {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (boundary v.price a.capital b.capital) (boundaryRate v b t) t := by
  exact (v.costate t ht).mul ((a.dynamics t ht).sub (b.dynamics t ht))

theorem boundaryRate_continuous {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m) :
    ContinuousOn (boundaryRate v b) (Ici 0) := by
  exact (((continuousOn_const.mul v.price_continuous).sub
    ((v.weight_continuous.mul v.marginalUtility_continuous).mul
      v.marginalProduct_continuous)).mul
        (a.capital_continuous.sub b.capital_continuous)).add
    (v.price_continuous.mul ((a.investment_continuous.sub
      (continuousOn_const.mul a.capital_continuous)).sub
        (b.investment_continuous.sub (continuousOn_const.mul b.capital_continuous))))

theorem welfare_integrand_continuous {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m) :
    ContinuousOn (fun t => w t * U (b.consumption t)) (Ici 0) := by
  exact v.weight_continuous.mul (v.utility_continuous.comp b.consumption_continuous
    (fun t ht => b.consumption_pos t ht))

/-- The algebraic comparison is applied to the actual resource and price laws. -/
theorem pointwise_comparison {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ w t * (U (a.consumption t) - U (b.consumption t)) + boundaryRate v b t := by
  apply present_value_comparison_nonneg
    (U (a.consumption t)) (U (b.consumption t))
    (f (a.capital t)) (f (b.capital t))
    (a.consumption t) (b.consumption t) (a.investment t) (b.investment t)
    (a.capital t) (b.capital t) (v.marginalProduct t) (v.marginalUtility t)
    (v.price t) m (w t)
    (m * v.price t - w t * v.marginalUtility t * v.marginalProduct t)
    (a.resource t ht) (b.resource t ht)
  · nlinarith [v.utility_support t ht (b.consumption t) (b.consumption_pos t ht)]
  · nlinarith [v.production_support t ht (b.capital t) (b.capital_nonneg t ht)]
  · exact v.weight_nonneg t ht
  · exact v.marginalUtility_nonneg t ht
  · exact halloc t ht
  · rfl

/-- Finite-horizon comparison, with the economically correct boundary sign:
competitor minus candidate welfare is at most price times candidate minus
competitor terminal capital. No terminal condition is used here. -/
theorem finite_horizon_comparison {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    {T : ℝ} (hT : 0 ≤ T) :
    welfare U w b.consumption T - welfare U w a.consumption T ≤
      boundary v.price a.capital b.capital T := by
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
  have hB0 : boundary v.price a.capital b.capital 0 = 0 := by simp [boundary, hinit]
  rw [hB0] at hnonneg
  change welfare U w a.consumption T - welfare U w b.consumption T +
    (boundary v.price a.capital b.capital T - 0) ≥ 0 at hnonneg
  linarith

/-- Infinite-horizon verification for competitors with finite limiting welfare.
The candidate is not assumed optimal; the conclusion follows from the proved
finite comparison and the explicit terminal limit. -/
theorem infinite_horizon_optimality {f U w : ℝ → ℝ} {m Ja Jb : ℝ}
    {a : FeasiblePath f m} (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0)) :
    Jb ≤ Ja := by
  have hle : Jb - Ja ≤ 0 := le_of_tendsto_of_tendsto (hb.sub ha) hterminal
    (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      exact finite_horizon_comparison v b halloc hinit hT)
  linarith

/-- Price decay and bounded feasible capital discharge the terminal premise. -/
theorem infinite_horizon_optimality_of_bounded_capital
    {f U w : ℝ → ℝ} {m Ja Jb K : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (ha : HasWelfare U w a.consumption Ja) (hb : HasWelfare U w b.consumption Jb)
    (hp : Tendsto v.price atTop (𝓝 0))
    (hka : ∀ t, 0 ≤ t → a.capital t ≤ K)
    (hkb : ∀ t, 0 ≤ t → b.capital t ≤ K) : Jb ≤ Ja := by
  exact infinite_horizon_optimality v b halloc hinit ha hb
    (Terminal.terminal_tendsto_zero_of_bounded_capital hp
      (fun t ht => ⟨a.capital_nonneg t ht, hka t ht⟩)
      (fun t ht => ⟨b.capital_nonneg t ht, hkb t ht⟩))

end RamseyCassKoopmans
