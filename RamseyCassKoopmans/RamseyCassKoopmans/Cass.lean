import RamseyCassKoopmans.Verification
import RamseyCassKoopmans.Concavity

/-!
# Cass's current-value certificate

This connects actual derivatives of concave utility and production to the
verification theorem. It includes nonnegative investment and complementary
slackness. It does not replace complementary slackness by an everywhere-interior
Euler equation. Positive consumption and continuous controls are explicit
regularity restrictions. Finite welfare is expressed as a limit of finite integrals.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

/-- Supporting prices derived from concavity, differentiability, and the actual
current-value costate equation, rather than postulated tangent inequalities. -/
noncomputable def cassSupportingPrices
    (f U q : ℝ → ℝ) (d m : ℝ) (a : FeasiblePath f m)
    (hfconc : ConcaveOn ℝ (Ici 0) f) (hUconc : ConcaveOn ℝ (Ioi 0) U)
    (hUcont : ContinuousOn U (Ioi 0))
    (hfderiv : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hUderiv : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hak : ∀ t, 0 ≤ t → 0 < a.capital t)
    (hmu : ∀ t, 0 ≤ t → 0 ≤ deriv U (a.consumption t))
    (hq : ∀ t, 0 ≤ t → HasDerivAt q
      ((d + m) * q t - deriv U (a.consumption t) * deriv f (a.capital t)) t) :
    SupportingPrices f U (discount d) m a where
  price := fun t => discount d t * q t
  marginalUtility := fun t => deriv U (a.consumption t)
  marginalProduct := fun t => deriv f (a.capital t)
  weight_nonneg := fun t _ => (discount_pos d t).le
  weight_continuous := (discount_continuous d).continuousOn
  utility_continuous := hUcont
  marginalUtility_continuous := hUprime.comp a.consumption_continuous a.consumption_pos
  marginalProduct_continuous := hfprime.comp a.capital_continuous hak
  marginalUtility_nonneg := hmu
  utility_support := fun t ht _c hc => concave_support hUconc
    (a.consumption_pos t ht) hc (hUderiv _ (a.consumption_pos t ht)).hasDerivAt
  production_support := fun t ht _k hk => concave_support hfconc
    (a.capital_nonneg t ht) hk (hfderiv _ (hak t ht)).hasDerivAt
  costate := fun t ht => hasDerivAt_discounted_costate (hq t ht)

/-- The source resource equation supplies the right derivative needed by the
capital comparison lemma. -/
theorem FeasiblePath.resource_derivative {f : ℝ → ℝ} {m : ℝ}
    (a : FeasiblePath f m) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt a.capital
      (f (a.capital t) - a.consumption t - m * a.capital t) (Ici t) t := by
  convert (a.dynamics t ht).hasDerivWithinAt using 1
  linarith [a.resource t ht]

/-- A capacity assumption and feasibility imply the capital bound used in
transversality. Consumption is positive in this library's admissible class. -/
theorem FeasiblePath.capital_le_capacity {f : ℝ → ℝ} {m K : ℝ}
    (a : FeasiblePath f m) (hK : ∀ k, K ≤ k → f k ≤ m * k)
    (hinit : a.capital 0 ≤ K) : ∀ t, 0 ≤ t → a.capital t ≤ K :=
  Terminal.capital_le_capacity a.capital_continuous
    (fun _ ht => a.resource_derivative ht)
    (fun t ht => (a.consumption_pos t ht).le) hK hinit

/-- Cass verification for continuous positive-consumption paths. The theorem
uses the current-value costate equation, the investment corner, and a genuine
terminal price condition; capital bounds are proved from feasibility. It is a
sufficiency theorem for a supplied candidate, not an existence theorem. -/
theorem cass_candidate_dominates
    (f U q : ℝ → ℝ) (d m K Ja Jb : ℝ) (a b : FeasiblePath f m)
    (hfconc : ConcaveOn ℝ (Ici 0) f) (hUconc : ConcaveOn ℝ (Ioi 0) U)
    (hUcont : ContinuousOn U (Ioi 0))
    (hfderiv : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hUderiv : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hak : ∀ t, 0 ≤ t → 0 < a.capital t)
    (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hq : ∀ t, 0 ≤ t → HasDerivAt q
      ((d + m) * q t - deriv U (a.consumption t) * deriv f (a.capital t)) t)
    (hwedge : ∀ t, 0 ≤ t → q t ≤ deriv U (a.consumption t))
    (hslack : ∀ t, 0 ≤ t → (q t - deriv U (a.consumption t)) * a.investment t = 0)
    (hbinvest : b.NonnegativeInvestment)
    (hinit : a.capital 0 = b.capital 0)
    (hcapacity : ∀ k, K ≤ k → f k ≤ m * k) (ha0 : a.capital 0 ≤ K)
    (ha : HasWelfare U (discount d) a.consumption Ja)
    (hb : HasWelfare U (discount d) b.consumption Jb)
    (htrans : Tendsto (fun t => discount d t * q t) atTop (𝓝 0)) : Jb ≤ Ja := by
  let v := cassSupportingPrices f U q d m a hfconc hUconc hUcont hfderiv hUderiv
    hfprime hUprime hak (fun t ht => (hqn t ht).trans (hwedge t ht)) hq
  have halloc : AllocationComparison v b := by
    apply allocation_of_cass v
    · intro t ht
      exact mul_le_mul_of_nonneg_left (hwedge t ht) (discount_pos d t).le
    · intro t ht
      change (discount d t * q t - discount d t * deriv U (a.consumption t)) *
        a.investment t = 0
      calc
        _ = discount d t * ((q t - deriv U (a.consumption t)) * a.investment t) := by ring
        _ = 0 := by rw [hslack t ht, mul_zero]
    · exact hbinvest
  exact infinite_horizon_optimality_of_bounded_capital v b halloc hinit ha hb htrans
    (a.capital_le_capacity hcapacity ha0)
    (b.capital_le_capacity hcapacity (hinit ▸ ha0))

/-- Optimality within this library's continuous-control, positive-consumption,
finite-welfare version of Cass's feasible class. Candidate membership is explicit. -/
def IsCassOptimal {f : ℝ → ℝ} {m : ℝ} (U : ℝ → ℝ) (d : ℝ)
    (a : FeasiblePath f m) (Ja : ℝ) : Prop :=
  a.NonnegativeInvestment ∧ HasWelfare U (discount d) a.consumption Ja ∧
    ∀ (b : FeasiblePath f m), b.NonnegativeInvestment → a.capital 0 = b.capital 0 →
      ∀ Jb, HasWelfare U (discount d) b.consumption Jb → Jb ≤ Ja

/-- A feasible Cass candidate satisfying the certificate really is optimal in
the stated admissible class, including its own nonnegative investment. -/
theorem cass_certificate_is_optimal
    (f U q : ℝ → ℝ) (d m K Ja : ℝ) (a : FeasiblePath f m)
    (hfconc : ConcaveOn ℝ (Ici 0) f) (hUconc : ConcaveOn ℝ (Ioi 0) U)
    (hUcont : ContinuousOn U (Ioi 0))
    (hfderiv : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hUderiv : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hak : ∀ t, 0 ≤ t → 0 < a.capital t)
    (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    (hq : ∀ t, 0 ≤ t → HasDerivAt q
      ((d + m) * q t - deriv U (a.consumption t) * deriv f (a.capital t)) t)
    (hwedge : ∀ t, 0 ≤ t → q t ≤ deriv U (a.consumption t))
    (hslack : ∀ t, 0 ≤ t → (q t - deriv U (a.consumption t)) * a.investment t = 0)
    (hainvest : a.NonnegativeInvestment)
    (hcapacity : ∀ k, K ≤ k → f k ≤ m * k) (ha0 : a.capital 0 ≤ K)
    (ha : HasWelfare U (discount d) a.consumption Ja)
    (htrans : Tendsto (fun t => discount d t * q t) atTop (𝓝 0)) :
    IsCassOptimal U d a Ja := by
  refine ⟨hainvest, ha, ?_⟩
  intro b hbinvest hinit Jb hb
  exact cass_candidate_dominates f U q d m K Ja Jb a b hfconc hUconc hUcont
    hfderiv hUderiv hfprime hUprime hak hqn hq hwedge hslack hbinvest hinit
    hcapacity ha0 ha hb htrans

end RamseyCassKoopmans
