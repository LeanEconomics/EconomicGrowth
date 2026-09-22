import RamseyCassKoopmans.Cass
import RamseyCassKoopmans.Uniqueness

/-! # Uniqueness and necessity from a Cass certificate -/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

theorem cass_certificate_unique
    (f U q : ℝ → ℝ) (d m K Ja Jb : ℝ) (a b : FeasiblePath f m)
    (hfconc : StrictConcaveOn ℝ (Ici 0) f) (hUconc : StrictConcaveOn ℝ (Ioi 0) U)
    (hUcont : ContinuousOn U (Ioi 0))
    (hfderiv : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hUderiv : ∀ c, 0 < c → DifferentiableAt ℝ U c)
    (hfprime : ContinuousOn (deriv f) (Ioi 0))
    (hUprime : ContinuousOn (deriv U) (Ioi 0))
    (hak : ∀ t, 0 ≤ t → 0 < a.capital t)
    (hmu : ∀ t, 0 ≤ t → 0 < deriv U (a.consumption t))
    (hq : ∀ t, 0 ≤ t → HasDerivAt q
      ((d + m) * q t - deriv U (a.consumption t) * deriv f (a.capital t)) t)
    (hwedge : ∀ t, 0 ≤ t → q t ≤ deriv U (a.consumption t))
    (hslack : ∀ t, 0 ≤ t → (q t - deriv U (a.consumption t)) * a.investment t = 0)
    (hbinvest : b.NonnegativeInvestment) (hinit : a.capital 0 = b.capital 0)
    (hcapacity : ∀ k, K ≤ k → f k ≤ m * k) (ha0 : a.capital 0 ≤ K)
    (ha : HasWelfare U (discount d) a.consumption Ja)
    (hb : HasWelfare U (discount d) b.consumption Jb)
    (htrans : Tendsto (fun t => discount d t * q t) atTop (𝓝 0)) (heq : Jb = Ja) :
    ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
      b.consumption t = a.consumption t ∧ b.investment t = a.investment t := by
  let v := cassSupportingPrices f U q d m a hfconc.concaveOn hUconc.concaveOn hUcont
    hfderiv hUderiv hfprime hUprime hak (fun t ht => (hmu t ht).le) hq
  have halloc : AllocationComparison v b := by
    apply allocation_of_cass v
    · intro t ht
      exact mul_le_mul_of_nonneg_left (hwedge t ht) (discount_pos d t).le
    · intro t ht
      change (discount d t * q t - discount d t * deriv U (a.consumption t)) * a.investment t = 0
      calc
        _ = discount d t * ((q t - deriv U (a.consumption t)) * a.investment t) := by ring
        _ = 0 := by rw [hslack t ht, mul_zero]
    · exact hbinvest
  have hterm : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0) :=
    Terminal.terminal_tendsto_zero_of_bounded_capital htrans
      (fun t ht => ⟨a.capital_nonneg t ht, a.capital_le_capacity hcapacity ha0 t ht⟩)
      (fun t ht => ⟨b.capital_nonneg t ht, b.capital_le_capacity hcapacity (hinit ▸ ha0) t ht⟩)
  exact path_eq_of_welfare_eq v b halloc hinit ha hb hterm hUconc hfconc
    (fun t ht => (hUderiv _ (a.consumption_pos t ht)).hasDerivAt)
    (fun t ht => (hfderiv _ (hak t ht)).hasDerivAt)
    (fun t _ => discount_pos d t) hmu heq

end RamseyCassKoopmans
