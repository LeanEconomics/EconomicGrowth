import RamseyCassKoopmans.ClosedFormDynamics
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Finite welfare from bounded nonnegative felicity

This removes a separate finite-welfare assumption for every Cass competitor in
the square-root economy. The general verification library still permits utility
functions unbounded below and therefore retains its explicit welfare hypotheses.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

/-- A continuous, nonnegative, bounded felicity stream has finite discounted
welfare. This proves convergence of finite integrals, without assigning a value
to a potentially divergent infinite integral. -/
theorem exists_hasWelfare_of_nonneg_bounded
    (U c : ℝ → ℝ) {d M : ℝ} (hd : 0 < d)
    (hcont : ContinuousOn (fun t => U (c t)) (Ici 0))
    (hbound : ∀ t, 0 ≤ t → 0 ≤ U (c t) ∧ U (c t) ≤ M) :
    ∃ J, HasWelfare U (discount d) c J := by
  have hint : ∀ T, 0 ≤ T → IntervalIntegrable
      (fun t => discount d t * U (c t)) volume 0 T := by
    intro T hT
    exact (((discount_continuous d).continuousOn.mul hcont).mono
      (fun _ ht => ht.1)).intervalIntegrable_of_Icc hT
  have hmono : MonotoneOn (welfare U (discount d) c) (Ici 0) := by
    intro S hS T _ hST
    apply intervalIntegral.integral_mono_interval le_rfl hS hST
      _ (hint T (hS.trans hST))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact mul_nonneg (discount_pos d t).le (hbound t ht.1.le).1
  have hupper : ∀ T, 0 ≤ T → welfare U (discount d) c T ≤ M / d := by
    intro T hT
    have hM : 0 ≤ M := (hbound 0 le_rfl).1.trans (hbound 0 le_rfl).2
    have hle : welfare U (discount d) c T ≤ M * ((1 - discount d T) / d) := by
      calc
        _ ≤ ∫ t in (0 : ℝ)..T, M * discount d t := by
          apply intervalIntegral.integral_mono_on hT (hint T hT)
            ((continuous_const.mul (discount_continuous d)).intervalIntegrable 0 T)
          intro t ht
          change discount d t * U (c t) ≤ M * discount d t
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left
            (hbound t ht.1).2 (discount_pos d t).le
        _ = _ := by rw [intervalIntegral.integral_const_mul,
          ClosedForm.integral_discount d T hd]
    have hdpos := discount_pos d T
    have hprod : 0 ≤ M * discount d T := mul_nonneg hM hdpos.le
    apply hle.trans
    apply (le_div_iff₀ hd).mpr
    field_simp
    nlinarith
  let W : ℝ → ℝ := fun T => welfare U (discount d) c (max 0 T)
  have hmW : Monotone W := by
    intro S T hST
    exact hmono (a := max 0 S) (b := max 0 T)
      (le_max_left (0 : ℝ) S) (le_max_left (0 : ℝ) T) (max_le_max_left _ hST)
  have hbW : BddAbove (range W) := ⟨M / d, by
    rintro _ ⟨T, rfl⟩
    exact hupper _ (le_max_left _ _)⟩
  refine ⟨⨆ T, W T, (tendsto_atTop_ciSup hmW hbW).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact congrArg (welfare U (discount d) c) (max_eq_right hT)

namespace ClosedForm

/-- Finite lifetime welfare is automatic for every Cass-admissible path in this
economy, including competitors for which no Euler equation is assumed. -/
theorem cass_path_hasWelfare (b : FeasiblePath Examples.production 1)
    (hb : b.NonnegativeInvestment) :
    ∃ J, HasWelfare utility (discount 1) b.consumption J := by
  let K := max 4 (b.capital 0)
  have hcapacity : ∀ k, K ≤ k → Examples.production k ≤ 1 * k :=
    fun k hk => Examples.production_capacity k ((le_max_left _ _).trans hk)
  have hk : ∀ t, 0 ≤ t → b.capital t ≤ K :=
    b.capital_le_capacity hcapacity (le_max_right _ _)
  apply exists_hasWelfare_of_nonneg_bounded utility b.consumption
    (d := 1) (M := 2 * Real.sqrt (2 * Real.sqrt K)) (by norm_num)
    (utility_continuous.comp_continuousOn b.consumption_continuous)
  intro t ht
  have hc : b.consumption t ≤ 2 * Real.sqrt K := by
    have hr := b.resource t ht
    have hi := hb t ht
    have hs := Real.sqrt_le_sqrt (hk t ht)
    dsimp [Examples.production] at hr
    linarith
  exact ⟨mul_nonneg (by norm_num) (Real.sqrt_nonneg _),
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hc) (by norm_num)⟩

end ClosedForm
end RamseyCassKoopmans
