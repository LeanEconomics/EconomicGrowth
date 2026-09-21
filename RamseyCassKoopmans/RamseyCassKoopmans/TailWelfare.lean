import RamseyCassKoopmans.Model

/-! # Discounted welfare after a finite transition regime -/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

theorem discount_shift (d τ t : ℝ) : discount d t = discount d τ * discount d (t - τ) := by
  simp only [discount, ← Real.exp_add]
  congr 1
  ring

theorem welfare_of_tail_eq {U c tail : ℝ → ℝ} {d τ T : ℝ}
    (hτ : 0 ≤ τ) (hT : τ ≤ T)
    (hcont : ContinuousOn (fun t => discount d t * U (c t)) (Ici 0))
    (heq : ∀ t, τ ≤ t → c t = tail (t - τ)) :
    welfare U (discount d) c T = welfare U (discount d) c τ +
      discount d τ * welfare U (discount d) tail (T - τ) := by
  have h0 : IntervalIntegrable (fun t => discount d t * U (c t)) volume 0 τ :=
    (hcont.mono (fun _ ht => ht.1)).intervalIntegrable_of_Icc hτ
  have h1 : IntervalIntegrable (fun t => discount d t * U (c t)) volume τ T :=
    (hcont.mono (fun _ ht => hτ.trans ht.1)).intervalIntegrable_of_Icc hT
  have hsplit := intervalIntegral.integral_add_adjacent_intervals h0 h1
  have htail : (∫ t in τ..T, discount d t * U (c t)) =
      discount d τ * welfare U (discount d) tail (T - τ) := by
    calc
      _ = ∫ t in τ..T, discount d τ * (discount d (t - τ) * U (tail (t - τ))) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hT] at ht
        dsimp only
        rw [heq t ht.1, discount_shift d τ t]
        ring
      _ = discount d τ * ∫ t in τ..T, discount d (t - τ) * U (tail (t - τ)) :=
        intervalIntegral.integral_const_mul _ _
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_right
          (fun t => discount d t * U (tail t)) τ]
        simp only [sub_self, welfare]
  change (∫ t in (0 : ℝ)..T, discount d t * U (c t)) = _
  rw [← hsplit, htail]
  rfl

theorem hasWelfare_of_tail_eq {U c tail : ℝ → ℝ} {d τ J : ℝ}
    (hτ : 0 ≤ τ)
    (hcont : ContinuousOn (fun t => discount d t * U (c t)) (Ici 0))
    (heq : ∀ t, τ ≤ t → c t = tail (t - τ))
    (htail : HasWelfare U (discount d) tail J) :
    HasWelfare U (discount d) c (welfare U (discount d) c τ + discount d τ * J) := by
  have hshift : Tendsto (fun T : ℝ => T - τ) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (-τ) tendsto_id |>.congr
      (fun T => by simp only [sub_eq_add_neg, id_eq])
  have h := ((htail.comp hshift).const_mul (discount d τ)).const_add
    (welfare U (discount d) c τ)
  apply h.congr'
  filter_upwards [eventually_ge_atTop τ] with T hT
  exact (welfare_of_tail_eq hτ hT hcont heq).symm

end RamseyCassKoopmans
