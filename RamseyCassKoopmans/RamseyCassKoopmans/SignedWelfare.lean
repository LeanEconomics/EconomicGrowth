import RamseyCassKoopmans.BoundedWelfare
import Mathlib.Topology.Order.Lattice

/-! # Finite welfare for bounded, possibly negative felicity -/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

theorem exists_hasWelfare_of_abs_bounded (U c : ℝ → ℝ) {d M : ℝ} (hd : 0 < d)
    (hcont : ContinuousOn (fun t => U (c t)) (Ici 0))
    (hb : ∀ t, 0 ≤ t → |U (c t)| ≤ M) : ∃ J, HasWelfare U (discount d) c J := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hb 0 le_rfl)
  let Up : ℝ → ℝ := fun x => max (U x) 0
  let Un : ℝ → ℝ := fun x => max (-U x) 0
  have hpc : ContinuousOn (fun t => Up (c t)) (Ici 0) := hcont.sup continuousOn_const
  have hnc : ContinuousOn (fun t => Un (c t)) (Ici 0) := hcont.neg.sup continuousOn_const
  obtain ⟨Jp, hp⟩ := exists_hasWelfare_of_nonneg_bounded Up c hd hpc (fun t ht =>
    ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hb t ht)) hM⟩)
  obtain ⟨Jn, hn⟩ := exists_hasWelfare_of_nonneg_bounded Un c hd hnc (fun t ht =>
    ⟨le_max_right _ _, max_le ((neg_le_abs _).trans (hb t ht)) hM⟩)
  have hid : ∀ x, Up x - Un x = U x := by
    intro x
    dsimp [Up, Un]
    rcases le_total 0 (U x) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
      ring
  have hW : ∀ T, 0 ≤ T → welfare Up (discount d) c T - welfare Un (discount d) c T =
      welfare U (discount d) c T := by
    intro T hT
    have hpi : IntervalIntegrable (fun t => discount d t * Up (c t)) volume 0 T :=
      (((discount_continuous d).continuousOn.mul hpc).mono
      (fun _ ht => ht.1)).intervalIntegrable_of_Icc hT
    have hni : IntervalIntegrable (fun t => discount d t * Un (c t)) volume 0 T :=
      (((discount_continuous d).continuousOn.mul hnc).mono
      (fun _ ht => ht.1)).intervalIntegrable_of_Icc hT
    unfold welfare
    rw [← intervalIntegral.integral_sub hpi hni]
    apply intervalIntegral.integral_congr
    intro t _
    change discount d t * Up (c t) - discount d t * Un (c t) = discount d t * U (c t)
    rw [← mul_sub, hid]
  refine ⟨Jp - Jn, (hp.sub hn).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  exact hW T hT

theorem exists_hasWelfare_of_compact_consumption (U c : ℝ → ℝ) {a b d : ℝ}
    (hd : 0 < d) (hab : a ≤ b) (hU : ContinuousOn U (Icc a b))
    (hc : ContinuousOn c (Ici 0)) (hb : ∀ t, 0 ≤ t → c t ∈ Icc a b) :
    ∃ J, HasWelfare U (discount d) c J := by
  obtain ⟨x, _, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hU.norm
  apply exists_hasWelfare_of_abs_bounded U c hd (hU.comp hc hb)
  exact fun t ht => hmax (hb t ht)

end RamseyCassKoopmans
