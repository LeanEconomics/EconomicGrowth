import RamseyCassKoopmans.CompactExtension
import RamseyCassKoopmans.CooperativeShooting

/-! # Cass's cooperative capital and shadow-price system

Consumption is the smaller of inverse marginal utility and current output.
Writing its marginal utility as `max q (μ (f k))` makes the price equation
continuous at a zero-investment switch. All economic identities below are
proved explicitly, including the investment constraint and complementarity.
-/

open Set
open scoped NNReal

namespace RamseyCassKoopmans

def cassConsumption (f C : ℝ → ℝ) (x : ℝ × ℝ) : ℝ := min (C x.2) (f x.1)

def cassInvestment (f C : ℝ → ℝ) (x : ℝ × ℝ) : ℝ := f x.1 - cassConsumption f C x

def cassField (f mp μ C : ℝ → ℝ) (d m : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  (cassInvestment f C x - m * x.1, (d + m) * x.2 - max x.2 (μ (f x.1)) * mp x.1)

def cassExtension (f mp μ C : ℝ → ℝ) (d m kl ku ql qu : ℝ) (x : ℝ × ℝ) : ℝ × ℝ :=
  cassField f mp μ C d m (clip kl ku x.1, clip ql qu x.2)

theorem cass_consumption_pos {f C : ℝ → ℝ} {x : ℝ × ℝ}
    (hf : 0 < f x.1) (hC : 0 < C x.2) : 0 < cassConsumption f C x :=
  lt_min hC hf

theorem cass_investment_nonneg (f C : ℝ → ℝ) (x : ℝ × ℝ) :
    0 ≤ cassInvestment f C x := sub_nonneg.mpr (min_le_right _ _)

theorem cass_resource (f C : ℝ → ℝ) (x : ℝ × ℝ) :
    cassConsumption f C x + cassInvestment f C x = f x.1 := by
  unfold cassInvestment
  ring

theorem marginal_utility_min {μ : ℝ → ℝ} (hμ : AntitoneOn μ (Ioi 0))
    {c y : ℝ} (hc : 0 < c) (hy : 0 < y) : μ (min c y) = max (μ c) (μ y) := by
  rcases le_total c y with h | h
  · rw [min_eq_left h, max_eq_left (hμ hc hy h)]
  · rw [min_eq_right h, max_eq_right (hμ hy hc h)]

/-- This covers prices below the lowest price used in the inverse construction:
the production constraint then selects output itself as consumption. -/
theorem cass_marginal_utility {f μ C : ℝ → ℝ} {a b : ℝ} {x : ℝ × ℝ}
    (hμ : AntitoneOn μ (Ioi 0)) (ha : 0 < a)
    (hy : f x.1 ∈ Icc a b) (hC : C x.2 ∈ Icc a b)
    (hinv : μ (C x.2) = clip (μ b) (μ a) x.2) (hq : x.2 ≤ μ a) :
    μ (cassConsumption f C x) = max x.2 (μ (f x.1)) := by
  have hyp : 0 < f x.1 := ha.trans_le hy.1
  have hbp : 0 < b := hyp.trans_le hy.2
  have hby : μ b ≤ μ (f x.1) := hμ hyp hbp hy.2
  rw [cassConsumption, marginal_utility_min hμ (ha.trans_le hC.1) hyp,
    hinv, clip, min_eq_right hq]
  rw [max_assoc]
  exact max_left_comm _ _ _ |>.trans (congrArg (max x.2) (max_eq_right hby))

theorem cass_wedge_and_slack {f μ C : ℝ → ℝ} {x : ℝ × ℝ}
    (heq : μ (cassConsumption f C x) = max x.2 (μ (f x.1)))
    (hstrict : StrictAntiOn μ (Ioi 0))
    (hy : 0 < f x.1) (hC : 0 < C x.2) :
    x.2 ≤ μ (cassConsumption f C x) ∧
      (x.2 - μ (cassConsumption f C x)) * cassInvestment f C x = 0 := by
  refine ⟨heq ▸ le_max_left _ _, ?_⟩
  rcases lt_or_ge (C x.2) (f x.1) with h | h
  · have hmu : μ (f x.1) < μ (cassConsumption f C x) := by
      simpa only [cassConsumption, min_eq_left h.le] using hstrict hC hy h
    have hmax : μ (f x.1) < x.2 := by
      rw [heq] at hmu
      exact (lt_max_iff.mp hmu).resolve_right (lt_irrefl _)
    rw [heq, max_eq_left hmax.le, sub_self, zero_mul]
  · simp only [cassInvestment, cassConsumption, min_eq_right h, sub_self, mul_zero]

theorem cass_field_costate {f mp μ C : ℝ → ℝ} {d m : ℝ} {x : ℝ × ℝ}
    (heq : μ (cassConsumption f C x) = max x.2 (μ (f x.1))) :
    (cassField f mp μ C d m x).2 =
      (d + m) * x.2 - μ (cassConsumption f C x) * mp x.1 := by
  rw [heq]
  rfl

theorem cass_extension_eq {f mp μ C : ℝ → ℝ} {d m kl ku ql qu : ℝ} {x : ℝ × ℝ}
    (hk : x.1 ∈ Icc kl ku) (hq : x.2 ∈ Icc ql qu) :
    cassExtension f mp μ C d m kl ku ql qu x = cassField f mp μ C d m x := by
  simp only [cassExtension, clip_eq hk, clip_eq hq, Prod.mk.eta]

/-- Cooperation needs decreasing inverse demand and decreasing, nonnegative
marginal utility of output and marginal product. No derivative at the switch
is assumed. -/
theorem cass_extension_cooperative {f mp μ C : ℝ → ℝ} {d m kl ku ql qu : ℝ}
    (hkk : kl ≤ ku) (hC : Antitone C)
    (hH : AntitoneOn (fun k => μ (f k)) (Icc kl ku))
    (hP : AntitoneOn mp (Icc kl ku))
    (hHpos : ∀ k ∈ Icc kl ku, 0 ≤ μ (f k))
    (hPpos : ∀ k ∈ Icc kl ku, 0 ≤ mp k) :
    ODE.Cooperative (cassExtension f mp μ C d m kl ku ql qu) := by
  constructor
  · intro k p q hpq
    have hCorder := hC (monotone_clip ql qu hpq)
    have hmin := min_le_min_right (f (clip kl ku k)) hCorder
    change f _ - min (C (clip ql qu p)) _ - _ ≤
      f _ - min (C (clip ql qu q)) _ - _
    linarith
  · intro q k l hkl
    have hk := clip_mem hkk k
    have hl := clip_mem hkk l
    have horder := monotone_clip kl ku hkl
    have hmax := max_le_max_left (clip ql qu q) (hH hk hl horder)
    have hprod := mul_le_mul hmax (hP hk hl horder)
      (hPpos _ hl) ((hHpos _ hk).trans (le_max_right _ _))
    change (d + m) * _ - _ ≤ (d + m) * _ - _
    linarith

theorem cass_extension_boundedLip {f mp μ C : ℝ → ℝ} {d m kl ku ql qu : ℝ}
    (hkk : kl ≤ ku) (hqq : ql ≤ qu)
    (hf : BoundedLip (f ∘ clip kl ku))
    (hmp : BoundedLip (mp ∘ clip kl ku))
    (hmu : BoundedLip ((fun k => μ (f k)) ∘ clip kl ku))
    (hC : BoundedLip C) :
    BoundedLip (cassExtension f mp μ C d m kl ku ql qu) := by
  have hk := (boundedLip_clip hkk).comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))
  have hq := (boundedLip_clip hqq).comp (LipschitzWith.prod_snd (α := ℝ) (β := ℝ))
  have hf' := hf.comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))
  have hmp' := hmp.comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))
  have hmu' := hmu.comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))
  obtain ⟨Kq, Mq, hqLip, hqBound⟩ := hq
  have hc' := hC.comp hqLip
  have hfst := (hf'.sub (hc'.min_function hf')).sub ((BoundedLip.const m).mul hk)
  have hsnd := ((BoundedLip.const (d + m)).mul ⟨Kq, Mq, hqLip, hqBound⟩).sub
    ((BoundedLip.max_function ⟨Kq, Mq, hqLip, hqBound⟩ hmu').mul hmp')
  exact hfst.prodMk hsnd

end RamseyCassKoopmans
