import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! # Constructing a Lipschitz inverse of marginal utility on a compact interval

The inverse is obtained by the intermediate value theorem. Its Lipschitz bound
is proved from a strictly negative bound on the derivative of marginal utility.
Only two derivatives of utility are needed; no derivative of its curvature is
introduced. Clipping the price argument makes this inverse globally defined.
-/

open Set
open scoped NNReal

namespace RamseyCassKoopmans

def clip (a b x : ℝ) : ℝ := max a (min b x)

theorem clip_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clip a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clip_eq {a b x : ℝ} (hx : x ∈ Icc a b) : clip a b x = x := by
  simp only [clip, min_eq_right hx.2, max_eq_right hx.1]

theorem monotone_clip (a b : ℝ) : Monotone (clip a b) :=
  fun _ _ h => max_le_max_left _ (min_le_min_left _ h)

theorem lipschitz_clip (a b : ℝ) : LipschitzWith 1 (clip a b) :=
  (LipschitzWith.id.const_min b).const_max a

/-- A quantitative version of decreasing marginal utility on a compact
consumption interval. -/
theorem strong_decrease_of_deriv_bound {μ : ℝ → ℝ} {a b η : ℝ}
    (hc : ContinuousOn μ (Icc a b))
    (hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ μ x)
    (hb : ∀ x ∈ Icc a b, deriv μ x ≤ -η) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → η * (y - x) ≤ μ x - μ y := by
  intro x hx y hy hxy
  have h := (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le hc
    (fun z hz => (hd z (interior_subset hz)).differentiableWithinAt)
    (fun z hz => hb z (interior_subset hz)) x hx y hy hxy
  linarith

/-- Construct a global, antitone, Lipschitz consumption demand by inverting
marginal utility between two ordinary, finite, positive consumption levels.
The conclusion includes the exact inverse equation with a clipped price. -/
theorem exists_compact_demand {μ : ℝ → ℝ} {a b η : ℝ}
    (hab : a ≤ b) (hη : 0 < η) (hc : ContinuousOn μ (Icc a b))
    (hs : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → η * (y - x) ≤ μ x - μ y) :
    ∃ C : ℝ → ℝ, (∀ q, C q ∈ Icc a b) ∧ Antitone C ∧
      LipschitzWith ⟨1 / η, (one_div_pos.mpr hη).le⟩ C ∧
      ∀ q, μ (C q) = clip (μ b) (μ a) q := by
  have hμ : μ b ≤ μ a := by
    have h := hs a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
    have hp := mul_nonneg hη.le (sub_nonneg.mpr hab)
    linarith
  have hex : ∀ q, ∃ c ∈ Icc a b, μ c = clip (μ b) (μ a) q := by
    intro q
    exact intermediate_value_Icc' hab hc (clip_mem hμ q)
  choose C hC heq using hex
  have hanti : Antitone C := by
    intro p q hpq
    by_contra hn
    have hlt : C p < C q := lt_of_not_ge hn
    have hslope := hs (C p) (hC p) (C q) (hC q) hlt.le
    have hpositive := mul_pos hη (sub_pos.mpr hlt)
    rw [heq p, heq q] at hslope
    have horder := monotone_clip (μ b) (μ a) hpq
    linarith
  refine ⟨C, hC, hanti, ?_, heq⟩
  apply LipschitzWith.of_dist_le_mul
  have hord : ∀ p q, p ≤ q → dist (C p) (C q) ≤ (1 / η) * dist p q := by
    intro p q hpq
    have hCp := hanti hpq
    have hslope := hs (C q) (hC q) (C p) (hC p) hCp
    rw [heq p, heq q] at hslope
    have hclip := (lipschitz_clip (μ b) (μ a)).dist_le_mul p q
    have hclipord := monotone_clip (μ b) (μ a) hpq
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hclipord),
      abs_of_nonpos (sub_nonpos.mpr hpq)] at hclip
    simp only [NNReal.coe_one, one_mul] at hclip
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hCp),
      abs_of_nonpos (sub_nonpos.mpr hpq)]
    have hdiv : C p - C q ≤ (q - p) / η :=
      (le_div_iff₀ hη).mpr (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul, mul_one, neg_sub, mul_comm] using hdiv
  intro p q
  change dist (C p) (C q) ≤ (1 / η) * dist p q
  rcases le_total p q with hpq | hqp
  · exact hord p q hpq
  · simpa only [dist_comm] using hord q p hqp

/-- Continuous strict negativity supplies the finite curvature bound used in
the inverse construction. It is a conclusion, not an extra curvature axiom. -/
theorem exists_uniform_negative_deriv {μ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hc : ContinuousOn (deriv μ) (Icc a b))
    (hn : ∀ x ∈ Icc a b, deriv μ x < 0) :
    ∃ η : ℝ, 0 < η ∧ ∀ x ∈ Icc a b, deriv μ x ≤ -η := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc
  refine ⟨-deriv μ x, neg_pos.mpr (hn x hx), ?_⟩
  intro y hy
  simp only [neg_neg]
  exact hmax hy

theorem exists_compact_demand_of_deriv {μ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ μ x)
    (hc : ContinuousOn (deriv μ) (Icc a b))
    (hn : ∀ x ∈ Icc a b, deriv μ x < 0) :
    ∃ K : ℝ≥0, ∃ C : ℝ → ℝ, (∀ q, C q ∈ Icc a b) ∧ Antitone C ∧
      LipschitzWith K C ∧ ∀ q, μ (C q) = clip (μ b) (μ a) q := by
  obtain ⟨η, hη, hb⟩ := exists_uniform_negative_deriv hab hc hn
  have hm : ContinuousOn μ (Icc a b) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := exists_compact_demand hab hη hm
    (strong_decrease_of_deriv_bound hm hd hb)
  exact ⟨_, C, hC⟩

end RamseyCassKoopmans
