import RamseyCassKoopmans.CompactDemand
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Tactic.Ring

/-! # Bounded Lipschitz extensions for the economic differential equations -/

open Set
open scoped NNReal

namespace RamseyCassKoopmans

def BoundedLip {E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F]
    (f : E → F) : Prop :=
  ∃ K M : ℝ≥0, LipschitzWith K f ∧ ∀ x, ‖f x‖ ≤ M

namespace BoundedLip

variable {E : Type*} [PseudoMetricSpace E]

theorem const (a : ℝ) : BoundedLip (fun _ : E => a) :=
  ⟨0, ‖a‖₊, LipschitzWith.const a, fun _ => le_rfl⟩

theorem sub {f g : E → ℝ} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => f x - g x) := by
  obtain ⟨K, M, hK, hM⟩ := hf
  obtain ⟨L, N, hL, hN⟩ := hg
  exact ⟨K + L, M + N, hK.sub hL,
    fun x => (norm_sub_le _ _).trans (add_le_add (hM x) (hN x))⟩

theorem mul {f g : E → ℝ} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => f x * g x) := by
  obtain ⟨K, M, hK, hM⟩ := hf
  obtain ⟨L, N, hL, hN⟩ := hg
  refine ⟨M * L + N * K, M * N, LipschitzWith.of_dist_le_mul ?_, ?_⟩
  · intro x y
    have hfxy : ‖f x - f y‖ ≤ K * dist x y := by
      simpa only [dist_eq_norm] using hK.dist_le_mul x y
    have hgxy : ‖g x - g y‖ ≤ L * dist x y := by
      simpa only [dist_eq_norm] using hL.dist_le_mul x y
    have hdecomp : f x * g x - f y * g y =
        f x * (g x - g y) + (f x - f y) * g y := by ring
    calc
      dist (f x * g x) (f y * g y)
          = ‖f x * (g x - g y) + (f x - f y) * g y‖ := by
            rw [dist_eq_norm, hdecomp]
      _ ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ := by
        simpa only [norm_mul] using norm_add_le
          (f x * (g x - g y)) ((f x - f y) * g y)
      _ ≤ M * (L * dist x y) + (K * dist x y) * N :=
        add_le_add
          (mul_le_mul (hM x) hgxy (norm_nonneg _) M.coe_nonneg)
          (mul_le_mul hfxy (hN y) (norm_nonneg _) (by positivity))
      _ = (↑(M * L + N * K) : ℝ) * dist x y := by
        push_cast
        ring
  · intro x
    rw [norm_mul]
    exact mul_le_mul (hM x) (hN x) (norm_nonneg _) M.coe_nonneg

theorem min_function {f g : E → ℝ} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => min (f x) (g x)) := by
  obtain ⟨K, M, hK, hM⟩ := hf
  obtain ⟨L, N, hL, hN⟩ := hg
  refine ⟨max K L, max M N, hK.min hL, fun x => ?_⟩
  rcases le_total (f x) (g x) with h | h
  · simpa only [min_eq_left h] using (hM x).trans (show (M : ℝ) ≤ max M N from le_max_left _ _)
  · simpa only [min_eq_right h] using (hN x).trans (show (N : ℝ) ≤ max M N from le_max_right _ _)

theorem max_function {f g : E → ℝ} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => max (f x) (g x)) := by
  obtain ⟨K, M, hK, hM⟩ := hf
  obtain ⟨L, N, hL, hN⟩ := hg
  refine ⟨max K L, max M N, hK.max hL, fun x => ?_⟩
  rcases le_total (f x) (g x) with h | h
  · simpa only [max_eq_right h] using (hN x).trans (show (N : ℝ) ≤ max M N from le_max_right _ _)
  · simpa only [max_eq_left h] using (hM x).trans (show (M : ℝ) ≤ max M N from le_max_left _ _)

theorem comp {D : Type*} [PseudoMetricSpace D] {f : E → ℝ} {g : D → E}
    (hf : BoundedLip f) {K : ℝ≥0} (hg : LipschitzWith K g) : BoundedLip (f ∘ g) := by
  obtain ⟨L, M, hL, hM⟩ := hf
  exact ⟨L * K, M, hL.comp hg, fun x => hM (g x)⟩

theorem prodMk {f g : E → ℝ} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => (f x, g x)) := by
  obtain ⟨K, M, hK, hM⟩ := hf
  obtain ⟨L, N, hL, hN⟩ := hg
  refine ⟨max K L, max M N, hK.prodMk hL, fun x => ?_⟩
  exact max_le_max (hM x) (hN x)

end BoundedLip

theorem boundedLip_clip {a b : ℝ} (hab : a ≤ b) : BoundedLip (clip a b) := by
  refine ⟨1, max ‖a‖₊ ‖b‖₊, lipschitz_clip a b, fun x => ?_⟩
  have hx := clip_mem hab x
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have ha := neg_abs_le a
    have hma : |a| ≤ max ‖a‖ ‖b‖ := le_max_left _ _
    change -(max ‖a‖ ‖b‖) ≤ clip a b x
    linarith [hx.1]
  · have hb := le_abs_self b
    have hmb : |b| ≤ max ‖a‖ ‖b‖ := le_max_right _ _
    change clip a b x ≤ max ‖a‖ ‖b‖
    linarith [hx.2]

/-- Clipping a continuously differentiable function to a compact argument
interval gives both global boundedness and a global Lipschitz constant. -/
theorem boundedLip_comp_clip {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hc : ContinuousOn (deriv f) (Icc a b)) : BoundedLip (f ∘ clip a b) := by
  have hfc : ContinuousOn f (Icc a b) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hc.norm
  obtain ⟨w, hw, hwmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hfc.norm
  have hL : LipschitzOnWith ‖deriv f z‖₊ f (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le hd (fun x hx => hmax hx)
  refine ⟨‖deriv f z‖₊, ‖f w‖₊, LipschitzWith.of_dist_le_mul ?_, ?_⟩
  · intro x y
    exact (hL.dist_le_mul _ (clip_mem hab x) _ (clip_mem hab y)).trans
      (mul_le_mul_of_nonneg_left
        (by simpa only [NNReal.coe_one, one_mul] using (lipschitz_clip a b).dist_le_mul x y)
        (norm_nonneg _))
  · intro x
    exact hwmax (clip_mem hab x)

end RamseyCassKoopmans
