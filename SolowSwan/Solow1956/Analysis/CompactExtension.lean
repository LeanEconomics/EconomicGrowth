/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
Analytic helpers adapted from the project's Cass formalization; see source-map.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Uniform

open Set
open scoped NNReal

namespace Solow1956.ODE

def clip (a b x : ℝ) : ℝ := max a (min b x)

theorem clip_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : clip a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clip_eq {a b x : ℝ} (hx : x ∈ Icc a b) : clip a b x = x := by
  simp only [clip, min_eq_right hx.2, max_eq_right hx.1]

theorem monotone_clip (a b : ℝ) : Monotone (clip a b) :=
  fun _ _ h => max_le_max_left _ (min_le_min_left _ h)

theorem lipschitz_clip (a b : ℝ) : LipschitzWith 1 (clip a b) :=
  (LipschitzWith.id.const_min b).const_max a

/-- Clipping a continuously differentiable function to a compact argument
interval gives both global boundedness and a global Lipschitz constant. -/
theorem bounded_lipschitz_clip {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x)
    (hc : ContinuousOn (deriv f) (Icc a b)) :
    ∃ K M : ℝ≥0, LipschitzWith K (f ∘ clip a b) ∧ ∀ x, ‖f (clip a b x)‖ ≤ M := by
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


end Solow1956.ODE
