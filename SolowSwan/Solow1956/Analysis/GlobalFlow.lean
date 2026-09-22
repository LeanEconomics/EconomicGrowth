/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
Analytic helpers adapted from the project's Cass formalization; see source-map.
-/
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.Linarith

/-!
# Global flows for bounded Lipschitz vector fields

This analytic helper proves global existence for bounded Lipschitz vector fields
on complete normed real vector spaces. The Solow construction applies it after
clipping its scalar field to a compact positive capital interval.
-/

open Set Filter Metric
open scoped Topology NNReal

namespace Solow1956.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_global_solution {v : E → E} {L K : ℝ≥0}
    (hlip : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (v (γ t)) t := by
  have hlocal (T : ℝ) : ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Ioo (-(|T| + 1)) (|T| + 1), HasDerivAt γ (v (γ t)) t := by
    let a : ℝ≥0 := ⟨L * (|T| + 1), mul_nonneg L.coe_nonneg (by positivity)⟩
    have hpl : IsPicardLindelof (fun (_ : ℝ) => v)
        (⟨0, by constructor <;> linarith [abs_nonneg T]⟩ : Icc (-(|T| + 1)) (|T| + 1))
        x a 0 L K := by
      refine ⟨fun _ _ => hlip.lipschitzOnWith, fun _ _ => continuousOn_const,
        fun _ _ y _ => hbound y, ?_⟩
      change (L : ℝ) * max ((|T| + 1) - 0) (0 - -(|T| + 1)) ≤
        (L : ℝ) * (|T| + 1) - 0
      simp
    obtain ⟨γ, hγ0, hγ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨γ, hγ0, fun t ht => (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)⟩
  choose γ hγ0 hγ using hlocal
  have hagree (S T t : ℝ) (hs : |t| < |S| + 1) (ht : |t| < |T| + 1) :
      γ S t = γ T t := by
    let R := min (|S| + 1) (|T| + 1)
    have hR : 0 < R := lt_min (by positivity) (by positivity)
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun (_ : ℝ) => v) (s := fun _ => univ)
      (a := -R) (b := R) (t₀ := 0) (fun _ _ => hlip.lipschitzOnWith)
      ⟨by linarith, hR⟩
      (fun u hu => ⟨hγ S u ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hu.1,
        lt_of_lt_of_le hu.2 (min_le_left _ _)⟩, mem_univ _⟩)
      (fun u hu => ⟨hγ T u ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hu.1,
        lt_of_lt_of_le hu.2 (min_le_right _ _)⟩, mem_univ _⟩)
      ((hγ0 S).trans (hγ0 T).symm)
    exact abs_lt.mp (lt_min hs ht)
  refine ⟨fun t => γ t t, hγ0 0, ?_⟩
  intro t
  apply (hγ t t (abs_lt.mp (by linarith : |t| < |t| + 1))).congr_of_eventuallyEq
  have hn : {u : ℝ | |u| < |t| + 1} ∈ 𝓝 t :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp)
  filter_upwards [hn] with u hu
  exact hagree u t u (by linarith) hu

end Solow1956.ODE
