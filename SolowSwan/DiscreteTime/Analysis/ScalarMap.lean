/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Positive scalar difference equations with a unique attracting fixed point

The discrete-time counterpart of `Solow1956.ODE.exists_attracting_scalar_path`.
For an increasing map that is continuous on positive reals, lies above the
diagonal below a positive fixed point and below the diagonal above it, every
positive orbit is strictly monotone, stays on its side of the fixed point, and
converges to it. No derivative is needed.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime.Map

theorem attracting_orbit {g : ℝ → ℝ} {xs : ℝ} {x : ℕ → ℝ}
    (hmono : StrictMonoOn g (Ioi 0)) (hc : ContinuousOn g (Ioi 0))
    (hxs : 0 < xs) (hfix : g xs = xs)
    (hbelow : ∀ y, 0 < y → y < xs → y < g y) (habove : ∀ y, xs < y → g y < y)
    (h0 : 0 < x 0) (hsucc : ∀ t, x (t + 1) = g (x t)) :
    (∀ t, 0 < x t) ∧
      (x 0 < xs → StrictMono x ∧ ∀ t, x t < xs) ∧
      (xs < x 0 → StrictAnti x ∧ ∀ t, xs < x t) ∧
      (x 0 = xs → ∀ t, x t = xs) ∧
      (∀ t, min (x 0) xs ≤ x t ∧ x t ≤ max (x 0) xs) ∧
      Tendsto x atTop (𝓝 xs) := by
  -- the limit of a convergent positive orbit is a positive fixed point, hence `xs`
  have hlimit : ∀ L, 0 < L → Tendsto x atTop (𝓝 L) → L = xs := by
    intro L hL hx
    have h1 : Tendsto (fun t => x (t + 1)) atTop (𝓝 L) := hx.comp (tendsto_add_atTop_nat 1)
    have h2 : Tendsto (fun t => x (t + 1)) atTop (𝓝 (g L)) := by
      simp only [hsucc]
      exact ((hc.continuousAt (Ioi_mem_nhds hL)).tendsto).comp hx
    have hgL : g L = L := tendsto_nhds_unique h2 h1
    rcases lt_trichotomy L xs with hlt | heq | hgt
    · exact absurd hgL (ne_of_gt (hbelow L hL hlt))
    · exact heq
    · exact absurd hgL (ne_of_lt (habove L hgt))
  have hlow : x 0 < xs → StrictMono x ∧ ∀ t, x t < xs := by
    intro hx0
    have hb : ∀ t, 0 < x t ∧ x t < xs := by
      intro t
      induction t with
      | zero => exact ⟨h0, hx0⟩
      | succ t ih =>
        rw [hsucc]
        exact ⟨ih.1.trans (hbelow _ ih.1 ih.2),
          hfix ▸ hmono ih.1 hxs ih.2⟩
    exact ⟨strictMono_nat_of_lt_succ (fun t => by
      rw [hsucc]; exact hbelow _ (hb t).1 (hb t).2), fun t => (hb t).2⟩
  have hhigh : xs < x 0 → StrictAnti x ∧ ∀ t, xs < x t := by
    intro hx0
    have hb : ∀ t, xs < x t := by
      intro t
      induction t with
      | zero => exact hx0
      | succ t ih =>
        rw [hsucc]
        exact hfix ▸ hmono hxs (hxs.trans ih) ih
    exact ⟨strictAnti_nat_of_succ_lt (fun t => by rw [hsucc]; exact habove _ (hb t)), hb⟩
  have hconst : x 0 = xs → ∀ t, x t = xs := by
    intro hx0 t
    induction t with
    | zero => exact hx0
    | succ t ih => rw [hsucc, ih, hfix]
  have hpos : ∀ t, 0 < x t := by
    intro t
    rcases lt_trichotomy (x 0) xs with hlt | heq | hgt
    · exact h0.trans_le ((hlow hlt).1.monotone (Nat.zero_le t))
    · rw [hconst heq t]; exact hxs
    · exact hxs.trans ((hhigh hgt).2 t)
  have hbounds : ∀ t, min (x 0) xs ≤ x t ∧ x t ≤ max (x 0) xs := by
    intro t
    rcases lt_trichotomy (x 0) xs with hlt | heq | hgt
    · exact ⟨(min_le_left _ _).trans ((hlow hlt).1.monotone (Nat.zero_le t)),
        ((hlow hlt).2 t).le.trans (le_max_right _ _)⟩
    · rw [hconst heq t]; exact ⟨min_le_right _ _, le_max_right _ _⟩
    · exact ⟨(min_le_right _ _).trans ((hhigh hgt).2 t).le,
        ((hhigh hgt).1.antitone (Nat.zero_le t)).trans (le_max_left _ _)⟩
  refine ⟨hpos, hlow, hhigh, hconst, hbounds, ?_⟩
  rcases lt_trichotomy (x 0) xs with hlt | heq | hgt
  · obtain ⟨hm, hb⟩ := hlow hlt
    have hbdd : BddAbove (range x) := ⟨xs, by rintro _ ⟨t, rfl⟩; exact (hb t).le⟩
    have hx := tendsto_atTop_ciSup hm.monotone hbdd
    have hL : 0 < ⨆ t, x t := h0.trans_le (le_ciSup hbdd 0)
    rwa [hlimit _ hL hx] at hx
  · have : x = fun _ => xs := funext (hconst heq)
    rw [this]
    exact tendsto_const_nhds
  · obtain ⟨hm, hb⟩ := hhigh hgt
    have hbdd : BddBelow (range x) := ⟨xs, by rintro _ ⟨t, rfl⟩; exact (hb t).le⟩
    have hx := tendsto_atTop_ciInf hm.antitone hbdd
    have hL : 0 < ⨅ t, x t := hxs.trans_le (le_ciInf fun t => (hb t).le)
    rwa [hlimit _ hL hx] at hx

end Solow1956.DiscreteTime.Map
