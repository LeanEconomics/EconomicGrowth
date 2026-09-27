/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import DiscreteTime.SolowSwanDynamics
import Solow1956.Growth.SolowSwanExamples

/-! # Realizable discrete-time Cobb–Douglas paths and explicit boundary checks

The discrete counterpart of `Solow1956.Growth.SolowSwanExamples`.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime.CobbDouglas

open Solow1956.Neoclassical

theorem example_params : Params 1 1 1 := ⟨by norm_num, le_rfl, by norm_num, by norm_num⟩

/-- A nonstationary positive initial condition with an explicit path:
`k₀ = 4`, `k* = 1`, `k(t) = 4^((1/2)^t)`. -/
theorem example_path (t : ℕ) :
    path (fun k : ℝ => k ^ (1 / 2 : ℝ)) 1 1 1 4 t = 4 ^ ((1 / 2 : ℝ) ^ t) := by
  rw [path_full_depreciation (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    SolowSwan.CobbDouglas.normalized_steadyState, Real.one_rpow, one_mul]

theorem example_converges :
    Tendsto (path (fun k : ℝ => k ^ (1 / 2 : ℝ)) 1 1 1 4) atTop (𝓝 1) := by
  have := tendsto_path_full_depreciation (b := 1) (γ := 1) (α := 1 / 2) (k₀ := 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rwa [SolowSwan.CobbDouglas.normalized_steadyState] at this

theorem normalized_steady :
    steady (technology_rpow (α := 1 / 2) (by norm_num) (by norm_num)) 1 1 1 = 1 := by
  rw [steady_eq (by norm_num) (by norm_num) example_params]
  norm_num [SolowSwan.CobbDouglas.steadyState]

/-- Zero is a fixed point of the nonlinear map, excluded by strict positivity. -/
theorem zero_fixed {b δ γ α : ℝ} (hα : 0 < α) : next (fun k : ℝ => k ^ α) b δ γ 0 = 0 :=
  next_zero hα

theorem zero_orbit_not_isPath (f : ℝ → ℝ) (s δ γ : ℝ) : ¬ IsPath f s δ γ (fun _ => 0) :=
  fun h => lt_irrefl (0 : ℝ) h.initial_pos

/-- At the excluded exponent one with `b > γ - 1 + δ`, capital grows every period:
there is no positive fixed point. -/
theorem no_positive_fixed_at_exponent_one {b δ γ k : ℝ} (hγ : 0 < γ)
    (hbm : γ - 1 + δ < b) (hk : 0 < k) : k < next (fun k : ℝ => k ^ (1 : ℝ)) b δ γ k := by
  have hd := next_sub_self (f := fun k : ℝ => k ^ (1 : ℝ)) (s := b) (δ := δ) hγ k
  have hr : 0 < rate (fun k : ℝ => k ^ (1 : ℝ)) b (γ - 1 + δ) k := by
    simp only [rate, Real.rpow_one]
    nlinarith
  have := div_pos hr hγ
  linarith

/-- Effective labour grows by the factor `(1 + n)(1 + g)` each period. -/
theorem effectiveLabour_succ {B L : ℕ → ℝ} {g n : ℝ} {t : ℕ}
    (hB : B (t + 1) = (1 + g) * B t) (hL : L (t + 1) = (1 + n) * L t) :
    B (t + 1) * L (t + 1) = (1 + n) * (1 + g) * (B t * L t) := by
  rw [hB, hL]
  ring

end Solow1956.DiscreteTime.CobbDouglas
