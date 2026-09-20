/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/
import Solow1956.Growth.SolowSwanDynamics

/-! # Realizable Solow–Swan paths and explicit boundary checks -/

open Set Filter Topology

namespace Solow1956.SolowSwan.CobbDouglas

/-- A nonstationary positive initial condition satisfies the complete theorem. -/
theorem example_positive_path :
    IsPositiveSolution 1 1 (1 / 2) 4 (path 1 1 (1 / 2) 4) ∧
    Tendsto (path 1 1 (1 / 2) 4) atTop (𝓝 (steadyState 1 1 (1 / 2))) ∧
    ∀ k, IsPositiveSolution 1 1 (1 / 2) 4 k → EqOn k (path 1 1 (1 / 2) 4) (Ici 0) := by
  exact positive_dynamics (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

theorem normalized_steadyState : steadyState 1 1 (1 / 2) = 1 := by
  simp [steadyState]

/-- Zero is an actual solution of the nonlinear equation, excluded by strict positivity. -/
theorem zero_solution {b m α t : ℝ} (hα : 0 < α) :
    HasDerivAt (fun _ : ℝ => (0 : ℝ)) (rate b m α 0) t := by
  rw [rate_zero hα]
  exact hasDerivAt_const t 0

theorem zero_solution_not_positive (b m α : ℝ) :
    ¬ IsPositiveSolution b m α 0 (fun _ => 0) := by
  intro h
  exact (lt_irrefl (0 : ℝ)) (h.2 0 le_rfl).1

/-- At the excluded exponent one and `b > m`, there is no positive stationary stock. -/
theorem no_positive_stationary_at_exponent_one {b m k : ℝ} (hbm : m < b) (hk : 0 < k) :
    0 < rate b m 1 k := by
  simpa only [rate, Real.rpow_one, sub_mul] using mul_pos (sub_pos.mpr hbm) hk

/-- Effective labour grows at the sum of technology and population growth rates. -/
theorem hasDerivAt_effectiveLabour {B L : ℝ → ℝ} {g n t : ℝ}
    (hB : HasDerivAt B (g * B t) t) (hL : HasDerivAt L (n * L t) t) :
    HasDerivAt (fun u => B u * L u) ((n + g) * (B t * L t)) t := by
  convert! hB.mul hL using 1
  ring

end Solow1956.SolowSwan.CobbDouglas
