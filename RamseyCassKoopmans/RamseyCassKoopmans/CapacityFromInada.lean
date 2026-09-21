import RamseyCassKoopmans.Concavity
import Mathlib.Topology.Order.Basic

/-! # A finite capital capacity from a vanishing marginal product -/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

theorem exists_capacity_of_marginal_tendsto_zero (f : ℝ → ℝ) {m k0 : ℝ}
    (hm : 0 < m) (hf : ConcaveOn ℝ (Ici 0) f)
    (hd : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hpos : ∀ k, 0 < k → 0 ≤ deriv f k)
    (hlim : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))) :
    ∃ K, k0 ≤ K ∧ ∀ k, K ≤ k → f k ≤ m * k := by
  obtain ⟨a, ha, hma⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (hlim.eventually (gt_mem_nhds (half_pos hm)))).exists
  let K := max k0 (max a (2 * |f a| / m))
  refine ⟨K, le_max_left _ _, ?_⟩
  intro k hk
  have hak : a ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hratio : 2 * |f a| / m ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hmk : 2 * |f a| ≤ k * m := (div_le_iff₀ hm).mp hratio
  have hs := concave_support hf ha.le (ha.le.trans hak) (hd a ha).hasDerivAt
  have hpk := mul_le_mul_of_nonneg_right hma.le (ha.le.trans hak)
  have hpa := mul_nonneg (hpos a ha) ha.le
  have hfabs := le_abs_self (f a)
  nlinarith

end RamseyCassKoopmans
