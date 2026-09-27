/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import DiscreteTime.GeneralSolow
import Solow1956.Growth.SolowSwan
import Solow1956.Growth.GeneralSolowExamples

/-!
# Solow's net-output model in discrete time, with square-root production

The discrete counterpart of `Solow1956.Growth.SolowSwan`. Net accumulation
`K(t+1) = K(t) + s F(K(t), L(t))` with labour `L(t+1) = (1 + n) L(t)` gives

`k(t+1) = (s f(k(t)) + k(t)) / (1 + n)`,

the general map with `δ = 0` and `γ = 1 + n`, whose effective dilution is `n`.
Homogeneity (`intensiveForm_of_homogeneous`) is a static fact and is reused. For
`f(k) = A √k` the fixed points are exactly `0` and Solow's `k* = (sA/n)^2`; the
comparative statics and capital/output ratio of the continuous module are
statements about this same stock. Unlike the continuous module, which proves
only signs for this economy, the discrete map is solved globally: every positive
path converges monotonically to `k*`.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime

open Solow1956.Neoclassical Solow1956.SolowSwan

/-- Derive the intensive map from aggregate net accumulation, labour growth, and the
constant-returns normalization. -/
theorem capitalPerWorker_succ {K L : ℕ → ℝ} {f : ℝ → ℝ} {F : ℝ → ℝ → ℝ} {s n : ℝ} {t : ℕ}
    (hn : 0 < 1 + n) (hL : 0 < L t)
    (hK : K (t + 1) = K t + s * F (K t) (L t)) (hLs : L (t + 1) = (1 + n) * L t)
    (hF : F (K t) (L t) = L t * f (K t / L t)) :
    K (t + 1) / L (t + 1) = next f s 0 (1 + n) (K t / L t) := by
  rw [hK, hLs, hF]
  unfold next
  field_simp
  ring

/-- The net-output map moves capital by Solow's `capitalChange` divided by `1 + n`. -/
theorem next_sub_self_net {f : ℝ → ℝ} {s n : ℝ} (hn : 0 < 1 + n) (k : ℝ) :
    next f s 0 (1 + n) k - k = capitalChange f s n k / (1 + n) := by
  unfold next capitalChange
  field_simp
  ring

namespace SquareRoot

open Solow1956.SolowSwan.SquareRoot

/-- Square-root production is a power technology after absorbing `A` into saving. -/
theorem next_production (s A δ γ : ℝ) :
    next (production A) s δ γ = next (fun k : ℝ => k ^ (1 / 2 : ℝ)) (s * A) δ γ := by
  funext k
  simp only [next, production, Real.sqrt_eq_rpow, one_div]
  ring

@[simp] theorem next_zero (s A n : ℝ) : next (production A) s 0 (1 + n) 0 = 0 := by
  simp [next, production]

/-- On the economic domain, the fixed points are exactly zero and `k*`. -/
theorem next_eq_self_iff {s A n k : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A) (hn : 0 < n) (hk : 0 ≤ k) :
    next (production A) s 0 (1 + n) k = k ↔ k = 0 ∨ k = steadyState s A n := by
  have hn1 : 0 < 1 + n := by linarith
  rw [← sub_eq_zero, next_sub_self_net hn1, div_eq_zero_iff, or_iff_left (ne_of_gt hn1)]
  exact capitalChange_eq_zero_iff hs hA hn hk

/-- Existence and uniqueness of the positive fixed point. -/
theorem existsUnique_positive_fixed {s A n : ℝ} (hs : 0 < s) (hA : 0 < A) (hn : 0 < n) :
    ∃! k : ℝ, 0 < k ∧ next (production A) s 0 (1 + n) k = k := by
  refine ⟨steadyState s A n, ⟨steadyState_pos hs hA hn,
    (next_eq_self_iff hs.le hA.le hn (steadyState_pos hs hA hn).le).mpr (Or.inr rfl)⟩, ?_⟩
  intro k hk
  exact ((next_eq_self_iff hs.le hA.le hn hk.1.le).mp hk.2).resolve_left (ne_of_gt hk.1)

/-- Capital rises in every period at a positive stock below `k*`. -/
theorem lt_next_of_lt {s A n k : ℝ} (hs : 0 < s) (hA : 0 < A) (hn : 0 < n) (hk : 0 < k)
    (hlt : k < steadyState s A n) : k < next (production A) s 0 (1 + n) k := by
  have hn1 : 0 < 1 + n := by linarith
  have := div_pos (capitalChange_pos_of_lt hs hA hn hk hlt) hn1
  have := next_sub_self_net (f := production A) (s := s) hn1 k
  linarith

/-- Capital falls in every period at a stock above `k*`. -/
theorem next_lt_of_gt {s A n k : ℝ} (hs : 0 < s) (hA : 0 < A) (hn : 0 < n)
    (hgt : steadyState s A n < k) : next (production A) s 0 (1 + n) k < k := by
  have hn1 : 0 < 1 + n := by linarith
  have := div_neg_of_neg_of_pos (capitalChange_neg_of_gt hs hA hn hgt) hn1
  have := next_sub_self_net (f := production A) (s := s) hn1 k
  linarith

theorem params {s A n : ℝ} (hs : 0 < s) (hA : 0 < A) (hn : 0 < n) :
    Params (s * A) 0 (1 + n) :=
  ⟨mul_pos hs hA, by norm_num, by linarith, by linarith⟩

/-- The general steady state of the net-output economy is Solow's `(sA/n)^2`. -/
theorem steady_eq_steadyState {s A n : ℝ} (hs : 0 < s) (hA : 0 < A) (hn : 0 < n) :
    steady (technology_rpow (α := 1 / 2) (by norm_num) (by norm_num)) (s * A) 0 (1 + n) =
      steadyState s A n := by
  apply steady_eq _ (params hs hA hn) (steadyState_pos hs hA hn)
  rw [← next_production]
  exact (next_eq_self_iff hs.le hA.le hn (steadyState_pos hs hA hn).le).mpr (Or.inr rfl)

/-- Global dynamics of the square-root economy in discrete time: from any positive
stock, capital converges monotonically to `k* = (sA/n)^2` and never crosses it. -/
theorem global_dynamics {s A n k₀ : ℝ} (hs : 0 < s) (hA : 0 < A) (hn : 0 < n) (hk₀ : 0 < k₀) :
    (∀ t, 0 < path (production A) s 0 (1 + n) k₀ t) ∧
      (k₀ < steadyState s A n → StrictMono (path (production A) s 0 (1 + n) k₀) ∧
        ∀ t, path (production A) s 0 (1 + n) k₀ t < steadyState s A n) ∧
      (steadyState s A n < k₀ → StrictAnti (path (production A) s 0 (1 + n) k₀) ∧
        ∀ t, steadyState s A n < path (production A) s 0 (1 + n) k₀ t) ∧
      Tendsto (path (production A) s 0 (1 + n) k₀) atTop (𝓝 (steadyState s A n)) := by
  have hT := technology_rpow (α := 1 / 2) (by norm_num) (by norm_num)
  have hp : path (production A) s 0 (1 + n) k₀ =
      path (fun k : ℝ => k ^ (1 / 2 : ℝ)) (s * A) 0 (1 + n) k₀ := by
    unfold path; rw [next_production]
  obtain ⟨hpos, hlow, hhigh, _, _, hlim⟩ := (isPath_path (f := fun k : ℝ => k ^ (1 / 2 : ℝ))
    (s := s * A) (δ := 0) (γ := 1 + n) hk₀).orbit hT (params hs hA hn)
  rw [steady_eq_steadyState hs hA hn] at hlow hhigh hlim
  rw [hp]
  exact ⟨hpos, hlow, hhigh, hlim⟩

/-- The stationary capital/output ratio of the discrete economy is `s/n`, as in
Solow (p. 77); it is a property of the shared stock `k*`. -/
theorem fixed_capital_output_ratio {s A n : ℝ} (hs : 0 < s) (hA : 0 < A) (hn : 0 < n) :
    steadyState s A n / production A (steadyState s A n) = s / n :=
  steadyState_capital_output_ratio hs hA hn

end SquareRoot

end Solow1956.DiscreteTime
