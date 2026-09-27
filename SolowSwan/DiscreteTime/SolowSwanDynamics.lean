/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import DiscreteTime.GeneralSolow
import DiscreteTime.SolowComparative
import Solow1956.Growth.SolowSwanDynamics
import Solow1956.Growth.GeneralSolowExamples

/-!
# Discrete-time Cobb–Douglas dynamics

The discrete counterpart of `Solow1956.Growth.SolowSwanDynamics`, for

`k(t+1) = (b k(t)^α + (1 - δ) k(t)) / γ`,   `b = sA`.

The positive fixed point is Solow's `k* = (b/m)^(1/(1-α))` with `m = γ - 1 + δ`.
The continuous model linearises in `z = k^(1-α)`; the discrete map does not, and
for `δ < 1` there is no closed form. With full depreciation `δ = 1` the map is
`k ↦ (b/γ) k^α`, which is linear in `log k`, and the path is explicit:
`k(t) = k*^(1 - α^t) k₀^(α^t)`, so the log distance to `k*` shrinks by exactly `α`
every period. For general `δ` the dynamics come from the general theorem.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime.CobbDouglas

open Solow1956.Neoclassical Solow1956.SolowSwan.CobbDouglas

/-- The positive fixed point is the continuous Cobb–Douglas steady state at dilution
`γ - 1 + δ`. -/
theorem steady_eq {b δ γ α : ℝ} (hα : 0 < α) (hα1 : α < 1) (P : Params b δ γ) :
    steady (technology_rpow hα hα1) b δ γ = steadyState b (γ - 1 + δ) α :=
  DiscreteTime.steady_eq _ P (steadyState_pos P.saving_pos P.dilution_pos)
    ((next_eq_self_iff P.growth_pos).mpr (rate_steadyState P.saving_pos P.dilution_pos hα1))

theorem next_zero {b δ γ α : ℝ} (hα : 0 < α) : next (fun k : ℝ => k ^ α) b δ γ 0 = 0 := by
  simp [next, Real.zero_rpow (ne_of_gt hα)]

/-- Full depreciation: the map is `k ↦ (b/γ) k^α`. -/
theorem next_full_depreciation (b γ α k : ℝ) :
    next (fun k : ℝ => k ^ α) b 1 γ k = b / γ * k ^ α := by
  simp only [next, sub_self, zero_mul, add_zero]
  ring

/-- Closed form under full depreciation: `k(t) = k*^(1 - α^t) k₀^(α^t)`. -/
theorem path_full_depreciation {b γ α k₀ : ℝ} (hb : 0 < b) (hγ : 0 < γ) (hα1 : α < 1)
    (hk₀ : 0 < k₀) (t : ℕ) :
    path (fun k : ℝ => k ^ α) b 1 γ k₀ t =
      steadyState b γ α ^ (1 - α ^ t) * k₀ ^ (α ^ t) := by
  have hks := steadyState_pos (α := α) hb hγ
  have hpow : steadyState b γ α ^ (1 - α) = b / γ := by
    have := steadyState_power (α := α) hb hγ hα1
    exact this
  induction t with
  | zero => simp [path_zero]
  | succ t ih =>
    rw [path_succ, ih, next_full_depreciation,
      Real.mul_rpow (Real.rpow_pos_of_pos hks _).le (Real.rpow_pos_of_pos hk₀ _).le,
      ← Real.rpow_mul hks.le, ← Real.rpow_mul hk₀.le, ← hpow, ← mul_assoc,
      ← Real.rpow_add hks, pow_succ]
    congr 2
    ring

/-- Exact convergence rate under full depreciation: the log distance to `k*` is
multiplied by `α` every period, `log k(t) - log k* = α^t (log k₀ - log k*)`. -/
theorem log_gap_full_depreciation {b γ α k₀ : ℝ} (hb : 0 < b) (hγ : 0 < γ) (hα1 : α < 1)
    (hk₀ : 0 < k₀) (t : ℕ) :
    Real.log (path (fun k : ℝ => k ^ α) b 1 γ k₀ t) - Real.log (steadyState b γ α) =
      α ^ t * (Real.log k₀ - Real.log (steadyState b γ α)) := by
  have hks := steadyState_pos (α := α) hb hγ
  rw [path_full_depreciation hb hγ hα1 hk₀,
    Real.log_mul (Real.rpow_pos_of_pos hks _).ne' (Real.rpow_pos_of_pos hk₀ _).ne',
    Real.log_rpow hks, Real.log_rpow hk₀]
  ring

/-- Under full depreciation the path converges to `k*`. -/
theorem tendsto_path_full_depreciation {b γ α k₀ : ℝ} (hb : 0 < b) (hγ : 0 < γ)
    (hα : 0 < α) (hα1 : α < 1) (hk₀ : 0 < k₀) :
    Tendsto (path (fun k : ℝ => k ^ α) b 1 γ k₀) atTop (𝓝 (steadyState b γ α)) := by
  have hks := steadyState_pos (α := α) hb hγ
  have hpow : Tendsto (fun t : ℕ => α ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hα.le hα1
  have h1 : Tendsto (fun t : ℕ => steadyState b γ α ^ (1 - α ^ t)) atTop
      (𝓝 (steadyState b γ α ^ (1 - 0 : ℝ))) :=
    ((Real.continuousAt_const_rpow (ne_of_gt hks)).tendsto).comp
      (tendsto_const_nhds.sub hpow)
  have h2 : Tendsto (fun t : ℕ => k₀ ^ (α ^ t)) atTop (𝓝 (k₀ ^ (0 : ℝ))) :=
    ((Real.continuousAt_const_rpow (ne_of_gt hk₀)).tendsto).comp hpow
  have := h1.mul h2
  simp only [sub_zero, Real.rpow_one, Real.rpow_zero, mul_one] at this
  exact this.congr (fun t => (path_full_depreciation hb hγ hα1 hk₀ t).symm)

/-- Solow's Cobb–Douglas theorem in discrete time: the iterated path is positive,
converges to `k*`, and is the only path from `k₀`. -/
theorem positive_dynamics {b δ γ α k₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (P : Params b δ γ)
    (hk₀ : 0 < k₀) :
    IsPath (fun k : ℝ => k ^ α) b δ γ (path (fun k : ℝ => k ^ α) b δ γ k₀) ∧
      (∀ t, 0 < path (fun k : ℝ => k ^ α) b δ γ k₀ t) ∧
      Tendsto (path (fun k : ℝ => k ^ α) b δ γ k₀) atTop (𝓝 (steadyState b (γ - 1 + δ) α)) ∧
      ∀ k : ℕ → ℝ, k 0 = k₀ → (∀ t, k (t + 1) = next (fun k : ℝ => k ^ α) b δ γ (k t)) →
        k = path (fun k : ℝ => k ^ α) b δ γ k₀ := by
  have hp := isPath_path (f := fun k : ℝ => k ^ α) (s := b) (δ := δ) (γ := γ) hk₀
  have ho := hp.orbit (technology_rpow hα hα1) P
  rw [steady_eq hα hα1 P] at ho
  exact ⟨hp, ho.1, ho.2.2.2.2.2, fun k hk0 hk => path_unique hk (path_succ b δ γ k₀) hk0⟩

/-- Convergence holds for every admissible path, not only the iterated witness. -/
theorem tendsto_of_isPath {b δ γ α : ℝ} (hα : 0 < α) (hα1 : α < 1) (P : Params b δ γ)
    {k : ℕ → ℝ} (hk : IsPath (fun k : ℝ => k ^ α) b δ γ k) :
    Tendsto k atTop (𝓝 (steadyState b (γ - 1 + δ) α)) := by
  have := hk.tendsto (technology_rpow hα hα1) P
  rwa [steady_eq hα hα1 P] at this

/-- Paths never cross the stationary stock. -/
theorem path_lt_steadyState_iff {b δ γ α : ℝ} (hα : 0 < α) (hα1 : α < 1) (P : Params b δ γ)
    {k : ℕ → ℝ} (hk : IsPath (fun k : ℝ => k ^ α) b δ γ k) (t : ℕ) :
    k t < steadyState b (γ - 1 + δ) α ↔ k 0 < steadyState b (γ - 1 + δ) α := by
  obtain ⟨_, hlow, hhigh, hconst, _, _⟩ := hk.orbit (technology_rpow hα hα1) P
  rw [steady_eq hα hα1 P] at hlow hhigh hconst
  constructor
  · intro ht
    rcases lt_trichotomy (k 0) (steadyState b (γ - 1 + δ) α) with hlt | heq | hgt
    · exact hlt
    · exact absurd (hconst heq t) (ne_of_lt ht)
    · exact absurd ((hhigh hgt).2 t) (not_lt.mpr ht.le)
  · intro h0
    exact (hlow h0).2 t

/-- Starting below the steady state gives a strictly increasing path. -/
theorem path_strictMono_of_lt {b δ γ α : ℝ} (hα : 0 < α) (hα1 : α < 1) (P : Params b δ γ)
    {k : ℕ → ℝ} (hk : IsPath (fun k : ℝ => k ^ α) b δ γ k)
    (hbelow : k 0 < steadyState b (γ - 1 + δ) α) : StrictMono k := by
  obtain ⟨_, hlow, _, _, _, _⟩ := hk.orbit (technology_rpow hα hα1) P
  rw [steady_eq hα hα1 P] at hlow
  exact (hlow hbelow).1

/-- Starting above the steady state gives a strictly decreasing path. -/
theorem path_strictAnti_of_gt {b δ γ α : ℝ} (hα : 0 < α) (hα1 : α < 1) (P : Params b δ γ)
    {k : ℕ → ℝ} (hk : IsPath (fun k : ℝ => k ^ α) b δ γ k)
    (habove : steadyState b (γ - 1 + δ) α < k 0) : StrictAnti k := by
  obtain ⟨_, _, hhigh, _, _, _⟩ := hk.orbit (technology_rpow hα hα1) P
  rw [steady_eq hα hα1 P] at hhigh
  exact (hhigh habove).1

/-- Below the positive steady state capital rises; above it capital falls. -/
theorem lt_next_iff {b δ γ α k : ℝ} (hα : 0 < α) (hα1 : α < 1) (P : Params b δ γ)
    (hk : 0 < k) :
    (k < steadyState b (γ - 1 + δ) α → k < next (fun k : ℝ => k ^ α) b δ γ k) ∧
      (steadyState b (γ - 1 + δ) α < k → next (fun k : ℝ => k ^ α) b δ γ k < k) := by
  rw [← steady_eq hα hα1 P]
  exact ⟨next_gt_self (technology_rpow hα hα1) P hk, next_lt_self (technology_rpow hα hα1) P⟩

/-- Output per effective worker converges. -/
theorem tendsto_output {b δ γ α A : ℝ} (hα : 0 < α) (hα1 : α < 1) (P : Params b δ γ)
    {k : ℕ → ℝ} (hk : IsPath (fun k : ℝ => k ^ α) b δ γ k) :
    Tendsto (fun t => A * k t ^ α) atTop (𝓝 (A * steadyState b (γ - 1 + δ) α ^ α)) :=
  ((Real.continuousAt_rpow_const _ α (Or.inl (ne_of_gt
    (steadyState_pos P.saving_pos P.dilution_pos)))).tendsto.comp
      (tendsto_of_isPath hα hα1 P hk)).const_mul A

/-- Higher investment raises the discrete steady state. -/
theorem steady_strictMono_investment {b₁ b₂ δ γ α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (P : Params b₁ δ γ) (hbb : b₁ < b₂) :
    steady (technology_rpow hα hα1) b₁ δ γ < steady (technology_rpow hα hα1) b₂ δ γ := by
  have P2 : Params b₂ δ γ := ⟨P.saving_pos.trans hbb, P.depreciation_le_one, P.growth_pos,
    P.dilution_pos⟩
  rw [steady_eq hα hα1 P, steady_eq hα hα1 P2]
  exact steadyState_strictMono_investment P.saving_pos hbb P.dilution_pos hα1

/-- Higher depreciation or faster effective-labour growth lowers the steady state. -/
theorem steady_strictAnti_dilution {b δ₁ δ₂ γ₁ γ₂ α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (P : Params b δ₁ γ₁) (P2 : Params b δ₂ γ₂) (hlt : γ₁ - 1 + δ₁ < γ₂ - 1 + δ₂) :
    steady (technology_rpow hα hα1) b δ₂ γ₂ < steady (technology_rpow hα hα1) b δ₁ γ₁ := by
  rw [steady_eq hα hα1 P, steady_eq hα hα1 P2]
  exact steadyState_strictAnti_dilution P.saving_pos P.dilution_pos hlt hα1

/-- The stationary capital/output ratio is saving over effective dilution. -/
theorem steady_capital_output_ratio {s A δ γ α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 < A) (P : Params (s * A) δ γ) (hs : 0 < s) :
    steady (technology_rpow hα hα1) (s * A) δ γ /
        (A * steady (technology_rpow hα hα1) (s * A) δ γ ^ α) = s / (γ - 1 + δ) := by
  rw [steady_eq hα hα1 P]
  exact steadyState_capital_output_ratio hs hA P.dilution_pos hα1

end Solow1956.DiscreteTime.CobbDouglas
