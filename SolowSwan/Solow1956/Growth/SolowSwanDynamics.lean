/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/
import Solow1956.Growth.SolowSwan
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.LinearCombination

/-!
# Solow–Swan: arbitrary Cobb–Douglas exponent and positive trajectories

For `k' = b k^α - m k`, `b > 0`, `m > 0`, `0 < α < 1`, and `k₀ > 0`,
the change of variable `z = k^(1-α)` gives a linear equation. We construct
the solution, prove uniqueness among positive differentiable trajectories
on nonnegative time, and prove convergence. In the original net-output model,
`b = s A` and `m = n`; in the effective-labour extension, `m = n + g + δ`.

Source: Solow (1956), QJE 70(1), 65–94, DOI 10.2307/1884513,
equation (6), p. 69, and Example 2, pp. 76–77. The depreciation and
effective-labour normalization below is stated as an explicit extension.
-/

open Set Filter Topology

namespace Solow1956.SolowSwan

/-- Effective capital with gross investment, depreciation, and growing effective labour. -/
theorem hasDerivAt_capitalPerEffectiveWorker {K E f : ℝ → ℝ} {Y s δ n g t : ℝ}
    (hE : 0 < E t) (hK : HasDerivAt K (s * Y - δ * K t) t)
    (hE' : HasDerivAt E ((n + g) * E t) t)
    (hY : Y = E t * f (K t / E t)) :
    HasDerivAt (fun u => K u / E u)
      (s * f (K t / E t) - (n + g + δ) * (K t / E t)) t := by
  convert! hK.fun_div hE' (ne_of_gt hE) using 1
  rw [hY]
  field_simp
  ring

namespace CobbDouglas

/-- Accumulation in intensive form; `b` is saving times constant productivity. -/
noncomputable def rate (b m α k : ℝ) : ℝ := b * k ^ α - m * k

/-- The strictly positive steady state. -/
noncomputable def steadyState (b m α : ℝ) : ℝ := (b / m) ^ (1 - α)⁻¹

/-- Linearized path, with initial transformed stock `z₀`. -/
noncomputable def transformedPath (b m α z₀ t : ℝ) : ℝ :=
  b / m + (z₀ - b / m) * Real.exp (-((1 - α) * m) * t)

/-- The explicit path starting from `k₀` at time zero. -/
noncomputable def path (b m α k₀ t : ℝ) : ℝ :=
  transformedPath b m α (k₀ ^ (1 - α)) t ^ (1 - α)⁻¹

theorem steadyState_pos {b m α : ℝ} (hb : 0 < b) (hm : 0 < m) :
    0 < steadyState b m α := Real.rpow_pos_of_pos (div_pos hb hm) _

/-- The zero boundary is stationary too. -/
theorem rate_zero {b m α : ℝ} (hα : 0 < α) : rate b m α 0 = 0 := by
  simp [rate, Real.zero_rpow (ne_of_gt hα)]

theorem rate_factor {b m α k : ℝ} (hk : 0 < k) :
    rate b m α k = k ^ α * (b - m * k ^ (1 - α)) := by
  have hp : k ^ α * k ^ (1 - α) = k := by
    rw [← Real.rpow_add hk]; simp
  unfold rate
  linear_combination m * hp

theorem steadyState_power {b m α : ℝ} (hb : 0 < b) (hm : 0 < m) (hα : α < 1) :
    steadyState b m α ^ (1 - α) = b / m := by
  exact Real.rpow_inv_rpow (le_of_lt (div_pos hb hm)) (by linarith)

theorem rate_steadyState {b m α : ℝ} (hb : 0 < b) (hm : 0 < m) (hα : α < 1) :
    rate b m α (steadyState b m α) = 0 := by
  rw [rate_factor (steadyState_pos hb hm), steadyState_power hb hm hα]
  field_simp
  ring

theorem eq_steadyState_of_pos {b m α k : ℝ} (hm : 0 < m) (hα : α < 1)
    (hk : 0 < k) (h : rate b m α k = 0) : k = steadyState b m α := by
  rw [rate_factor hk] at h
  have he : k ^ (1 - α) = b / m := by
    have := (mul_eq_zero.mp h).resolve_left (ne_of_gt (Real.rpow_pos_of_pos hk α))
    apply (eq_div_iff (ne_of_gt hm)).2
    nlinarith
  have := congrArg (fun x : ℝ => x ^ (1 - α)⁻¹) he
  simpa [steadyState, Real.rpow_rpow_inv hk.le (show 1 - α ≠ 0 by linarith)] using this

theorem existsUnique_positive_steadyState {b m α : ℝ}
    (hb : 0 < b) (hm : 0 < m) (hα : α < 1) :
    ∃! k : ℝ, 0 < k ∧ rate b m α k = 0 := by
  exact ⟨steadyState b m α, ⟨steadyState_pos hb hm, rate_steadyState hb hm hα⟩,
    fun k h => eq_steadyState_of_pos hm hα h.1 h.2⟩

theorem rate_eq_zero_iff {b m α k : ℝ} (hb : 0 < b) (hm : 0 < m)
    (hα₀ : 0 < α) (hα₁ : α < 1) (hk : 0 ≤ k) :
    rate b m α k = 0 ↔ k = 0 ∨ k = steadyState b m α := by
  constructor
  · intro h
    rcases hk.eq_or_lt with he | hp
    · exact Or.inl he.symm
    · exact Or.inr (eq_steadyState_of_pos hm hα₁ hp h)
  · rintro (rfl | rfl)
    · exact rate_zero hα₀
    · exact rate_steadyState hb hm hα₁

theorem transformedPath_zero (b m α z₀ : ℝ) : transformedPath b m α z₀ 0 = z₀ := by
  simp [transformedPath]

/-- Positive initial and stationary transformed stocks give positivity at all future times. -/
theorem transformedPath_pos {b m α z₀ t : ℝ} (hb : 0 < b) (hm : 0 < m)
    (hα : α < 1) (hz : 0 < z₀) (ht : 0 ≤ t) : 0 < transformedPath b m α z₀ t := by
  have he : 0 < Real.exp (-((1 - α) * m) * t) := Real.exp_pos _
  have he₁ : Real.exp (-((1 - α) * m) * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_pos (sub_pos.mpr hα) hm])
  have hb' := div_pos hb hm
  have h₁ := mul_nonneg hb'.le (sub_nonneg.mpr he₁)
  have h₂ := mul_pos hz he
  unfold transformedPath
  nlinarith

theorem path_pos {b m α k₀ t : ℝ} (hb : 0 < b) (hm : 0 < m)
    (hα : α < 1) (hk : 0 < k₀) (ht : 0 ≤ t) : 0 < path b m α k₀ t :=
  Real.rpow_pos_of_pos (transformedPath_pos hb hm hα (Real.rpow_pos_of_pos hk _) ht) _

theorem path_zero {b m α k₀ : ℝ} (hα : α < 1) (hk : 0 ≤ k₀) :
    path b m α k₀ 0 = k₀ := by
  rw [path, transformedPath_zero, Real.rpow_rpow_inv hk (by linarith)]

theorem hasDerivAt_transformedPath {b m α z₀ t : ℝ} (hm : m ≠ 0) :
    HasDerivAt (transformedPath b m α z₀)
      ((1 - α) * (b - m * transformedPath b m α z₀ t)) t := by
  convert! (((hasDerivAt_id t).const_mul (-((1 - α) * m))).exp.const_mul
    (z₀ - b / m)).const_add (b / m) using 1
  simp only [transformedPath, id_eq]
  field_simp
  ring

/-- Chain-rule justification for the linearization; positivity makes negative powers legitimate. -/
theorem hasDerivAt_power {k : ℝ → ℝ} {b m α t : ℝ} (hk : 0 < k t)
    (hd : HasDerivAt k (rate b m α (k t)) t) :
    HasDerivAt (fun u => k u ^ (1 - α))
      ((1 - α) * (b - m * k t ^ (1 - α))) t := by
  convert! hd.rpow_const (p := 1 - α) (Or.inl (ne_of_gt hk)) using 1
  rw [rate_factor hk]
  have hp : (k t) ^ α * (k t) ^ (1 - α - 1) = 1 := by
    rw [← Real.rpow_add hk]; ring_nf; exact Real.rpow_zero _
  linear_combination -(1 - α) * (b - m * k t ^ (1 - α)) * hp

/-- Recover the nonlinear differential equation from the explicitly solved linear one. -/
theorem hasDerivAt_path {b m α k₀ t : ℝ} (hb : 0 < b) (hm : 0 < m)
    (hα : α < 1) (hk : 0 < k₀) (ht : 0 ≤ t) :
    HasDerivAt (path b m α k₀) (rate b m α (path b m α k₀ t)) t := by
  have hz := transformedPath_pos hb hm hα (Real.rpow_pos_of_pos hk (1 - α)) ht
  have hq : 1 - α ≠ 0 := by linarith
  let z := transformedPath b m α (k₀ ^ (1 - α)) t
  have hz' : 0 < z := hz
  have hp : (z ^ (1 - α)⁻¹) ^ α = z ^ ((1 - α)⁻¹ - 1) := by
    rw [← Real.rpow_mul hz'.le]
    congr 1
    field_simp
    ring
  have hmul : z * z ^ ((1 - α)⁻¹ - 1) = z ^ (1 - α)⁻¹ := by
    conv_lhs => lhs; rw [← Real.rpow_one z]
    rw [← Real.rpow_add hz']
    congr 1
    ring
  convert! (hasDerivAt_transformedPath (b := b) (α := α)
    (z₀ := k₀ ^ (1 - α)) (t := t) (ne_of_gt hm)).rpow_const
      (p := (1 - α)⁻¹) (Or.inl (ne_of_gt hz)) using 1
  change b * (z ^ (1 - α)⁻¹) ^ α - m * z ^ (1 - α)⁻¹ = _
  rw [hp, ← hmul]
  field_simp
  ring

/-- Integrating-factor uniqueness for the transformed equation, including time zero. -/
theorem eq_transformedPath_of_hasDerivAt {z : ℝ → ℝ} {b m α t : ℝ} (hm : m ≠ 0)
    (ht : 0 ≤ t)
    (hd : ∀ u, 0 ≤ u → HasDerivAt z ((1 - α) * (b - m * z u)) u) :
    z t = transformedPath b m α (z 0) t := by
  let w : ℝ → ℝ := fun u => (z u - b / m) * Real.exp (((1 - α) * m) * u)
  have hw : ∀ u, 0 ≤ u → HasDerivAt w 0 u := by
    intro u hu
    convert! ((hd u hu).sub_const (b / m)).mul
      (((hasDerivAt_id u).const_mul ((1 - α) * m)).exp) using 1
    simp only [id_eq]
    field_simp
    ring
  have hconst : w t = w 0 := constant_of_has_deriv_right_zero
    (fun u hu => (hw u hu.1).continuousAt.continuousWithinAt)
    (fun u hu => (hw u hu.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  have he := Real.exp_ne_zero (((1 - α) * m) * t)
  dsimp [w] at hconst
  simp only [mul_zero, Real.exp_zero, mul_one] at hconst
  unfold transformedPath
  rw [show -((1 - α) * m) * t = -(((1 - α) * m) * t) by ring, Real.exp_neg]
  have hz := (eq_div_iff he).mpr hconst
  simp only [div_eq_mul_inv] at hz ⊢
  linarith

/-- Every positive solution has the constructed time path on nonnegative time. -/
theorem solution_eq_path {k : ℝ → ℝ} {b m α t : ℝ} (hm : 0 < m) (hα : α < 1)
    (ht : 0 ≤ t) (hk : ∀ u, 0 ≤ u → 0 < k u)
    (hd : ∀ u, 0 ≤ u → HasDerivAt k (rate b m α (k u)) u) :
    k t = path b m α (k 0) t := by
  have h := eq_transformedPath_of_hasDerivAt (ne_of_gt hm) ht
    (fun u hu => hasDerivAt_power (hk u hu) (hd u hu))
  have he := congrArg (fun x : ℝ => x ^ (1 - α)⁻¹) h
  simpa [path, Real.rpow_rpow_inv (hk t ht).le (show 1 - α ≠ 0 by linarith)] using he

theorem tendsto_transformedPath {b m α z₀ : ℝ} (hm : 0 < m) (hα : α < 1) :
    Tendsto (transformedPath b m α z₀) atTop (𝓝 (b / m)) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-((1 - α) * m) * t)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (mul_pos (sub_pos.mpr hα) hm))
    simpa only [Function.comp_def, neg_mul, id_eq] using h
  unfold transformedPath
  simpa only [mul_zero, add_zero] using
    (tendsto_const_nhds (x := b / m)).add (he.const_mul (z₀ - b / m))

theorem tendsto_path {b m α k₀ : ℝ} (hb : 0 < b) (hm : 0 < m) (hα : α < 1) :
    Tendsto (path b m α k₀) atTop (𝓝 (steadyState b m α)) := by
  exact (Real.continuousAt_rpow_const (b / m) (1 - α)⁻¹
    (Or.inl (ne_of_gt (div_pos hb hm)))).tendsto.comp (tendsto_transformedPath hm hα)

/-- Exact convergence rate in the transformed coordinate. -/
theorem path_power_gap {b m α k₀ t : ℝ} (hb : 0 < b) (hm : 0 < m)
    (hα : α < 1) (hk : 0 < k₀) (ht : 0 ≤ t) :
    path b m α k₀ t ^ (1 - α) - steadyState b m α ^ (1 - α) =
      (k₀ ^ (1 - α) - steadyState b m α ^ (1 - α)) *
        Real.exp (-((1 - α) * m) * t) := by
  rw [steadyState_power hb hm hα, path,
    Real.rpow_inv_rpow (transformedPath_pos hb hm hα (Real.rpow_pos_of_pos hk _) ht).le
      (by linarith)]
  simp [transformedPath]

/-- A precise solution concept; the equation and strict positivity hold at every future time. -/
def IsPositiveSolution (b m α k₀ : ℝ) (k : ℝ → ℝ) : Prop :=
  k 0 = k₀ ∧ ∀ t, 0 ≤ t → 0 < k t ∧ HasDerivAt k (rate b m α (k t)) t

/-- Solow's Cobb–Douglas convergence theorem, with existence and uniqueness on future time.
The lower bound on the exponent gives the economic model and its zero stationary boundary;
the positive-path argument itself only needs `α < 1`. -/
theorem positive_dynamics {b m α k₀ : ℝ} (hb : 0 < b) (hm : 0 < m)
    (_hα₀ : 0 < α) (hα₁ : α < 1) (hk : 0 < k₀) :
    IsPositiveSolution b m α k₀ (path b m α k₀) ∧
    Tendsto (path b m α k₀) atTop (𝓝 (steadyState b m α)) ∧
    ∀ k, IsPositiveSolution b m α k₀ k → EqOn k (path b m α k₀) (Ici 0) := by
  refine ⟨⟨path_zero hα₁ hk.le, fun t ht =>
    ⟨path_pos hb hm hα₁ hk ht, hasDerivAt_path hb hm hα₁ hk ht⟩⟩,
    tendsto_path hb hm hα₁, ?_⟩
  intro k h t ht
  simpa only [h.1] using solution_eq_path hm hα₁ ht
    (fun u hu => (h.2 u hu).1) (fun u hu => (h.2 u hu).2)

/-- Below the positive steady state, capital accumulation is strictly positive. -/
theorem rate_pos_of_lt {b m α k : ℝ} (hb : 0 < b) (hm : 0 < m)
    (hα : α < 1) (hk : 0 < k) (hlt : k < steadyState b m α) : 0 < rate b m α k := by
  have hp := Real.rpow_lt_rpow hk.le hlt (sub_pos.mpr hα)
  rw [steadyState_power hb hm hα] at hp
  rw [rate_factor hk]
  apply mul_pos (Real.rpow_pos_of_pos hk α)
  have := (lt_div_iff₀ hm).mp hp
  nlinarith

theorem rate_neg_of_gt {b m α k : ℝ} (hb : 0 < b) (hm : 0 < m)
    (hα : α < 1) (hlt : steadyState b m α < k) : rate b m α k < 0 := by
  have hs := steadyState_pos (α := α) hb hm
  have hp := Real.rpow_lt_rpow hs.le hlt (sub_pos.mpr hα)
  rw [steadyState_power hb hm hα] at hp
  rw [rate_factor (hs.trans hlt)]
  apply mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos (hs.trans hlt) α)
  have := (div_lt_iff₀ hm).mp hp
  nlinarith

theorem steadyState_strictMono_investment {b₁ b₂ m α : ℝ}
    (hb : 0 < b₁) (hbb : b₁ < b₂) (hm : 0 < m) (hα : α < 1) :
    steadyState b₁ m α < steadyState b₂ m α :=
  Real.rpow_lt_rpow (div_pos hb hm).le ((div_lt_div_iff_of_pos_right hm).2 hbb)
    (inv_pos.mpr (sub_pos.mpr hα))

theorem steadyState_strictAnti_dilution {b m₁ m₂ α : ℝ}
    (hb : 0 < b) (hm : 0 < m₁) (hmm : m₁ < m₂) (hα : α < 1) :
    steadyState b m₂ α < steadyState b m₁ α :=
  Real.rpow_lt_rpow (div_pos hb (hm.trans hmm)).le
    (div_lt_div_of_pos_left hb hm hmm) (inv_pos.mpr (sub_pos.mpr hα))

/-- Higher saving raises the steady state when productivity and dilution are fixed. -/
theorem steadyState_strictMono_saving {s₁ s₂ A m α : ℝ}
    (hs : 0 < s₁) (hss : s₁ < s₂) (hA : 0 < A) (hm : 0 < m) (hα : α < 1) :
    steadyState (s₁ * A) m α < steadyState (s₂ * A) m α :=
  steadyState_strictMono_investment (mul_pos hs hA) (mul_lt_mul_of_pos_right hss hA) hm hα

/-- The stationary capital/output ratio is saving divided by effective dilution. -/
theorem steadyState_capital_output_ratio {s A m α : ℝ}
    (hs : 0 < s) (hA : 0 < A) (hm : 0 < m) (hα : α < 1) :
    steadyState (s * A) m α / (A * steadyState (s * A) m α ^ α) = s / m := by
  have hk := steadyState_pos (α := α) (mul_pos hs hA) hm
  have hr := rate_steadyState (mul_pos hs hA) hm hα
  apply (div_eq_div_iff (ne_of_gt (mul_pos hA (Real.rpow_pos_of_pos hk α))) (ne_of_gt hm)).2
  unfold rate at hr
  nlinarith [hr]

/-- Positive paths never cross the stationary path. -/
theorem path_lt_steadyState_iff {b m α k₀ t : ℝ} (hb : 0 < b) (hm : 0 < m)
    (hα : α < 1) (hk : 0 < k₀) (ht : 0 ≤ t) :
    path b m α k₀ t < steadyState b m α ↔ k₀ < steadyState b m α := by
  rw [← Real.rpow_lt_rpow_iff (path_pos hb hm hα hk ht).le
    (steadyState_pos hb hm).le (sub_pos.mpr hα),
    ← Real.rpow_lt_rpow_iff hk.le (steadyState_pos hb hm).le (sub_pos.mpr hα)]
  have h := path_power_gap hb hm hα hk ht
  have he := Real.exp_pos (-((1 - α) * m) * t)
  constructor <;> intro hlt
  · have hprod : (k₀ ^ (1 - α) - steadyState b m α ^ (1 - α)) *
        Real.exp (-((1 - α) * m) * t) < 0 := by linarith
    by_contra hn
    have hn' : 0 ≤ k₀ ^ (1 - α) - steadyState b m α ^ (1 - α) := by linarith
    exact (not_le_of_gt hprod) (mul_nonneg hn' he.le)
  · have := mul_neg_of_neg_of_pos (sub_neg.mpr hlt) he
    linarith

/-- Convergence holds for every positive solution, not merely the constructed witness. -/
theorem tendsto_of_isPositiveSolution {b m α k₀ : ℝ} {k : ℝ → ℝ}
    (hb : 0 < b) (hm : 0 < m) (hα : α < 1) (h : IsPositiveSolution b m α k₀ k) :
    Tendsto k atTop (𝓝 (steadyState b m α)) := by
  apply (tendsto_path (k₀ := k₀) hb hm hα).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  symm
  simpa only [h.1] using (solution_eq_path hm hα ht
    (fun u hu => (h.2 u hu).1) (fun u hu => (h.2 u hu).2))

/-- Starting below the steady state gives a nondecreasing time path. -/
theorem path_monotoneOn_of_le {b m α k₀ : ℝ} (hb : 0 < b) (hm : 0 < m)
    (hα : α < 1) (hk : 0 < k₀) (hbelow : k₀ ≤ steadyState b m α) :
    MonotoneOn (path b m α k₀) (Ici 0) := by
  have hc := Real.rpow_le_rpow hk.le hbelow (sub_pos.mpr hα).le
  rw [steadyState_power hb hm hα] at hc
  intro x hx y _ hxy
  have he : Real.exp (-((1 - α) * m) * y) ≤ Real.exp (-((1 - α) * m) * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr
      (mul_pos (sub_pos.mpr hα) hm).le))
  apply Real.rpow_le_rpow (transformedPath_pos hb hm hα (Real.rpow_pos_of_pos hk _) hx).le
    _ (inv_pos.mpr (sub_pos.mpr hα)).le
  unfold transformedPath
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr he)]

/-- Starting above the steady state gives a nonincreasing time path. -/
theorem path_antitoneOn_of_le {b m α k₀ : ℝ} (hb : 0 < b) (hm : 0 < m)
    (hα : α < 1) (hk : 0 < k₀) (habove : steadyState b m α ≤ k₀) :
    AntitoneOn (path b m α k₀) (Ici 0) := by
  have hc := Real.rpow_le_rpow (steadyState_pos hb hm).le habove (sub_pos.mpr hα).le
  rw [steadyState_power hb hm hα] at hc
  intro x _ y hy hxy
  have he : Real.exp (-((1 - α) * m) * y) ≤ Real.exp (-((1 - α) * m) * x) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hxy (neg_nonpos.mpr
      (mul_pos (sub_pos.mpr hα) hm).le))
  apply Real.rpow_le_rpow (transformedPath_pos hb hm hα (Real.rpow_pos_of_pos hk _) hy).le
    _ (inv_pos.mpr (sub_pos.mpr hα)).le
  unfold transformedPath
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr he)]

/-- Output per effective worker converges by continuity of the production function. -/
theorem tendsto_output {b m α k₀ A : ℝ} (hb : 0 < b) (hm : 0 < m) (hα : α < 1) :
    Tendsto (fun t => A * path b m α k₀ t ^ α) atTop
      (𝓝 (A * steadyState b m α ^ α)) := by
  exact ((Real.continuousAt_rpow_const (steadyState b m α) α
    (Or.inl (ne_of_gt (steadyState_pos hb hm)))).tendsto.comp
      (tendsto_path hb hm hα)).const_mul A

/-- Investment makes capital multiplied by its dilution factor nondecreasing. -/
theorem weightedCapital_monotoneOn {k : ℝ → ℝ} {b m α : ℝ} (hb : 0 ≤ b)
    (hk : ∀ t, 0 ≤ t → 0 ≤ k t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt k (rate b m α (k t)) t) :
    MonotoneOn (fun t => k t * Real.exp (m * t)) (Ici 0) := by
  have hw (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (fun u => k u * Real.exp (m * u))
        (b * k t ^ α * Real.exp (m * t)) t := by
    convert! (hd t ht).mul (((hasDerivAt_id t).const_mul m).exp) using 1
    simp only [rate, id_eq]
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro t ht
    exact (hw t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hw t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hw t (interior_subset ht)).deriv]
    exact mul_nonneg (mul_nonneg hb (Real.rpow_nonneg (hk t (interior_subset ht)) α))
      (Real.exp_pos _).le

/-- A nonnegative solution starting positively cannot hit the zero boundary in finite time. -/
theorem positive_of_nonnegative_solution {k : ℝ → ℝ} {b m α : ℝ} (hb : 0 ≤ b)
    (hk₀ : 0 < k 0) (hk : ∀ t, 0 ≤ t → 0 ≤ k t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt k (rate b m α (k t)) t)
    {t : ℝ} (ht : 0 ≤ t) : 0 < k t := by
  have h := weightedCapital_monotoneOn hb hk hd (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
  simp only [mul_zero, Real.exp_zero, mul_one] at h
  have hpos := lt_of_lt_of_le hk₀ h
  by_contra hn
  have := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) (Real.exp_pos (m * t)).le
  linarith

/-- An economically nonnegative solution; strict future positivity is a conclusion. -/
def IsNonnegativeSolution (b m α k₀ : ℝ) (k : ℝ → ℝ) : Prop :=
  k 0 = k₀ ∧ ∀ t, 0 ≤ t → 0 ≤ k t ∧ HasDerivAt k (rate b m α (k t)) t

theorem IsNonnegativeSolution.isPositiveSolution {k : ℝ → ℝ} {b m α k₀ : ℝ}
    (h : IsNonnegativeSolution b m α k₀ k) (hb : 0 ≤ b) (hk₀ : 0 < k₀) :
    IsPositiveSolution b m α k₀ k := by
  refine ⟨h.1, fun t ht => ⟨?_, (h.2 t ht).2⟩⟩
  exact positive_of_nonnegative_solution hb (h.1.symm ▸ hk₀)
    (fun u hu => (h.2 u hu).1) (fun u hu => (h.2 u hu).2) ht

/-- Complete future dynamics among nonnegative capital paths with positive initial capital. -/
theorem nonnegative_dynamics {b m α k₀ : ℝ} (hb : 0 < b) (hm : 0 < m)
    (hα₀ : 0 < α) (hα₁ : α < 1) (hk₀ : 0 < k₀) :
    IsNonnegativeSolution b m α k₀ (path b m α k₀) ∧
    ∀ k, IsNonnegativeSolution b m α k₀ k →
      (∀ t, 0 ≤ t → 0 < k t) ∧ EqOn k (path b m α k₀) (Ici 0) ∧
        Tendsto k atTop (𝓝 (steadyState b m α)) := by
  have h := positive_dynamics hb hm hα₀ hα₁ hk₀
  refine ⟨⟨h.1.1, fun t ht => ⟨(h.1.2 t ht).1.le, (h.1.2 t ht).2⟩⟩, ?_⟩
  intro k hnonneg
  have hp := hnonneg.isPositiveSolution hb.le hk₀
  exact ⟨fun t ht => (hp.2 t ht).1, h.2.2 k hp, tendsto_of_isPositiveSolution hb hm hα₁ hp⟩

end CobbDouglas
end Solow1956.SolowSwan
