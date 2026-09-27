import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false

/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/

/-!
# Solow–Swan growth: capital per worker and square-root production

The accumulation equation is `K' = s F(K,L)` and labour grows at rate `n`.
Writing constant-returns output as `F(K,L) = L f(K/L)` gives
`k' = s f(k) - n k`. Output is net of depreciation; there is no separate
depreciation or technological-progress term in this first model.

`SquareRoot` specializes to `f(k) = A √k`, the Cobb–Douglas exponent `1/2`.
It proves the two stationary states, uniqueness among positive stocks,
the sign of adjustment, and steady-state comparative statics. Sign results
alone do not assert existence, uniqueness, or convergence of ODE solutions.

Source: R. M. Solow (1956), *A Contribution to the Theory of Economic Growth*,
QJE 70(1), 65–94, DOI 10.2307/1884513: equation (6), p. 69; the zero-stock
qualification, footnote 4, pp. 70–71; Cobb–Douglas Example 2, pp. 76–77.
Productivity `A` is an explicit constant multiplier of that example.
-/

namespace Solow1956.SolowSwan

/-- Net accumulation of capital per worker at stock `k`. -/
def capitalChange (f : ℝ → ℝ) (s n k : ℝ) : ℝ := s * f k - n * k

/-- Derive the intensive-form equation from aggregate accumulation, labour
growth, and the constant-returns normalization at the time under study. -/
theorem hasDerivAt_capitalPerWorker {K L f : ℝ → ℝ} {F : ℝ → ℝ → ℝ}
    {s n t : ℝ} (hL : 0 < L t)
    (hK' : HasDerivAt K (s * F (K t) (L t)) t)
    (hL' : HasDerivAt L (n * L t) t)
    (hF : F (K t) (L t) = L t * f (K t / L t)) :
    HasDerivAt (fun u => K u / L u) (capitalChange f s n (K t / L t)) t := by
  have hder := hK'.fun_div hL' (ne_of_gt hL)
  have hrate : ((s * F (K t) (L t)) * L t - K t * (n * L t)) / L t ^ 2 =
      capitalChange f s n (K t / L t) := by
    rw [hF]
    unfold capitalChange
    field_simp
  rw [hrate] at hder
  exact hder

/-- Homogeneity of degree one supplies the intensive-form normalization. -/
theorem intensiveForm_of_homogeneous {F : ℝ → ℝ → ℝ} {K L : ℝ} (hL : 0 < L)
    (hF : ∀ (k l a : ℝ), 0 < a → F (a * k) (a * l) = a * F k l) :
    F K L = L * F (K / L) 1 := by
  simpa [mul_div_cancel₀ K (ne_of_gt hL)] using hF (K / L) 1 L hL

namespace SquareRoot

/-- Cobb–Douglas output per worker with capital exponent `1/2`. -/
noncomputable def production (A k : ℝ) : ℝ := A * Real.sqrt k

/-- The positive stationary capital stock when `s`, `A`, and `n` are positive. -/
noncomputable def steadyState (s A n : ℝ) : ℝ := (s * A / n) ^ 2

theorem steadyState_pos {s A n : ℝ} (hs : 0 < s) (hA : 0 < A) (hn : 0 < n) :
    0 < steadyState s A n := by
  unfold steadyState
  positivity

theorem sqrt_steadyState {s A n : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A) (hn : 0 < n) :
    Real.sqrt (steadyState s A n) = s * A / n := by
  exact Real.sqrt_sq (div_nonneg (mul_nonneg hs hA) hn.le)

/-- The zero-stock stationary state must not be lost by dividing by `√k`. -/
@[simp] theorem capitalChange_zero (s A n : ℝ) :
    capitalChange (production A) s n 0 = 0 := by
  simp [capitalChange, production]

theorem capitalChange_factor {s A n k : ℝ} (hk : 0 ≤ k) :
    capitalChange (production A) s n k =
      Real.sqrt k * (s * A - n * Real.sqrt k) := by
  unfold capitalChange production
  calc
    s * (A * Real.sqrt k) - n * k =
        s * (A * Real.sqrt k) - n * (Real.sqrt k) ^ 2 := by rw [Real.sq_sqrt hk]
    _ = _ := by ring

theorem capitalChange_steadyState {s A n : ℝ}
    (hs : 0 ≤ s) (hA : 0 ≤ A) (hn : 0 < n) :
    capitalChange (production A) s n (steadyState s A n) = 0 := by
  have hk : 0 ≤ steadyState s A n := sq_nonneg _
  rw [capitalChange_factor hk, sqrt_steadyState hs hA hn]
  have h : n * (s * A / n) = s * A := by field_simp
  rw [h, sub_self, mul_zero]

/-- Every strictly positive stationary stock is the stated steady state. -/
theorem eq_steadyState_of_pos {s A n k : ℝ} (hn : 0 < n) (hk : 0 < k)
    (h : capitalChange (production A) s n k = 0) : k = steadyState s A n := by
  rw [capitalChange_factor hk.le] at h
  have hroot : 0 < Real.sqrt k := Real.sqrt_pos.mpr hk
  have hfactor := (mul_eq_zero.mp h).resolve_left (ne_of_gt hroot)
  have heq : Real.sqrt k = s * A / n := by
    apply (eq_div_iff (ne_of_gt hn)).mpr
    nlinarith [hfactor]
  rw [← Real.sq_sqrt hk.le, heq]
  rfl

/-- On the economic domain, the stationary stocks are exactly zero and `k*`. -/
theorem capitalChange_eq_zero_iff {s A n k : ℝ}
    (hs : 0 ≤ s) (hA : 0 ≤ A) (hn : 0 < n) (hk : 0 ≤ k) :
    capitalChange (production A) s n k = 0 ↔ k = 0 ∨ k = steadyState s A n := by
  constructor
  · intro h
    by_cases hk0 : k = 0
    · exact Or.inl hk0
    · exact Or.inr (eq_steadyState_of_pos hn (lt_of_le_of_ne hk (Ne.symm hk0)) h)
  · rintro (rfl | rfl)
    · exact capitalChange_zero s A n
    · exact capitalChange_steadyState hs hA hn

/-- Existence and uniqueness hold on strictly positive capital stocks. -/
theorem existsUnique_positive_steadyState {s A n : ℝ}
    (hs : 0 < s) (hA : 0 < A) (hn : 0 < n) :
    ∃! k : ℝ, 0 < k ∧ capitalChange (production A) s n k = 0 := by
  refine ⟨steadyState s A n,
    ⟨steadyState_pos hs hA hn, capitalChange_steadyState hs.le hA.le hn⟩, ?_⟩
  intro k hk
  exact eq_steadyState_of_pos hn hk.1 hk.2

/-- Capital increases at every strictly positive stock below `k*`. -/
theorem capitalChange_pos_of_lt {s A n k : ℝ}
    (hs : 0 < s) (hA : 0 < A) (hn : 0 < n) (hk : 0 < k)
    (hlt : k < steadyState s A n) : 0 < capitalChange (production A) s n k := by
  have hroot : Real.sqrt k < s * A / n := by
    rw [← sqrt_steadyState hs.le hA.le hn]
    exact Real.sqrt_lt_sqrt hk.le hlt
  have hfactor : 0 < s * A - n * Real.sqrt k := by
    have := (lt_div_iff₀ hn).mp hroot
    nlinarith
  rw [capitalChange_factor hk.le]
  exact mul_pos (Real.sqrt_pos.mpr hk) hfactor

/-- Capital decreases at every stock above `k*`. -/
theorem capitalChange_neg_of_gt {s A n k : ℝ}
    (hs : 0 < s) (hA : 0 < A) (hn : 0 < n)
    (hgt : steadyState s A n < k) : capitalChange (production A) s n k < 0 := by
  have hstar := steadyState_pos hs hA hn
  have hk : 0 < k := lt_trans hstar hgt
  have hroot : s * A / n < Real.sqrt k := by
    rw [← sqrt_steadyState hs.le hA.le hn]
    exact Real.sqrt_lt_sqrt hstar.le hgt
  have hfactor : s * A - n * Real.sqrt k < 0 := by
    have := (div_lt_iff₀ hn).mp hroot
    nlinarith
  rw [capitalChange_factor hk.le]
  exact mul_neg_of_pos_of_neg (Real.sqrt_pos.mpr hk) hfactor

/-- Higher saving raises the positive stationary stock. No upper bound on
the saving fraction is needed for this mathematical implication. -/
theorem steadyState_strictMono_saving {A n : ℝ} (hA : 0 < A) (hn : 0 < n) :
    StrictMonoOn (fun s => steadyState s A n) (Set.Ici 0) := by
  intro s₁ hs₁ s₂ _ hs
  unfold steadyState
  have hs₁' : 0 ≤ s₁ := hs₁
  have h₁ : 0 ≤ s₁ * A / n := by positivity
  have h₂ : s₁ * A / n < s₂ * A / n := by gcongr
  nlinarith

/-- Higher productivity raises the positive stationary stock. -/
theorem steadyState_strictMono_productivity {s n : ℝ} (hs : 0 < s) (hn : 0 < n) :
    StrictMonoOn (fun A => steadyState s A n) (Set.Ici 0) := by
  intro A₁ hA₁ A₂ _ hA
  unfold steadyState
  have hA₁' : 0 ≤ A₁ := hA₁
  have h₁ : 0 ≤ s * A₁ / n := by positivity
  have h₂ : s * A₁ / n < s * A₂ / n := by gcongr
  nlinarith

/-- Faster labour growth lowers the positive stationary stock. -/
theorem steadyState_strictAnti_population {s A : ℝ} (hs : 0 < s) (hA : 0 < A) :
    StrictAntiOn (steadyState s A) (Set.Ioi 0) := by
  intro n₁ hn₁ n₂ _ hn
  unfold steadyState
  have hn₁' : 0 < n₁ := hn₁
  have hn₂' : 0 < n₂ := lt_trans hn₁' hn
  have h₁ : 0 < s * A / n₂ := by positivity
  have h₂ : s * A / n₂ < s * A / n₁ := by gcongr
  nlinarith

/-- The stationary capital/output ratio is `s/n` (Solow, p. 77). -/
theorem steadyState_capital_output_ratio {s A n : ℝ}
    (hs : 0 < s) (hA : 0 < A) (hn : 0 < n) :
    steadyState s A n / production A (steadyState s A n) = s / n := by
  unfold production
  rw [sqrt_steadyState hs.le hA.le hn]
  unfold steadyState
  field_simp

end SquareRoot
end Solow1956.SolowSwan

/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/

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

/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/

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

/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
Analytic helpers adapted from the project's Cass formalization; see source-map.
-/

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

/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
Analytic helpers adapted from the project's Cass formalization; see source-map.
-/

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

/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
Analytic helpers adapted from the project's Cass formalization; see source-map.
-/

/-! # Drift bounds and limits of autonomous trajectories -/

open Set Filter
open scoped Topology NNReal

namespace Solow1956.ODE

theorem linear_lower_bound_on {f df : ℝ → ℝ} {A T c : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hAT : A ≤ T)
    (hb : ∀ t ∈ Icc A T, c ≤ df t) : c * (T - A) ≤ f T - f A := by
  exact (convex_Icc A T).mul_sub_le_image_sub_of_le_deriv
    (HasDerivAt.continuousOn (fun t _ => hf t))
    (fun t _ => (hf t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hf t).deriv]; exact hb t (interior_subset ht))
    A ⟨le_rfl, hAT⟩ T ⟨hAT, le_rfl⟩ hAT

theorem linear_upper_bound_on {f df : ℝ → ℝ} {A T c : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hAT : A ≤ T)
    (hb : ∀ t ∈ Icc A T, df t ≤ c) : f T - f A ≤ c * (T - A) := by
  have h := linear_lower_bound_on (fun t => (hf t).neg) hAT
    (c := -c) (fun t ht => neg_le_neg (hb t ht))
  change -c * (T - A) ≤ -f T - -f A at h
  linarith

theorem linear_lower_bound {f df : ℝ → ℝ} {A T c : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hAT : A ≤ T)
    (hb : ∀ t, A ≤ t → c ≤ df t) : c * (T - A) ≤ f T - f A := by
  apply (convex_Ici A).mul_sub_le_image_sub_of_le_deriv
    (HasDerivAt.continuousOn (fun t _ => hf t))
    (fun t _ => (hf t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hf t).deriv]; exact hb t (interior_subset ht))
    A (mem_Ici.mpr le_rfl) T (mem_Ici.mpr hAT) hAT

theorem linear_upper_bound {f df : ℝ → ℝ} {A T c : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hAT : A ≤ T)
    (hb : ∀ t, A ≤ t → df t ≤ c) : f T - f A ≤ c * (T - A) := by
  have h := linear_lower_bound (fun t => (hf t).neg) hAT
    (c := -c) (fun t ht => neg_le_neg (hb t ht))
  change -c * (T - A) ≤ -f T - -f A at h
  linarith

theorem not_bounded_below_of_negative_drift {f df : ℝ → ℝ} {ε B : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hε : 0 < ε)
    (hd : ∀ t, 0 ≤ t → df t ≤ -ε)
    (hb : ∀ t, 0 ≤ t → B ≤ f t) : False := by
  let T := max 0 ((f 0 - B + 1) / ε)
  have hT : 0 ≤ T := le_max_left _ _
  have htime : f 0 - B + 1 ≤ ε * T := by
    have h := le_max_right 0 ((f 0 - B + 1) / ε)
    exact (div_le_iff₀ hε).mp h |>.trans_eq (mul_comm _ _)
  have hbound := linear_upper_bound hf hT hd
  have hbelow := hb T hT
  simp only [sub_zero] at hbound
  nlinarith

theorem not_bounded_above_of_positive_drift {f df : ℝ → ℝ} {ε B : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (hε : 0 < ε)
    (hd : ∀ t, 0 ≤ t → ε ≤ df t)
    (hb : ∀ t, 0 ≤ t → f t ≤ B) : False :=
  not_bounded_below_of_negative_drift (fun t => (hf t).neg) hε
    (fun t ht => neg_le_neg (hd t ht)) (fun t ht => neg_le_neg (hb t ht))

/-- A convergent differentiable function cannot have a nonzero limiting
derivative. The proof uses an eventual uniform drift bound and the mean value
theorem, rather than exchanging a derivative and a limit. -/
theorem derivative_limit_zero {f df : ℝ → ℝ} {l v : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t)
    (hlim : Tendsto f atTop (𝓝 l)) (hdlim : Tendsto df atTop (𝓝 v)) : v = 0 := by
  have hposImpossible : ∀ {f df : ℝ → ℝ} {l v : ℝ},
      (∀ t, HasDerivAt f (df t) t) → Tendsto f atTop (𝓝 l) →
      Tendsto df atTop (𝓝 v) → 0 < v → False := by
    intro f df l v hf hl hd hv
    obtain ⟨A, hA⟩ := eventually_atTop.mp
      ((hl.eventually (gt_mem_nhds (show l < l + 1 by linarith))).and
        (hd.eventually (lt_mem_nhds (show v / 2 < v by linarith))))
    have hs : ∀ t, HasDerivAt (fun u => f (u + A)) (df (t + A)) t := by
      intro t
      simpa only [Function.comp_def, id_eq, mul_one] using
        (hf (t + A)).comp t ((hasDerivAt_id t).add_const A)
    exact not_bounded_above_of_positive_drift hs (show 0 < v / 2 by linarith)
      (fun t ht => (hA (t + A) (by linarith)).2.le)
      (fun t ht => (hA (t + A) (by linarith)).1.le)
  rcases lt_trichotomy v 0 with hv | hv | hv
  · exact False.elim (hposImpossible (fun t => (hf t).neg) hlim.neg hdlim.neg (neg_pos.mpr hv))
  · exact hv
  · exact False.elim (hposImpossible hf hlim hdlim hv)

theorem exists_limit_of_monotone_bounded {f : ℝ → ℝ} {B : ℝ}
    (hm : MonotoneOn f (Ici 0)) (hb : ∀ t, 0 ≤ t → f t ≤ B) :
    ∃ l, Tendsto f atTop (𝓝 l) := by
  let g := fun t => f (max 0 t)
  have hmono : Monotone g := fun s t hst =>
    hm (mem_Ici.mpr (le_max_left _ _)) (mem_Ici.mpr (le_max_left _ _))
      (max_le_max_left _ hst)
  have hbound : BddAbove (range g) := ⟨B, by
    rintro _ ⟨t, rfl⟩
    exact hb _ (le_max_left _ _)⟩
  refine ⟨⨆ t, g t, (tendsto_atTop_ciSup hmono hbound).congr' ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact congrArg f (max_eq_right ht)

theorem exists_limit_of_antitone_bounded {f : ℝ → ℝ} {B : ℝ}
    (hm : AntitoneOn f (Ici 0)) (hb : ∀ t, 0 ≤ t → B ≤ f t) :
    ∃ l, Tendsto f atTop (𝓝 l) := by
  obtain ⟨l, hl⟩ := exists_limit_of_monotone_bounded
    (f := fun t => -f t) (fun _ hx _ hy hxy => neg_le_neg (hm hx hy hxy))
    (fun t ht => neg_le_neg (hb t ht))
  exact ⟨-l, by simpa only [neg_neg] using hl.neg⟩

theorem exponential_lower_bound {f df : ℝ → ℝ} {A : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t)
    (hb : ∀ t, 0 ≤ t → -A * f t ≤ df t) :
    ∀ T, 0 ≤ T → f 0 * Real.exp (-A * T) ≤ f T := by
  intro T hT
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (a := 0) (b := T) (δ := -f 0) (K := -A) (ε := 0)
    (HasDerivAt.continuousOn (fun t _ => (hf t).neg))
    (fun t _ r hr => by
      simpa only [slope_def_field, div_eq_mul_inv, mul_comm] using
        ((hf t).neg).hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl (fun t ht => by
      have hh := hb t ht.1
      change -df t ≤ -A * -f t + 0
      linarith) T ⟨hT, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at h
  change -f T ≤ -f 0 * Real.exp (-A * T) at h
  nlinarith

end Solow1956.ODE

/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/

/-! # Global positive scalar trajectories with a unique attracting equilibrium

The field is extended from a compact positive interval. Boundary inequalities
keep the constructed trajectory inside that interval, so the extension has no
effect on the economic solution. ODE uniqueness rules out finite-time arrival
at the equilibrium, and a nonzero limiting drift contradicts convergence.
-/

open Set Filter Topology
open scoped NNReal

namespace Solow1956.ODE

theorem exists_attracting_scalar_path {v : ℝ → ℝ} {ks x : ℝ}
    (hd : ∀ k, 0 < k → DifferentiableAt ℝ v k)
    (hc : ContinuousOn (deriv v) (Ioi 0))
    (hks : 0 < ks) (hvks : v ks = 0) (hx : 0 < x)
    (hbelow : ∀ k, 0 < k → k < ks → 0 < v k)
    (habove : ∀ k, ks < k → v k < 0) :
    ∃ γ : ℝ → ℝ, γ 0 = x ∧
      (∀ t, 0 ≤ t → 0 < γ t ∧ HasDerivAt γ (v (γ t)) t) ∧
      (x < ks → StrictMonoOn γ (Ici 0) ∧ ∀ t, 0 ≤ t → γ t < ks) ∧
      (ks < x → StrictAntiOn γ (Ici 0) ∧ ∀ t, 0 ≤ t → ks < γ t) ∧
      (x = ks → ∀ t, 0 ≤ t → γ t = ks) ∧
      (∀ t, 0 ≤ t → min x ks ≤ γ t ∧ γ t ≤ max x ks) ∧
      Tendsto γ atTop (𝓝 ks) := by
  let a := min x ks / 2
  let b := max x ks + 1
  have ha : 0 < a := half_pos (lt_min hx hks)
  have hax : a < x := by have := min_le_left x ks; dsimp [a]; linarith
  have haks : a < ks := by have := min_le_right x ks; dsimp [a]; linarith
  have hxb : x < b := by have := le_max_left x ks; dsimp [b]; linarith
  have hksb : ks < b := by have := le_max_right x ks; dsimp [b]; linarith
  have hab : a ≤ b := (hax.trans hxb).le
  obtain ⟨K, M, hK, hM⟩ := bounded_lipschitz_clip hab
    (fun k hk => hd k (ha.trans_le hk.1))
    (hc.mono (fun k hk => ha.trans_le hk.1))
  let w := v ∘ clip a b
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_solution hK hM x
  have hwa : w a = v a := by simp [w, clip_eq (show a ∈ Icc a b from ⟨le_rfl, hab⟩)]
  have hwb : w b = v b := by simp [w, clip_eq (show b ∈ Icc a b from ⟨hab, le_rfl⟩)]
  have hwks : w ks = 0 := by simp [w, clip_eq ⟨haks.le, hksb.le⟩, hvks]
  have hmem : ∀ t, 0 ≤ t → γ t ∈ Icc a b := by
    intro t ht
    constructor
    · have hr := image_le_of_deriv_right_lt_deriv_boundary
        (HasDerivAt.continuousOn (fun u _ => (hγ u).neg))
        (fun u _ => (hγ u).neg.hasDerivWithinAt)
        (B := fun _ => -a) (a := 0) (b := t)
        (by change -γ 0 ≤ -a; rw [hγ0]; linarith)
        (fun u => hasDerivAt_const u (-a))
        (fun u _ heq => by
          change -γ u = -a at heq
          have he : γ u = a := by linarith
          change -w (γ u) < 0
          rw [he, hwa]
          exact neg_neg_of_pos (hbelow a ha haks)) ⟨ht, le_rfl⟩
      change -γ t ≤ -a at hr
      linarith
    · exact image_le_of_deriv_right_lt_deriv_boundary
        (HasDerivAt.continuousOn (fun u _ => hγ u))
        (fun u _ => (hγ u).hasDerivWithinAt)
        (B := fun _ => b) (a := 0) (b := t)
        (by rw [hγ0]; exact hxb.le)
        (fun u => hasDerivAt_const u b)
        (fun u _ heq => by change w (γ u) < 0; rw [heq, hwb]; exact habove b hksb)
        ⟨ht, le_rfl⟩
  have hreal : ∀ t, 0 ≤ t → HasDerivAt γ (v (γ t)) t := by
    intro t ht
    simpa only [Function.comp_apply, clip_eq (hmem t ht)] using hγ t
  have hpos : ∀ t, 0 ≤ t → 0 < γ t := fun t ht => ha.trans_le (hmem t ht).1
  have heq (t : ℝ) (he : γ t = ks) : γ = fun _ => ks :=
    ODE_solution_unique_univ (v := fun _ => w) (s := fun _ => univ)
      (fun _ => hK.lipschitzOnWith)
      (fun u => ⟨hγ u, mem_univ _⟩)
      (fun u => ⟨by simpa only [hwks] using hasDerivAt_const u ks, mem_univ _⟩) he
  have hnot (hne : x ≠ ks) (t : ℝ) : γ t ≠ ks := by
    intro he
    have h := congrFun (heq t he) 0
    exact hne (hγ0.symm.trans h)
  have hlow (h : x < ks) : StrictMonoOn γ (Ici 0) ∧ ∀ t, 0 ≤ t → γ t < ks := by
    have hb : ∀ t, 0 ≤ t → γ t < ks := by
      intro t ht
      by_contra hn
      obtain ⟨u, hu, heu⟩ := intermediate_value_Icc ht
        (HasDerivAt.continuousOn (fun u _ => hγ u))
        (show ks ∈ Icc (γ 0) (γ t) from ⟨by rw [hγ0]; exact h.le, le_of_not_gt hn⟩)
      exact hnot h.ne u heu
    refine ⟨strictMonoOn_of_deriv_pos (convex_Ici 0)
      (HasDerivAt.continuousOn (fun t _ => hγ t)) ?_, hb⟩
    intro t ht
    have ht' : 0 ≤ t := interior_subset ht
    rw [(hreal t ht').deriv]
    exact hbelow _ (hpos t ht') (hb t ht')
  have hhigh (h : ks < x) : StrictAntiOn γ (Ici 0) ∧ ∀ t, 0 ≤ t → ks < γ t := by
    have hb : ∀ t, 0 ≤ t → ks < γ t := by
      intro t ht
      by_contra hn
      obtain ⟨u, hu, heu⟩ := intermediate_value_Icc' ht
        (HasDerivAt.continuousOn (fun u _ => hγ u))
        (show ks ∈ Icc (γ t) (γ 0) from ⟨le_of_not_gt hn, by rw [hγ0]; exact h.le⟩)
      exact hnot h.ne' u heu
    refine ⟨strictAntiOn_of_deriv_neg (convex_Ici 0)
      (HasDerivAt.continuousOn (fun t _ => hγ t)) ?_, hb⟩
    intro t ht
    have ht' : 0 ≤ t := interior_subset ht
    rw [(hreal t ht').deriv]
    exact habove _ (hb t ht')
  have hconstant (h : x = ks) : ∀ t, γ t = ks :=
    fun t => congrFun (heq 0 (hγ0.trans h)) t
  have htight : ∀ t, 0 ≤ t → min x ks ≤ γ t ∧ γ t ≤ max x ks := by
    intro t ht
    rcases lt_trichotomy x ks with h | h | h
    · obtain ⟨hm, hb⟩ := hlow h
      rw [min_eq_left h.le, max_eq_right h.le]
      exact ⟨by rw [← hγ0]; exact hm.monotoneOn (by simp) ht ht, (hb t ht).le⟩
    · simp [h, hconstant h t]
    · obtain ⟨hm, hb⟩ := hhigh h
      rw [min_eq_right h.le, max_eq_left h.le]
      exact ⟨(hb t ht).le, by rw [← hγ0]; exact hm.antitoneOn (by simp) ht ht⟩
  have hlimit : ∃ l, Tendsto γ atTop (𝓝 l) := by
    rcases lt_trichotomy x ks with h | h | h
    · exact exists_limit_of_monotone_bounded (hlow h).1.monotoneOn
        (fun t ht => (hlow h).2 t ht |>.le)
    · refine ⟨ks, ?_⟩
      have he : γ = fun _ => ks := funext (hconstant h)
      rw [he]
      exact tendsto_const_nhds
    · exact exists_limit_of_antitone_bounded (hhigh h).1.antitoneOn
        (fun t ht => (hhigh h).2 t ht |>.le)
  obtain ⟨l, hl⟩ := hlimit
  have hlmem : l ∈ Icc a b := isClosed_Icc.mem_of_tendsto hl
    ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht => hmem t ht))
  have hleq : v l = 0 := by
    have := derivative_limit_zero hγ hl (hK.continuous.continuousAt.tendsto.comp hl)
    simpa only [Function.comp_apply, clip_eq hlmem] using this
  have hlks : l = ks := by
    rcases lt_trichotomy l ks with h | h | h
    · exact False.elim ((ne_of_gt (hbelow l (ha.trans_le hlmem.1) h)) hleq)
    · exact h
    · exact False.elim ((ne_of_lt (habove l h)) hleq)
  exact ⟨γ, hγ0, fun t ht => ⟨hpos t ht, hreal t ht⟩, hlow, hhigh,
    fun h t _ => hconstant h t, htight, hlks ▸ hl⟩

end Solow1956.ODE

/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/

/-!
# Neoclassical production and the general Solow steady state

Source: Acemoglu, Introduction to Modern Economic Growth, Chapter 2,
Assumptions 1–2 and Proposition 2.7. The assumptions below are stated for
the intensive production function. No derivative at zero is required.
-/

open Set Filter Topology

namespace Solow1956.Neoclassical

/-- Intensive-form neoclassical assumptions. Strict concavity and a continuous
first derivative suffice; the source's negative second derivative implies them. -/
structure Technology (f : ℝ → ℝ) : Prop where
  continuous : ContinuousOn f (Ici 0)
  zero : f 0 = 0
  differentiable : ∀ k, 0 < k → DifferentiableAt ℝ f k
  derivative_continuous : ContinuousOn (deriv f) (Ioi 0)
  concave : StrictConcaveOn ℝ (Ici 0) f
  marginal_positive : ∀ k, 0 < k → 0 < deriv f k
  inada_zero : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop
  inada_top : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))

/-- The source's twice-differentiable primitive assumptions imply `Technology`.
Continuity of the first derivative is deduced from its differentiability. -/
theorem technology_of_second_derivative {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ici 0)) (h0 : f 0 = 0)
    (hd : ∀ k, 0 < k → DifferentiableAt ℝ f k)
    (hd2 : ∀ k, 0 < k → DifferentiableAt ℝ (deriv f) k)
    (hp : ∀ k, 0 < k → 0 < deriv f k)
    (hn : ∀ k, 0 < k → deriv (deriv f) k < 0)
    (hz : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop)
    (ht : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))) : Technology f := by
  refine ⟨hc, h0, hd, fun k hk => (hd2 k hk).continuousAt.continuousWithinAt,
    strictConcaveOn_of_deriv2_neg (convex_Ici 0) hc ?_, hp, hz, ht⟩
  intro k hk
  exact hn k (by simpa only [interior_Ici, mem_Ioi] using hk)

variable {f : ℝ → ℝ}

theorem Technology.marginal_strictAnti (h : Technology f) :
    StrictAntiOn (deriv f) (Ioi 0) :=
  (h.concave.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv h.differentiable

theorem Technology.output_gap (h : Technology f) {k : ℝ} (hk : 0 < k) :
    deriv f k * k < f k := by
  have hs := h.concave.deriv_lt_slope (show (0 : ℝ) ∈ Ici 0 by simp)
    hk.le hk (h.differentiable k hk)
  rw [slope_def_field, h.zero, sub_zero, sub_zero] at hs
  exact (lt_div_iff₀ hk).mp hs

theorem Technology.output_pos (h : Technology f) {k : ℝ} (hk : 0 < k) : 0 < f k :=
  (mul_pos (h.marginal_positive k hk) hk).trans (h.output_gap hk)

theorem Technology.output_nonneg (h : Technology f) {k : ℝ} (hk : 0 ≤ k) : 0 ≤ f k := by
  rcases hk.eq_or_lt with he | he
  · rw [← he, h.zero]
  · exact (h.output_pos he).le

theorem Technology.output_strictMono (h : Technology f) : StrictMonoOn f (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) h.continuous
  intro k hk
  exact h.marginal_positive k (by simpa only [interior_Ici, mem_Ioi] using hk)

/-- Average product is strictly decreasing, a conclusion of concavity. -/
theorem Technology.average_strictAnti (h : Technology f) :
    StrictAntiOn (fun k => f k / k) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun k hk => ((h.differentiable k hk).hasDerivAt.div (hasDerivAt_id k)
      (ne_of_gt hk)).continuousAt.continuousWithinAt)
  intro k hk
  have hk' : 0 < k := by simpa only [interior_Ioi, mem_Ioi] using hk
  rw [((h.differentiable k hk').hasDerivAt.div (hasDerivAt_id k) (ne_of_gt hk')).deriv]
  simp only [mul_one]
  exact div_neg_of_neg_of_pos (sub_neg.mpr (h.output_gap hk')) (sq_pos_of_pos hk')

noncomputable def rate (f : ℝ → ℝ) (s m k : ℝ) : ℝ := s * f k - m * k

theorem rate_zero (h : Technology f) (s m : ℝ) : rate f s m 0 = 0 := by
  simp [rate, h.zero]

theorem rate_hasDerivAt (h : Technology f) (s m : ℝ) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (rate f s m) (s * deriv f k - m) k := by
  change HasDerivAt (fun y => s * f y - m * y) (s * deriv f k - m) k
  convert! ((h.differentiable k hk).hasDerivAt.const_mul s).sub
    ((hasDerivAt_id k).const_mul m) using 1
  simp only [mul_one]

theorem rate_derivative_continuous (h : Technology f) (s m : ℝ) :
    ContinuousOn (deriv (rate f s m)) (Ioi 0) := by
  apply ((h.derivative_continuous.const_mul s).sub
    (continuousOn_const (c := m))).congr
  intro k hk
  exact (rate_hasDerivAt h s m hk).deriv

/-- A tangent at a sufficiently large stock gives a finite upper bracket. -/
theorem Technology.exists_capacity (h : Technology f) {r k0 : ℝ} (hr : 0 < r) :
    ∃ K, k0 ≤ K ∧ ∀ k, K ≤ k → f k ≤ r * k := by
  obtain ⟨a, ha, hma⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (h.inada_top.eventually (gt_mem_nhds (half_pos hr)))).exists
  let K := max k0 (max (a + 1) (2 * |f a| / r))
  refine ⟨K, le_max_left _ _, ?_⟩
  intro k hk
  have hak : a < k := by have := (le_max_left _ _).trans ((le_max_right _ _).trans hk); linarith
  have hratio : 2 * |f a| / r ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hmk := (div_le_iff₀ hr).mp hratio
  have hs := h.concave.concaveOn.slope_le_of_hasDerivAt ha.le (ha.le.trans hak.le)
    hak (h.differentiable a ha).hasDerivAt
  rw [slope_def_field] at hs
  have htan := (div_le_iff₀ (sub_pos.mpr hak)).mp hs
  have hpk := mul_le_mul_of_nonneg_right hma.le (ha.le.trans hak.le)
  have hpa := mul_nonneg (h.marginal_positive a ha).le ha.le
  nlinarith [le_abs_self (f a)]

/-- Acemoglu Proposition 2.7: the positive stationary capital stock exists
uniquely. The stationary zero boundary is not asserted to be unique. -/
theorem existsUnique_steadyState (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    ∃! k : ℝ, 0 < k ∧ rate f s m k = 0 := by
  have hz : ∀ᶠ k : ℝ in 𝓝[>] (0 : ℝ), 0 < k := self_mem_nhdsWithin
  obtain ⟨a, ha, hma⟩ := (hz.and
    (h.inada_zero.eventually_gt_atTop (m / s))).exists
  have hapos : 0 < rate f s m a := by
    have hg := h.output_gap ha
    have hm' := (div_lt_iff₀ hs).mp hma
    have := mul_lt_mul_of_pos_left hg hs
    dsimp [rate]
    nlinarith
  obtain ⟨b, hab, hb⟩ := h.exists_capacity (k0 := a) (div_pos hm hs)
  have hbpos := ha.trans_le hab
  have hbrate : rate f s m b ≤ 0 := by
    have := mul_le_mul_of_nonneg_left (hb b le_rfl) hs.le
    have hc : s * (m / s * b) = m * b := by field_simp
    dsimp [rate]; linarith
  have hc : ContinuousOn (rate f s m) (Icc a b) :=
    (h.continuous.mono (fun _ hx => ha.le.trans hx.1)).const_mul s |>.sub
      (continuousOn_id.const_mul m)
  obtain ⟨k, hk, heq⟩ := intermediate_value_Icc' hab hc ⟨hbrate, hapos.le⟩
  have hkpos := ha.trans_le hk.1
  refine ⟨k, ⟨hkpos, heq⟩, ?_⟩
  intro y hy
  apply h.average_strictAnti.injOn hy.1 hkpos
  have heq' : f k / k = m / s := by
    apply (div_eq_div_iff (ne_of_gt hkpos) (ne_of_gt hs)).mpr
    dsimp [rate] at heq; nlinarith
  have hy' : f y / y = m / s := by
    apply (div_eq_div_iff (ne_of_gt hy.1) (ne_of_gt hs)).mpr
    have := hy.2; dsimp [rate] at this; nlinarith
  exact hy'.trans heq'.symm

theorem rate_pos_below (h : Technology f) {s m ks k : ℝ}
    (hs : 0 < s) (hk : 0 < k) (hkk : k < ks) (hks : rate f s m ks = 0) :
    0 < rate f s m k := by
  have hp := h.average_strictAnti hk (hk.trans hkk) hkk
  have hp' := (div_lt_div_iff₀ (hk.trans hkk) hk).mp hp
  have hm := mul_lt_mul_of_pos_left hp' hs
  dsimp [rate] at *
  nlinarith

theorem rate_neg_above (h : Technology f) {s m ks k : ℝ}
    (hs : 0 < s) (hkspos : 0 < ks) (hkk : ks < k) (hks : rate f s m ks = 0) :
    rate f s m k < 0 := by
  have hp := h.average_strictAnti hkspos (hkspos.trans hkk) hkk
  have hp' := (div_lt_div_iff₀ (hkspos.trans hkk) hkspos).mp hp
  have hm := mul_lt_mul_of_pos_left hp' hs
  dsimp [rate] at *
  nlinarith

end Solow1956.Neoclassical

/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/

/-! # Acemoglu's general continuous-time Solow dynamics -/

open Set Filter Topology
open scoped NNReal

namespace Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- Nonnegative solutions from positive initial capital stay strictly positive.
The inequality follows from nonnegative gross investment and an integrating
factor; local Lipschitz continuity at zero is not assumed. -/
theorem capital_lower_bound (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k : ℝ → ℝ} (hk : ∀ t, 0 ≤ t → 0 ≤ k t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt k (rate f s m (k t)) t)
    {t : ℝ} (ht : 0 ≤ t) : k 0 * Real.exp (-m * t) ≤ k t := by
  have hg := le_gronwallBound_of_liminf_deriv_right_le
    (a := 0) (b := t) (δ := -k 0) (K := -m) (ε := 0)
    (HasDerivAt.continuousOn (fun u hu => (hd u hu.1).neg))
    (fun u hu r hr => by
      simpa only [slope_def_field, div_eq_mul_inv, mul_comm] using
        (hd u hu.1).neg.hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl (fun u hu => by
      have hgross := mul_nonneg hs (h.output_nonneg (hk u hu.1))
      change -rate f s m (k u) ≤ -m * -k u + 0
      dsimp [rate]; linarith) t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at hg
  change -k t ≤ -k 0 * Real.exp (-m * t) at hg
  nlinarith

theorem capital_positive (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k : ℝ → ℝ} (h0 : 0 < k 0) (hk : ∀ t, 0 ≤ t → 0 ≤ k t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt k (rate f s m (k t)) t)
    {t : ℝ} (ht : 0 ≤ t) : 0 < k t :=
  (mul_pos h0 (Real.exp_pos _)).trans_le (capital_lower_bound h hs hk hd ht)

/-- Uniqueness holds among all nonnegative classical future solutions. -/
theorem path_unique (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k l : ℝ → ℝ} (h0 : 0 < k 0) (heq : k 0 = l 0)
    (hk : ∀ t, 0 ≤ t → 0 ≤ k t) (hl : ∀ t, 0 ≤ t → 0 ≤ l t)
    (hkd : ∀ t, 0 ≤ t → HasDerivAt k (rate f s m (k t)) t)
    (hld : ∀ t, 0 ≤ t → HasDerivAt l (rate f s m (l t)) t) :
    EqOn k l (Ici 0) := by
  intro T hT
  change 0 ≤ T at hT
  have hkp : ∀ t, 0 ≤ t → 0 < k t := fun t ht => capital_positive h hs h0 hk hkd ht
  have hlp : ∀ t, 0 ≤ t → 0 < l t := fun t ht =>
    capital_positive h hs (heq ▸ h0) hl hld ht
  have hkc : ContinuousOn k (Icc 0 T) := HasDerivAt.continuousOn (fun t ht => hkd t ht.1)
  have hlc : ContinuousOn l (Icc 0 T) := HasDerivAt.continuousOn (fun t ht => hld t ht.1)
  obtain ⟨ta, hta, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT) (hkc.inf hlc)
  obtain ⟨tb, htb, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) (hkc.sup hlc)
  let a := min (k ta) (l ta)
  let b := max (k tb) (l tb)
  have ha : 0 < a := lt_min (hkp ta hta.1) (hlp ta hta.1)
  have hkm : ∀ t ∈ Icc 0 T, k t ∈ Icc a b := fun t ht =>
    ⟨(hmin ht).trans (min_le_left _ _), (le_max_left _ _).trans (hmax ht)⟩
  have hlm : ∀ t ∈ Icc 0 T, l t ∈ Icc a b := fun t ht =>
    ⟨(hmin ht).trans (min_le_right _ _), (le_max_right _ _).trans (hmax ht)⟩
  have hab : a ≤ b := (hkm 0 ⟨le_rfl, hT⟩).1.trans (hkm 0 ⟨le_rfl, hT⟩).2
  have hdc : ContinuousOn (deriv (rate f s m)) (Icc a b) :=
    (rate_derivative_continuous h s m).mono (fun _ hx => ha.trans_le hx.1)
  obtain ⟨z, hz, hzmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hdc.norm
  have hLip : LipschitzOnWith ‖deriv (rate f s m) z‖₊ (rate f s m) (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le
      (fun k hk => (rate_hasDerivAt h s m (ha.trans_le hk.1)).differentiableAt)
      (fun k hk => hzmax hk)
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => rate f s m) (s := fun _ => Icc a b)
    (fun _ _ => hLip) hkc (fun t ht => (hkd t ht.1).hasDerivWithinAt)
    (fun t ht => hkm t (Ico_subset_Icc_self ht))
    hlc (fun t ht => (hld t ht.1).hasDerivWithinAt)
    (fun t ht => hlm t (Ico_subset_Icc_self ht)) heq ⟨hT, le_rfl⟩

/-- Propositions 2.7 and 2.9, with constructive existence and uniqueness made
explicit. Saving is positive and effective depreciation/dilution is positive.
The usual upper bound `s < 1` is needed for positive consumption, not for this
capital dynamics theorem. -/
theorem general_solow (h : Technology f) {s m k0 : ℝ}
    (hs : 0 < s) (hm : 0 < m) (hk0 : 0 < k0) :
    ∃ ks : ℝ, 0 < ks ∧ rate f s m ks = 0 ∧
      (∀ k, 0 < k → rate f s m k = 0 → k = ks) ∧
      ∃ k : ℝ → ℝ, k 0 = k0 ∧
        (∀ t, 0 ≤ t → 0 < k t ∧ HasDerivAt k (rate f s m (k t)) t) ∧
        (k0 < ks → StrictMonoOn k (Ici 0) ∧ ∀ t, 0 ≤ t → k t < ks) ∧
        (ks < k0 → StrictAntiOn k (Ici 0) ∧ ∀ t, 0 ≤ t → ks < k t) ∧
        (k0 = ks → ∀ t, 0 ≤ t → k t = ks) ∧
        (∀ t, 0 ≤ t → min k0 ks ≤ k t ∧ k t ≤ max k0 ks) ∧
        Tendsto k atTop (𝓝 ks) ∧
        (∀ l : ℝ → ℝ, l 0 = k0 → (∀ t, 0 ≤ t → 0 ≤ l t) →
          (∀ t, 0 ≤ t → HasDerivAt l (rate f s m (l t)) t) → EqOn l k (Ici 0)) := by
  obtain ⟨ks, ⟨hks, heq⟩, hu⟩ := existsUnique_steadyState h hs hm
  obtain ⟨k, h0, hk, hlow, hhigh, hconstant, hbound, hlim⟩ :=
    ODE.exists_attracting_scalar_path
      (fun x hx => (rate_hasDerivAt h s m hx).differentiableAt)
      (rate_derivative_continuous h s m) hks heq hk0
      (fun x hx hlt => rate_pos_below h hs hx hlt heq)
      (fun x hlt => rate_neg_above h hs hks hlt heq)
  refine ⟨ks, hks, heq, fun x hx he => hu x ⟨hx, he⟩,
    k, h0, hk, hlow, hhigh, hconstant, hbound, hlim, ?_⟩
  intro l hl0 hl hld
  exact path_unique h hs.le (hl0 ▸ hk0) (hl0.trans h0.symm) hl
    (fun t ht => (hk t ht).1.le) hld (fun t ht => (hk t ht).2)

/-- Output and consumption converge along any positive path converging to the
positive steady stock; positive consumption requires `s < 1`. -/
theorem output_consumption_limit (h : Technology f) {s ks : ℝ} {k : ℝ → ℝ}
    (hks : 0 < ks) (hlim : Tendsto k atTop (𝓝 ks)) :
    Tendsto (fun t => f (k t)) atTop (𝓝 (f ks)) ∧
    Tendsto (fun t => (1 - s) * f (k t)) atTop (𝓝 ((1 - s) * f ks)) := by
  have hy := (h.differentiable ks hks).continuousAt.tendsto.comp hlim
  exact ⟨hy, hy.const_mul (1 - s)⟩

end Solow1956.Neoclassical

/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/

/-! # General Solow comparative statics, Acemoglu Proposition 2.8

The equilibrium function is constructed for every positive ratio `m/s`.
Its differentiability follows from the inverse function theorem, rather than
being assumed when differentiating the equilibrium equation.
-/

open Set Filter Topology

namespace Solow1956.Neoclassical

variable {f : ℝ → ℝ}

noncomputable def capitalAtRatio (h : Technology f) (r : ℝ) : ℝ :=
  if hr : 0 < r then Classical.choose (existsUnique_steadyState h (show (0 : ℝ) < 1 by norm_num) hr)
  else 0

theorem capitalAtRatio_spec (h : Technology f) {r : ℝ} (hr : 0 < r) :
    0 < capitalAtRatio h r ∧ f (capitalAtRatio h r) / capitalAtRatio h r = r := by
  have hspec : 0 < capitalAtRatio h r ∧ rate f 1 r (capitalAtRatio h r) = 0 := by
    simpa only [capitalAtRatio, dite_eq_left hr] using (Classical.choose_spec
      (existsUnique_steadyState h (show (0 : ℝ) < 1 by norm_num) hr)).1
  obtain ⟨hp, he⟩ := hspec
  refine ⟨hp, (div_eq_iff (ne_of_gt hp)).mpr ?_⟩
  dsimp [rate] at he
  nlinarith

theorem capitalAtRatio_average (h : Technology f) {k : ℝ} (hk : 0 < k) :
    capitalAtRatio h (f k / k) = k := by
  have hs := capitalAtRatio_spec h (div_pos (h.output_pos hk) hk)
  exact h.average_strictAnti.injOn hs.1 hk hs.2

theorem capitalAtRatio_strictAnti (h : Technology f) :
    StrictAntiOn (capitalAtRatio h) (Ioi 0) := by
  intro a ha b hb hab
  have hA := capitalAtRatio_spec h ha
  have hB := capitalAtRatio_spec h hb
  by_contra hn
  have hp := h.average_strictAnti.antitoneOn hA.1 hB.1 (le_of_not_gt hn)
  rw [hA.2, hB.2] at hp
  linarith

noncomputable def averageSlope (f : ℝ → ℝ) (k : ℝ) : ℝ :=
  (deriv f k * k - f k) / k ^ 2

theorem averageSlope_neg (h : Technology f) {k : ℝ} (hk : 0 < k) :
    averageSlope f k < 0 :=
  div_neg_of_neg_of_pos (sub_neg.mpr (h.output_gap hk)) (sq_pos_of_pos hk)

theorem average_hasStrictDerivAt (h : Technology f) {k : ℝ} (hk : 0 < k) :
    HasStrictDerivAt (fun x => f x / x) (averageSlope f k) k := by
  have hstrict : HasStrictDerivAt f (deriv f k) k :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      ((lt_mem_nhds hk).mono (fun x hx => (h.differentiable x hx).hasDerivAt))
      (h.derivative_continuous.continuousAt (Ioi_mem_nhds hk))
  simpa only [id_eq, mul_one, averageSlope] using
    hstrict.fun_div (hasStrictDerivAt_id k) (ne_of_gt hk)

theorem capitalAtRatio_hasDerivAt (h : Technology f) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (capitalAtRatio h) (averageSlope f (capitalAtRatio h r))⁻¹ r := by
  have hs := capitalAtRatio_spec h hr
  have hi := (average_hasStrictDerivAt h hs.1).to_local_left_inverse
    (ne_of_lt (averageSlope_neg h hs.1))
    ((lt_mem_nhds hs.1).mono (fun k hk => capitalAtRatio_average h hk))
  rw [hs.2] at hi
  exact hi.hasDerivAt

noncomputable def steadyCapital (h : Technology f) (s m : ℝ) : ℝ := capitalAtRatio h (m / s)

theorem steadyCapital_spec (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    0 < steadyCapital h s m ∧ rate f s m (steadyCapital h s m) = 0 := by
  obtain ⟨hp, he⟩ := capitalAtRatio_spec h (div_pos hm hs)
  refine ⟨hp, ?_⟩
  have he' := (div_eq_div_iff (ne_of_gt hp) (ne_of_gt hs)).mp he
  dsimp [rate, steadyCapital]
  nlinarith

theorem steadyCapital_eq (h : Technology f) {s m k : ℝ}
    (hs : 0 < s) (hm : 0 < m) (hk : 0 < k) (he : rate f s m k = 0) :
    steadyCapital h s m = k := by
  obtain ⟨_, _, hu⟩ := existsUnique_steadyState h hs hm
  exact (hu _ (steadyCapital_spec h hs hm)).trans (hu k ⟨hk, he⟩).symm

/-- A larger saving rate strictly raises stationary capital. -/
theorem steadyCapital_strictMono_saving (h : Technology f) {m : ℝ} (hm : 0 < m) :
    StrictMonoOn (fun s => steadyCapital h s m) (Ioi 0) := by
  intro s hs t ht hst
  exact capitalAtRatio_strictAnti h (div_pos hm ht) (div_pos hm hs)
    (div_lt_div_of_pos_left hm hs hst)

/-- Greater depreciation/population dilution strictly lowers stationary capital. -/
theorem steadyCapital_strictAnti_dilution (h : Technology f) {s : ℝ} (hs : 0 < s) :
    StrictAntiOn (steadyCapital h s) (Ioi 0) := by
  intro m hm n hn hmn
  exact capitalAtRatio_strictAnti h (div_pos hm hs) (div_pos hn hs)
    ((div_lt_div_iff_of_pos_right hs).mpr hmn)

noncomputable def savingResponse (h : Technology f) (s m : ℝ) : ℝ :=
  (averageSlope f (steadyCapital h s m))⁻¹ * (-(m / s ^ 2))

noncomputable def dilutionResponse (h : Technology f) (s m : ℝ) : ℝ :=
  (averageSlope f (steadyCapital h s m))⁻¹ * (1 / s)

theorem steadyCapital_hasDerivAt_saving (h : Technology f) {s m : ℝ}
    (hs : 0 < s) (hm : 0 < m) :
    HasDerivAt (fun z => steadyCapital h z m) (savingResponse h s m) s := by
  have hr : HasDerivAt (fun z : ℝ => m / z) (-(m / s ^ 2)) s := by
    simpa only [zero_mul, mul_one, zero_sub, neg_div, id_eq] using
      (hasDerivAt_const s m).fun_div (hasDerivAt_id s) (ne_of_gt hs)
  exact (capitalAtRatio_hasDerivAt h (div_pos hm hs)).comp s hr

theorem steadyCapital_hasDerivAt_dilution (h : Technology f) {s m : ℝ}
    (hs : 0 < s) (hm : 0 < m) :
    HasDerivAt (steadyCapital h s) (dilutionResponse h s m) m :=
  (capitalAtRatio_hasDerivAt h (div_pos hm hs)).comp m ((hasDerivAt_id m).div_const s)

theorem savingResponse_pos (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    0 < savingResponse h s m :=
  mul_pos_of_neg_of_neg (inv_lt_zero.mpr (averageSlope_neg h (steadyCapital_spec h hs hm).1))
    (neg_neg_of_pos (div_pos hm (sq_pos_of_pos hs)))

theorem dilutionResponse_neg (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    dilutionResponse h s m < 0 :=
  mul_neg_of_neg_of_pos (inv_lt_zero.mpr (averageSlope_neg h (steadyCapital_spec h hs hm).1))
    (one_div_pos.mpr hs)

/-- Actual partial derivatives, not conditional implicit-differentiation rules. -/
theorem steadyCapital_derivative_signs (h : Technology f) {s m : ℝ}
    (hs : 0 < s) (hm : 0 < m) :
    0 < deriv (fun z => steadyCapital h z m) s ∧ deriv (steadyCapital h s) m < 0 := by
  rw [(steadyCapital_hasDerivAt_saving h hs hm).deriv,
    (steadyCapital_hasDerivAt_dilution h hs hm).deriv]
  exact ⟨savingResponse_pos h hs hm, dilutionResponse_neg h hs hm⟩

theorem output_derivative_signs (h : Technology f) {s m : ℝ}
    (hs : 0 < s) (hm : 0 < m) :
    0 < deriv (fun z => f (steadyCapital h z m)) s ∧
      deriv (fun z => f (steadyCapital h s z)) m < 0 := by
  have hk := (steadyCapital_spec h hs hm).1
  have hd := (h.differentiable _ hk).hasDerivAt
  change 0 < deriv (f ∘ fun z => steadyCapital h z m) s ∧
    deriv (f ∘ steadyCapital h s) m < 0
  rw [(hd.comp s (steadyCapital_hasDerivAt_saving h hs hm)).deriv,
    (hd.comp m (steadyCapital_hasDerivAt_dilution h hs hm)).deriv]
  exact ⟨mul_pos (h.marginal_positive _ hk) (savingResponse_pos h hs hm),
    mul_neg_of_pos_of_neg (h.marginal_positive _ hk) (dilutionResponse_neg h hs hm)⟩

/-- All four capital partial-derivative signs in Acemoglu Proposition 2.8,
with `f` the baseline technology and productivity entering as `A * f`. -/
theorem acemoglu_capital_partials (h : Technology f) {A s δ n : ℝ}
    (hA : 0 < A) (hs : 0 < s) (hm : 0 < δ + n) :
    0 < deriv (fun a => steadyCapital h (s * a) (δ + n)) A ∧
    0 < deriv (fun z => steadyCapital h (z * A) (δ + n)) s ∧
    deriv (fun z => steadyCapital h (s * A) (z + n)) δ < 0 ∧
    deriv (fun z => steadyCapital h (s * A) (δ + z)) n < 0 := by
  have hsave := steadyCapital_hasDerivAt_saving h (mul_pos hs hA) hm
  have hdil := steadyCapital_hasDerivAt_dilution h (mul_pos hs hA) hm
  have hAp : HasDerivAt (fun a => steadyCapital h (s * a) (δ + n))
      (savingResponse h (s * A) (δ + n) * s) A := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      hsave.comp A ((hasDerivAt_id A).const_mul s)
  have hsp : HasDerivAt (fun z => steadyCapital h (z * A) (δ + n))
      (savingResponse h (s * A) (δ + n) * A) s := by
    simpa only [Function.comp_def, id_eq, one_mul] using
      hsave.comp s ((hasDerivAt_id s).mul_const A)
  have hδp : HasDerivAt (fun z => steadyCapital h (s * A) (z + n))
      (dilutionResponse h (s * A) (δ + n)) δ := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      hdil.comp δ ((hasDerivAt_id δ).add_const n)
  have hnp : HasDerivAt (fun z => steadyCapital h (s * A) (δ + z))
      (dilutionResponse h (s * A) (δ + n)) n := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      hdil.comp n ((hasDerivAt_id n).const_add δ)
  rw [hAp.deriv, hsp.deriv, hδp.deriv, hnp.deriv]
  exact ⟨mul_pos (savingResponse_pos h (mul_pos hs hA) hm) hs,
    mul_pos (savingResponse_pos h (mul_pos hs hA) hm) hA,
    dilutionResponse_neg h (mul_pos hs hA) hm,
    dilutionResponse_neg h (mul_pos hs hA) hm⟩

/-- The output partials include productivity's direct effect on output. -/
theorem acemoglu_output_partials (h : Technology f) {A s δ n : ℝ}
    (hA : 0 < A) (hs : 0 < s) (hm : 0 < δ + n) :
    0 < deriv (fun a => a * f (steadyCapital h (s * a) (δ + n))) A ∧
    0 < deriv (fun z => A * f (steadyCapital h (z * A) (δ + n))) s ∧
    deriv (fun z => A * f (steadyCapital h (s * A) (z + n))) δ < 0 ∧
    deriv (fun z => A * f (steadyCapital h (s * A) (δ + z))) n < 0 := by
  have hk := (steadyCapital_spec h (mul_pos hs hA) hm).1
  have hf := (h.differentiable _ hk).hasDerivAt
  have hsave := steadyCapital_hasDerivAt_saving h (mul_pos hs hA) hm
  have hdil := steadyCapital_hasDerivAt_dilution h (mul_pos hs hA) hm
  have hAp := (hasDerivAt_id A).fun_mul (hf.comp A
    (hsave.comp A ((hasDerivAt_id A).const_mul s)))
  have hsp := (hf.comp s (hsave.comp s ((hasDerivAt_id s).mul_const A))).const_mul A
  have hδp := (hf.comp δ (hdil.comp δ ((hasDerivAt_id δ).add_const n))).const_mul A
  have hnp := (hf.comp n (hdil.comp n ((hasDerivAt_id n).const_add δ))).const_mul A
  simp only [Function.comp_def, id_eq, one_mul, mul_one] at hAp hsp hδp hnp
  rw [hAp.deriv, hsp.deriv, hδp.deriv, hnp.deriv]
  have hmp := h.marginal_positive _ hk
  have hpos := savingResponse_pos h (mul_pos hs hA) hm
  have hneg := dilutionResponse_neg h (mul_pos hs hA) hm
  exact ⟨add_pos (h.output_pos hk) (mul_pos hA (mul_pos hmp (mul_pos hpos hs))),
    mul_pos hA (mul_pos hmp (mul_pos hpos hA)),
    mul_neg_of_pos_of_neg hA (mul_neg_of_pos_of_neg hmp hneg),
    mul_neg_of_pos_of_neg hA (mul_neg_of_pos_of_neg hmp hneg)⟩

end Solow1956.Neoclassical

/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/

/-! # Golden Rule saving and the stationary connection to Cass

Acemoglu Chapter 2, Proposition 2.4, with depreciation replaced by effective
dilution `m`. The supporting-line proof and the modified-Golden-Rule comparison
adapt the corresponding lemmas in our Cass formalization. Matching steady states
does not assert that the Solow and Cass transition paths are identical.
-/

open Set Filter Topology

namespace Solow1956.Neoclassical

variable {f : ℝ → ℝ}

theorem existsUnique_marginal_root (h : Technology f) {r : ℝ} (hr : 0 < r) :
    ∃! k : ℝ, 0 < k ∧ deriv f k = r := by
  have hz : ∀ᶠ k : ℝ in 𝓝[>] (0 : ℝ), 0 < k := self_mem_nhdsWithin
  obtain ⟨a, ha, hma⟩ := (hz.and (h.inada_zero.eventually_gt_atTop r)).exists
  obtain ⟨b, hab, hmb⟩ := ((eventually_gt_atTop a).and
    (h.inada_top.eventually (gt_mem_nhds hr))).exists
  obtain ⟨k, hk, he⟩ := intermediate_value_Icc' hab.le
    (h.derivative_continuous.mono (fun _ hx => ha.trans_le hx.1)) ⟨hmb.le, hma.le⟩
  have hp := ha.trans_le hk.1
  exact ⟨k, ⟨hp, he⟩, fun y hy => h.marginal_strictAnti.injOn hy.1 hp (hy.2.trans he.symm)⟩

theorem golden_rule_maximizes (h : Technology f) {kg m k : ℝ}
    (hkg : 0 < kg) (hgold : deriv f kg = m) (hk : 0 ≤ k) (hne : k ≠ kg) :
    f k - m * k < f kg - m * kg := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have ht := h.concave.deriv_lt_slope hk hkg.le hlt (h.differentiable kg hkg)
    rw [hgold, slope_def_field] at ht
    have := (lt_div_iff₀ (sub_pos.mpr hlt)).mp ht
    nlinarith
  · have ht := h.concave.slope_lt_deriv hkg.le hk hgt (h.differentiable kg hkg)
    rw [hgold, slope_def_field] at ht
    have := (div_lt_iff₀ (sub_pos.mpr hgt)).mp ht
    nlinarith

noncomputable def sustainingSaving (f : ℝ → ℝ) (m k : ℝ) : ℝ := m * k / f k

theorem sustainingSaving_bounds (h : Technology f) {m k : ℝ}
    (hm : 0 < m) (hk : 0 < k) (hmp : m ≤ deriv f k) :
    0 < sustainingSaving f m k ∧ sustainingSaving f m k < 1 := by
  have hy := h.output_pos hk
  refine ⟨div_pos (mul_pos hm hk) hy, (div_lt_one hy).mpr ?_⟩
  exact (mul_le_mul_of_nonneg_right hmp hk.le).trans_lt (h.output_gap hk)

theorem sustainingSaving_equilibrium (h : Technology f) {m k : ℝ} (hk : 0 < k) :
    rate f (sustainingSaving f m k) m k = 0 := by
  simp only [rate, sustainingSaving, div_mul_cancel₀ _ (ne_of_gt (h.output_pos hk)), sub_self]

theorem sustainingSaving_stock (h : Technology f) {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    steadyCapital h (sustainingSaving f m k) m = k :=
  steadyCapital_eq h (div_pos (mul_pos hm hk) (h.output_pos hk)) hm hk
    (sustainingSaving_equilibrium h hk)

theorem sustainingSaving_strictMono (h : Technology f) {m : ℝ} (hm : 0 < m) :
    StrictMonoOn (sustainingSaving f m) (Ioi 0) := by
  intro k hk l hl hkl
  have hg := (div_lt_div_iff₀ hl hk).mp (h.average_strictAnti hk hl hkl)
  apply (div_lt_div_iff₀ (h.output_pos hk) (h.output_pos hl)).mpr
  have := mul_lt_mul_of_pos_left hg hm
  nlinarith

theorem stationary_consumption_identity (h : Technology f) {s m : ℝ}
    (hs : 0 < s) (hm : 0 < m) :
    (1 - s) * f (steadyCapital h s m) =
      f (steadyCapital h s m) - m * steadyCapital h s m := by
  have he := (steadyCapital_spec h hs hm).2
  dsimp [rate] at he
  nlinarith

/-- The Golden Rule is a unique global optimum over all saving rates in (0,1),
not only a first-order condition or a local maximum. -/
theorem exists_unique_golden_saving (h : Technology f) {m : ℝ} (hm : 0 < m) :
    ∃ kg sg : ℝ, 0 < kg ∧ deriv f kg = m ∧
      0 < sg ∧ sg < 1 ∧ sg = sustainingSaving f m kg ∧
      steadyCapital h sg m = kg ∧
      ∀ s, 0 < s → s < 1 → s ≠ sg →
        (1 - s) * f (steadyCapital h s m) < (1 - sg) * f kg := by
  obtain ⟨kg, ⟨hkg, hg⟩, _⟩ := existsUnique_marginal_root h hm
  let sg := sustainingSaving f m kg
  obtain ⟨hsg, hsg1⟩ := sustainingSaving_bounds h hm hkg hg.ge
  have hstock := sustainingSaving_stock h hm hkg
  refine ⟨kg, sg, hkg, hg, hsg, hsg1, rfl, hstock, ?_⟩
  intro s hs _ hne
  have hne' : steadyCapital h s m ≠ kg := by
    intro he
    have hsroot := (steadyCapital_spec h hs hm).2
    have hgroot := sustainingSaving_equilibrium h (m := m) hkg
    rw [he] at hsroot
    dsimp [rate] at hsroot hgroot
    have hprod : (s - sg) * f kg = 0 := by dsimp [sg]; nlinarith
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (ne_of_gt (h.output_pos hkg))))
  rw [stationary_consumption_identity h hs hm]
  have hgoldc : (1 - sg) * f kg = f kg - m * kg := by
    simpa only [hstock] using stationary_consumption_identity h hsg hm
  rw [hgoldc]
  exact golden_rule_maximizes h hkg hg (steadyCapital_spec h hs hm).1.le hne'

/-- A Cass stationary stock satisfying `f'(kc)=d+m` is supported by a unique
constant Solow saving rate below Golden Rule saving when `d>0`. This comparison
uses the stationary equations, not an assertion about identical transition paths. -/
theorem cass_stationary_bridge (h : Technology f) {d m kc kg : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hkc : 0 < kc) (hkg : 0 < kg)
    (hc : deriv f kc = d + m) (hg : deriv f kg = m) :
    kc < kg ∧ 0 < sustainingSaving f m kc ∧
      sustainingSaving f m kc < sustainingSaving f m kg ∧
      sustainingSaving f m kg < 1 ∧
      steadyCapital h (sustainingSaving f m kc) m = kc ∧
      (1 - sustainingSaving f m kc) * f kc = f kc - m * kc := by
  have hlt : kc < kg := by
    by_contra hn
    have := h.marginal_strictAnti.antitoneOn hkg hkc (le_of_not_gt hn)
    rw [hc, hg] at this
    linarith
  refine ⟨hlt, (sustainingSaving_bounds h hm hkc (by rw [hc]; linarith)).1,
    sustainingSaving_strictMono h hm hkc hkg hlt,
    (sustainingSaving_bounds h hm hkg hg.ge).2, sustainingSaving_stock h hm hkc, ?_⟩
  have he := sustainingSaving_equilibrium h (m := m) hkc
  dsimp [rate] at he
  nlinarith

end Solow1956.Neoclassical

/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/

/-! # Stability, permanent saving changes, and effective-labour normalization -/

open Set Filter Topology

namespace Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- Global attraction for every admissible classical trajectory, not only the
constructed representative. -/
theorem every_path_converges (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k : ℝ → ℝ} (h0 : 0 < k 0) (hk : ∀ t, 0 ≤ t → 0 ≤ k t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt k (rate f s m (k t)) t) :
    Tendsto k atTop (𝓝 (steadyCapital h s m)) := by
  obtain ⟨ks, hks, he, _, l, hl0, hl, _, _, _, _, hlim, _⟩ := general_solow h hs hm h0
  have heq := path_unique h hs.le h0 hl0.symm hk (fun t ht => (hl t ht).1.le)
    hd (fun t ht => (hl t ht).2)
  rw [steadyCapital_eq h hs hm hks he]
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (heq ht).symm

/-- Quantitative Lyapunov stability: the distance from the steady stock never
exceeds its initial value. Together with attraction this gives global
asymptotic stability on the positive half-line. -/
theorem path_stable (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k : ℝ → ℝ} (h0 : 0 < k 0) (hk : ∀ t, 0 ≤ t → 0 ≤ k t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt k (rate f s m (k t)) t)
    {t : ℝ} (ht : 0 ≤ t) :
    |k t - steadyCapital h s m| ≤ |k 0 - steadyCapital h s m| := by
  obtain ⟨ks, hks, he, _, l, hl0, hl, _, _, _, hb, _, _⟩ := general_solow h hs hm h0
  have heq := path_unique h hs.le h0 hl0.symm hk (fun t ht => (hl t ht).1.le)
    hd (fun t ht => (hl t ht).2)
  rw [steadyCapital_eq h hs hm hks he, heq ht]
  obtain ⟨hlo, hhi⟩ := hb t ht
  rcases le_total (k 0) ks with h | h
  · rw [min_eq_left h] at hlo
    rw [max_eq_right h] at hhi
    rw [abs_of_nonpos (sub_nonpos.mpr hhi), abs_of_nonpos (sub_nonpos.mpr h)]
    linarith
  · rw [min_eq_right h] at hlo
    rw [max_eq_left h] at hhi
    rw [abs_of_nonneg (sub_nonneg.mpr hlo), abs_of_nonneg (sub_nonneg.mpr h)]
    linarith

/-- Section 2.8: a permanent saving increase from an old steady state produces
strict capital deepening and convergence to the higher new steady state. -/
theorem saving_increase_transition (h : Technology f) {s0 s1 m : ℝ}
    (hs0 : 0 < s0) (hs : s0 < s1) (hm : 0 < m) :
    ∃ k : ℝ → ℝ, k 0 = steadyCapital h s0 m ∧
      (∀ t, 0 ≤ t → 0 < k t ∧ HasDerivAt k (rate f s1 m (k t)) t) ∧
      StrictMonoOn k (Ici 0) ∧
      (∀ t, 0 ≤ t → k t < steadyCapital h s1 m) ∧
      Tendsto k atTop (𝓝 (steadyCapital h s1 m)) ∧
      (1 - s1) * f (k 0) < (1 - s0) * f (k 0) := by
  have hs1 := hs0.trans hs
  have h0 := (steadyCapital_spec h hs0 hm).1
  obtain ⟨ks, hks, he, _, k, hk0, hk, hlow, _, _, _, hlim, _⟩ :=
    general_solow h hs1 hm h0
  have hsks := steadyCapital_eq h hs1 hm hks he
  have hlt : steadyCapital h s0 m < ks := by
    rw [← hsks]
    exact steadyCapital_strictMono_saving h hm hs0 hs1 hs
  refine ⟨k, hk0, hk, (hlow hlt).1, ?_, ?_, ?_⟩
  · simpa only [hsks] using (hlow hlt).2
  · simpa only [hsks] using hlim
  · have hy : 0 < f (k 0) := h.output_pos (hk0 ▸ h0)
    exact mul_lt_mul_of_pos_right (by linarith) hy

/-- Proposition 2.13: effective capital converges with Harrod-neutral progress.
The quotient equation is derived from actual aggregate derivatives. -/
theorem effective_labour_convergence (h : Technology f)
    {K E Y : ℝ → ℝ} {s δ n g : ℝ} (hs : 0 < s) (hm : 0 < n + g + δ)
    (hK0 : 0 < K 0) (hK : ∀ t, 0 ≤ t → 0 ≤ K t)
    (hE : ∀ t, 0 ≤ t → 0 < E t)
    (hKd : ∀ t, 0 ≤ t → HasDerivAt K (s * Y t - δ * K t) t)
    (hEd : ∀ t, 0 ≤ t → HasDerivAt E ((n + g) * E t) t)
    (hY : ∀ t, 0 ≤ t → Y t = E t * f (K t / E t)) :
    Tendsto (fun t => K t / E t) atTop (𝓝 (steadyCapital h s (n + g + δ))) := by
  apply every_path_converges h hs hm (k := fun t => K t / E t)
    (div_pos hK0 (hE 0 le_rfl))
    (fun t ht => div_nonneg (hK t ht) (hE t ht).le)
  intro t ht
  exact SolowSwan.hasDerivAt_capitalPerEffectiveWorker (hE t ht)
    (hKd t ht) (hEd t ht) (hY t ht)

end Solow1956.Neoclassical

/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/

/-! # Concrete technologies and boundary checks for the general theorem -/

open Set Filter Topology

namespace Solow1956.Neoclassical

theorem technology_rpow {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Technology (fun k : ℝ => k ^ α) := by
  have hd (k : ℝ) (hk : 0 < k) : HasDerivAt (fun k : ℝ => k ^ α)
      (α * k ^ (α - 1)) k := Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hk))
  have hdc : ContinuousOn (fun k : ℝ => α * k ^ (α - 1)) (Ioi 0) := by
    intro k hk
    have hh := Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl (ne_of_gt hk))
    exact (hh.continuousAt.const_mul α).continuousWithinAt
  refine ⟨(Real.continuous_rpow_const hα.le).continuousOn,
    Real.zero_rpow (ne_of_gt hα), fun k hk => (hd k hk).differentiableAt,
    hdc.congr (fun k hk => (hd k hk).deriv), Real.strictConcaveOn_rpow hα hα1,
    ?_, ?_, ?_⟩
  · intro k hk
    rw [(hd k hk).deriv]
    exact mul_pos hα (Real.rpow_pos_of_pos hk _)
  · apply (Tendsto.const_mul_atTop hα (tendsto_rpow_neg_nhdsGT_zero (sub_neg.mpr hα1))).congr'
    filter_upwards [self_mem_nhdsWithin] with k hk
    exact (hd k hk).deriv.symm
  · have hl : Tendsto (fun k : ℝ => α * k ^ (α - 1)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (sub_pos.mpr hα1)).const_mul α
      simpa only [neg_sub, mul_zero] using this
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
    exact (hd k hk).deriv.symm

theorem Technology.add {f g : ℝ → ℝ} (hf : Technology f) (hg : Technology g) :
    Technology (fun k => f k + g k) := by
  have hd (k : ℝ) (hk : 0 < k) :
      HasDerivAt (fun k => f k + g k) (deriv f k + deriv g k) k :=
    (hf.differentiable k hk).hasDerivAt.add (hg.differentiable k hk).hasDerivAt
  refine ⟨hf.continuous.add hg.continuous, by rw [hf.zero, hg.zero]; ring,
    fun k hk => (hd k hk).differentiableAt,
    (hf.derivative_continuous.add hg.derivative_continuous).congr (fun k hk => (hd k hk).deriv),
    hf.concave.add hg.concave, ?_, ?_, ?_⟩
  · intro k hk
    rw [(hd k hk).deriv]
    exact add_pos (hf.marginal_positive k hk) (hg.marginal_positive k hk)
  · apply (Filter.Tendsto.atTop_add_atTop hf.inada_zero hg.inada_zero).congr'
    filter_upwards [self_mem_nhdsWithin] with k hk
    exact (hd k hk).deriv.symm
  · have hh : Tendsto (fun k => deriv f k + deriv g k) atTop (𝓝 (0 : ℝ)) := by
      simpa only [add_zero] using hf.inada_top.add hg.inada_top
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with k hk
    exact (hd k hk).deriv.symm

/-- A sum of powers is covered without solving the trajectory in closed form. -/
theorem mixed_power_technology : Technology (fun k : ℝ => k ^ (1 / 2 : ℝ) + k ^ (1 / 3 : ℝ)) :=
  (technology_rpow (by norm_num) (by norm_num)).add
    (technology_rpow (by norm_num) (by norm_num))

/-- A concrete non-Cobb–Douglas economy has a positive unique steady state. -/
theorem mixed_power_steady_exists :
    ∃! k : ℝ, 0 < k ∧ rate (fun k : ℝ => k ^ (1 / 2 : ℝ) + k ^ (1 / 3 : ℝ))
      (1 / 4) 1 k = 0 :=
  existsUnique_steadyState mixed_power_technology (by norm_num) (by norm_num)

/-- Without positive effective dilution, there is no positive stationary stock
under the maintained production and positive-saving assumptions. -/
theorem no_positive_steady_without_dilution {f : ℝ → ℝ} (h : Technology f)
    {s m k : ℝ} (hs : 0 < s) (hm : m ≤ 0) (hk : 0 < k) : 0 < rate f s m k := by
  have hsave := mul_pos hs (h.output_pos hk)
  have hdil := mul_nonpos_of_nonpos_of_nonneg hm hk.le
  dsimp [rate]
  linarith

/-- Linear technology can have more than one positive steady stock. It lacks
the strict-concavity/Inada assumptions of the general theorem. -/
theorem linear_technology_multiple_steady :
    rate (fun k : ℝ => 2 * k) (1 / 2) 1 1 = 0 ∧
    rate (fun k : ℝ => 2 * k) (1 / 2) 1 2 = 0 ∧ (1 : ℝ) ≠ 2 := by
  norm_num [rate]

end Solow1956.Neoclassical

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# Absolute convergence among identical Solow economies, and its speed

Two economies share the saving rate `s`, the effective dilution `m`, and the
intensive technology `f`, and differ only in their initial capital. We prove:

* `path_eq_of_meet`, `paths_ordered`: two paths that meet at some date coincide
  at every earlier date (backward uniqueness), so paths never cross; the
  poorer economy stays poorer.
* `poorer_grows_faster`: at every date the poorer economy's capital grows at a
  strictly higher proportional rate (the `β`-convergence sign).
* `log_gap_strictAnti`, `absolute_convergence`: the proportional gap
  `log l - log k` is strictly decreasing, and the level gap, log gap and ratio all
  converge (to `0`, `0`, `1`).
* `log_gap_le_of_speed_bound`, `exists_uniform_rate`, `absolute_convergence_rate`,
  `level_gap_le`: a global
  exponential rate. If `λ` bounds the local speed
  `σ(k) = s (f(k)/k - f'(k))` from below on the range of the two paths, the log
  gap is at most its initial value times `exp(-λ t)`. Such a `λ > 0` exists.
* `sharp_convergence_rate`: the exact asymptotic rate is
  `β* = σ(k*) = m - s f'(k*) = m (1 - capital share at k*)`; for every
  `ε`, the log gap lies between two exponentials with rates `β* ± ε`.
  `log_gap_rate_tendsto` states it as `log (gap t) / t → -β*`.
* `cobbDouglas_speed`: with `f(k) = k^α`, `β* = (1 - α) m`.

Since the constant path at `k*` is itself an admissible path, every result also
gives the rate of convergence of a single economy to its steady state
(`log_gap_steady_le`).

The level gap `l - k` need not be monotone, because `s f(k) - m k` is increasing
at low capital; the monotone quantity is the proportional (log) gap.
-/

open Set Filter Topology

namespace Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- An admissible classical future path of `k' = s f(k) - m k` from positive capital. -/
structure IsPath (f : ℝ → ℝ) (s m : ℝ) (k : ℝ → ℝ) : Prop where
  initial_pos : 0 < k 0
  nonneg : ∀ t, 0 ≤ t → 0 ≤ k t
  hasDerivAt : ∀ t, 0 ≤ t → HasDerivAt k (rate f s m (k t)) t

/-- Proportional growth rate `k'/k = s f(k)/k - m` of capital at the stock `k`. -/
noncomputable def growthRate (f : ℝ → ℝ) (s m k : ℝ) : ℝ := s * (f k / k) - m

/-- Local speed of convergence `σ(k) = s (f(k)/k - f'(k))`: minus the slope of the
growth rate with respect to `log k`. -/
noncomputable def convergenceSpeed (f : ℝ → ℝ) (s k : ℝ) : ℝ := s * (f k / k - deriv f k)

theorem rate_div_eq_growthRate (s m : ℝ) {k : ℝ} (hk : 0 < k) :
    rate f s m k / k = growthRate f s m k := by
  unfold rate growthRate
  field_simp

theorem growthRate_strictAnti (h : Technology f) {s : ℝ} (hs : 0 < s) (m : ℝ) :
    StrictAntiOn (growthRate f s m) (Ioi 0) := by
  intro a ha b hb hab
  have := mul_lt_mul_of_pos_left (h.average_strictAnti ha hb hab) hs
  unfold growthRate
  linarith

theorem convergenceSpeed_pos (h : Technology f) {s k : ℝ} (hs : 0 < s) (hk : 0 < k) :
    0 < convergenceSpeed f s k := by
  have hg := h.output_gap hk
  have : deriv f k < f k / k := (lt_div_iff₀ hk).mpr hg
  exact mul_pos hs (sub_pos.mpr this)

theorem convergenceSpeed_continuousOn (h : Technology f) (s : ℝ) :
    ContinuousOn (convergenceSpeed f s) (Ioi 0) := by
  have hf : ContinuousOn f (Ioi 0) := fun k hk =>
    (h.differentiable k hk).continuousAt.continuousWithinAt
  exact continuousOn_const.mul
    ((hf.div continuousOn_id (fun k hk => ne_of_gt hk)).sub h.derivative_continuous)

/-- The asymptotic speed is `m - s f'(k*)`. -/
theorem convergenceSpeed_steady (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    convergenceSpeed f s (steadyCapital h s m) = m - s * deriv f (steadyCapital h s m) := by
  obtain ⟨hk, he⟩ := steadyCapital_spec h hs hm
  set ks := steadyCapital h s m
  have hfk : s * (f ks / ks) = m := by
    unfold rate at he
    field_simp
    linarith
  unfold convergenceSpeed
  rw [mul_sub, hfk]

/-- The asymptotic speed is dilution times the labour share at the steady state. -/
theorem convergenceSpeed_steady_share (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    convergenceSpeed f s (steadyCapital h s m) =
      m * (1 - deriv f (steadyCapital h s m) * steadyCapital h s m /
        f (steadyCapital h s m)) := by
  obtain ⟨hk, he⟩ := steadyCapital_spec h hs hm
  set ks := steadyCapital h s m
  have hy := h.output_pos hk
  have hfk : s * f ks = m * ks := by unfold rate at he; linarith
  unfold convergenceSpeed
  field_simp
  linear_combination (f ks - deriv f ks * ks) * hfk

theorem IsPath.pos (h : Technology f) {s m : ℝ} (hs : 0 ≤ s) {k : ℝ → ℝ}
    (hk : IsPath f s m k) {t : ℝ} (ht : 0 ≤ t) : 0 < k t :=
  capital_positive h hs hk.initial_pos hk.nonneg hk.hasDerivAt ht

/-- The constant path at the steady state is admissible. -/
theorem isPath_steady (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    IsPath f s m (fun _ => steadyCapital h s m) := by
  obtain ⟨hk, he⟩ := steadyCapital_spec h hs hm
  exact ⟨hk, fun _ _ => hk.le, fun t _ => by rw [he]; exact hasDerivAt_const t _⟩

/-- Every admissible path stays between its initial stock and the steady state. -/
theorem IsPath.bounds (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k : ℝ → ℝ} (hk : IsPath f s m k) {t : ℝ} (ht : 0 ≤ t) :
    min (k 0) (steadyCapital h s m) ≤ k t ∧ k t ≤ max (k 0) (steadyCapital h s m) := by
  obtain ⟨ks, hks, he, _, l, hl0, hl, _, _, _, hb, _, _⟩ :=
    general_solow h hs hm hk.initial_pos
  have heq := path_unique h hs.le hk.initial_pos hl0.symm hk.nonneg
    (fun t ht => (hl t ht).1.le) hk.hasDerivAt (fun t ht => (hl t ht).2)
  rw [steadyCapital_eq h hs hm hks he, heq ht]
  exact hb t ht

theorem IsPath.tendsto (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k : ℝ → ℝ} (hk : IsPath f s m k) :
    Tendsto k atTop (𝓝 (steadyCapital h s m)) :=
  every_path_converges h hs hm hk.initial_pos hk.nonneg hk.hasDerivAt

/-- Backward uniqueness: two paths that meet at a date agree at every earlier date. -/
theorem path_eq_of_meet (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l)
    {T : ℝ} (hT : 0 ≤ T) (hmeet : k T = l T) : EqOn k l (Icc 0 T) := by
  have hkp : ∀ t, 0 ≤ t → 0 < k t := fun t ht => hk.pos h hs ht
  have hlp : ∀ t, 0 ≤ t → 0 < l t := fun t ht => hl.pos h hs ht
  have hkc : ContinuousOn k (Icc 0 T) :=
    HasDerivAt.continuousOn (fun t ht => hk.hasDerivAt t ht.1)
  have hlc : ContinuousOn l (Icc 0 T) :=
    HasDerivAt.continuousOn (fun t ht => hl.hasDerivAt t ht.1)
  obtain ⟨ta, hta, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT) (hkc.inf hlc)
  obtain ⟨tb, htb, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) (hkc.sup hlc)
  let a := min (k ta) (l ta)
  let b := max (k tb) (l tb)
  have ha : 0 < a := lt_min (hkp ta hta.1) (hlp ta hta.1)
  have hkm : ∀ t ∈ Icc 0 T, k t ∈ Icc a b := fun t ht =>
    ⟨(hmin ht).trans (min_le_left _ _), (le_max_left _ _).trans (hmax ht)⟩
  have hlm : ∀ t ∈ Icc 0 T, l t ∈ Icc a b := fun t ht =>
    ⟨(hmin ht).trans (min_le_right _ _), (le_max_right _ _).trans (hmax ht)⟩
  have hab : a ≤ b := (hkm 0 ⟨le_rfl, hT⟩).1.trans (hkm 0 ⟨le_rfl, hT⟩).2
  have hdc : ContinuousOn (deriv (rate f s m)) (Icc a b) :=
    (rate_derivative_continuous h s m).mono (fun _ hx => ha.trans_le hx.1)
  obtain ⟨z, hz, hzmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hdc.norm
  have hLip : LipschitzOnWith ‖deriv (rate f s m) z‖₊ (rate f s m) (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le
      (fun k hk => (rate_hasDerivAt h s m (ha.trans_le hk.1)).differentiableAt)
      (fun k hk => hzmax hk)
  exact ODE_solution_unique_of_mem_Icc_left
    (v := fun _ => rate f s m) (s := fun _ => Icc a b)
    (fun _ _ => hLip) hkc (fun t ht => (hk.hasDerivAt t ht.1.le).hasDerivWithinAt)
    (fun t ht => hkm t (Ioc_subset_Icc_self ht))
    hlc (fun t ht => (hl.hasDerivAt t ht.1.le).hasDerivWithinAt)
    (fun t ht => hlm t (Ioc_subset_Icc_self ht)) hmeet

/-- Paths of identical economies never cross: the initially poorer economy is
strictly poorer at every future date. -/
theorem paths_ordered (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {t : ℝ} (ht : 0 ≤ t) : k t < l t := by
  by_contra hle
  push Not at hle
  have hc : ContinuousOn (fun u => l u - k u) (Icc 0 t) :=
    (HasDerivAt.continuousOn (fun u hu => hl.hasDerivAt u hu.1)).sub
      (HasDerivAt.continuousOn (fun u hu => hk.hasDerivAt u hu.1))
  obtain ⟨τ, hτ, hτeq⟩ := intermediate_value_Icc' ht hc
    ⟨sub_nonpos.mpr hle, (sub_pos.mpr h0).le⟩
  have hmeet : k τ = l τ := by simp only at hτeq; linarith
  have := path_eq_of_meet h hs hk hl hτ.1 hmeet ⟨le_rfl, hτ.1⟩
  exact (ne_of_lt h0) this

/-- `β`-convergence sign: the poorer economy grows strictly faster at every date. -/
theorem poorer_grows_faster (h : Technology f) {s m : ℝ} (hs : 0 < s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {t : ℝ} (ht : 0 ≤ t) : growthRate f s m (l t) < growthRate f s m (k t) :=
  growthRate_strictAnti h hs m (hk.pos h hs.le ht) (hl.pos h hs.le ht)
    (paths_ordered h hs.le hk hl h0 ht)

theorem hasDerivAt_log_gap (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u => Real.log (l u) - Real.log (k u))
      (growthRate f s m (l t) - growthRate f s m (k t)) t := by
  have hkt := hk.pos h hs ht
  have hlt := hl.pos h hs ht
  have := ((hl.hasDerivAt t ht).log (ne_of_gt hlt)).sub
    ((hk.hasDerivAt t ht).log (ne_of_gt hkt))
  rwa [rate_div_eq_growthRate s m hlt, rate_div_eq_growthRate s m hkt] at this

/-- The proportional gap between the two economies shrinks strictly. -/
theorem log_gap_strictAnti (h : Technology f) {s m : ℝ} (hs : 0 < s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0) :
    StrictAntiOn (fun u => Real.log (l u) - Real.log (k u)) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    (HasDerivAt.continuousOn (fun u hu => hasDerivAt_log_gap h hs.le hk hl hu))
  intro t ht
  have ht' : 0 ≤ t := (by simpa only [interior_Ici, mem_Ioi] using ht : 0 < t).le
  rw [(hasDerivAt_log_gap h hs.le hk hl ht').deriv]
  exact sub_neg.mpr (poorer_grows_faster h hs hk hl h0 ht')

/-- Absolute convergence: identical economies converge to each other in levels,
in logs, and in ratio, whatever their initial capital. -/
theorem absolute_convergence (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) :
    Tendsto (fun t => l t - k t) atTop (𝓝 0) ∧
      Tendsto (fun t => Real.log (l t) - Real.log (k t)) atTop (𝓝 0) ∧
      Tendsto (fun t => l t / k t) atTop (𝓝 1) := by
  have hks := (steadyCapital_spec h hs hm).1
  have hkl := hk.tendsto h hs hm
  have hll := hl.tendsto h hs hm
  refine ⟨by simpa only [sub_self] using hll.sub hkl, ?_, ?_⟩
  · have hlog := (Real.continuousAt_log (ne_of_gt hks)).tendsto
    have := (hlog.comp hll).sub (hlog.comp hkl)
    rw [sub_self] at this
    exact this
  · have := hll.div hkl (ne_of_gt hks)
    rw [div_self (ne_of_gt hks)] at this
    exact this

/-- A lower bound `λ` on the local speed turns into a lower bound on how fast the
growth-rate gap closes, measured against the log gap. -/
theorem growthRate_gap_ge {s m a b lam : ℝ} (h : Technology f) (ha : 0 < a)
    (hlam : ∀ z ∈ Icc a b, lam ≤ convergenceSpeed f s z)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    lam * (Real.log y - Real.log x) ≤ growthRate f s m x - growthRate f s m y := by
  have hd : ∀ z, 0 < z → HasDerivAt (fun z => growthRate f s m z + lam * Real.log z)
      ((lam - convergenceSpeed f s z) / z) z := by
    intro z hz
    have h1 : HasDerivAt (fun z => s * (f z / z) - m)
        (s * ((deriv f z * z - f z * 1) / z ^ 2)) z :=
      (((h.differentiable z hz).hasDerivAt.div (hasDerivAt_id' z)
        (ne_of_gt hz)).const_mul s).sub_const m
    have h2 := (Real.hasDerivAt_log (ne_of_gt hz)).const_mul lam
    exact (h1.add h2).congr_deriv (by unfold convergenceSpeed; field_simp; ring)
  have hanti : AntitoneOn (fun z => growthRate f s m z + lam * Real.log z) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (HasDerivAt.continuousOn (fun z hz => hd z (ha.trans_le hz.1)))
      (fun z hz => (hd z (ha.trans_le
        (interior_subset hz : z ∈ Icc a b).1)).differentiableAt.differentiableWithinAt)
    intro z hz
    have hz' : z ∈ Icc a b := interior_subset hz
    rw [(hd z (ha.trans_le hz'.1)).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hlam z hz'))
      (ha.trans_le hz'.1).le
  have := hanti hx hy hxy
  simp only at this
  linarith

/-- An upper bound `μ` on the local speed bounds how fast the growth-rate gap closes. -/
theorem growthRate_gap_le {s m a b mu : ℝ} (h : Technology f) (ha : 0 < a)
    (hmu : ∀ z ∈ Icc a b, convergenceSpeed f s z ≤ mu)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    growthRate f s m x - growthRate f s m y ≤ mu * (Real.log y - Real.log x) := by
  have hd : ∀ z, 0 < z → HasDerivAt (fun z => growthRate f s m z + mu * Real.log z)
      ((mu - convergenceSpeed f s z) / z) z := by
    intro z hz
    have h1 : HasDerivAt (fun z => s * (f z / z) - m)
        (s * ((deriv f z * z - f z * 1) / z ^ 2)) z :=
      (((h.differentiable z hz).hasDerivAt.div (hasDerivAt_id' z)
        (ne_of_gt hz)).const_mul s).sub_const m
    have h2 := (Real.hasDerivAt_log (ne_of_gt hz)).const_mul mu
    exact (h1.add h2).congr_deriv (by unfold convergenceSpeed; field_simp; ring)
  have hmono : MonotoneOn (fun z => growthRate f s m z + mu * Real.log z) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (HasDerivAt.continuousOn (fun z hz => hd z (ha.trans_le hz.1)))
      (fun z hz => (hd z (ha.trans_le
        (interior_subset hz : z ∈ Icc a b).1)).differentiableAt.differentiableWithinAt)
    intro z hz
    have hz' : z ∈ Icc a b := interior_subset hz
    rw [(hd z (ha.trans_le hz'.1)).deriv]
    exact div_nonneg (sub_nonneg.mpr (hmu z hz')) (ha.trans_le hz'.1).le
  have := hmono hx hy hxy
  simp only at this
  linarith

/-- Gronwall bound from above: from any date `T` after which both ordered paths stay
in `[a, b]`, a lower bound `λ` for the local speed on `[a, b]` makes the log gap
decay at least at rate `λ`. -/
theorem log_gap_upper (h : Technology f) {s m : ℝ} (hs : 0 < s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {a b lam T : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    (hkw : ∀ t, T ≤ t → k t ∈ Icc a b) (hlw : ∀ t, T ≤ t → l t ∈ Icc a b)
    (hlam : ∀ z ∈ Icc a b, lam ≤ convergenceSpeed f s z) {t : ℝ} (ht : T ≤ t) :
    Real.log (l t) - Real.log (k t) ≤
      (Real.log (l T) - Real.log (k T)) * Real.exp (-lam * (t - T)) := by
  set D : ℝ → ℝ := fun u => Real.log (l u) - Real.log (k u) with hD
  have hint : ∀ u, u ∈ interior (Ici T) → T ≤ u := fun u hu =>
    (by simpa only [interior_Ici, mem_Ioi] using hu : T < u).le
  have hex : ∀ u, HasDerivAt (fun u => Real.exp (lam * (u - T)))
      (Real.exp (lam * (u - T)) * lam) u := by
    intro u
    have := ((hasDerivAt_id u).sub_const T).const_mul lam
    simpa only [id, mul_one] using this.exp
  have hE : ∀ u, T ≤ u → HasDerivAt (fun u => D u * Real.exp (lam * (u - T)))
      ((growthRate f s m (l u) - growthRate f s m (k u)) * Real.exp (lam * (u - T)) +
        D u * (Real.exp (lam * (u - T)) * lam)) u :=
    fun u hu => (hasDerivAt_log_gap h hs.le hk hl (hT.trans hu)).mul (hex u)
  have hanti : AntitoneOn (fun u => D u * Real.exp (lam * (u - T))) (Ici T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici T)
      (HasDerivAt.continuousOn (fun u hu => hE u hu))
      (fun u hu => (hE u (hint u hu)).differentiableAt.differentiableWithinAt)
    intro u hu
    have hu' := hint u hu
    rw [(hE u hu').deriv]
    have hg := growthRate_gap_ge (m := m) h ha hlam (hkw u hu') (hlw u hu')
      (paths_ordered h hs.le hk hl h0 (hT.trans hu')).le
    have hpos := Real.exp_pos (lam * (u - T))
    have : (growthRate f s m (l u) - growthRate f s m (k u)) + D u * lam ≤ 0 := by
      simp only [hD]; linarith
    nlinarith
  have := hanti (mem_Ici.mpr le_rfl) (show t ∈ Ici T from ht) ht
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at this
  have he : Real.exp (lam * (t - T)) * Real.exp (-lam * (t - T)) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc D t = D t * Real.exp (lam * (t - T)) * Real.exp (-lam * (t - T)) := by
        rw [mul_assoc, he, mul_one]
    _ ≤ D T * Real.exp (-lam * (t - T)) :=
        mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

/-- Gronwall bound from below: an upper bound `μ` for the local speed on `[a, b]`
means the log gap decays no faster than rate `μ`. -/
theorem log_gap_lower (h : Technology f) {s m : ℝ} (hs : 0 < s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {a b mu T : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    (hkw : ∀ t, T ≤ t → k t ∈ Icc a b) (hlw : ∀ t, T ≤ t → l t ∈ Icc a b)
    (hmu : ∀ z ∈ Icc a b, convergenceSpeed f s z ≤ mu) {t : ℝ} (ht : T ≤ t) :
    (Real.log (l T) - Real.log (k T)) * Real.exp (-mu * (t - T)) ≤
      Real.log (l t) - Real.log (k t) := by
  set D : ℝ → ℝ := fun u => Real.log (l u) - Real.log (k u) with hD
  have hint : ∀ u, u ∈ interior (Ici T) → T ≤ u := fun u hu =>
    (by simpa only [interior_Ici, mem_Ioi] using hu : T < u).le
  have hex : ∀ u, HasDerivAt (fun u => Real.exp (mu * (u - T)))
      (Real.exp (mu * (u - T)) * mu) u := by
    intro u
    have := ((hasDerivAt_id u).sub_const T).const_mul mu
    simpa only [id, mul_one] using this.exp
  have hE : ∀ u, T ≤ u → HasDerivAt (fun u => D u * Real.exp (mu * (u - T)))
      ((growthRate f s m (l u) - growthRate f s m (k u)) * Real.exp (mu * (u - T)) +
        D u * (Real.exp (mu * (u - T)) * mu)) u :=
    fun u hu => (hasDerivAt_log_gap h hs.le hk hl (hT.trans hu)).mul (hex u)
  have hmono : MonotoneOn (fun u => D u * Real.exp (mu * (u - T))) (Ici T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici T)
      (HasDerivAt.continuousOn (fun u hu => hE u hu))
      (fun u hu => (hE u (hint u hu)).differentiableAt.differentiableWithinAt)
    intro u hu
    have hu' := hint u hu
    rw [(hE u hu').deriv]
    have hg := growthRate_gap_le (m := m) h ha hmu (hkw u hu') (hlw u hu')
      (paths_ordered h hs.le hk hl h0 (hT.trans hu')).le
    have hpos := Real.exp_pos (mu * (u - T))
    have : 0 ≤ (growthRate f s m (l u) - growthRate f s m (k u)) + D u * mu := by
      simp only [hD]; linarith
    nlinarith
  have := hmono (mem_Ici.mpr le_rfl) (show t ∈ Ici T from ht) ht
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at this
  have he : Real.exp (-mu * (t - T)) * Real.exp (mu * (t - T)) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc D T * Real.exp (-mu * (t - T))
      ≤ D t * Real.exp (mu * (t - T)) * Real.exp (-mu * (t - T)) :=
        mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    _ = D t := by rw [mul_assoc, mul_comm (Real.exp _), he, mul_one]

/-- Both ordered paths lie, at every date, between the lower initial stock (or the
steady state) and the higher initial stock (or the steady state). -/
theorem paths_window (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {t : ℝ} (ht : 0 ≤ t) :
    k t ∈ Icc (min (k 0) (steadyCapital h s m)) (max (l 0) (steadyCapital h s m)) ∧
      l t ∈ Icc (min (k 0) (steadyCapital h s m)) (max (l 0) (steadyCapital h s m)) := by
  obtain ⟨hk1, hk2⟩ := hk.bounds h hs hm ht
  obtain ⟨hl1, hl2⟩ := hl.bounds h hs hm ht
  have h1 : min (k 0) (steadyCapital h s m) ≤ min (l 0) (steadyCapital h s m) :=
    min_le_min_right _ h0.le
  have h2 : max (k 0) (steadyCapital h s m) ≤ max (l 0) (steadyCapital h s m) :=
    max_le_max_right _ h0.le
  exact ⟨⟨hk1, hk2.trans h2⟩, ⟨h1.trans hl1, hl2⟩⟩

/-- Global exponential convergence at an explicit rate: any lower bound `λ` for the
local speed over the range of the two paths is a rate for the log gap. -/
theorem log_gap_le_of_speed_bound (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0) {lam : ℝ}
    (hlam : ∀ z ∈ Icc (min (k 0) (steadyCapital h s m)) (max (l 0) (steadyCapital h s m)),
      lam ≤ convergenceSpeed f s z)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.log (l t) - Real.log (k t) ≤
      (Real.log (l 0) - Real.log (k 0)) * Real.exp (-lam * t) := by
  have ha : 0 < min (k 0) (steadyCapital h s m) :=
    lt_min hk.initial_pos (steadyCapital_spec h hs hm).1
  simpa only [sub_zero] using log_gap_upper h hs hk hl h0 ha le_rfl
    (fun u hu => (paths_window h hs hm hk hl h0 hu).1)
    (fun u hu => (paths_window h hs hm hk hl h0 hu).2) hlam ht

/-- The log gap of ordered paths is strictly positive. -/
theorem log_gap_pos (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {t : ℝ} (ht : 0 ≤ t) : 0 < Real.log (l t) - Real.log (k t) :=
  sub_pos.mpr (Real.log_lt_log (hk.pos h hs ht) (paths_ordered h hs hk hl h0 ht))

/-- A uniform exponential rate exists: some `λ > 0` bounds the local speed over the
whole range of the two paths. -/
theorem exists_uniform_rate (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0) :
    ∃ lam, 0 < lam ∧ ∀ t, 0 ≤ t →
      Real.log (l t) - Real.log (k t) ≤
        (Real.log (l 0) - Real.log (k 0)) * Real.exp (-lam * t) := by
  set a := min (k 0) (steadyCapital h s m)
  set b := max (l 0) (steadyCapital h s m)
  have ha : 0 < a := lt_min hk.initial_pos (steadyCapital_spec h hs hm).1
  have hab : a ≤ b := (min_le_right _ _).trans (le_max_right _ _)
  obtain ⟨z, hz, hzmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
    ((convergenceSpeed_continuousOn h s).mono (fun _ hx => ha.trans_le hx.1))
  exact ⟨convergenceSpeed f s z, convergenceSpeed_pos h hs (ha.trans_le hz.1),
    fun t ht => log_gap_le_of_speed_bound h hs hm hk hl h0 (fun y hy => hzmin hy) ht⟩

/-- Absolute convergence at an exponential rate for any two identical economies,
stated symmetrically in absolute value. -/
theorem absolute_convergence_rate (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) :
    ∃ lam, 0 < lam ∧ ∀ t, 0 ≤ t →
      |Real.log (l t) - Real.log (k t)| ≤
        |Real.log (l 0) - Real.log (k 0)| * Real.exp (-lam * t) := by
  rcases lt_trichotomy (k 0) (l 0) with h0 | h0 | h0
  · obtain ⟨lam, hlam, hb⟩ := exists_uniform_rate h hs hm hk hl h0
    refine ⟨lam, hlam, fun t ht => ?_⟩
    rw [abs_of_pos (log_gap_pos h hs.le hk hl h0 ht),
      abs_of_pos (log_gap_pos h hs.le hk hl h0 le_rfl)]
    exact hb t ht
  · refine ⟨1, one_pos, fun t ht => ?_⟩
    have he := path_unique h hs.le hk.initial_pos h0 hk.nonneg hl.nonneg
      hk.hasDerivAt hl.hasDerivAt (mem_Ici.mpr ht)
    rw [he, h0, sub_self, sub_self, abs_zero, zero_mul]
  · obtain ⟨lam, hlam, hb⟩ := exists_uniform_rate h hs hm hl hk h0
    refine ⟨lam, hlam, fun t ht => ?_⟩
    rw [abs_sub_comm, abs_sub_comm (Real.log (l 0)),
      abs_of_pos (log_gap_pos h hs.le hl hk h0 ht),
      abs_of_pos (log_gap_pos h hs.le hl hk h0 le_rfl)]
    exact hb t ht

/-- A single economy converges to its steady state at an exponential rate: the
constant steady-state path is an admissible comparison economy. -/
theorem log_gap_steady_le (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k : ℝ → ℝ} (hk : IsPath f s m k) :
    ∃ lam, 0 < lam ∧ ∀ t, 0 ≤ t →
      |Real.log (k t) - Real.log (steadyCapital h s m)| ≤
        |Real.log (k 0) - Real.log (steadyCapital h s m)| * Real.exp (-lam * t) := by
  obtain ⟨lam, hlam, hb⟩ :=
    absolute_convergence_rate h hs hm (isPath_steady h hs hm) hk
  exact ⟨lam, hlam, hb⟩

/-- The level gap is bounded by the richer stock times the log gap, so it also
closes exponentially: `l t - k t ≤ max (l 0) k* · log (l 0 / k 0) · exp (-λ t)`. -/
theorem level_gap_le (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0) :
    ∃ lam, 0 < lam ∧ ∀ t, 0 ≤ t →
      0 < l t - k t ∧
      l t - k t ≤ max (l 0) (steadyCapital h s m) *
        (Real.log (l 0) - Real.log (k 0)) * Real.exp (-lam * t) := by
  obtain ⟨lam, hlam, hb⟩ := exists_uniform_rate h hs hm hk hl h0
  refine ⟨lam, hlam, fun t ht => ⟨sub_pos.mpr (paths_ordered h hs.le hk hl h0 ht), ?_⟩⟩
  have hkt := hk.pos h hs.le ht
  have hlt := hl.pos h hs.le ht
  have hlog : l t - k t ≤ l t * (Real.log (l t) - Real.log (k t)) := by
    have he := Real.add_one_le_exp (Real.log (k t) - Real.log (l t))
    rw [Real.exp_sub, Real.exp_log hkt, Real.exp_log hlt, le_div_iff₀ hlt] at he
    nlinarith
  have hD := log_gap_pos h hs.le hk hl h0 ht
  have hup := (paths_window h hs hm hk hl h0 ht).2.2
  calc l t - k t ≤ l t * (Real.log (l t) - Real.log (k t)) := hlog
    _ ≤ max (l 0) (steadyCapital h s m) * (Real.log (l t) - Real.log (k t)) :=
        mul_le_mul_of_nonneg_right hup hD.le
    _ ≤ max (l 0) (steadyCapital h s m) *
          ((Real.log (l 0) - Real.log (k 0)) * Real.exp (-lam * t)) :=
        mul_le_mul_of_nonneg_left (hb t ht) (hlt.le.trans hup)
    _ = _ := by ring

/-- Sharp rate. Let `β* = σ(k*) = m - s f'(k*)`. For every `0 < ε < β*` the log gap
between two identical economies is squeezed between exponentials with rates
`β* + ε` and `β* - ε`. -/
theorem sharp_convergence_rate (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {ε : ℝ} (hε : 0 < ε) (hεβ : ε < convergenceSpeed f s (steadyCapital h s m)) :
    ∃ c, 0 < c ∧ ∃ C, 0 < C ∧ ∀ t, 0 ≤ t →
      c * Real.exp (-(convergenceSpeed f s (steadyCapital h s m) + ε) * t) ≤
          Real.log (l t) - Real.log (k t) ∧
        Real.log (l t) - Real.log (k t) ≤
          C * Real.exp (-(convergenceSpeed f s (steadyCapital h s m) - ε) * t) := by
  set ks := steadyCapital h s m with hks_def
  set β := convergenceSpeed f s ks
  set D : ℝ → ℝ := fun u => Real.log (l u) - Real.log (k u) with hD
  have hks := (steadyCapital_spec h hs hm).1
  -- a window around `k*` on which the local speed is within `ε` of `β`
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.mp
    ((convergenceSpeed_continuousOn h s).continuousAt (Ioi_mem_nhds hks)) ε hε
  set r := min (δ / 2) (ks / 2)
  have hr : 0 < r := lt_min (half_pos hδ) (half_pos hks)
  have ha : 0 < ks - r := by have := min_le_right (δ / 2) (ks / 2); linarith
  have hwin : ∀ z ∈ Icc (ks - r) (ks + r), |convergenceSpeed f s z - β| < ε := by
    intro z hz
    have : dist z ks < δ := by
      rw [Real.dist_eq, abs_lt]
      have := min_le_left (δ / 2) (ks / 2)
      constructor <;> linarith [hz.1, hz.2]
    have := hδb this
    rwa [Real.dist_eq] at this
  have hlam : ∀ z ∈ Icc (ks - r) (ks + r), β - ε ≤ convergenceSpeed f s z :=
    fun z hz => by linarith [(abs_lt.mp (hwin z hz)).1]
  have hmu : ∀ z ∈ Icc (ks - r) (ks + r), convergenceSpeed f s z ≤ β + ε :=
    fun z hz => by linarith [(abs_lt.mp (hwin z hz)).2]
  have hnhds : Icc (ks - r) (ks + r) ∈ 𝓝 ks := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp
    (((hk.tendsto h hs hm).eventually hnhds).and ((hl.tendsto h hs hm).eventually hnhds))
  set T := max T0 0
  have hT : 0 ≤ T := le_max_right _ _
  have hkw : ∀ t, T ≤ t → k t ∈ Icc (ks - r) (ks + r) :=
    fun t ht => (hT0 t ((le_max_left _ _).trans ht)).1
  have hlw : ∀ t, T ≤ t → l t ∈ Icc (ks - r) (ks + r) :=
    fun t ht => (hT0 t ((le_max_left _ _).trans ht)).2
  have hanti := log_gap_strictAnti h hs hk hl h0
  have hDpos : ∀ t, 0 ≤ t → 0 < D t := fun t ht => log_gap_pos h hs.le hk hl h0 ht
  have hlamp : 0 < β - ε := sub_pos.mpr hεβ
  have hmup : 0 < β + ε := by linarith
  refine ⟨D T, hDpos T hT, D 0 * Real.exp ((β - ε) * T),
    mul_pos (hDpos 0 le_rfl) (Real.exp_pos _), fun t ht => ⟨?_, ?_⟩⟩
  · rcases le_total T t with hTt | htT
    · have hlow := log_gap_lower h hs hk hl h0 ha hT hkw hlw hmu hTt
      have : Real.exp (-(β + ε) * t) ≤ Real.exp (-(β + ε) * (t - T)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      calc D T * Real.exp (-(β + ε) * t) ≤ D T * Real.exp (-(β + ε) * (t - T)) :=
            mul_le_mul_of_nonneg_left this (hDpos T hT).le
        _ ≤ D t := by simpa only [neg_mul] using hlow
    · have hmono : D T ≤ D t := hanti.antitoneOn (mem_Ici.mpr ht) (mem_Ici.mpr hT) htT
      have : Real.exp (-(β + ε) * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      calc D T * Real.exp (-(β + ε) * t) ≤ D T * 1 :=
            mul_le_mul_of_nonneg_left this (hDpos T hT).le
        _ ≤ D t := by rw [mul_one]; exact hmono
  · have hsplit : Real.exp ((β - ε) * T) * Real.exp (-(β - ε) * t) =
        Real.exp (-(β - ε) * (t - T)) := by rw [← Real.exp_add]; ring_nf
    rcases le_total T t with hTt | htT
    · have hup := log_gap_upper h hs hk hl h0 ha hT hkw hlw hlam hTt
      have hmono : D T ≤ D 0 := hanti.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hT) hT
      calc D t ≤ D T * Real.exp (-(β - ε) * (t - T)) := hup
        _ ≤ D 0 * Real.exp (-(β - ε) * (t - T)) :=
            mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le
        _ = D 0 * Real.exp ((β - ε) * T) * Real.exp (-(β - ε) * t) := by
            rw [mul_assoc, hsplit]
    · have hmono : D t ≤ D 0 := hanti.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
      have : 1 ≤ Real.exp (-(β - ε) * (t - T)) := Real.one_le_exp (by nlinarith)
      calc D t ≤ D 0 * 1 := by rw [mul_one]; exact hmono
        _ ≤ D 0 * Real.exp (-(β - ε) * (t - T)) :=
            mul_le_mul_of_nonneg_left this (hDpos 0 le_rfl).le
        _ = D 0 * Real.exp ((β - ε) * T) * Real.exp (-(β - ε) * t) := by
            rw [mul_assoc, hsplit]

/-- The exact asymptotic rate of convergence: `log (log-gap) / t → -β*`, where
`β* = σ(k*) = m - s f'(k*)`. -/
theorem log_gap_rate_tendsto (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0) :
    Tendsto (fun t => Real.log (Real.log (l t) - Real.log (k t)) / t) atTop
      (𝓝 (-convergenceSpeed f s (steadyCapital h s m))) := by
  set β := convergenceSpeed f s (steadyCapital h s m)
  have hβ : 0 < β := convergenceSpeed_pos h hs (steadyCapital_spec h hs hm).1
  rw [Metric.tendsto_nhds]
  intro e he
  set ε := min (e / 4) (β / 2)
  have hε : 0 < ε := lt_min (by linarith) (half_pos hβ)
  have hεβ : ε < β := (min_le_right _ _).trans_lt (half_lt_self hβ)
  have hεe : ε ≤ e / 4 := min_le_left _ _
  obtain ⟨c, hc, C, hC, hb⟩ := sharp_convergence_rate h hs hm hk hl h0 hε hεβ
  have hz : ∀ a : ℝ, Tendsto (fun t : ℝ => a / t) atTop (𝓝 0) :=
    fun a => tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (hz (Real.log c)).eventually (Metric.ball_mem_nhds 0 (by linarith : 0 < e / 2)),
    (hz (Real.log C)).eventually (Metric.ball_mem_nhds 0 (by linarith : 0 < e / 2))]
    with t ht hct hCt
  rw [Real.dist_eq, sub_zero] at hct hCt
  obtain ⟨hlo, hhi⟩ := hb t ht.le
  have hlo' := Real.log_le_log (mul_pos hc (Real.exp_pos _)) hlo
  have hhi' := Real.log_le_log ((mul_pos hc (Real.exp_pos _)).trans_le hlo) hhi
  rw [Real.log_mul (ne_of_gt hc) (Real.exp_pos _).ne', Real.log_exp] at hlo'
  rw [Real.log_mul (ne_of_gt hC) (Real.exp_pos _).ne', Real.log_exp] at hhi'
  have h1 : Real.log c / t - (β + ε) ≤
      Real.log (Real.log (l t) - Real.log (k t)) / t := by
    rw [div_sub' (ne_of_gt ht), div_le_div_iff_of_pos_right ht]; linarith
  have h2 : Real.log (Real.log (l t) - Real.log (k t)) / t ≤
      Real.log C / t - (β - ε) := by
    rw [div_sub' (ne_of_gt ht), div_le_div_iff_of_pos_right ht]; linarith
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [(abs_lt.mp hct).1]
  · linarith [(abs_lt.mp hCt).2]

/-- Cobb–Douglas: with `f(k) = k^α` the asymptotic rate is `β* = (1 - α) m`. -/
theorem cobbDouglas_speed {α s m : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s) (hm : 0 < m) :
    convergenceSpeed (fun k : ℝ => k ^ α) s
      (steadyCapital (technology_rpow hα hα1) s m) = (1 - α) * m := by
  have ht := technology_rpow hα hα1
  obtain ⟨hk, he⟩ := steadyCapital_spec ht hs hm
  set ks := steadyCapital ht s m
  have hd : deriv (fun k : ℝ => k ^ α) ks = α * (ks ^ α / ks) := by
    rw [(Real.hasDerivAt_rpow_const (p := α) (Or.inl (ne_of_gt hk))).deriv,
      Real.rpow_sub_one (ne_of_gt hk)]
  unfold convergenceSpeed
  rw [hd]
  unfold rate at he
  field_simp
  linear_combination (1 - α) * he

end Solow1956.Neoclassical

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

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

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# The discrete-time Solow map and its steady state

Source: Acemoglu, *Introduction to Modern Economic Growth*, Chapter 2,
equation (2.17) and Proposition 2.2. With saving `s`, depreciation `δ` and gross
growth `γ = (1 + n)(1 + g)` of effective labour, capital per effective worker
obeys

`k(t+1) = (s f(k(t)) + (1 - δ) k(t)) / γ`.

Acemoglu's equation (2.17) is the case `γ = 1`. The map moves capital by
`rate f s m k / γ` with `m = γ - 1 + δ`, so its positive fixed point is the
continuous-time steady state `steadyCapital h s m`: stationary results are shared
by the two models, only the dynamics differ. The restriction `δ ≤ 1` makes the
map increasing, which the global dynamics require.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime

open Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- Discrete-time parameters: positive saving, depreciation at most one, positive
gross growth of effective labour, and positive effective dilution `γ - 1 + δ`. -/
structure Params (s δ γ : ℝ) : Prop where
  saving_pos : 0 < s
  depreciation_le_one : δ ≤ 1
  growth_pos : 0 < γ
  dilution_pos : 0 < γ - 1 + δ

/-- The discrete-time law of motion for capital per effective worker. -/
noncomputable def next (f : ℝ → ℝ) (s δ γ k : ℝ) : ℝ := (s * f k + (1 - δ) * k) / γ

/-- The positive steady state of the map: the continuous steady state with
effective dilution `m = γ - 1 + δ`. -/
noncomputable def steady (h : Technology f) (s δ γ : ℝ) : ℝ := steadyCapital h s (γ - 1 + δ)

/-- The one-period change in capital is the continuous accumulation rate divided by `γ`. -/
theorem next_sub_self {s δ γ : ℝ} (hγ : 0 < γ) (k : ℝ) :
    next f s δ γ k - k = rate f s (γ - 1 + δ) k / γ := by
  unfold next rate
  field_simp
  ring

/-- Acemoglu's case `γ = 1`: `k(t+1) = s f(k(t)) + (1 - δ) k(t)`. -/
theorem next_acemoglu (s δ k : ℝ) : next f s δ 1 k = s * f k + (1 - δ) * k := by
  simp [next]

theorem next_zero (h : Technology f) (s δ γ : ℝ) : next f s δ γ 0 = 0 := by
  simp [next, h.zero]

theorem next_pos (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ) (hk : 0 < k) :
    0 < next f s δ γ k := by
  have h1 := mul_pos P.saving_pos (h.output_pos hk)
  have h2 := mul_nonneg (sub_nonneg.mpr P.depreciation_le_one) hk.le
  exact div_pos (by linarith) P.growth_pos

theorem next_nonneg (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ) (hk : 0 ≤ k) :
    0 ≤ next f s δ γ k := by
  rcases hk.eq_or_lt with he | he
  · rw [← he, next_zero h]
  · exact (next_pos h P he).le

/-- Acemoglu's proof of Proposition 2.5 starts from `g' > 0`: the map is increasing. -/
theorem next_strictMono (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    StrictMonoOn (next f s δ γ) (Ici 0) := by
  intro a ha b hb hab
  have h1 := mul_lt_mul_of_pos_left (h.output_strictMono ha hb hab) P.saving_pos
  have h2 := mul_le_mul_of_nonneg_left hab.le (sub_nonneg.mpr P.depreciation_le_one)
  exact div_lt_div_of_pos_right (by linarith) P.growth_pos

theorem next_continuousOn (h : Technology f) (s δ γ : ℝ) :
    ContinuousOn (next f s δ γ) (Ici 0) :=
  (((h.continuous.const_mul s).add (continuousOn_id.const_mul (1 - δ)))).div_const γ

theorem next_hasDerivAt (h : Technology f) (s δ γ : ℝ) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (next f s δ γ) ((s * deriv f k + (1 - δ)) / γ) k := by
  have h1 : HasDerivAt (fun y => s * f y + (1 - δ) * y) (s * deriv f k + (1 - δ) * 1) k :=
    ((h.differentiable k hk).hasDerivAt.const_mul s).add ((hasDerivAt_id' k).const_mul (1 - δ))
  rw [mul_one] at h1
  exact h1.div_const γ

/-- Positive fixed points of the map are exactly the positive roots of the continuous rate. -/
theorem next_eq_self_iff {s δ γ k : ℝ} (hγ : 0 < γ) :
    next f s δ γ k = k ↔ rate f s (γ - 1 + δ) k = 0 := by
  rw [← sub_eq_zero, next_sub_self hγ, div_eq_zero_iff]
  exact ⟨fun h => h.resolve_right (ne_of_gt hγ), fun h => Or.inl h⟩

/-- Acemoglu Proposition 2.2: a unique positive steady state exists. -/
theorem existsUnique_steadyState (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    ∃! k : ℝ, 0 < k ∧ next f s δ γ k = k := by
  simpa only [next_eq_self_iff P.growth_pos] using
    Neoclassical.existsUnique_steadyState h P.saving_pos P.dilution_pos

theorem steady_spec (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    0 < steady h s δ γ ∧ next f s δ γ (steady h s δ γ) = steady h s δ γ := by
  obtain ⟨hk, he⟩ := steadyCapital_spec h P.saving_pos P.dilution_pos
  exact ⟨hk, (next_eq_self_iff P.growth_pos).mpr he⟩

theorem steady_eq (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ) (hk : 0 < k)
    (he : next f s δ γ k = k) : steady h s δ γ = k :=
  steadyCapital_eq h P.saving_pos P.dilution_pos hk ((next_eq_self_iff P.growth_pos).mp he)

/-- Zero is also a fixed point; Proposition 2.2 ignores it by convention. -/
theorem zero_fixed (h : Technology f) (s δ γ : ℝ) : next f s δ γ 0 = 0 := next_zero h s δ γ

/-- Proposition 2.2 in full: the steady state, its output `y* = f(k*)`, and its
consumption `c* = (1 - s) f(k*) = f(k*) - m k*`. -/
theorem steady_state_equilibrium (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    0 < steady h s δ γ ∧ next f s δ γ (steady h s δ γ) = steady h s δ γ ∧
      s * f (steady h s δ γ) = (γ - 1 + δ) * steady h s δ γ ∧
      (1 - s) * f (steady h s δ γ) = f (steady h s δ γ) - (γ - 1 + δ) * steady h s δ γ := by
  obtain ⟨hk, he⟩ := steady_spec h P
  have hr := (next_eq_self_iff P.growth_pos).mp he
  unfold rate at hr
  exact ⟨hk, he, by linarith, by linarith⟩

theorem next_gt_self (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ)
    (hk : 0 < k) (hlt : k < steady h s δ γ) : k < next f s δ γ k := by
  have hr := rate_pos_below h P.saving_pos hk hlt
    ((next_eq_self_iff P.growth_pos).mp (steady_spec h P).2)
  have := next_sub_self (f := f) (s := s) (δ := δ) P.growth_pos k
  have := div_pos hr P.growth_pos
  linarith

theorem next_lt_self (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ)
    (hgt : steady h s δ γ < k) : next f s δ γ k < k := by
  have hr := rate_neg_above h P.saving_pos (steady_spec h P).1 hgt
    ((next_eq_self_iff P.growth_pos).mp (steady_spec h P).2)
  have := next_sub_self (f := f) (s := s) (δ := δ) P.growth_pos k
  have := div_neg_of_neg_of_pos hr P.growth_pos
  linarith

/-- Local stability, Proposition 2.5: the slope of the map at `k*` lies in `(0, 1)`. -/
theorem slope_at_steady (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    0 < (s * deriv f (steady h s δ γ) + (1 - δ)) / γ ∧
      (s * deriv f (steady h s δ γ) + (1 - δ)) / γ < 1 := by
  obtain ⟨hk, _, hss, _⟩ := steady_state_equilibrium h P
  set ks := steady h s δ γ
  have hmp := mul_pos P.saving_pos (h.marginal_positive ks hk)
  have hgap := mul_lt_mul_of_pos_left (h.output_gap hk) P.saving_pos
  refine ⟨div_pos (by linarith [P.depreciation_le_one]) P.growth_pos,
    (div_lt_one P.growth_pos).mpr ?_⟩
  have : s * deriv f ks < γ - 1 + δ := by
    have h' : s * (deriv f ks * ks) < (γ - 1 + δ) * ks := by linarith
    nlinarith
  linarith

end Solow1956.DiscreteTime

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-! # Global dynamics of the discrete-time Solow model, Acemoglu Proposition 2.5

In discrete time a path is generated by iterating the map, so existence and
uniqueness are immediate. The substance is global monotone convergence.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime

open Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- An admissible discrete-time path from positive initial capital. -/
structure IsPath (f : ℝ → ℝ) (s δ γ : ℝ) (k : ℕ → ℝ) : Prop where
  initial_pos : 0 < k 0
  succ : ∀ t, k (t + 1) = next f s δ γ (k t)

/-- The path obtained by iterating the map from `k₀`. -/
noncomputable def path (f : ℝ → ℝ) (s δ γ k₀ : ℝ) (t : ℕ) : ℝ := (next f s δ γ)^[t] k₀

theorem path_zero (s δ γ k₀ : ℝ) : path f s δ γ k₀ 0 = k₀ := rfl

theorem path_succ (s δ γ k₀ : ℝ) (t : ℕ) :
    path f s δ γ k₀ (t + 1) = next f s δ γ (path f s δ γ k₀ t) :=
  Function.iterate_succ_apply' _ _ _

theorem isPath_path {s δ γ k₀ : ℝ} (hk₀ : 0 < k₀) : IsPath f s δ γ (path f s δ γ k₀) :=
  ⟨hk₀, path_succ s δ γ k₀⟩

/-- Uniqueness: a path is determined by its initial stock. -/
theorem path_unique {s δ γ : ℝ} {k l : ℕ → ℝ}
    (hk : ∀ t, k (t + 1) = next f s δ γ (k t)) (hl : ∀ t, l (t + 1) = next f s δ γ (l t))
    (h0 : k 0 = l 0) : k = l := by
  funext t
  induction t with
  | zero => exact h0
  | succ t ih => rw [hk, hl, ih]

theorem IsPath.eq_path {s δ γ : ℝ} {k : ℕ → ℝ} (hk : IsPath f s δ γ k) :
    k = path f s δ γ (k 0) :=
  path_unique hk.succ (path_succ s δ γ (k 0)) rfl

/-- A nonnegative initial stock stays nonnegative; zero stays at zero. -/
theorem path_nonneg (h : Technology f) {s δ γ k₀ : ℝ} (P : Params s δ γ) (hk₀ : 0 ≤ k₀)
    (t : ℕ) : 0 ≤ path f s δ γ k₀ t := by
  induction t with
  | zero => exact hk₀
  | succ t ih => rw [path_succ]; exact next_nonneg h P ih

theorem path_of_zero (h : Technology f) (s δ γ : ℝ) (t : ℕ) : path f s δ γ 0 t = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => rw [path_succ, ih, next_zero h]

/-- Acemoglu Proposition 2.5, with existence and uniqueness explicit: from any
positive stock the path is positive, strictly monotone toward `k*`, stays on its
side of `k*`, and converges to it. -/
theorem general_solow (h : Technology f) {s δ γ k₀ : ℝ} (P : Params s δ γ) (hk₀ : 0 < k₀) :
    ∃ ks : ℝ, 0 < ks ∧ next f s δ γ ks = ks ∧
      (∀ k, 0 < k → next f s δ γ k = k → k = ks) ∧
      ∃ k : ℕ → ℝ, k 0 = k₀ ∧ (∀ t, 0 < k t ∧ k (t + 1) = next f s δ γ (k t)) ∧
        (k₀ < ks → StrictMono k ∧ ∀ t, k t < ks) ∧
        (ks < k₀ → StrictAnti k ∧ ∀ t, ks < k t) ∧
        (k₀ = ks → ∀ t, k t = ks) ∧
        (∀ t, min k₀ ks ≤ k t ∧ k t ≤ max k₀ ks) ∧
        Tendsto k atTop (𝓝 ks) ∧
        (∀ l : ℕ → ℝ, l 0 = k₀ → (∀ t, l (t + 1) = next f s δ γ (l t)) → l = k) := by
  obtain ⟨hks, hfix⟩ := steady_spec h P
  obtain ⟨hpos, hlow, hhigh, hconst, hbd, hlim⟩ := Map.attracting_orbit
    (x := path f s δ γ k₀)
    ((next_strictMono h P).mono Ioi_subset_Ici_self)
    ((next_continuousOn h s δ γ).mono Ioi_subset_Ici_self) hks hfix
    (fun _ hy hlt => next_gt_self h P hy hlt) (fun _ hgt => next_lt_self h P hgt)
    hk₀ (path_succ s δ γ k₀)
  refine ⟨steady h s δ γ, hks, hfix, fun k hk he => (steady_eq h P hk he).symm,
    path f s δ γ k₀, rfl, fun t => ⟨hpos t, path_succ s δ γ k₀ t⟩,
    hlow, hhigh, hconst, hbd, hlim, fun l hl0 hl => ?_⟩
  exact path_unique hl (path_succ s δ γ k₀) hl0

/-- Every admissible path has the full Proposition 2.5 behaviour relative to `k*`. -/
theorem IsPath.orbit (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) {k : ℕ → ℝ}
    (hk : IsPath f s δ γ k) :
    (∀ t, 0 < k t) ∧
      (k 0 < steady h s δ γ → StrictMono k ∧ ∀ t, k t < steady h s δ γ) ∧
      (steady h s δ γ < k 0 → StrictAnti k ∧ ∀ t, steady h s δ γ < k t) ∧
      (k 0 = steady h s δ γ → ∀ t, k t = steady h s δ γ) ∧
      (∀ t, min (k 0) (steady h s δ γ) ≤ k t ∧ k t ≤ max (k 0) (steady h s δ γ)) ∧
      Tendsto k atTop (𝓝 (steady h s δ γ)) :=
  Map.attracting_orbit ((next_strictMono h P).mono Ioi_subset_Ici_self)
    ((next_continuousOn h s δ γ).mono Ioi_subset_Ici_self) (steady_spec h P).1
    (steady_spec h P).2 (fun _ hy hlt => next_gt_self h P hy hlt)
    (fun _ hgt => next_lt_self h P hgt) hk.initial_pos hk.succ

theorem IsPath.pos (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) {k : ℕ → ℝ}
    (hk : IsPath f s δ γ k) (t : ℕ) : 0 < k t :=
  (hk.orbit h P).1 t

theorem IsPath.tendsto (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) {k : ℕ → ℝ}
    (hk : IsPath f s δ γ k) : Tendsto k atTop (𝓝 (steady h s δ γ)) :=
  (hk.orbit h P).2.2.2.2.2

theorem IsPath.bounds (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) {k : ℕ → ℝ}
    (hk : IsPath f s δ γ k) (t : ℕ) :
    min (k 0) (steady h s δ γ) ≤ k t ∧ k t ≤ max (k 0) (steady h s δ γ) :=
  (hk.orbit h P).2.2.2.2.1 t

/-- Output and consumption converge along any path; positive consumption needs `s < 1`. -/
theorem output_consumption_limit (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k : ℕ → ℝ} (hk : IsPath f s δ γ k) :
    Tendsto (fun t => f (k t)) atTop (𝓝 (f (steady h s δ γ))) ∧
      Tendsto (fun t => (1 - s) * f (k t)) atTop (𝓝 ((1 - s) * f (steady h s δ γ))) := by
  have hy := (h.differentiable _ (steady_spec h P).1).continuousAt.tendsto.comp (hk.tendsto h P)
  exact ⟨hy, hy.const_mul (1 - s)⟩

end Solow1956.DiscreteTime

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-! # Discrete-time comparative statics, Acemoglu Proposition 2.3

The discrete steady state is the continuous steady state at effective dilution
`γ - 1 + δ`, so its derivatives follow from the inverse-function construction in
`Solow1956.Growth.SolowComparative`. With `γ = 1 + n` the dilution is exactly
`δ + n`, and Acemoglu's discrete Proposition 2.3 is recovered, together with the
population-growth partial.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime

open Solow1956.Neoclassical

variable {f : ℝ → ℝ}

theorem steady_strictMono_saving (h : Technology f) {δ γ : ℝ} (hm : 0 < γ - 1 + δ) :
    StrictMonoOn (fun s => steady h s δ γ) (Ioi 0) :=
  steadyCapital_strictMono_saving h hm

theorem steady_strictAnti_depreciation (h : Technology f) {s γ δ₁ δ₂ : ℝ} (hs : 0 < s)
    (hm : 0 < γ - 1 + δ₁) (hδ : δ₁ < δ₂) : steady h s δ₂ γ < steady h s δ₁ γ :=
  steadyCapital_strictAnti_dilution h hs hm (by simp only [mem_Ioi]; linarith) (by linarith)

theorem steady_strictAnti_growth (h : Technology f) {s δ γ₁ γ₂ : ℝ} (hs : 0 < s)
    (hm : 0 < γ₁ - 1 + δ) (hγ : γ₁ < γ₂) : steady h s δ γ₂ < steady h s δ γ₁ :=
  steadyCapital_strictAnti_dilution h hs hm (by simp only [mem_Ioi]; linarith) (by linarith)

/-- Actual partial derivatives of the discrete steady state in saving, depreciation
and effective-labour growth. -/
theorem steady_derivative_signs (h : Technology f) {s δ γ : ℝ} (hs : 0 < s)
    (hm : 0 < γ - 1 + δ) :
    0 < deriv (fun z => steady h z δ γ) s ∧
      deriv (fun z => steady h s z γ) δ < 0 ∧
      deriv (fun z => steady h s δ z) γ < 0 := by
  have hsave := steadyCapital_hasDerivAt_saving h hs hm
  have hdil := steadyCapital_hasDerivAt_dilution h hs hm
  have hδ : HasDerivAt (fun z => steady h s z γ) (dilutionResponse h s (γ - 1 + δ) * 1) δ :=
    hdil.comp δ ((hasDerivAt_id δ).const_add (γ - 1))
  have hγ : HasDerivAt (fun z => steady h s δ z) (dilutionResponse h s (γ - 1 + δ) * 1) γ :=
    hdil.comp γ (((hasDerivAt_id γ).sub_const 1).add_const δ)
  rw [mul_one] at hδ hγ
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun z => steady h z δ γ) = fun z => steadyCapital h z (γ - 1 + δ) from rfl,
      hsave.deriv]
    exact savingResponse_pos h hs hm
  · rw [hδ.deriv]; exact dilutionResponse_neg h hs hm
  · rw [hγ.deriv]; exact dilutionResponse_neg h hs hm

theorem steady_rewrite (h : Technology f) (s δ n : ℝ) :
    steady h s δ (1 + n) = steadyCapital h s (δ + n) := by
  unfold steady
  congr 1
  ring

/-- Acemoglu Proposition 2.3 in discrete time, with `f = A f̃` and `γ = 1 + n`:
capital rises with productivity and saving and falls with depreciation and
population growth. -/
theorem acemoglu_capital_partials (h : Technology f) {A s δ n : ℝ}
    (hA : 0 < A) (hs : 0 < s) (hm : 0 < δ + n) :
    0 < deriv (fun a => steady h (s * a) δ (1 + n)) A ∧
    0 < deriv (fun z => steady h (z * A) δ (1 + n)) s ∧
    deriv (fun z => steady h (s * A) z (1 + n)) δ < 0 ∧
    deriv (fun z => steady h (s * A) δ (1 + z)) n < 0 := by
  simp only [steady_rewrite]
  exact Neoclassical.acemoglu_capital_partials h hA hs hm

/-- The output partials of Proposition 2.3, including productivity's direct effect. -/
theorem acemoglu_output_partials (h : Technology f) {A s δ n : ℝ}
    (hA : 0 < A) (hs : 0 < s) (hm : 0 < δ + n) :
    0 < deriv (fun a => a * f (steady h (s * a) δ (1 + n))) A ∧
    0 < deriv (fun z => A * f (steady h (z * A) δ (1 + n))) s ∧
    deriv (fun z => A * f (steady h (s * A) z (1 + n))) δ < 0 ∧
    deriv (fun z => A * f (steady h (s * A) δ (1 + z))) n < 0 := by
  simp only [steady_rewrite]
  exact Neoclassical.acemoglu_output_partials h hA hs hm

end Solow1956.DiscreteTime

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-! # Discrete-time Golden Rule, Acemoglu Proposition 2.4, and the Cass comparison

Acemoglu states Proposition 2.4 in the discrete-time model with `γ = 1`, where the
Golden Rule stock solves `f'(k) = δ`. With effective-labour growth the condition is
`f'(k) = γ - 1 + δ`. The discrete Cass modified Golden Rule is
`β (1 + f'(k) - δ) = γ`; for `0 < β < 1` it lies strictly below the Golden Rule.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime

open Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- Stationary consumption is output less the investment that keeps `k*` constant. -/
theorem stationary_consumption (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    (1 - s) * f (steady h s δ γ) = f (steady h s δ γ) - (γ - 1 + δ) * steady h s δ γ :=
  (steady_state_equilibrium h P).2.2.2

/-- Acemoglu Proposition 2.4 in discrete time: a unique saving rate in `(0, 1)`
maximises steady-state consumption, and its stock satisfies `f'(k) = γ - 1 + δ`
(`f'(k) = δ` in Acemoglu's case `γ = 1`). -/
theorem exists_unique_golden_saving (h : Technology f) {δ γ : ℝ}
    (hm : 0 < γ - 1 + δ) :
    ∃ kg sg : ℝ, 0 < kg ∧ deriv f kg = γ - 1 + δ ∧ 0 < sg ∧ sg < 1 ∧
      steady h sg δ γ = kg ∧
      ∀ s, 0 < s → s < 1 → s ≠ sg →
        (1 - s) * f (steady h s δ γ) < (1 - sg) * f kg := by
  obtain ⟨kg, sg, hkg, hg, hsg, hsg1, _, hstock, hmax⟩ :=
    Neoclassical.exists_unique_golden_saving h hm
  exact ⟨kg, sg, hkg, hg, hsg, hsg1, hstock, hmax⟩

/-- Acemoglu's own statement, `γ = 1`: the Golden Rule stock solves `f'(k) = δ`. -/
theorem acemoglu_golden_rule (h : Technology f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ kg sg : ℝ, 0 < kg ∧ deriv f kg = δ ∧ 0 < sg ∧ sg < 1 ∧
      steady h sg δ 1 = kg ∧
      ∀ s, 0 < s → s < 1 → s ≠ sg →
        (1 - s) * f (steady h s δ 1) < (1 - sg) * f kg := by
  have hm : (0 : ℝ) < 1 - 1 + δ := by linarith
  obtain ⟨kg, sg, hkg, hg, hsg, hsg1, hstock, hmax⟩ := exists_unique_golden_saving h hm
  exact ⟨kg, sg, hkg, by rw [hg]; ring, hsg, hsg1, hstock, hmax⟩

/-- Discrete Cass comparison. A stationary optimal-growth stock with discount factor
`0 < β < 1`, `β (1 + f'(kc) - δ) = γ`, lies strictly below the Golden Rule stock
and is sustained by a unique constant Solow saving rate below Golden Rule saving.
This compares stationary equations only, not transition paths. -/
theorem cass_stationary_bridge (h : Technology f) {β δ γ kc kg : ℝ}
    (hβ : 0 < β) (hβ1 : β < 1) (hγ : 0 < γ) (hm : 0 < γ - 1 + δ)
    (hkc : 0 < kc) (hkg : 0 < kg)
    (hc : β * (1 + deriv f kc - δ) = γ) (hg : deriv f kg = γ - 1 + δ) :
    kc < kg ∧ 0 < sustainingSaving f (γ - 1 + δ) kc ∧
      sustainingSaving f (γ - 1 + δ) kc < sustainingSaving f (γ - 1 + δ) kg ∧
      sustainingSaving f (γ - 1 + δ) kg < 1 ∧
      steady h (sustainingSaving f (γ - 1 + δ) kc) δ γ = kc ∧
      (1 - sustainingSaving f (γ - 1 + δ) kc) * f kc = f kc - (γ - 1 + δ) * kc := by
  have hd : 0 < γ * (1 / β - 1) :=
    mul_pos hγ (sub_pos.mpr ((one_lt_div hβ).mpr hβ1))
  have hc' : deriv f kc = γ * (1 / β - 1) + (γ - 1 + δ) := by
    field_simp
    linarith
  exact Neoclassical.cass_stationary_bridge h hd hm hkc hkg hc' hg

end Solow1956.DiscreteTime

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-! # Discrete-time stability, saving shocks, effective labour, and factor prices

Discrete counterparts of `Solow1956.Growth.GeneralSolowApplications`, together with
Acemoglu Proposition 2.6: along a path from below the steady state the wage rises
and the rental rate falls every period.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime

open Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- Global attraction for every admissible path. -/
theorem every_path_converges (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k : ℕ → ℝ} (hk : IsPath f s δ γ k) : Tendsto k atTop (𝓝 (steady h s δ γ)) :=
  hk.tendsto h P

/-- Lyapunov stability, strictly: away from `k*` the distance to `k*` falls every period. -/
theorem path_stable (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k : ℕ → ℝ} (hk : IsPath f s δ γ k) (t : ℕ) :
    |k (t + 1) - steady h s δ γ| ≤ |k t - steady h s δ γ| ∧
      (k t ≠ steady h s δ γ → |k (t + 1) - steady h s δ γ| < |k t - steady h s δ γ|) := by
  obtain ⟨hks, hfix⟩ := steady_spec h P
  have hkt := hk.pos h P t
  set ks := steady h s δ γ
  rw [hk.succ]
  rcases lt_trichotomy (k t) ks with hlt | heq | hgt
  · have h1 := next_gt_self h P hkt hlt
    have h2 : next f s δ γ (k t) < ks := hfix ▸ next_strictMono h P hkt.le hks.le hlt
    rw [abs_of_neg (sub_neg.mpr h2), abs_of_neg (sub_neg.mpr hlt)]
    exact ⟨by linarith, fun _ => by linarith⟩
  · rw [heq, hfix]
    exact ⟨le_rfl, fun hne => absurd rfl hne⟩
  · have h1 := next_lt_self h P hgt
    have h2 : ks < next f s δ γ (k t) := hfix ▸ next_strictMono h P hks.le hkt.le hgt
    rw [abs_of_pos (sub_pos.mpr h2), abs_of_pos (sub_pos.mpr hgt)]
    exact ⟨by linarith, fun _ => by linarith⟩

/-- The distance to `k*` never exceeds its initial value. -/
theorem path_stable_initial (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k : ℕ → ℝ} (hk : IsPath f s δ γ k) (t : ℕ) :
    |k t - steady h s δ γ| ≤ |k 0 - steady h s δ γ| := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (path_stable h P hk t).1.trans ih

/-- A permanent saving increase from an old steady state: strict capital deepening,
convergence to the higher new steady state, and an immediate consumption loss. -/
theorem saving_increase_transition (h : Technology f) {s0 s1 δ γ : ℝ}
    (P0 : Params s0 δ γ) (hs : s0 < s1) :
    ∃ k : ℕ → ℝ, k 0 = steady h s0 δ γ ∧ IsPath f s1 δ γ k ∧ StrictMono k ∧
      (∀ t, k t < steady h s1 δ γ) ∧ Tendsto k atTop (𝓝 (steady h s1 δ γ)) ∧
      (1 - s1) * f (k 0) < (1 - s0) * f (k 0) := by
  have P1 : Params s1 δ γ := ⟨P0.saving_pos.trans hs, P0.depreciation_le_one,
    P0.growth_pos, P0.dilution_pos⟩
  have h0 := (steady_spec h P0).1
  have hk := isPath_path (f := f) (s := s1) (δ := δ) (γ := γ) h0
  have hlt : steady h s0 δ γ < steady h s1 δ γ :=
    steady_strictMono_saving h P0.dilution_pos P0.saving_pos P1.saving_pos hs
  obtain ⟨_, hlow, _, _, _, hlim⟩ := hk.orbit h P1
  obtain ⟨hmono, hbelow⟩ := hlow hlt
  refine ⟨_, rfl, hk, hmono, hbelow, hlim, ?_⟩
  have hy : 0 < f (steady h s0 δ γ) := h.output_pos h0
  exact mul_lt_mul_of_pos_right (by linarith) hy

/-- Aggregate accumulation `K(t+1) = s Y(t) + (1 - δ) K(t)` with effective labour
`E(t+1) = γ E(t)` and `Y = E f(K/E)` gives the intensive map. -/
theorem capitalPerEffectiveWorker_succ {K E Y : ℕ → ℝ} {s δ γ : ℝ} {t : ℕ}
    (hγ : 0 < γ) (hE : 0 < E t)
    (hK : K (t + 1) = s * Y t + (1 - δ) * K t) (hEs : E (t + 1) = γ * E t)
    (hY : Y t = E t * f (K t / E t)) :
    K (t + 1) / E (t + 1) = next f s δ γ (K t / E t) := by
  rw [hK, hEs, hY]
  unfold next
  field_simp

/-- Effective capital converges with labour-augmenting progress, derived from the
aggregate equations. -/
theorem effective_labour_convergence (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {K E Y : ℕ → ℝ} (hK0 : 0 < K 0) (hE : ∀ t, 0 < E t)
    (hK : ∀ t, K (t + 1) = s * Y t + (1 - δ) * K t) (hEs : ∀ t, E (t + 1) = γ * E t)
    (hY : ∀ t, Y t = E t * f (K t / E t)) :
    Tendsto (fun t => K t / E t) atTop (𝓝 (steady h s δ γ)) :=
  IsPath.tendsto h P ⟨div_pos hK0 (hE 0), fun t =>
    capitalPerEffectiveWorker_succ P.growth_pos (hE t) (hK t) (hEs t) (hY t)⟩

/-- Competitive wage per worker, `w = f(k) - k f'(k)`. -/
noncomputable def wage (f : ℝ → ℝ) (k : ℝ) : ℝ := f k - k * deriv f k

/-- The wage is strictly increasing in capital per worker. -/
theorem wage_strictMono (h : Technology f) : StrictMonoOn (wage f) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hs := h.concave.deriv_lt_slope (show a ∈ Ici 0 from ha'.le)
    (show b ∈ Ici 0 from (ha'.trans hab).le) hab (h.differentiable b (ha'.trans hab))
  rw [slope_def_field] at hs
  have hs' := (lt_div_iff₀ (sub_pos.mpr hab)).mp hs
  have hm := h.marginal_strictAnti ha hb hab
  unfold wage
  nlinarith

/-- Acemoglu Proposition 2.6: from below the steady state the wage rises and the
rental rate `R = f'(k)` falls every period; from above the opposite holds. -/
theorem factor_prices (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k : ℕ → ℝ} (hk : IsPath f s δ γ k) :
    (k 0 < steady h s δ γ →
      StrictMono (fun t => wage f (k t)) ∧ StrictAnti (fun t => deriv f (k t))) ∧
    (steady h s δ γ < k 0 →
      StrictAnti (fun t => wage f (k t)) ∧ StrictMono (fun t => deriv f (k t))) := by
  obtain ⟨hpos, hlow, hhigh, _, _, _⟩ := hk.orbit h P
  refine ⟨fun hlt => ⟨fun a b hab => ?_, fun a b hab => ?_⟩,
    fun hgt => ⟨fun a b hab => ?_, fun a b hab => ?_⟩⟩
  · exact wage_strictMono h (hpos a) (hpos b) ((hlow hlt).1 hab)
  · exact h.marginal_strictAnti (hpos a) (hpos b) ((hlow hlt).1 hab)
  · exact wage_strictMono h (hpos b) (hpos a) ((hhigh hgt).1 hab)
  · exact h.marginal_strictAnti (hpos b) (hpos a) ((hhigh hgt).1 hab)

end Solow1956.DiscreteTime

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-! # Concrete discrete-time economies and boundary checks

The technology examples of `Solow1956.Growth.GeneralSolowExamples` are time-free
and are reused. The checks below concern the map itself, including why the
restrictions in `Params` cannot be dropped.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime

open Solow1956.Neoclassical

/-- Sample parameters for a concrete non-Cobb–Douglas economy satisfy `Params`. -/
theorem example_params : Params (1 / 4) (1 / 2) 1 := ⟨by norm_num, by norm_num, by norm_num,
  by norm_num⟩

/-- A sum of powers has a unique positive fixed point of the discrete map. -/
theorem mixed_power_fixed_exists :
    ∃! k : ℝ, 0 < k ∧
      next (fun k : ℝ => k ^ (1 / 2 : ℝ) + k ^ (1 / 3 : ℝ)) (1 / 4) (1 / 2) 1 k = k :=
  existsUnique_steadyState mixed_power_technology example_params

/-- Every positive path of that economy converges monotonically to its steady state. -/
theorem mixed_power_converges {k₀ : ℝ} (hk₀ : 0 < k₀) :
    Tendsto (path (fun k : ℝ => k ^ (1 / 2 : ℝ) + k ^ (1 / 3 : ℝ)) (1 / 4) (1 / 2) 1 k₀) atTop
      (𝓝 (steady mixed_power_technology (1 / 4) (1 / 2) 1)) :=
  (isPath_path hk₀).tendsto mixed_power_technology example_params

/-- Without positive effective dilution capital grows every period: there is no
positive steady state. -/
theorem no_positive_fixed_without_dilution {f : ℝ → ℝ} (h : Technology f)
    {s δ γ k : ℝ} (hs : 0 < s) (hγ : 0 < γ) (hm : γ - 1 + δ ≤ 0) (hk : 0 < k) :
    k < next f s δ γ k := by
  have := no_positive_steady_without_dilution h hs hm hk
  have hd := next_sub_self (f := f) (s := s) (δ := δ) hγ k
  have := div_pos this hγ
  linarith

/-- Depreciation above one breaks positivity of the map, so `δ ≤ 1` cannot be dropped:
with `f = √k`, `s = 1`, `δ = 3`, `γ = 1`, the stock `4` is sent to `-6`. -/
theorem depreciation_above_one_breaks_positivity :
    next (fun k : ℝ => k ^ (1 / 2 : ℝ)) 1 3 1 4 = -6 := by
  have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  simp only [next, h4]
  norm_num

/-- Linear technology can have more than one positive fixed point. -/
theorem linear_technology_multiple_fixed :
    next (fun k : ℝ => 2 * k) (1 / 2) 1 1 1 = 1 ∧
      next (fun k : ℝ => 2 * k) (1 / 2) 1 1 2 = 2 ∧ (1 : ℝ) ≠ 2 := by
  norm_num [next]

end Solow1956.DiscreteTime

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

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

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

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

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

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

/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/

/-!
# Absolute convergence among identical discrete-time Solow economies, and its speed

The discrete counterpart of `Solow1956.Growth.SolowConvergence`. Two economies share
`s`, `δ`, `γ` and `f` and differ only in initial capital. We prove:

* `path_eq_of_meet`, `paths_ordered`: paths that meet at a date agree at every
  earlier date (the map is injective), so paths never cross.
* `poorer_grows_faster`: the poorer economy's gross growth factor `k(t+1)/k(t)` is
  strictly higher every period.
* `log_gap_strictAnti`, `absolute_convergence`: the log gap `D t = log l t - log k t`
  strictly decreases, and the level gap, log gap and ratio converge to `0`, `0`, `1`.
* `log_gap_le_of_contraction_bound`, `exists_uniform_rate`,
  `absolute_convergence_rate`, `level_gap_le`: geometric convergence. The local
  contraction `κ(k) = k G'(k) / G(k)` (the elasticity of the map) lies in `(0, 1)`;
  an upper bound `ρ` for it on the range of the paths gives `D t ≤ ρ^t D 0`.
* `sharp_convergence_rate`, `log_gap_ratio_tendsto`, `log_gap_rate_tendsto`: the exact
  asymptotic factor is `ρ* = κ(k*) = G'(k*) = (s f'(k*) + 1 - δ) / γ`:
  `D (t+1) / D t → ρ*` and `log (D t) / t → log ρ*`.
* `contraction_steady_eq`: `ρ* = 1 - β*/γ`, with `β* = m - s f'(k*)` the
  continuous-time speed; `cobbDouglas_contraction`: `ρ* = 1 - (1 - α) m / γ`
  (`= α` under full depreciation and `γ = 1`).

The constant steady-state path is admissible, so every result also bounds a single
economy's convergence to its steady state (`log_gap_steady_le`).
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime

open Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- Gross growth factor of capital, `k(t+1)/k(t) = (s f(k)/k + 1 - δ)/γ`. -/
noncomputable def growthFactor (f : ℝ → ℝ) (s δ γ k : ℝ) : ℝ := (s * (f k / k) + (1 - δ)) / γ

/-- Local contraction `κ(k) = k G'(k)/G(k)`: the elasticity of the map, the slope of
`log k(t+1)` against `log k(t)`. -/
noncomputable def contraction (f : ℝ → ℝ) (s δ k : ℝ) : ℝ :=
  k * (s * deriv f k + (1 - δ)) / (s * f k + (1 - δ) * k)

theorem next_div_eq_growthFactor (s δ γ : ℝ) {k : ℝ} (hk : 0 < k) :
    next f s δ γ k / k = growthFactor f s δ γ k := by
  unfold next growthFactor
  field_simp

theorem growthFactor_strictAnti (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    StrictAntiOn (growthFactor f s δ γ) (Ioi 0) := by
  intro a ha b hb hab
  have := mul_lt_mul_of_pos_left (h.average_strictAnti ha hb hab) P.saving_pos
  exact div_lt_div_of_pos_right (by linarith) P.growth_pos

theorem gross_pos (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ) (hk : 0 < k) :
    0 < s * f k + (1 - δ) * k := by
  have := mul_pos P.saving_pos (h.output_pos hk)
  have := mul_nonneg (sub_nonneg.mpr P.depreciation_le_one) hk.le
  linarith

theorem contraction_pos (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ) (hk : 0 < k) :
    0 < contraction f s δ k := by
  have := mul_pos P.saving_pos (h.marginal_positive k hk)
  have := sub_nonneg.mpr P.depreciation_le_one
  exact div_pos (mul_pos hk (by linarith)) (gross_pos h P hk)

theorem contraction_lt_one (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ) (hk : 0 < k) :
    contraction f s δ k < 1 := by
  have hg := mul_lt_mul_of_pos_left (h.output_gap hk) P.saving_pos
  apply (div_lt_one (gross_pos h P hk)).mpr
  nlinarith

theorem contraction_continuousOn (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    ContinuousOn (contraction f s δ) (Ioi 0) := by
  have hf : ContinuousOn f (Ioi 0) := fun k hk =>
    (h.differentiable k hk).continuousAt.continuousWithinAt
  exact (continuousOn_id.mul ((h.derivative_continuous.const_mul s).add continuousOn_const)).div
    ((hf.const_mul s).add (continuousOn_id.const_mul (1 - δ)))
    (fun k hk => ne_of_gt (gross_pos h P hk))

/-- At the steady state the contraction is the slope of the map, `G'(k*)`. -/
theorem contraction_steady (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    contraction f s δ (steady h s δ γ) = (s * deriv f (steady h s δ γ) + (1 - δ)) / γ := by
  obtain ⟨hk, hfix⟩ := steady_spec h P
  set ks := steady h s δ γ
  have hgross : s * f ks + (1 - δ) * ks = γ * ks := by
    unfold next at hfix
    field_simp [ne_of_gt P.growth_pos] at hfix
    linarith
  unfold contraction
  rw [hgross]
  field_simp [ne_of_gt P.growth_pos, ne_of_gt hk]

/-- The discrete factor and the continuous speed: `ρ* = 1 - β*/γ`. -/
theorem contraction_steady_eq (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    contraction f s δ (steady h s δ γ) =
      1 - convergenceSpeed f s (steady h s δ γ) / γ := by
  rw [contraction_steady h P, steady,
    convergenceSpeed_steady h P.saving_pos P.dilution_pos]
  field_simp [ne_of_gt P.growth_pos]
  ring

/-- Cobb–Douglas: `ρ* = 1 - (1 - α)(γ - 1 + δ)/γ`. -/
theorem cobbDouglas_contraction {α b δ γ : ℝ} (hα : 0 < α) (hα1 : α < 1) (P : Params b δ γ) :
    contraction (fun k : ℝ => k ^ α) b δ (steady (technology_rpow hα hα1) b δ γ) =
      1 - (1 - α) * (γ - 1 + δ) / γ := by
  rw [contraction_steady_eq _ P, steady, cobbDouglas_speed hα hα1 P.saving_pos P.dilution_pos]

/-- The constant path at `k*` is admissible. -/
theorem isPath_steady (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    IsPath f s δ γ (fun _ => steady h s δ γ) :=
  ⟨(steady_spec h P).1, fun _ => (steady_spec h P).2.symm⟩

/-- Backward uniqueness: paths that meet at a date agree at every earlier date. -/
theorem path_eq_of_meet (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l)
    {T : ℕ} (hmeet : k T = l T) {t : ℕ} (ht : t ≤ T) : k t = l t := by
  induction T with
  | zero => rwa [Nat.le_zero.mp ht]
  | succ T ih =>
    rcases Nat.lt_or_eq_of_le ht with hlt | heq
    · apply ih _ (Nat.lt_succ_iff.mp hlt)
      rw [hk.succ, hl.succ] at hmeet
      exact (next_strictMono h P).injOn (hk.pos h P T).le (hl.pos h P T).le hmeet
    · rw [heq]; exact hmeet

/-- Paths never cross: the initially poorer economy is strictly poorer every period. -/
theorem paths_ordered (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0)
    (t : ℕ) : k t < l t := by
  induction t with
  | zero => exact h0
  | succ t ih =>
    rw [hk.succ, hl.succ]
    exact next_strictMono h P (hk.pos h P t).le (hl.pos h P t).le ih

/-- The poorer economy grows by a strictly larger factor every period. -/
theorem poorer_grows_faster (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0)
    (t : ℕ) : l (t + 1) / l t < k (t + 1) / k t := by
  rw [hk.succ, hl.succ, next_div_eq_growthFactor s δ γ (hk.pos h P t),
    next_div_eq_growthFactor s δ γ (hl.pos h P t)]
  exact growthFactor_strictAnti h P (hk.pos h P t) (hl.pos h P t) (paths_ordered h P hk hl h0 t)

theorem log_gap_pos (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0)
    (t : ℕ) : 0 < Real.log (l t) - Real.log (k t) :=
  sub_pos.mpr (Real.log_lt_log (hk.pos h P t) (paths_ordered h P hk hl h0 t))

/-- The proportional gap shrinks strictly every period. -/
theorem log_gap_strictAnti (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) :
    StrictAnti (fun t => Real.log (l t) - Real.log (k t)) := by
  apply strictAnti_nat_of_succ_lt
  intro t
  have hkt := hk.pos h P t
  have hlt := hl.pos h P t
  have hfast := poorer_grows_faster h P hk hl h0 t
  have hk1 := hk.pos h P (t + 1)
  have hl1 := hl.pos h P (t + 1)
  have hlog := Real.log_lt_log (div_pos hl1 hlt) hfast
  rw [Real.log_div hl1.ne' hlt.ne', Real.log_div hk1.ne' hkt.ne'] at hlog
  linarith

/-- Absolute convergence: identical economies converge to each other in levels, in
logs, and in ratio. -/
theorem absolute_convergence (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) :
    Tendsto (fun t => l t - k t) atTop (𝓝 0) ∧
      Tendsto (fun t => Real.log (l t) - Real.log (k t)) atTop (𝓝 0) ∧
      Tendsto (fun t => l t / k t) atTop (𝓝 1) := by
  have hks := (steady_spec h P).1
  have hkl := hk.tendsto h P
  have hll := hl.tendsto h P
  refine ⟨by simpa only [sub_self] using hll.sub hkl, ?_, ?_⟩
  · have hlog := (Real.continuousAt_log (ne_of_gt hks)).tendsto
    have := (hlog.comp hll).sub (hlog.comp hkl)
    rw [sub_self] at this
    exact this
  · have := hll.div hkl (ne_of_gt hks)
    rw [div_self (ne_of_gt hks)] at this
    exact this

theorem hasDerivAt_log_next_sub (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) (r : ℝ)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z => Real.log (next f s δ γ z) - r * Real.log z)
      ((contraction f s δ z - r) / z) z := by
  have hg := gross_pos h P hz
  have h1 := (next_hasDerivAt h s δ γ hz).log (ne_of_gt (next_pos h P hz))
  have h2 := (Real.hasDerivAt_log (ne_of_gt hz)).const_mul r
  refine (h1.sub h2).congr_deriv ?_
  unfold contraction next
  field_simp [ne_of_gt P.growth_pos, ne_of_gt hg, ne_of_gt hz]

/-- An upper bound `ρ` on the contraction over `[a, b]` bounds the one-period log gap. -/
theorem log_next_gap_le (h : Technology f) {s δ γ a b r : ℝ} (P : Params s δ γ) (ha : 0 < a)
    (hr : ∀ z ∈ Icc a b, contraction f s δ z ≤ r)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    Real.log (next f s δ γ y) - Real.log (next f s δ γ x) ≤ r * (Real.log y - Real.log x) := by
  have hanti : AntitoneOn (fun z => Real.log (next f s δ γ z) - r * Real.log z) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (HasDerivAt.continuousOn (fun z hz => hasDerivAt_log_next_sub h P r (ha.trans_le hz.1)))
      (fun z hz => (hasDerivAt_log_next_sub h P r (ha.trans_le
        (interior_subset hz : z ∈ Icc a b).1)).differentiableAt.differentiableWithinAt)
    intro z hz
    have hz' : z ∈ Icc a b := interior_subset hz
    rw [(hasDerivAt_log_next_sub h P r (ha.trans_le hz'.1)).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hr z hz')) (ha.trans_le hz'.1).le
  have := hanti hx hy hxy
  simp only at this
  linarith

/-- A lower bound `ρ'` on the contraction over `[a, b]` bounds the one-period log gap below. -/
theorem log_next_gap_ge (h : Technology f) {s δ γ a b r : ℝ} (P : Params s δ γ) (ha : 0 < a)
    (hr : ∀ z ∈ Icc a b, r ≤ contraction f s δ z)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    r * (Real.log y - Real.log x) ≤ Real.log (next f s δ γ y) - Real.log (next f s δ γ x) := by
  have hmono : MonotoneOn (fun z => Real.log (next f s δ γ z) - r * Real.log z) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (HasDerivAt.continuousOn (fun z hz => hasDerivAt_log_next_sub h P r (ha.trans_le hz.1)))
      (fun z hz => (hasDerivAt_log_next_sub h P r (ha.trans_le
        (interior_subset hz : z ∈ Icc a b).1)).differentiableAt.differentiableWithinAt)
    intro z hz
    have hz' : z ∈ Icc a b := interior_subset hz
    rw [(hasDerivAt_log_next_sub h P r (ha.trans_le hz'.1)).deriv]
    exact div_nonneg (sub_nonneg.mpr (hr z hz')) (ha.trans_le hz'.1).le
  have := hmono hx hy hxy
  simp only at this
  linarith

/-- Geometric bound from above: from any date `T` after which both ordered paths stay
in `[a, b]`, an upper bound `ρ ≥ 0` on the contraction gives `D (T + n) ≤ ρ^n D T`. -/
theorem log_gap_upper (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0)
    {a b r : ℝ} {T : ℕ} (ha : 0 < a) (hr0 : 0 ≤ r)
    (hkw : ∀ t, T ≤ t → k t ∈ Icc a b) (hlw : ∀ t, T ≤ t → l t ∈ Icc a b)
    (hr : ∀ z ∈ Icc a b, contraction f s δ z ≤ r) (n : ℕ) :
    Real.log (l (T + n)) - Real.log (k (T + n)) ≤
      r ^ n * (Real.log (l T) - Real.log (k T)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hT : T ≤ T + n := Nat.le_add_right T n
    have hstep := log_next_gap_le (γ := γ) h P ha hr (hkw _ hT) (hlw _ hT)
      (paths_ordered h P hk hl h0 (T + n)).le
    rw [← hk.succ, ← hl.succ] at hstep
    rw [← add_assoc, pow_succ]
    calc Real.log (l (T + n + 1)) - Real.log (k (T + n + 1))
        ≤ r * (Real.log (l (T + n)) - Real.log (k (T + n))) := hstep
      _ ≤ r * (r ^ n * (Real.log (l T) - Real.log (k T))) :=
          mul_le_mul_of_nonneg_left ih hr0
      _ = _ := by ring

/-- Geometric bound from below: a lower bound `ρ' ≥ 0` on the contraction gives
`ρ'^n D T ≤ D (T + n)`. -/
theorem log_gap_lower (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0)
    {a b r : ℝ} {T : ℕ} (ha : 0 < a) (hr0 : 0 ≤ r)
    (hkw : ∀ t, T ≤ t → k t ∈ Icc a b) (hlw : ∀ t, T ≤ t → l t ∈ Icc a b)
    (hr : ∀ z ∈ Icc a b, r ≤ contraction f s δ z) (n : ℕ) :
    r ^ n * (Real.log (l T) - Real.log (k T)) ≤
      Real.log (l (T + n)) - Real.log (k (T + n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hT : T ≤ T + n := Nat.le_add_right T n
    have hstep := log_next_gap_ge (γ := γ) h P ha hr (hkw _ hT) (hlw _ hT)
      (paths_ordered h P hk hl h0 (T + n)).le
    rw [← hk.succ, ← hl.succ] at hstep
    rw [← add_assoc, pow_succ]
    calc r ^ n * r * (Real.log (l T) - Real.log (k T))
        = r * (r ^ n * (Real.log (l T) - Real.log (k T))) := by ring
      _ ≤ r * (Real.log (l (T + n)) - Real.log (k (T + n))) :=
          mul_le_mul_of_nonneg_left ih hr0
      _ ≤ _ := hstep

/-- Both ordered paths lie between the lower initial stock (or `k*`) and the higher
initial stock (or `k*`). -/
theorem paths_window (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) (t : ℕ) :
    k t ∈ Icc (min (k 0) (steady h s δ γ)) (max (l 0) (steady h s δ γ)) ∧
      l t ∈ Icc (min (k 0) (steady h s δ γ)) (max (l 0) (steady h s δ γ)) := by
  obtain ⟨hk1, hk2⟩ := hk.bounds h P t
  obtain ⟨hl1, hl2⟩ := hl.bounds h P t
  have h1 : min (k 0) (steady h s δ γ) ≤ min (l 0) (steady h s δ γ) :=
    min_le_min_right _ h0.le
  have h2 : max (k 0) (steady h s δ γ) ≤ max (l 0) (steady h s δ γ) :=
    max_le_max_right _ h0.le
  exact ⟨⟨hk1, hk2.trans h2⟩, ⟨h1.trans hl1, hl2⟩⟩

/-- Global geometric convergence at an explicit factor: any bound `ρ` for the
contraction over the range of the two paths satisfies `D t ≤ ρ^t D 0`. -/
theorem log_gap_le_of_contraction_bound (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) {r : ℝ}
    (hr0 : 0 ≤ r)
    (hr : ∀ z ∈ Icc (min (k 0) (steady h s δ γ)) (max (l 0) (steady h s δ γ)),
      contraction f s δ z ≤ r) (t : ℕ) :
    Real.log (l t) - Real.log (k t) ≤ r ^ t * (Real.log (l 0) - Real.log (k 0)) := by
  have ha : 0 < min (k 0) (steady h s δ γ) := lt_min hk.initial_pos (steady_spec h P).1
  simpa only [zero_add] using log_gap_upper h P hk hl h0 (T := 0) ha hr0
    (fun u _ => (paths_window h P hk hl h0 u).1) (fun u _ => (paths_window h P hk hl h0 u).2)
    hr t

/-- A uniform geometric factor `ρ < 1` exists. -/
theorem exists_uniform_rate (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ t,
      Real.log (l t) - Real.log (k t) ≤ r ^ t * (Real.log (l 0) - Real.log (k 0)) := by
  set a := min (k 0) (steady h s δ γ)
  set b := max (l 0) (steady h s δ γ)
  have ha : 0 < a := lt_min hk.initial_pos (steady_spec h P).1
  have hab : a ≤ b := (min_le_right _ _).trans (le_max_right _ _)
  obtain ⟨z, hz, hzmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab)
    ((contraction_continuousOn h P).mono (fun _ hx => ha.trans_le hx.1))
  have hzpos := ha.trans_le hz.1
  exact ⟨contraction f s δ z, contraction_pos h P hzpos, contraction_lt_one h P hzpos,
    log_gap_le_of_contraction_bound h P hk hl h0 (contraction_pos h P hzpos).le
      (fun y hy => hzmax hy)⟩

/-- Absolute convergence at a geometric rate for any two identical economies. -/
theorem absolute_convergence_rate (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ t,
      |Real.log (l t) - Real.log (k t)| ≤ r ^ t * |Real.log (l 0) - Real.log (k 0)| := by
  rcases lt_trichotomy (k 0) (l 0) with h0 | h0 | h0
  · obtain ⟨r, hr, hr1, hb⟩ := exists_uniform_rate h P hk hl h0
    refine ⟨r, hr, hr1, fun t => ?_⟩
    rw [abs_of_pos (log_gap_pos h P hk hl h0 t), abs_of_pos (log_gap_pos h P hk hl h0 0)]
    exact hb t
  · refine ⟨1 / 2, by norm_num, by norm_num, fun t => ?_⟩
    have he := path_unique hk.succ hl.succ h0
    rw [he, sub_self, sub_self, abs_zero, mul_zero]
  · obtain ⟨r, hr, hr1, hb⟩ := exists_uniform_rate h P hl hk h0
    refine ⟨r, hr, hr1, fun t => ?_⟩
    rw [abs_sub_comm, abs_sub_comm (Real.log (l 0)), abs_of_pos (log_gap_pos h P hl hk h0 t),
      abs_of_pos (log_gap_pos h P hl hk h0 0)]
    exact hb t

/-- A single economy converges geometrically to its steady state. -/
theorem log_gap_steady_le (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k : ℕ → ℝ} (hk : IsPath f s δ γ k) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ t,
      |Real.log (k t) - Real.log (steady h s δ γ)| ≤
        r ^ t * |Real.log (k 0) - Real.log (steady h s δ γ)| :=
  absolute_convergence_rate h P (isPath_steady h P) hk

/-- The level gap also closes geometrically:
`l t - k t ≤ max (l 0) k* · log (l 0 / k 0) · ρ^t`. -/
theorem level_gap_le (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ t, 0 < l t - k t ∧
      l t - k t ≤ max (l 0) (steady h s δ γ) * (Real.log (l 0) - Real.log (k 0)) * r ^ t := by
  obtain ⟨r, hr, hr1, hb⟩ := exists_uniform_rate h P hk hl h0
  refine ⟨r, hr, hr1, fun t => ⟨sub_pos.mpr (paths_ordered h P hk hl h0 t), ?_⟩⟩
  have hkt := hk.pos h P t
  have hlt := hl.pos h P t
  have hlog : l t - k t ≤ l t * (Real.log (l t) - Real.log (k t)) := by
    have he := Real.add_one_le_exp (Real.log (k t) - Real.log (l t))
    rw [Real.exp_sub, Real.exp_log hkt, Real.exp_log hlt, le_div_iff₀ hlt] at he
    nlinarith
  have hD := log_gap_pos h P hk hl h0 t
  have hup := (paths_window h P hk hl h0 t).2.2
  calc l t - k t ≤ l t * (Real.log (l t) - Real.log (k t)) := hlog
    _ ≤ max (l 0) (steady h s δ γ) * (Real.log (l t) - Real.log (k t)) :=
        mul_le_mul_of_nonneg_right hup hD.le
    _ ≤ max (l 0) (steady h s δ γ) * (r ^ t * (Real.log (l 0) - Real.log (k 0))) :=
        mul_le_mul_of_nonneg_left (hb t) (hlt.le.trans hup)
    _ = _ := by ring

/-- Near the steady state the one-period ratio of log gaps is within `ε` of `ρ*`:
there is a date after which both paths lie in a window where `ρ* - ε ≤ κ ≤ ρ* + ε`. -/
theorem eventually_contraction_window (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℝ, 0 < a ∧ ∃ T : ℕ,
      (∀ t, T ≤ t → k t ∈ Icc a b) ∧ (∀ t, T ≤ t → l t ∈ Icc a b) ∧
      ∀ z ∈ Icc a b, |contraction f s δ z - contraction f s δ (steady h s δ γ)| < ε := by
  have hks := (steady_spec h P).1
  set ks := steady h s δ γ
  obtain ⟨d, hd, hdb⟩ := Metric.continuousAt_iff.mp
    ((contraction_continuousOn h P).continuousAt (Ioi_mem_nhds hks)) ε hε
  set r := min (d / 2) (ks / 2)
  have hr : 0 < r := lt_min (half_pos hd) (half_pos hks)
  have ha : 0 < ks - r := by have := min_le_right (d / 2) (ks / 2); linarith
  have hnhds : Icc (ks - r) (ks + r) ∈ 𝓝 ks := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((hk.tendsto h P).eventually hnhds).and ((hl.tendsto h P).eventually hnhds))
  refine ⟨ks - r, ks + r, ha, T, fun t ht => (hT t ht).1, fun t ht => (hT t ht).2, ?_⟩
  intro z hz
  have : dist z ks < d := by
    rw [Real.dist_eq, abs_lt]
    have := min_le_left (d / 2) (ks / 2)
    constructor <;> linarith [hz.1, hz.2]
  have := hdb this
  rwa [Real.dist_eq] at this

/-- The exact asymptotic factor: `D (t+1) / D t → ρ* = κ(k*) = G'(k*)`. -/
theorem log_gap_ratio_tendsto (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) :
    Tendsto (fun t => (Real.log (l (t + 1)) - Real.log (k (t + 1))) /
      (Real.log (l t) - Real.log (k t))) atTop (𝓝 (contraction f s δ (steady h s δ γ))) := by
  set ρ := contraction f s δ (steady h s δ γ)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨a, b, ha, T, hkw, hlw, hwin⟩ :=
    eventually_contraction_window h P hk hl (half_pos hε)
  refine ⟨T, fun t ht => ?_⟩
  have hD := log_gap_pos h P hk hl h0 t
  have hord := (paths_ordered h P hk hl h0 t).le
  have hup := log_next_gap_le (γ := γ) h P ha
    (fun z hz => (by linarith [(abs_lt.mp (hwin z hz)).2] : contraction f s δ z ≤ ρ + ε / 2))
    (hkw t ht) (hlw t ht) hord
  have hlo := log_next_gap_ge (γ := γ) h P ha
    (fun z hz => (by linarith [(abs_lt.mp (hwin z hz)).1] : ρ - ε / 2 ≤ contraction f s δ z))
    (hkw t ht) (hlw t ht) hord
  rw [← hk.succ, ← hl.succ] at hup hlo
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hD]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hD]; nlinarith

/-- Sharp geometric sandwich: for `0 < ε < ρ*` with `ρ* + ε ≤ 1`, the log gap lies
between multiples of `(ρ* - ε)^t` and `(ρ* + ε)^t`. -/
theorem sharp_convergence_rate (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0)
    {ε : ℝ} (hε : 0 < ε) (hερ : ε < contraction f s δ (steady h s δ γ))
    (hρ1 : contraction f s δ (steady h s δ γ) + ε ≤ 1) :
    ∃ c, 0 < c ∧ ∃ C, 0 < C ∧ ∀ t,
      c * (contraction f s δ (steady h s δ γ) - ε) ^ t ≤ Real.log (l t) - Real.log (k t) ∧
        Real.log (l t) - Real.log (k t) ≤ C * (contraction f s δ (steady h s δ γ) + ε) ^ t := by
  set ρ := contraction f s δ (steady h s δ γ)
  set D : ℕ → ℝ := fun u => Real.log (l u) - Real.log (k u) with hD
  obtain ⟨a, b, ha, T, hkw, hlw, hwin⟩ := eventually_contraction_window h P hk hl hε
  have hDpos : ∀ t, 0 < D t := log_gap_pos h P hk hl h0
  have hanti := log_gap_strictAnti h P hk hl h0
  have hlo0 : 0 ≤ ρ - ε := by linarith
  have hhi0 : 0 < ρ + ε := by linarith
  have hlo1 : ρ - ε ≤ 1 := by linarith
  have hupT := log_gap_upper h P hk hl h0 ha hhi0.le hkw hlw
    (fun z hz => (by linarith [(abs_lt.mp (hwin z hz)).2] : contraction f s δ z ≤ ρ + ε))
  have hloT := log_gap_lower h P hk hl h0 ha hlo0 hkw hlw
    (fun z hz => (by linarith [(abs_lt.mp (hwin z hz)).1] : ρ - ε ≤ contraction f s δ z))
  have hpowT := pow_pos hhi0 T
  refine ⟨D T, hDpos T, D 0 / (ρ + ε) ^ T, div_pos (hDpos 0) hpowT, fun t => ⟨?_, ?_⟩⟩
  · rcases le_total T t with hTt | htT
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hTt
      have h1 : (ρ - ε) ^ (T + n) ≤ (ρ - ε) ^ n := by
        rw [pow_add]
        exact mul_le_of_le_one_left (pow_nonneg hlo0 _) (pow_le_one₀ hlo0 hlo1)
      calc D T * (ρ - ε) ^ (T + n) ≤ D T * (ρ - ε) ^ n :=
            mul_le_mul_of_nonneg_left h1 (hDpos T).le
        _ = (ρ - ε) ^ n * D T := by ring
        _ ≤ D (T + n) := hloT n
    · have hmono : D T ≤ D t := hanti.antitone htT
      calc D T * (ρ - ε) ^ t ≤ D T * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hlo0 hlo1) (hDpos T).le
        _ ≤ D t := by rw [mul_one]; exact hmono
  · rcases le_total T t with hTt | htT
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hTt
      have hmono : D T ≤ D 0 := hanti.antitone (Nat.zero_le T)
      calc D (T + n) ≤ (ρ + ε) ^ n * D T := hupT n
        _ ≤ (ρ + ε) ^ n * D 0 := mul_le_mul_of_nonneg_left hmono (pow_nonneg hhi0.le _)
        _ = D 0 / (ρ + ε) ^ T * (ρ + ε) ^ (T + n) := by
            rw [pow_add]; field_simp
    · have hmono : D t ≤ D 0 := hanti.antitone (Nat.zero_le t)
      have hp : (ρ + ε) ^ T ≤ (ρ + ε) ^ t := pow_le_pow_of_le_one hhi0.le hρ1 htT
      calc D t ≤ D 0 := hmono
        _ = D 0 / (ρ + ε) ^ T * (ρ + ε) ^ T := by field_simp
        _ ≤ D 0 / (ρ + ε) ^ T * (ρ + ε) ^ t :=
            mul_le_mul_of_nonneg_left hp (div_pos (hDpos 0) hpowT).le

/-- The exact asymptotic rate in logarithms: `log (D t) / t → log ρ*`. -/
theorem log_gap_rate_tendsto (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) :
    Tendsto (fun t : ℕ => Real.log (Real.log (l t) - Real.log (k t)) / t) atTop
      (𝓝 (Real.log (contraction f s δ (steady h s δ γ)))) := by
  set ρ := contraction f s δ (steady h s δ γ)
  have hρ := contraction_pos h P (steady_spec h P).1
  have hρ1 := contraction_lt_one h P (steady_spec h P).1
  rw [Metric.tendsto_nhds]
  intro e he
  -- choose `ε` so that `log (ρ ± ε)` is within `e / 4` of `log ρ`
  obtain ⟨d, hd, hdb⟩ := Metric.continuousAt_iff.mp (Real.continuousAt_log (ne_of_gt hρ))
    (e / 4) (by linarith)
  set ε := min (d / 2) (min (ρ / 2) ((1 - ρ) / 2))
  have hε : 0 < ε := lt_min (half_pos hd) (lt_min (half_pos hρ) (by linarith))
  have hεd : ε < d := (min_le_left _ _).trans_lt (half_lt_self hd)
  have hερ : ε < ρ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hρ)
  have hε1 : ρ + ε ≤ 1 := by
    have := (min_le_right (d / 2) _).trans (min_le_right (ρ / 2) ((1 - ρ) / 2)); linarith
  have hlogm : |Real.log (ρ - ε) - Real.log ρ| < e / 4 := by
    have := hdb (x := ρ - ε) (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
    rwa [Real.dist_eq] at this
  have hlogp : |Real.log (ρ + ε) - Real.log ρ| < e / 4 := by
    have := hdb (x := ρ + ε) (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
    rwa [Real.dist_eq] at this
  obtain ⟨c, hc, C, hC, hb⟩ := sharp_convergence_rate h P hk hl h0 hε hερ hε1
  have hz : ∀ a : ℝ, Tendsto (fun t : ℕ => a / (t : ℝ)) atTop (𝓝 0) :=
    fun a => tendsto_const_div_atTop_nhds_zero_nat a
  filter_upwards [eventually_gt_atTop 0,
    (hz (Real.log c)).eventually (Metric.ball_mem_nhds 0 (by linarith : 0 < e / 4)),
    (hz (Real.log C)).eventually (Metric.ball_mem_nhds 0 (by linarith : 0 < e / 4))]
    with t ht hct hCt
  rw [Real.dist_eq, sub_zero] at hct hCt
  have htr : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  obtain ⟨hlo, hhi⟩ := hb t
  have hlpos : 0 < ρ - ε := by linarith
  have hlo' := Real.log_le_log (mul_pos hc (pow_pos hlpos t)) hlo
  have hhi' := Real.log_le_log ((mul_pos hc (pow_pos hlpos t)).trans_le hlo) hhi
  rw [Real.log_mul (ne_of_gt hc) (pow_pos hlpos t).ne', Real.log_pow] at hlo'
  rw [Real.log_mul (ne_of_gt hC) (pow_pos (by linarith) t).ne', Real.log_pow] at hhi'
  have h1 : Real.log c / t + Real.log (ρ - ε) ≤
      Real.log (Real.log (l t) - Real.log (k t)) / t := by
    rw [div_add' _ _ _ (ne_of_gt htr), div_le_div_iff_of_pos_right htr]; linarith
  have h2 : Real.log (Real.log (l t) - Real.log (k t)) / t ≤
      Real.log C / t + Real.log (ρ + ε) := by
    rw [div_add' _ _ _ (ne_of_gt htr), div_le_div_iff_of_pos_right htr]; linarith
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [(abs_lt.mp hct).1, (abs_lt.mp hlogm).1]
  · linarith [(abs_lt.mp hCt).2, (abs_lt.mp hlogp).2]

end Solow1956.DiscreteTime

#print axioms Solow1956.SolowSwan.capitalChange
#print axioms Solow1956.SolowSwan.hasDerivAt_capitalPerWorker
#print axioms Solow1956.SolowSwan.intensiveForm_of_homogeneous
#print axioms Solow1956.SolowSwan.SquareRoot.production
#print axioms Solow1956.SolowSwan.SquareRoot.steadyState
#print axioms Solow1956.SolowSwan.SquareRoot.steadyState_pos
#print axioms Solow1956.SolowSwan.SquareRoot.sqrt_steadyState
#print axioms Solow1956.SolowSwan.SquareRoot.capitalChange_zero
#print axioms Solow1956.SolowSwan.SquareRoot.capitalChange_factor
#print axioms Solow1956.SolowSwan.SquareRoot.capitalChange_steadyState
#print axioms Solow1956.SolowSwan.SquareRoot.eq_steadyState_of_pos
#print axioms Solow1956.SolowSwan.SquareRoot.capitalChange_eq_zero_iff
#print axioms Solow1956.SolowSwan.SquareRoot.existsUnique_positive_steadyState
#print axioms Solow1956.SolowSwan.SquareRoot.capitalChange_pos_of_lt
#print axioms Solow1956.SolowSwan.SquareRoot.capitalChange_neg_of_gt
#print axioms Solow1956.SolowSwan.SquareRoot.steadyState_strictMono_saving
#print axioms Solow1956.SolowSwan.SquareRoot.steadyState_strictMono_productivity
#print axioms Solow1956.SolowSwan.SquareRoot.steadyState_strictAnti_population
#print axioms Solow1956.SolowSwan.SquareRoot.steadyState_capital_output_ratio
#print axioms Solow1956.SolowSwan.hasDerivAt_capitalPerEffectiveWorker
#print axioms Solow1956.SolowSwan.CobbDouglas.rate
#print axioms Solow1956.SolowSwan.CobbDouglas.steadyState
#print axioms Solow1956.SolowSwan.CobbDouglas.transformedPath
#print axioms Solow1956.SolowSwan.CobbDouglas.path
#print axioms Solow1956.SolowSwan.CobbDouglas.steadyState_pos
#print axioms Solow1956.SolowSwan.CobbDouglas.rate_zero
#print axioms Solow1956.SolowSwan.CobbDouglas.rate_factor
#print axioms Solow1956.SolowSwan.CobbDouglas.steadyState_power
#print axioms Solow1956.SolowSwan.CobbDouglas.rate_steadyState
#print axioms Solow1956.SolowSwan.CobbDouglas.eq_steadyState_of_pos
#print axioms Solow1956.SolowSwan.CobbDouglas.existsUnique_positive_steadyState
#print axioms Solow1956.SolowSwan.CobbDouglas.rate_eq_zero_iff
#print axioms Solow1956.SolowSwan.CobbDouglas.transformedPath_zero
#print axioms Solow1956.SolowSwan.CobbDouglas.transformedPath_pos
#print axioms Solow1956.SolowSwan.CobbDouglas.path_pos
#print axioms Solow1956.SolowSwan.CobbDouglas.path_zero
#print axioms Solow1956.SolowSwan.CobbDouglas.hasDerivAt_transformedPath
#print axioms Solow1956.SolowSwan.CobbDouglas.hasDerivAt_power
#print axioms Solow1956.SolowSwan.CobbDouglas.hasDerivAt_path
#print axioms Solow1956.SolowSwan.CobbDouglas.eq_transformedPath_of_hasDerivAt
#print axioms Solow1956.SolowSwan.CobbDouglas.solution_eq_path
#print axioms Solow1956.SolowSwan.CobbDouglas.tendsto_transformedPath
#print axioms Solow1956.SolowSwan.CobbDouglas.tendsto_path
#print axioms Solow1956.SolowSwan.CobbDouglas.path_power_gap
#print axioms Solow1956.SolowSwan.CobbDouglas.IsPositiveSolution
#print axioms Solow1956.SolowSwan.CobbDouglas.positive_dynamics
#print axioms Solow1956.SolowSwan.CobbDouglas.rate_pos_of_lt
#print axioms Solow1956.SolowSwan.CobbDouglas.rate_neg_of_gt
#print axioms Solow1956.SolowSwan.CobbDouglas.steadyState_strictMono_investment
#print axioms Solow1956.SolowSwan.CobbDouglas.steadyState_strictAnti_dilution
#print axioms Solow1956.SolowSwan.CobbDouglas.steadyState_strictMono_saving
#print axioms Solow1956.SolowSwan.CobbDouglas.steadyState_capital_output_ratio
#print axioms Solow1956.SolowSwan.CobbDouglas.path_lt_steadyState_iff
#print axioms Solow1956.SolowSwan.CobbDouglas.tendsto_of_isPositiveSolution
#print axioms Solow1956.SolowSwan.CobbDouglas.path_monotoneOn_of_le
#print axioms Solow1956.SolowSwan.CobbDouglas.path_antitoneOn_of_le
#print axioms Solow1956.SolowSwan.CobbDouglas.tendsto_output
#print axioms Solow1956.SolowSwan.CobbDouglas.weightedCapital_monotoneOn
#print axioms Solow1956.SolowSwan.CobbDouglas.positive_of_nonnegative_solution
#print axioms Solow1956.SolowSwan.CobbDouglas.IsNonnegativeSolution
#print axioms Solow1956.SolowSwan.CobbDouglas.IsNonnegativeSolution.isPositiveSolution
#print axioms Solow1956.SolowSwan.CobbDouglas.nonnegative_dynamics
#print axioms Solow1956.SolowSwan.CobbDouglas.example_positive_path
#print axioms Solow1956.SolowSwan.CobbDouglas.normalized_steadyState
#print axioms Solow1956.SolowSwan.CobbDouglas.zero_solution
#print axioms Solow1956.SolowSwan.CobbDouglas.zero_solution_not_positive
#print axioms Solow1956.SolowSwan.CobbDouglas.no_positive_stationary_at_exponent_one
#print axioms Solow1956.SolowSwan.CobbDouglas.hasDerivAt_effectiveLabour
#print axioms Solow1956.ODE.exists_global_solution
#print axioms Solow1956.ODE.clip
#print axioms Solow1956.ODE.clip_mem
#print axioms Solow1956.ODE.clip_eq
#print axioms Solow1956.ODE.monotone_clip
#print axioms Solow1956.ODE.lipschitz_clip
#print axioms Solow1956.ODE.bounded_lipschitz_clip
#print axioms Solow1956.ODE.linear_lower_bound_on
#print axioms Solow1956.ODE.linear_upper_bound_on
#print axioms Solow1956.ODE.linear_lower_bound
#print axioms Solow1956.ODE.linear_upper_bound
#print axioms Solow1956.ODE.not_bounded_below_of_negative_drift
#print axioms Solow1956.ODE.not_bounded_above_of_positive_drift
#print axioms Solow1956.ODE.derivative_limit_zero
#print axioms Solow1956.ODE.exists_limit_of_monotone_bounded
#print axioms Solow1956.ODE.exists_limit_of_antitone_bounded
#print axioms Solow1956.ODE.exponential_lower_bound
#print axioms Solow1956.ODE.exists_attracting_scalar_path
#print axioms Solow1956.Neoclassical.Technology
#print axioms Solow1956.Neoclassical.Technology.mk
#print axioms Solow1956.Neoclassical.Technology.continuous
#print axioms Solow1956.Neoclassical.Technology.zero
#print axioms Solow1956.Neoclassical.Technology.differentiable
#print axioms Solow1956.Neoclassical.Technology.derivative_continuous
#print axioms Solow1956.Neoclassical.Technology.concave
#print axioms Solow1956.Neoclassical.Technology.marginal_positive
#print axioms Solow1956.Neoclassical.Technology.inada_zero
#print axioms Solow1956.Neoclassical.Technology.inada_top
#print axioms Solow1956.Neoclassical.technology_of_second_derivative
#print axioms Solow1956.Neoclassical.Technology.marginal_strictAnti
#print axioms Solow1956.Neoclassical.Technology.output_gap
#print axioms Solow1956.Neoclassical.Technology.output_pos
#print axioms Solow1956.Neoclassical.Technology.output_nonneg
#print axioms Solow1956.Neoclassical.Technology.output_strictMono
#print axioms Solow1956.Neoclassical.Technology.average_strictAnti
#print axioms Solow1956.Neoclassical.rate
#print axioms Solow1956.Neoclassical.rate_zero
#print axioms Solow1956.Neoclassical.rate_hasDerivAt
#print axioms Solow1956.Neoclassical.rate_derivative_continuous
#print axioms Solow1956.Neoclassical.Technology.exists_capacity
#print axioms Solow1956.Neoclassical.existsUnique_steadyState
#print axioms Solow1956.Neoclassical.rate_pos_below
#print axioms Solow1956.Neoclassical.rate_neg_above
#print axioms Solow1956.Neoclassical.capital_lower_bound
#print axioms Solow1956.Neoclassical.capital_positive
#print axioms Solow1956.Neoclassical.path_unique
#print axioms Solow1956.Neoclassical.general_solow
#print axioms Solow1956.Neoclassical.output_consumption_limit
#print axioms Solow1956.Neoclassical.capitalAtRatio
#print axioms Solow1956.Neoclassical.capitalAtRatio_spec
#print axioms Solow1956.Neoclassical.capitalAtRatio_average
#print axioms Solow1956.Neoclassical.capitalAtRatio_strictAnti
#print axioms Solow1956.Neoclassical.averageSlope
#print axioms Solow1956.Neoclassical.averageSlope_neg
#print axioms Solow1956.Neoclassical.average_hasStrictDerivAt
#print axioms Solow1956.Neoclassical.capitalAtRatio_hasDerivAt
#print axioms Solow1956.Neoclassical.steadyCapital
#print axioms Solow1956.Neoclassical.steadyCapital_spec
#print axioms Solow1956.Neoclassical.steadyCapital_eq
#print axioms Solow1956.Neoclassical.steadyCapital_strictMono_saving
#print axioms Solow1956.Neoclassical.steadyCapital_strictAnti_dilution
#print axioms Solow1956.Neoclassical.savingResponse
#print axioms Solow1956.Neoclassical.dilutionResponse
#print axioms Solow1956.Neoclassical.steadyCapital_hasDerivAt_saving
#print axioms Solow1956.Neoclassical.steadyCapital_hasDerivAt_dilution
#print axioms Solow1956.Neoclassical.savingResponse_pos
#print axioms Solow1956.Neoclassical.dilutionResponse_neg
#print axioms Solow1956.Neoclassical.steadyCapital_derivative_signs
#print axioms Solow1956.Neoclassical.output_derivative_signs
#print axioms Solow1956.Neoclassical.acemoglu_capital_partials
#print axioms Solow1956.Neoclassical.acemoglu_output_partials
#print axioms Solow1956.Neoclassical.existsUnique_marginal_root
#print axioms Solow1956.Neoclassical.golden_rule_maximizes
#print axioms Solow1956.Neoclassical.sustainingSaving
#print axioms Solow1956.Neoclassical.sustainingSaving_bounds
#print axioms Solow1956.Neoclassical.sustainingSaving_equilibrium
#print axioms Solow1956.Neoclassical.sustainingSaving_stock
#print axioms Solow1956.Neoclassical.sustainingSaving_strictMono
#print axioms Solow1956.Neoclassical.stationary_consumption_identity
#print axioms Solow1956.Neoclassical.exists_unique_golden_saving
#print axioms Solow1956.Neoclassical.cass_stationary_bridge
#print axioms Solow1956.Neoclassical.every_path_converges
#print axioms Solow1956.Neoclassical.path_stable
#print axioms Solow1956.Neoclassical.saving_increase_transition
#print axioms Solow1956.Neoclassical.effective_labour_convergence
#print axioms Solow1956.Neoclassical.technology_rpow
#print axioms Solow1956.Neoclassical.Technology.add
#print axioms Solow1956.Neoclassical.mixed_power_technology
#print axioms Solow1956.Neoclassical.mixed_power_steady_exists
#print axioms Solow1956.Neoclassical.no_positive_steady_without_dilution
#print axioms Solow1956.Neoclassical.linear_technology_multiple_steady
#print axioms Solow1956.Neoclassical.IsPath
#print axioms Solow1956.Neoclassical.IsPath.mk
#print axioms Solow1956.Neoclassical.IsPath.initial_pos
#print axioms Solow1956.Neoclassical.IsPath.nonneg
#print axioms Solow1956.Neoclassical.IsPath.hasDerivAt
#print axioms Solow1956.Neoclassical.growthRate
#print axioms Solow1956.Neoclassical.convergenceSpeed
#print axioms Solow1956.Neoclassical.rate_div_eq_growthRate
#print axioms Solow1956.Neoclassical.growthRate_strictAnti
#print axioms Solow1956.Neoclassical.convergenceSpeed_pos
#print axioms Solow1956.Neoclassical.convergenceSpeed_continuousOn
#print axioms Solow1956.Neoclassical.convergenceSpeed_steady
#print axioms Solow1956.Neoclassical.convergenceSpeed_steady_share
#print axioms Solow1956.Neoclassical.IsPath.pos
#print axioms Solow1956.Neoclassical.isPath_steady
#print axioms Solow1956.Neoclassical.IsPath.bounds
#print axioms Solow1956.Neoclassical.IsPath.tendsto
#print axioms Solow1956.Neoclassical.path_eq_of_meet
#print axioms Solow1956.Neoclassical.paths_ordered
#print axioms Solow1956.Neoclassical.poorer_grows_faster
#print axioms Solow1956.Neoclassical.hasDerivAt_log_gap
#print axioms Solow1956.Neoclassical.log_gap_strictAnti
#print axioms Solow1956.Neoclassical.absolute_convergence
#print axioms Solow1956.Neoclassical.growthRate_gap_ge
#print axioms Solow1956.Neoclassical.growthRate_gap_le
#print axioms Solow1956.Neoclassical.log_gap_upper
#print axioms Solow1956.Neoclassical.log_gap_lower
#print axioms Solow1956.Neoclassical.paths_window
#print axioms Solow1956.Neoclassical.log_gap_le_of_speed_bound
#print axioms Solow1956.Neoclassical.log_gap_pos
#print axioms Solow1956.Neoclassical.exists_uniform_rate
#print axioms Solow1956.Neoclassical.absolute_convergence_rate
#print axioms Solow1956.Neoclassical.log_gap_steady_le
#print axioms Solow1956.Neoclassical.level_gap_le
#print axioms Solow1956.Neoclassical.sharp_convergence_rate
#print axioms Solow1956.Neoclassical.log_gap_rate_tendsto
#print axioms Solow1956.Neoclassical.cobbDouglas_speed
#print axioms Solow1956.DiscreteTime.Map.attracting_orbit
#print axioms Solow1956.DiscreteTime.Params
#print axioms Solow1956.DiscreteTime.Params.mk
#print axioms Solow1956.DiscreteTime.Params.saving_pos
#print axioms Solow1956.DiscreteTime.Params.depreciation_le_one
#print axioms Solow1956.DiscreteTime.Params.growth_pos
#print axioms Solow1956.DiscreteTime.Params.dilution_pos
#print axioms Solow1956.DiscreteTime.next
#print axioms Solow1956.DiscreteTime.steady
#print axioms Solow1956.DiscreteTime.next_sub_self
#print axioms Solow1956.DiscreteTime.next_acemoglu
#print axioms Solow1956.DiscreteTime.next_zero
#print axioms Solow1956.DiscreteTime.next_pos
#print axioms Solow1956.DiscreteTime.next_nonneg
#print axioms Solow1956.DiscreteTime.next_strictMono
#print axioms Solow1956.DiscreteTime.next_continuousOn
#print axioms Solow1956.DiscreteTime.next_hasDerivAt
#print axioms Solow1956.DiscreteTime.next_eq_self_iff
#print axioms Solow1956.DiscreteTime.existsUnique_steadyState
#print axioms Solow1956.DiscreteTime.steady_spec
#print axioms Solow1956.DiscreteTime.steady_eq
#print axioms Solow1956.DiscreteTime.zero_fixed
#print axioms Solow1956.DiscreteTime.steady_state_equilibrium
#print axioms Solow1956.DiscreteTime.next_gt_self
#print axioms Solow1956.DiscreteTime.next_lt_self
#print axioms Solow1956.DiscreteTime.slope_at_steady
#print axioms Solow1956.DiscreteTime.IsPath
#print axioms Solow1956.DiscreteTime.IsPath.mk
#print axioms Solow1956.DiscreteTime.IsPath.initial_pos
#print axioms Solow1956.DiscreteTime.IsPath.succ
#print axioms Solow1956.DiscreteTime.path
#print axioms Solow1956.DiscreteTime.path_zero
#print axioms Solow1956.DiscreteTime.path_succ
#print axioms Solow1956.DiscreteTime.isPath_path
#print axioms Solow1956.DiscreteTime.path_unique
#print axioms Solow1956.DiscreteTime.IsPath.eq_path
#print axioms Solow1956.DiscreteTime.path_nonneg
#print axioms Solow1956.DiscreteTime.path_of_zero
#print axioms Solow1956.DiscreteTime.general_solow
#print axioms Solow1956.DiscreteTime.IsPath.orbit
#print axioms Solow1956.DiscreteTime.IsPath.pos
#print axioms Solow1956.DiscreteTime.IsPath.tendsto
#print axioms Solow1956.DiscreteTime.IsPath.bounds
#print axioms Solow1956.DiscreteTime.output_consumption_limit
#print axioms Solow1956.DiscreteTime.steady_strictMono_saving
#print axioms Solow1956.DiscreteTime.steady_strictAnti_depreciation
#print axioms Solow1956.DiscreteTime.steady_strictAnti_growth
#print axioms Solow1956.DiscreteTime.steady_derivative_signs
#print axioms Solow1956.DiscreteTime.steady_rewrite
#print axioms Solow1956.DiscreteTime.acemoglu_capital_partials
#print axioms Solow1956.DiscreteTime.acemoglu_output_partials
#print axioms Solow1956.DiscreteTime.stationary_consumption
#print axioms Solow1956.DiscreteTime.exists_unique_golden_saving
#print axioms Solow1956.DiscreteTime.acemoglu_golden_rule
#print axioms Solow1956.DiscreteTime.cass_stationary_bridge
#print axioms Solow1956.DiscreteTime.every_path_converges
#print axioms Solow1956.DiscreteTime.path_stable
#print axioms Solow1956.DiscreteTime.path_stable_initial
#print axioms Solow1956.DiscreteTime.saving_increase_transition
#print axioms Solow1956.DiscreteTime.capitalPerEffectiveWorker_succ
#print axioms Solow1956.DiscreteTime.effective_labour_convergence
#print axioms Solow1956.DiscreteTime.wage
#print axioms Solow1956.DiscreteTime.wage_strictMono
#print axioms Solow1956.DiscreteTime.factor_prices
#print axioms Solow1956.DiscreteTime.example_params
#print axioms Solow1956.DiscreteTime.mixed_power_fixed_exists
#print axioms Solow1956.DiscreteTime.mixed_power_converges
#print axioms Solow1956.DiscreteTime.no_positive_fixed_without_dilution
#print axioms Solow1956.DiscreteTime.depreciation_above_one_breaks_positivity
#print axioms Solow1956.DiscreteTime.linear_technology_multiple_fixed
#print axioms Solow1956.DiscreteTime.capitalPerWorker_succ
#print axioms Solow1956.DiscreteTime.next_sub_self_net
#print axioms Solow1956.DiscreteTime.SquareRoot.next_production
#print axioms Solow1956.DiscreteTime.SquareRoot.next_zero
#print axioms Solow1956.DiscreteTime.SquareRoot.next_eq_self_iff
#print axioms Solow1956.DiscreteTime.SquareRoot.existsUnique_positive_fixed
#print axioms Solow1956.DiscreteTime.SquareRoot.lt_next_of_lt
#print axioms Solow1956.DiscreteTime.SquareRoot.next_lt_of_gt
#print axioms Solow1956.DiscreteTime.SquareRoot.params
#print axioms Solow1956.DiscreteTime.SquareRoot.steady_eq_steadyState
#print axioms Solow1956.DiscreteTime.SquareRoot.global_dynamics
#print axioms Solow1956.DiscreteTime.SquareRoot.fixed_capital_output_ratio
#print axioms Solow1956.DiscreteTime.CobbDouglas.steady_eq
#print axioms Solow1956.DiscreteTime.CobbDouglas.next_zero
#print axioms Solow1956.DiscreteTime.CobbDouglas.next_full_depreciation
#print axioms Solow1956.DiscreteTime.CobbDouglas.path_full_depreciation
#print axioms Solow1956.DiscreteTime.CobbDouglas.log_gap_full_depreciation
#print axioms Solow1956.DiscreteTime.CobbDouglas.tendsto_path_full_depreciation
#print axioms Solow1956.DiscreteTime.CobbDouglas.positive_dynamics
#print axioms Solow1956.DiscreteTime.CobbDouglas.tendsto_of_isPath
#print axioms Solow1956.DiscreteTime.CobbDouglas.path_lt_steadyState_iff
#print axioms Solow1956.DiscreteTime.CobbDouglas.path_strictMono_of_lt
#print axioms Solow1956.DiscreteTime.CobbDouglas.path_strictAnti_of_gt
#print axioms Solow1956.DiscreteTime.CobbDouglas.lt_next_iff
#print axioms Solow1956.DiscreteTime.CobbDouglas.tendsto_output
#print axioms Solow1956.DiscreteTime.CobbDouglas.steady_strictMono_investment
#print axioms Solow1956.DiscreteTime.CobbDouglas.steady_strictAnti_dilution
#print axioms Solow1956.DiscreteTime.CobbDouglas.steady_capital_output_ratio
#print axioms Solow1956.DiscreteTime.CobbDouglas.example_params
#print axioms Solow1956.DiscreteTime.CobbDouglas.example_path
#print axioms Solow1956.DiscreteTime.CobbDouglas.example_converges
#print axioms Solow1956.DiscreteTime.CobbDouglas.normalized_steady
#print axioms Solow1956.DiscreteTime.CobbDouglas.zero_fixed
#print axioms Solow1956.DiscreteTime.CobbDouglas.zero_orbit_not_isPath
#print axioms Solow1956.DiscreteTime.CobbDouglas.no_positive_fixed_at_exponent_one
#print axioms Solow1956.DiscreteTime.CobbDouglas.effectiveLabour_succ
#print axioms Solow1956.DiscreteTime.growthFactor
#print axioms Solow1956.DiscreteTime.contraction
#print axioms Solow1956.DiscreteTime.next_div_eq_growthFactor
#print axioms Solow1956.DiscreteTime.growthFactor_strictAnti
#print axioms Solow1956.DiscreteTime.gross_pos
#print axioms Solow1956.DiscreteTime.contraction_pos
#print axioms Solow1956.DiscreteTime.contraction_lt_one
#print axioms Solow1956.DiscreteTime.contraction_continuousOn
#print axioms Solow1956.DiscreteTime.contraction_steady
#print axioms Solow1956.DiscreteTime.contraction_steady_eq
#print axioms Solow1956.DiscreteTime.cobbDouglas_contraction
#print axioms Solow1956.DiscreteTime.isPath_steady
#print axioms Solow1956.DiscreteTime.path_eq_of_meet
#print axioms Solow1956.DiscreteTime.paths_ordered
#print axioms Solow1956.DiscreteTime.poorer_grows_faster
#print axioms Solow1956.DiscreteTime.log_gap_pos
#print axioms Solow1956.DiscreteTime.log_gap_strictAnti
#print axioms Solow1956.DiscreteTime.absolute_convergence
#print axioms Solow1956.DiscreteTime.hasDerivAt_log_next_sub
#print axioms Solow1956.DiscreteTime.log_next_gap_le
#print axioms Solow1956.DiscreteTime.log_next_gap_ge
#print axioms Solow1956.DiscreteTime.log_gap_upper
#print axioms Solow1956.DiscreteTime.log_gap_lower
#print axioms Solow1956.DiscreteTime.paths_window
#print axioms Solow1956.DiscreteTime.log_gap_le_of_contraction_bound
#print axioms Solow1956.DiscreteTime.exists_uniform_rate
#print axioms Solow1956.DiscreteTime.absolute_convergence_rate
#print axioms Solow1956.DiscreteTime.log_gap_steady_le
#print axioms Solow1956.DiscreteTime.level_gap_le
#print axioms Solow1956.DiscreteTime.eventually_contraction_window
#print axioms Solow1956.DiscreteTime.log_gap_ratio_tendsto
#print axioms Solow1956.DiscreteTime.sharp_convergence_rate
#print axioms Solow1956.DiscreteTime.log_gap_rate_tendsto
