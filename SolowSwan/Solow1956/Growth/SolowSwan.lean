/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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
