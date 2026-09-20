/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Independent checks prompted by comparing Jones-Scrimgeour (2004, 2008)
and Schlicht (2006). These are research audit lemmas, not a completed
formalization of the 2004 paper's neoclassical model or its proof.
-/

namespace UzawaModern.VersionAudit

/-- Zero investment can coexist with positive capital: the coefficient
`gK + depreciation` can be zero. This is the omitted branch in Schlicht. -/
theorem zero_investment_positive_capital :
    (0 + (0 : ℝ)) * 1 = 0 ∧ (0 : ℝ) < 1 := by norm_num

/-- Two observations with fixed capital and proportional effective labor/output
are incompatible with CRS and strict increase in capital. This rules out ANY
such G, rather than only the frozen original production function. -/
theorem no_strict_capital_representation {G : ℝ → ℝ → ℝ} {A b : ℝ}
    (hA : 0 < A) (hb : 1 < b)
    (hCRS : ∀ K L s, 0 < K → 0 < L → 0 < s →
      G (s * K) (s * L) = s * G K L)
    (hinc : StrictMonoOn (fun K => G K A) (Set.Ioi 0))
    (hbase : G 1 A = 1) (hlater : G 1 (b * A) = b) : False := by
  have hbpos : 0 < b := lt_trans zero_lt_one hb
  have hbne : b ≠ 0 := ne_of_gt hbpos
  have hscaled : (1 / b) * (b * A) = A := by field_simp
  have hvalue : G (1 / b) A = 1 := by
    have h := hCRS 1 (b * A) (1 / b) zero_lt_one
      (mul_pos hbpos hA) (one_div_pos.mpr hbpos)
    simpa only [mul_one, hscaled, hlater, one_div_mul_cancel hbne] using h
  have hless : 1 / b < (1 : ℝ) := (div_lt_one hbpos).mpr hb
  have h := hinc (one_div_pos.mpr hbpos) (by norm_num) hless
  change G (1 / b) A < G 1 A at h
  rw [hvalue, hbase] at h
  exact lt_irrefl _ h

/-- Apply the two-point obstruction to A(t)=a*exp(t), Y(t)=exp(t), K(t)=1.
Every positive normalization a is covered. Exponential path assumptions
are explicit; the production model's curvature/Inada properties are not
asserted to have been formalized by this lemma. -/
theorem zero_investment_no_neoclassical_representation
    {G : ℝ → ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hCRS : ∀ K L s, 0 < K → 0 < L → 0 < s →
      G (s * K) (s * L) = s * G K L)
    (hinc : StrictMonoOn (fun K => G K a) (Set.Ioi 0))
    (hpath : ∀ t, 0 ≤ t → G 1 (a * Real.exp t) = Real.exp t) : False := by
  apply no_strict_capital_representation ha
    (Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)) hCRS hinc
  · simpa using hpath 0 le_rfl
  · simpa [mul_comm] using hpath 1 (by norm_num)


end UzawaModern.VersionAudit
