/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/
import UzawaModern.Growth.UzawaSeparation
import UzawaModern.Growth.UzawaExamples
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Nonvacuity and an economic application of the repaired elasticity proof -/

namespace UzawaModern.UzawaSeparation.Examples

open Technology

theorem sqrt_share {b k : ℝ} (hb : 0 < b) (hk : 0 < k) :
    (b / (2 * Real.sqrt k)) * k / (b * Real.sqrt k) = 1 / 2 := by
  have hs := Real.sqrt_pos.mpr hk
  have hsq := Real.sq_sqrt hk.le
  field_simp
  nlinarith

theorem sqrt_ratio_square {b x : ℝ} (hb : 0 < b) (hx : 0 < x) :
    (b * x) ^ 2 / (b * Real.sqrt ((b * x) ^ 2)) = x := by
  rw [Real.sqrt_sq (mul_pos hb hx).le]
  field_simp

/-- Every positive multiplier path supplies the full coordinate structure,
including surjectivity onto all positive capital/output ratios. -/
noncomputable def sqrtTechnology (b : ℝ → ℝ) (hb : ∀ t, 0 < b t) : Technology where
  output t k := b t * Real.sqrt k
  marginal t k := b t / (2 * Real.sqrt k)
  output_pos t k hk := mul_pos (hb t) (Real.sqrt_pos.mpr hk)
  hasDerivAt_output t k hk := by
    convert! (Real.hasDerivAt_sqrt (ne_of_gt hk)).const_mul (b t) using 1
    ring
  share_lt_one t k hk := by rw [sqrt_share (hb t) hk]; norm_num
  ratio_surjective t x hx :=
    ⟨(b t * x) ^ 2, sq_pos_of_pos (mul_pos (hb t) hx), sqrt_ratio_square (hb t) hx⟩

theorem sqrt_capital (b : ℝ → ℝ) (hb : ∀ t, 0 < b t) (t : ℝ)
    {x : ℝ} (hx : 0 < x) :
    (sqrtTechnology b hb).capital t x = (b t * x) ^ 2 := by
  have hk := sq_pos_of_pos (mul_pos (hb t) hx)
  have h := (sqrtTechnology b hb).capital_ratio t hk
  have hr : (sqrtTechnology b hb).ratio t ((b t * x) ^ 2) = x :=
    sqrt_ratio_square (hb t) hx
  rwa [hr] at h

theorem sqrt_phi (b : ℝ → ℝ) (hb : ∀ t, 0 < b t) (t : ℝ)
    {x : ℝ} (hx : 0 < x) : (sqrtTechnology b hb).phi t x = (b t) ^ 2 * x := by
  unfold Technology.phi
  rw [sqrt_capital b hb t hx]
  change b t * Real.sqrt ((b t * x) ^ 2) = _
  rw [Real.sqrt_sq (mul_pos (hb t) hx).le]
  ring

theorem sqrt_shares_invariant (b : ℝ → ℝ) (hb : ∀ t, 0 < b t) (reference : ℝ) :
    (sqrtTechnology b hb).SharesInvariant reference := by
  intro t x hx
  change b t / (2 * Real.sqrt _) * _ / (b t * Real.sqrt _) =
    b reference / (2 * Real.sqrt _) * _ / (b reference * Real.sqrt _)
  rw [sqrt_share (hb t) ((sqrtTechnology b hb).capital_pos t hx),
    sqrt_share (hb reference) ((sqrtTechnology b hb).capital_pos reference hx)]

theorem sqrt_technology (b : ℝ → ℝ) (hb : ∀ t, 0 < b t) (reference t : ℝ) :
    (sqrtTechnology b hb).technology reference t = (b t) ^ 2 / (b reference) ^ 2 := by
  simp only [Technology.technology, sqrt_phi b hb _ zero_lt_one, mul_one]

/-- The same positive-investment economy used for the Schlicht proof. -/
noncomputable def growingTechnology : Technology :=
  sqrtTechnology (fun t => 4 * Real.exp t) (fun t => mul_pos (by norm_num) (Real.exp_pos t))

theorem growing_shares_invariant : growingTechnology.SharesInvariant 0 :=
  sqrt_shares_invariant _ _ 0

theorem growing_production (t : ℝ) : Uzawa.Examples.growingEconomy.output t =
    growingTechnology.production t (Uzawa.Examples.growingEconomy.capital t)
      (Uzawa.Examples.growingEconomy.labor t) := by
  have h := Uzawa.Examples.production_on_path t
  simpa only [Technology.production, growingTechnology, sqrtTechnology,
    Uzawa.Examples.production, Uzawa.BalancedGrowthData.labor,
    Uzawa.Examples.growingEconomy, Uzawa.trajectory, zero_mul,
    Real.exp_zero, mul_one, one_mul, div_one] using h

/-- All premises of the repaired proof are checked, including the global
inverse range and share quantifier. The final theorem uses separation. -/
theorem growing_labor_augmenting (t : ℝ) (ht : 0 ≤ t) :
    Uzawa.Examples.growingEconomy.output t = growingTechnology.production 0
      (Uzawa.Examples.growingEconomy.capital t)
      (Uzawa.Examples.growingEconomy.technology t * Uzawa.Examples.growingEconomy.labor t) := by
  exact growingTechnology.repaired_labor_augmenting_representation
    Uzawa.Examples.growingEconomy growing_shares_invariant
    (by norm_num [Uzawa.Examples.growingEconomy])
    (by norm_num [Uzawa.Examples.growingEconomy])
    (by norm_num [Uzawa.Examples.growingEconomy])
    (by norm_num [Uzawa.Examples.growingEconomy])
    (fun u _ => Uzawa.Examples.resource u)
    (fun u _ => Uzawa.Examples.accumulation u)
    (fun u _ => growing_production u) t ht

/-- The inferred technology factor has rate 2, matching output per worker. -/
theorem growing_technology (t : ℝ) (ht : 0 ≤ t) :
    growingTechnology.technology 0 t = Real.exp (2 * t) := by
  have h := growingTechnology.technology_eq_balanced_growth
    Uzawa.Examples.growingEconomy growing_shares_invariant
    (by norm_num [Uzawa.Examples.growingEconomy])
    (by norm_num [Uzawa.Examples.growingEconomy])
    (by norm_num [Uzawa.Examples.growingEconomy])
    (by norm_num [Uzawa.Examples.growingEconomy])
    (fun u _ => Uzawa.Examples.resource u)
    (fun u _ => Uzawa.Examples.accumulation u)
    (fun u _ => growing_production u) t ht
  simpa [Uzawa.BalancedGrowthData.technology, Uzawa.Examples.growingEconomy] using h

end UzawaModern.UzawaSeparation.Examples
