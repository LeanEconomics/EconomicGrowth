import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Checked polynomial identities for Ramsey–Cass–Koopmans verification

The correspondingly named TheoryDebugger cases are stored under
`verification/theorydebugger/inputs`. Their generated certificates independently
check the exact polynomial abstractions with Lean. This module provides reusable
named lemmas, without importing the generated certificates' shared namespace.

None of these algebra lemmas alone asserts existence or optimality of a path.
-/

namespace RamseyCassKoopmans

/-- Discounting cancels the pure-discount term in the current-value costate law. -/
theorem discounted_costate_normalization (qdot d m q u fprime : ℝ)
    (h : qdot = (d + m) * q - u * fprime) :
    qdot - d * q = m * q - u * fprime := by
  rw [h]
  ring

/-- Normalized boundary derivative after the two capital laws and the costate
law are substituted. `K` and `Z` are candidate-minus-competitor gaps. -/
theorem present_value_boundary_derivative (p m w u fprime K Z : ℝ) :
    (m * p - w * u * fprime) * K + p * (Z - m * K) =
      p * Z - w * u * fprime * K := by
  ring

/-- Pointwise counterpart of the finite-horizon welfare identity. `bdot` is the
derivative of the discounted capital-value gap divided by the discount factor.
The named feasibility and costate equations are explicit; the TheoryDebugger
case `cass_pointwise_welfare_identity` substitutes these same equations first
and uses candidate-minus-competitor gap variables. -/
theorem cass_pointwise_welfare_identity
    (U0 U1 f0 f1 c0 c1 z0 z1 k0 k1 fprime u q m d qdot k0dot k1dot : ℝ)
    (hresource0 : c0 + z0 = f0) (hresource1 : c1 + z1 = f1)
    (hcapital0 : k0dot = z0 - m * k0) (hcapital1 : k1dot = z1 - m * k1)
    (hcostate : qdot = (d + m) * q - u * fprime) :
    U0 - U1 =
      (U0 - U1 - u * (c0 - c1)) +
      u * (f0 - f1 - fprime * (k0 - k1)) +
      (q - u) * (z0 - z1) -
      ((qdot - d * q) * (k0 - k1) + q * (k0dot - k1dot)) := by
  rw [← hresource0, ← hresource1, hcapital0, hcapital1, hcostate]
  ring

/-- Present-value formulation of the same decomposition. This matches
TheoryDebugger's `present_value_welfare_identity` after feasibility substitution
and the separately checked `present_value_boundary_derivative` identity. -/
theorem present_value_welfare_identity
    (Ua Ub fa fb ca cb za zb ka kb mp mu p m w pd : ℝ)
    (hresourceA : ca + za = fa) (hresourceB : cb + zb = fb)
    (hcostate : pd = m * p - w * mu * mp) :
    w * (Ua - Ub) +
      (pd * (ka - kb) + p * ((za - m * ka) - (zb - m * kb))) =
      w * (Ua - Ub - mu * (ca - cb)) +
      w * mu * (fa - fb - mp * (ka - kb)) +
      (p - w * mu) * (za - zb) := by
  rw [← hresourceA, ← hresourceB, hcostate]
  ring

/-- Supporting inequalities, nonnegative welfare weight and allocation
complementarity give the pointwise comparison used by the analytic theorem. -/
theorem present_value_comparison_nonneg
    (Ua Ub fa fb ca cb za zb ka kb mp mu p m w pd : ℝ)
    (hresourceA : ca + za = fa) (hresourceB : cb + zb = fb)
    (hutility : 0 ≤ Ua - Ub - mu * (ca - cb))
    (htechnology : 0 ≤ fa - fb - mp * (ka - kb))
    (hw : 0 ≤ w) (hmu : 0 ≤ mu)
    (hallocation : 0 ≤ (p - w * mu) * (za - zb))
    (hcostate : pd = m * p - w * mu * mp) :
    0 ≤ w * (Ua - Ub) +
      (pd * (ka - kb) + p * ((za - m * ka) - (zb - m * kb))) := by
  rw [present_value_welfare_identity Ua Ub fa fb ca cb za zb ka kb mp mu p m w pd
    hresourceA hresourceB hcostate]
  exact add_nonneg (add_nonneg (mul_nonneg hw hutility)
    (mul_nonneg (mul_nonneg hw hmu) htechnology)) hallocation

/-- Complementarity permits a strict costate gap at zero investment. -/
theorem corner_does_not_imply_euler_equality :
    ¬ (∀ (u q z : ℝ), 0 < u → 0 < q → 0 ≤ z → q ≤ u →
      (q - u) * z = 0 → q = u) := by
  intro h
  have hx := h 2 1 0 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at hx

/-- Strictly positive investment repairs the Euler-equality inference. -/
theorem interior_implies_euler_equality (u q z : ℝ)
    (hcomplementarity : (q - u) * z = 0) (hz : 0 < z) : q = u := by
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcomplementarity).resolve_right (ne_of_gt hz))

/-- The candidate's complementarity conditions make the investment gap term
nonnegative for every competitor with nonnegative investment. -/
theorem complementarity_welfare_term (u q z otherz : ℝ)
    (hgap : q ≤ u) (hcomplementarity : (q - u) * z = 0)
    (hother : 0 ≤ otherz) : 0 ≤ (q - u) * (z - otherz) := by
  have hprod : (q - u) * otherz ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
    (sub_nonpos.mpr hgap) hother
  nlinarith

/-- Concavity remainders and the complementarity remainder add nonnegatively. -/
theorem nonnegative_welfare_remainders (RU RF Rz u : ℝ)
    (hRU : 0 ≤ RU) (hRF : 0 ≤ RF) (hRz : 0 ≤ Rz) (hu : 0 ≤ u) :
    0 ≤ RU + u * RF + Rz := by
  positivity

/-- The competitor-minus-candidate welfare bound uses candidate-minus-competitor
terminal capital. This is an algebraic implication, not an integration theorem. -/
theorem correct_terminal_bound (A p k0 k1 : ℝ)
    (h : A ≤ -1 * p * (k1 - k0)) : A ≤ p * (k0 - k1) := by
  nlinarith

/-- Reversing that terminal-capital sign is invalid even for positive prices
and positive terminal capital in both paths. -/
theorem reversed_terminal_bound_is_invalid :
    ¬ (∀ (A p k0 k1 : ℝ), 0 < p → A ≤ -1 * p * (k1 - k0) →
      A ≤ p * (k1 - k0)) := by
  intro h
  have hx := h 1 1 2 1 (by norm_num) (by norm_num)
  norm_num at hx

/-- Population weighting cancels population growth from the stationary rate. -/
theorem population_weighted_stationary_rate (d m rho n depreciation : ℝ)
    (hd : d = rho - n) (hm : m = n + depreciation) :
    d + m = rho + depreciation := by
  linarith

end RamseyCassKoopmans
