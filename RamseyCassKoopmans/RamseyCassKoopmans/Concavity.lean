import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Linarith

/-!
# Supporting inequalities from actual concave functions

These results connect utility and production concavity to the tangent bounds
used in the welfare verification theorem. They include competitors on either
side of the candidate, and do not assume the desired supporting inequality.
Only the derivative at the candidate point is required.
-/

namespace RamseyCassKoopmans

open Set

/-- A differentiable concave function lies below its tangent at the candidate.
The competitor may be on either side, or equal to the candidate. -/
theorem concave_support {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
    (hconc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hderiv : HasDerivAt f f' x) :
    f y - f x ≤ f' * (y - x) := by
  rcases lt_trichotomy y x with hlt | heq | hgt
  · have hs := hconc.le_slope_of_hasDerivAt hy hx hlt hderiv
    rw [slope_def_field] at hs
    have hmul := (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    nlinarith
  · subst y
    simp
  · have hs := hconc.slope_le_of_hasDerivAt hx hy hgt hderiv
    rw [slope_def_field] at hs
    exact (div_le_iff₀ (sub_pos.mpr hgt)).mp hs

/-- Strict concavity makes the tangent inequality strict at every distinct
competitor, including admissible endpoints of the domain. -/
theorem strict_concave_support {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
    (hconc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hderiv : HasDerivAt f f' x) (hne : y ≠ x) :
    f y - f x < f' * (y - x) := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hs := hconc.lt_slope_of_hasDerivAt hy hx hlt hderiv
    rw [slope_def_field] at hs
    have hmul := (lt_div_iff₀ (sub_pos.mpr hlt)).mp hs
    nlinarith
  · have hs := hconc.slope_lt_of_hasDerivAt hx hy hgt hderiv
    rw [slope_def_field] at hs
    exact (div_lt_iff₀ (sub_pos.mpr hgt)).mp hs

/-- The source welfare comparison's concavity remainder is nonnegative. -/
theorem concavity_remainder_nonneg {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
    (hconc : ConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hderiv : HasDerivAt f f' x) :
    0 ≤ f x - f y - f' * (x - y) := by
  have h := concave_support hconc hx hy hderiv
  nlinarith

/-- A distinct competitor gives a strictly positive concavity remainder. -/
theorem concavity_remainder_pos {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
    (hconc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hderiv : HasDerivAt f f' x) (hne : y ≠ x) :
    0 < f x - f y - f' * (x - y) := by
  have h := strict_concave_support hconc hx hy hderiv hne
  nlinarith

/-- Under strict concavity the remainder vanishes precisely at the candidate.
This pointwise fact alone is not an integrated uniqueness theorem. -/
theorem concavity_remainder_eq_zero_iff {S : Set ℝ} {f : ℝ → ℝ} {x y f' : ℝ}
    (hconc : StrictConcaveOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hderiv : HasDerivAt f f' x) :
    f x - f y - f' * (x - y) = 0 ↔ y = x := by
  constructor
  · intro hzero
    by_contra hne
    have hpos := concavity_remainder_pos hconc hx hy hderiv hne
    linarith
  · intro heq
    subst y
    simp

end RamseyCassKoopmans
