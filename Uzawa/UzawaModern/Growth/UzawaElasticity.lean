/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The elasticity identity in Jones–Scrimgeour (2004)

NBER working paper 10921, equation (4) and footnotes 4–5, printed pp. 5–6.
For output per worker `f(k)`, capital/output is `h(k) = k/f(k)` and the capital
share is `α = f'(k) k / f(k)`. This file proves `h' = (1-α)/f(k)` and derives
the output-versus-capital/output elasticity `α/(1-α)` along a differentiable
local inverse parameterization. Its existence is an explicit hypothesis;
we do not assume that pointwise nonzero derivatives prove global surjectivity.

These are local calculus statements from the 2004 argument. They are not a
proof of its later separation-of-variables step. The independent `Uzawa`
module proves the published 2008 on-path theorem via the Schlicht argument.
-/

namespace UzawaModern.UzawaElasticity

open Filter
open scoped Topology

/-- Differentiate the capital/output ratio without assuming an inverse exists. -/
theorem hasDerivAt_capitalOutputRatio {f : ℝ → ℝ} {k m : ℝ}
    (hf : HasDerivAt f m k) (hy : f k ≠ 0) :
    HasDerivAt (fun u => u / f u) ((1 - m * k / f k) / f k) k := by
  have h := (hasDerivAt_id k).fun_div hf hy
  convert! h using 1
  dsimp
  field_simp

/-- A positive labor share makes the capital/output derivative strictly positive. -/
theorem capitalOutputRatio_derivative_pos {f : ℝ → ℝ} {k m : ℝ}
    (hy : 0 < f k) (hshare : m * k / f k < 1) :
    0 < (1 - m * k / f k) / f k :=
  div_pos (sub_pos.mpr hshare) hy

/-- Equation (4): the output elasticity with respect to capital/output is
the capital share divided by the labor share. The identity `k(x)=x f(k(x))`
is required in a neighborhood, so it can legitimately be differentiated. -/
theorem output_capitalOutput_elasticity {f k : ℝ → ℝ} {x m k' : ℝ}
    (hk : HasDerivAt k k' x) (hf : HasDerivAt f m (k x))
    (hy : 0 < f (k x))
    (hshare : m * k x / f (k x) < 1)
    (hidentity : ∀ᶠ u in 𝓝 x, k u = u * f (k u)) :
    (m * k') * x / f (k x) =
      (m * k x / f (k x)) / (1 - m * k x / f (k x)) := by
  have hid : k x = x * f (k x) :=
    Filter.EventuallyEq.eq_of_nhds (show k =ᶠ[𝓝 x] (fun u => u * f (k u)) from hidentity)
  have hcomp := hf.comp x hk
  have hproduct := (hasDerivAt_id x).mul hcomp
  have hder : k' = f (k x) + x * (m * k') := by
    simpa using hk.unique (hproduct.congr_of_eventuallyEq hidentity)
  have halpha : m * k x / f (k x) = m * x := by
    calc
      _ = m * (x * f (k x)) / f (k x) := congrArg (fun v => m * v / f (k x)) hid
      _ = _ := by field_simp
  have hden : 1 - m * x ≠ 0 := by rw [halpha] at hshare; linarith
  have hkprime : k' = f (k x) / (1 - m * x) := by
    apply (eq_div_iff hden).mpr
    nlinarith [hder]
  rw [halpha, hkprime]
  field_simp

end UzawaModern.UzawaElasticity
