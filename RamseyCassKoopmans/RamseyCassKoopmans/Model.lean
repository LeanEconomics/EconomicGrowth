import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Growth paths and finite welfare

Original work released under the Unlicense. A path is defined on real time,
but feasibility is imposed only for nonnegative time. Controls are continuous
and capital satisfies the resource equation classically. This is an explicit
regularity restriction, not a formalization of every measurable control.

Investment may be negative in `FeasiblePath` (Koopmans's resource convention).
Cass's additional nonnegative-investment restriction is `NonnegativeInvestment`.
Neither convergence nor optimality is part of feasibility.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

structure FeasiblePath (f : ℝ → ℝ) (m : ℝ) where
  capital : ℝ → ℝ
  consumption : ℝ → ℝ
  investment : ℝ → ℝ
  capital_nonneg : ∀ t, 0 ≤ t → 0 ≤ capital t
  consumption_pos : ∀ t, 0 ≤ t → 0 < consumption t
  consumption_continuous : ContinuousOn consumption (Ici 0)
  investment_continuous : ContinuousOn investment (Ici 0)
  resource : ∀ t, 0 ≤ t → consumption t + investment t = f (capital t)
  dynamics : ∀ t, 0 ≤ t →
    HasDerivAt capital (investment t - m * capital t) t

def FeasiblePath.NonnegativeInvestment {f : ℝ → ℝ} {m : ℝ}
    (a : FeasiblePath f m) : Prop := ∀ t, 0 ≤ t → 0 ≤ a.investment t

theorem FeasiblePath.capital_continuous {f : ℝ → ℝ} {m : ℝ}
    (a : FeasiblePath f m) : ContinuousOn a.capital (Ici 0) := by
  intro t ht
  exact (a.dynamics t ht).continuousAt.continuousWithinAt

noncomputable def discount (d t : ℝ) : ℝ := Real.exp (-d * t)

theorem discount_pos (d t : ℝ) : 0 < discount d t := Real.exp_pos _

theorem discount_continuous (d : ℝ) : Continuous (discount d) := by
  unfold discount
  fun_prop

theorem hasDerivAt_discount (d t : ℝ) :
    HasDerivAt (discount d) (-d * discount d t) t := by
  change HasDerivAt (fun s : ℝ => Real.exp (-d * s)) (-d * Real.exp (-d * t)) t
  simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id t).const_mul (-d)).exp

/-- Finite-horizon welfare is always a finite-interval integral. Infinite welfare
is specified using a limit, so a divergent Bochner integral is never mistaken for zero. -/
noncomputable def welfare (U w c : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, w t * U (c t)

def HasWelfare (U w c : ℝ → ℝ) (J : ℝ) : Prop :=
  Tendsto (welfare U w c) atTop (𝓝 J)

def boundary (p ka kb : ℝ → ℝ) (t : ℝ) : ℝ := p t * (ka t - kb t)

/-- Conversion from Cass's current-value costate to its present-value price. -/
theorem hasDerivAt_discounted_costate {q : ℝ → ℝ} {d m mu mp t : ℝ}
    (hq : HasDerivAt q ((d + m) * q t - mu * mp) t) :
    HasDerivAt (fun s => discount d s * q s)
      (m * (discount d t * q t) - discount d t * mu * mp) t := by
  convert (hasDerivAt_discount d t).mul hq using 1
  ring

end RamseyCassKoopmans
