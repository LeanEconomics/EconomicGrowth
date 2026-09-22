import RamseyCassKoopmans.Model
import RamseyCassKoopmans.Terminal

/-!
# Stationary feasible paths and their objective values

A resource-balanced pair of constant capital and positive consumption determines an
actual feasible path. With positive effective discounting, its welfare is finite.
Stationarity and feasibility alone do not assert optimality; supporting prices and
an appropriate comparison theorem are needed for that conclusion.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

/-- Constant capital and consumption, with replacement investment `m * k`. -/
def stationaryPath (f : ℝ → ℝ) (m k c : ℝ)
    (hk : 0 ≤ k) (hc : 0 < c) (hresource : c + m * k = f k) :
    FeasiblePath f m where
  capital := fun _ => k
  consumption := fun _ => c
  investment := fun _ => m * k
  capital_nonneg := fun _ _ => hk
  consumption_pos := fun _ _ => hc
  consumption_continuous := continuousOn_const
  investment_continuous := continuousOn_const
  resource := fun _ _ => hresource
  dynamics := fun t _ => by simpa using hasDerivAt_const t k

/-- Nonnegative effective depreciation makes stationary replacement investment
nonnegative, so this path also satisfies Cass's investment restriction. -/
theorem stationaryPath_nonnegativeInvestment
    (f : ℝ → ℝ) (m k c : ℝ) (hk : 0 ≤ k) (hc : 0 < c)
    (hresource : c + m * k = f k) (hm : 0 ≤ m) :
    (stationaryPath f m k c hk hc hresource).NonnegativeInvestment :=
  fun _ _ => mul_nonneg hm hk

/-- Exact finite-horizon welfare of constant consumption. This holds for every
real horizon; no integrability hypothesis on utility away from `c` is required. -/
theorem welfare_constant_consumption
    (U : ℝ → ℝ) (c d T : ℝ) (hd : 0 < d) :
    welfare U (discount d) (fun _ => c) T = U c * (1 - discount d T) / d := by
  have hprimitive : ∀ t : ℝ,
      HasDerivAt (fun s => U c * (1 - discount d s) / d)
        (discount d t * U c) t := by
    intro t
    convert ((hasDerivAt_discount d t).const_sub 1).const_mul (U c) |>.div_const d
      using 1
    field_simp [ne_of_gt hd]
  have hintegrable : IntervalIntegrable (fun t => discount d t * U c) volume 0 T :=
    ((discount_continuous d).mul continuous_const).intervalIntegrable 0 T
  unfold welfare
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hprimitive t) hintegrable]
  simp [discount]

/-- Constant positive-discount welfare converges to utility divided by discounting. -/
theorem hasWelfare_constant_consumption
    (U : ℝ → ℝ) (c d : ℝ) (hd : 0 < d) :
    HasWelfare U (discount d) (fun _ => c) (U c / d) := by
  unfold HasWelfare
  have hdiscount : Tendsto (discount d) atTop (𝓝 0) :=
    Terminal.discount_factor_tendsto_zero hd
  have hlimit := (hdiscount.const_sub 1).const_mul (U c) |>.div_const d
  simp only [sub_zero, mul_one] at hlimit
  exact hlimit.congr (fun T => (welfare_constant_consumption U c d T hd).symm)

/-- Every stationary feasible path has the explicit discounted objective `U c / d`. -/
theorem stationaryPath_hasWelfare
    (f U : ℝ → ℝ) (m k c d : ℝ) (hk : 0 ≤ k) (hc : 0 < c)
    (hresource : c + m * k = f k) (hd : 0 < d) :
    HasWelfare U (discount d)
      (stationaryPath f m k c hk hc hresource).consumption (U c / d) :=
  hasWelfare_constant_consumption U c d hd

end RamseyCassKoopmans
