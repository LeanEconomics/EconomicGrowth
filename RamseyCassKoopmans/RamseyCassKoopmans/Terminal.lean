import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith

/-!
# Vanishing terminal capital terms

The welfare comparison retains the terminal term `p t * (k₀ t - k₁ t)`.
This file proves its disappearance from explicit economic hypotheses. In particular,
convergence of consumption to a positive level and continuity of marginal utility there
yield a finite marginal-utility limit; positive discounting then makes prices vanish.
No Euler equation alone is asserted to imply either convergence or optimality.
-/

open Filter Set
open scoped Topology

namespace RamseyCassKoopmans.Terminal

/-- Bounded nonnegative capital paths have a vanishing terminal difference whenever
the present-value price tends to zero. The hypotheses concern nonnegative times only. -/
theorem terminal_tendsto_zero_of_bounded_capital
    {p k₀ k₁ : ℝ → ℝ} {K : ℝ}
    (hp : Tendsto p atTop (𝓝 0))
    (h₀ : ∀ t, 0 ≤ t → 0 ≤ k₀ t ∧ k₀ t ≤ K)
    (h₁ : ∀ t, 0 ≤ t → 0 ≤ k₁ t ∧ k₁ t ≤ K) :
    Tendsto (fun t => p t * (k₀ t - k₁ t)) atTop (𝓝 0) := by
  apply hp.zero_mul_isBoundedUnder_le
  apply isBoundedUnder_of_eventually_le (a := K)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  change ‖k₀ t - k₁ t‖ ≤ K
  rw [Real.norm_eq_abs, abs_le]
  have hzero := h₀ t ht
  have hone := h₁ t ht
  constructor <;> linarith

/-- A positive constant discount rate makes the discount factor vanish. -/
theorem discount_factor_tendsto_zero {d : ℝ} (hd : 0 < d) :
    Tendsto (fun t : ℝ => Real.exp (-d * t)) atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp
    (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr hd))

/-- Positive discounting and a finite marginal-utility limit imply vanishing
present-value prices. No sign assumption on marginal utility is needed for this limit. -/
theorem discounted_price_tendsto_zero
    {d μ : ℝ} {mu : ℝ → ℝ} (hd : 0 < d)
    (hmu : Tendsto mu atTop (𝓝 μ)) :
    Tendsto (fun t => Real.exp (-d * t) * mu t) atTop (𝓝 0) := by
  simpa only [zero_mul] using (discount_factor_tendsto_zero hd).mul hmu

/-- Discounted marginal utility times a bounded capital difference tends to zero. -/
theorem discounted_terminal_tendsto_zero
    {d μ K : ℝ} {mu k₀ k₁ : ℝ → ℝ} (hd : 0 < d)
    (hmu : Tendsto mu atTop (𝓝 μ))
    (h₀ : ∀ t, 0 ≤ t → 0 ≤ k₀ t ∧ k₀ t ≤ K)
    (h₁ : ∀ t, 0 ≤ t → 0 ≤ k₁ t ∧ k₁ t ≤ K) :
    Tendsto (fun t => (Real.exp (-d * t) * mu t) * (k₀ t - k₁ t))
      atTop (𝓝 0) :=
  terminal_tendsto_zero_of_bounded_capital (discounted_price_tendsto_zero hd hmu) h₀ h₁

/-- Consumption convergence plus continuity of marginal utility at the limit gives
the price-decay hypothesis used in the infinite-horizon comparison. A positive
consumption limit is economically natural but continuity is the exact analytic premise. -/
theorem discounted_price_tendsto_zero_of_consumption_limit
    {d cstar : ℝ} {c marginalUtility : ℝ → ℝ} (hd : 0 < d)
    (hc : Tendsto c atTop (𝓝 cstar))
    (hmu : ContinuousAt marginalUtility cstar) :
    Tendsto (fun t => Real.exp (-d * t) * marginalUtility (c t)) atTop (𝓝 0) :=
  discounted_price_tendsto_zero hd (hmu.tendsto.comp hc)

/-- A feasible capital path cannot cross above a capacity `K` at which net output
is nonpositive, provided net output remains nonpositive above that capacity.
The proof uses a strictly increasing comparison barrier and then lets its slope vanish.
Right derivatives suffice, matching the piecewise smooth admissibility in Koopmans. -/
theorem capital_le_capacity
    {k c f : ℝ → ℝ} {m K : ℝ}
    (hk : ContinuousOn k (Ici 0))
    (hd : ∀ t, 0 ≤ t →
      HasDerivWithinAt k (f (k t) - c t - m * k t) (Ici t) t)
    (hc : ∀ t, 0 ≤ t → 0 ≤ c t)
    (hK : ∀ x, K ≤ x → f x ≤ m * x)
    (hinit : k 0 ≤ K) :
    ∀ t, 0 ≤ t → k t ≤ K := by
  intro T hT
  apply le_of_forall_pos_le_add
  intro ε hε
  let a : ℝ := ε / (T + 1)
  have ha : 0 < a := div_pos hε (by linarith)
  have hbarrier : ∀ ⦃t⦄, t ∈ Icc 0 T → k t ≤ K + a * (t + 1) := by
    apply image_le_of_deriv_right_lt_deriv_boundary
      (b := T) (B := fun t => K + a * (t + 1))
      (hf' := fun t ht => hd t ht.1)
      (B' := fun _ => a)
    · exact hk.mono (fun _ hx => hx.1)
    · linarith
    · intro t
      convert ((hasDerivAt_id t).add_const 1).const_mul a |>.const_add K using 1 <;> simp
    · intro t ht heq
      have htk : K ≤ k t := by
        rw [heq]
        have := mul_nonneg (le_of_lt ha) (show 0 ≤ t + 1 by linarith [ht.1])
        linarith
      have hn := hK (k t) htk
      have hct := hc t ht.1
      linarith
  have hfinal := hbarrier ⟨hT, le_rfl⟩
  have haT : a * (T + 1) = ε := by
    dsimp [a]
    exact div_mul_cancel₀ ε (by linarith)
  rwa [haT] at hfinal

/-- The terminal condition follows from explicit production and feasibility bounds,
positive discounting, and convergence of marginal utility. Capital bounds are proved
from the resource equations instead of supplied as assumptions. -/
theorem discounted_terminal_tendsto_zero_of_feasible_paths
    {k₀ k₁ c₀ c₁ f mu : ℝ → ℝ} {d μ m K : ℝ}
    (hd : 0 < d) (hmu : Tendsto mu atTop (𝓝 μ))
    (hK : ∀ x, K ≤ x → f x ≤ m * x)
    (hk₀ : ContinuousOn k₀ (Ici 0))
    (hk₁ : ContinuousOn k₁ (Ici 0))
    (hresource₀ : ∀ t, 0 ≤ t →
      HasDerivWithinAt k₀ (f (k₀ t) - c₀ t - m * k₀ t) (Ici t) t)
    (hresource₁ : ∀ t, 0 ≤ t →
      HasDerivWithinAt k₁ (f (k₁ t) - c₁ t - m * k₁ t) (Ici t) t)
    (hc₀ : ∀ t, 0 ≤ t → 0 ≤ c₀ t)
    (hc₁ : ∀ t, 0 ≤ t → 0 ≤ c₁ t)
    (hcapital₀ : ∀ t, 0 ≤ t → 0 ≤ k₀ t)
    (hcapital₁ : ∀ t, 0 ≤ t → 0 ≤ k₁ t)
    (hinit₀ : k₀ 0 ≤ K) (hinit₁ : k₁ 0 ≤ K) :
    Tendsto (fun t => (Real.exp (-d * t) * mu t) * (k₀ t - k₁ t))
      atTop (𝓝 0) := by
  apply discounted_terminal_tendsto_zero hd hmu
  · exact fun t ht => ⟨hcapital₀ t ht,
      capital_le_capacity hk₀ hresource₀ hc₀ hK hinit₀ t ht⟩
  · exact fun t ht => ⟨hcapital₁ t ht,
      capital_le_capacity hk₁ hresource₁ hc₁ hK hinit₁ t ht⟩

end RamseyCassKoopmans.Terminal
