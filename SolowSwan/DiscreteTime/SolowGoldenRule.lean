/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import DiscreteTime.Neoclassical
import Solow1956.Growth.SolowGoldenRule

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
