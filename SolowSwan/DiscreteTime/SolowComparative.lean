/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import DiscreteTime.Neoclassical

/-! # Discrete-time comparative statics, Acemoglu Proposition 2.3

The discrete steady state is the continuous steady state at effective dilution
`γ - 1 + δ`, so its derivatives follow from the inverse-function construction in
`Solow1956.Growth.SolowComparative`. With `γ = 1 + n` the dilution is exactly
`δ + n`, and Acemoglu's discrete Proposition 2.3 is recovered, together with the
population-growth partial.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime

open Solow1956.Neoclassical

variable {f : ℝ → ℝ}

theorem steady_strictMono_saving (h : Technology f) {δ γ : ℝ} (hm : 0 < γ - 1 + δ) :
    StrictMonoOn (fun s => steady h s δ γ) (Ioi 0) :=
  steadyCapital_strictMono_saving h hm

theorem steady_strictAnti_depreciation (h : Technology f) {s γ δ₁ δ₂ : ℝ} (hs : 0 < s)
    (hm : 0 < γ - 1 + δ₁) (hδ : δ₁ < δ₂) : steady h s δ₂ γ < steady h s δ₁ γ :=
  steadyCapital_strictAnti_dilution h hs hm (by simp only [mem_Ioi]; linarith) (by linarith)

theorem steady_strictAnti_growth (h : Technology f) {s δ γ₁ γ₂ : ℝ} (hs : 0 < s)
    (hm : 0 < γ₁ - 1 + δ) (hγ : γ₁ < γ₂) : steady h s δ γ₂ < steady h s δ γ₁ :=
  steadyCapital_strictAnti_dilution h hs hm (by simp only [mem_Ioi]; linarith) (by linarith)

/-- Actual partial derivatives of the discrete steady state in saving, depreciation
and effective-labour growth. -/
theorem steady_derivative_signs (h : Technology f) {s δ γ : ℝ} (hs : 0 < s)
    (hm : 0 < γ - 1 + δ) :
    0 < deriv (fun z => steady h z δ γ) s ∧
      deriv (fun z => steady h s z γ) δ < 0 ∧
      deriv (fun z => steady h s δ z) γ < 0 := by
  have hsave := steadyCapital_hasDerivAt_saving h hs hm
  have hdil := steadyCapital_hasDerivAt_dilution h hs hm
  have hδ : HasDerivAt (fun z => steady h s z γ) (dilutionResponse h s (γ - 1 + δ) * 1) δ :=
    hdil.comp δ ((hasDerivAt_id δ).const_add (γ - 1))
  have hγ : HasDerivAt (fun z => steady h s δ z) (dilutionResponse h s (γ - 1 + δ) * 1) γ :=
    hdil.comp γ (((hasDerivAt_id γ).sub_const 1).add_const δ)
  rw [mul_one] at hδ hγ
  refine ⟨?_, ?_, ?_⟩
  · rw [show (fun z => steady h z δ γ) = fun z => steadyCapital h z (γ - 1 + δ) from rfl,
      hsave.deriv]
    exact savingResponse_pos h hs hm
  · rw [hδ.deriv]; exact dilutionResponse_neg h hs hm
  · rw [hγ.deriv]; exact dilutionResponse_neg h hs hm

theorem steady_rewrite (h : Technology f) (s δ n : ℝ) :
    steady h s δ (1 + n) = steadyCapital h s (δ + n) := by
  unfold steady
  congr 1
  ring

/-- Acemoglu Proposition 2.3 in discrete time, with `f = A f̃` and `γ = 1 + n`:
capital rises with productivity and saving and falls with depreciation and
population growth. -/
theorem acemoglu_capital_partials (h : Technology f) {A s δ n : ℝ}
    (hA : 0 < A) (hs : 0 < s) (hm : 0 < δ + n) :
    0 < deriv (fun a => steady h (s * a) δ (1 + n)) A ∧
    0 < deriv (fun z => steady h (z * A) δ (1 + n)) s ∧
    deriv (fun z => steady h (s * A) z (1 + n)) δ < 0 ∧
    deriv (fun z => steady h (s * A) δ (1 + z)) n < 0 := by
  simp only [steady_rewrite]
  exact Neoclassical.acemoglu_capital_partials h hA hs hm

/-- The output partials of Proposition 2.3, including productivity's direct effect. -/
theorem acemoglu_output_partials (h : Technology f) {A s δ n : ℝ}
    (hA : 0 < A) (hs : 0 < s) (hm : 0 < δ + n) :
    0 < deriv (fun a => a * f (steady h (s * a) δ (1 + n))) A ∧
    0 < deriv (fun z => A * f (steady h (z * A) δ (1 + n))) s ∧
    deriv (fun z => A * f (steady h (s * A) z (1 + n))) δ < 0 ∧
    deriv (fun z => A * f (steady h (s * A) δ (1 + z))) n < 0 := by
  simp only [steady_rewrite]
  exact Neoclassical.acemoglu_output_partials h hA hs hm

end Solow1956.DiscreteTime
