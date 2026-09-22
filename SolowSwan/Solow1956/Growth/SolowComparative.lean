/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/
import Solow1956.Growth.Neoclassical
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # General Solow comparative statics, Acemoglu Proposition 2.8

The equilibrium function is constructed for every positive ratio `m/s`.
Its differentiability follows from the inverse function theorem, rather than
being assumed when differentiating the equilibrium equation.
-/

open Set Filter Topology

namespace Solow1956.Neoclassical

variable {f : ℝ → ℝ}

noncomputable def capitalAtRatio (h : Technology f) (r : ℝ) : ℝ :=
  if hr : 0 < r then Classical.choose (existsUnique_steadyState h (show (0 : ℝ) < 1 by norm_num) hr)
  else 0

theorem capitalAtRatio_spec (h : Technology f) {r : ℝ} (hr : 0 < r) :
    0 < capitalAtRatio h r ∧ f (capitalAtRatio h r) / capitalAtRatio h r = r := by
  have hspec : 0 < capitalAtRatio h r ∧ rate f 1 r (capitalAtRatio h r) = 0 := by
    simpa only [capitalAtRatio, dite_eq_left hr] using (Classical.choose_spec
      (existsUnique_steadyState h (show (0 : ℝ) < 1 by norm_num) hr)).1
  obtain ⟨hp, he⟩ := hspec
  refine ⟨hp, (div_eq_iff (ne_of_gt hp)).mpr ?_⟩
  dsimp [rate] at he
  nlinarith

theorem capitalAtRatio_average (h : Technology f) {k : ℝ} (hk : 0 < k) :
    capitalAtRatio h (f k / k) = k := by
  have hs := capitalAtRatio_spec h (div_pos (h.output_pos hk) hk)
  exact h.average_strictAnti.injOn hs.1 hk hs.2

theorem capitalAtRatio_strictAnti (h : Technology f) :
    StrictAntiOn (capitalAtRatio h) (Ioi 0) := by
  intro a ha b hb hab
  have hA := capitalAtRatio_spec h ha
  have hB := capitalAtRatio_spec h hb
  by_contra hn
  have hp := h.average_strictAnti.antitoneOn hA.1 hB.1 (le_of_not_gt hn)
  rw [hA.2, hB.2] at hp
  linarith

noncomputable def averageSlope (f : ℝ → ℝ) (k : ℝ) : ℝ :=
  (deriv f k * k - f k) / k ^ 2

theorem averageSlope_neg (h : Technology f) {k : ℝ} (hk : 0 < k) :
    averageSlope f k < 0 :=
  div_neg_of_neg_of_pos (sub_neg.mpr (h.output_gap hk)) (sq_pos_of_pos hk)

theorem average_hasStrictDerivAt (h : Technology f) {k : ℝ} (hk : 0 < k) :
    HasStrictDerivAt (fun x => f x / x) (averageSlope f k) k := by
  have hstrict : HasStrictDerivAt f (deriv f k) k :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      ((lt_mem_nhds hk).mono (fun x hx => (h.differentiable x hx).hasDerivAt))
      (h.derivative_continuous.continuousAt (Ioi_mem_nhds hk))
  simpa only [id_eq, mul_one, averageSlope] using
    hstrict.fun_div (hasStrictDerivAt_id k) (ne_of_gt hk)

theorem capitalAtRatio_hasDerivAt (h : Technology f) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (capitalAtRatio h) (averageSlope f (capitalAtRatio h r))⁻¹ r := by
  have hs := capitalAtRatio_spec h hr
  have hi := (average_hasStrictDerivAt h hs.1).to_local_left_inverse
    (ne_of_lt (averageSlope_neg h hs.1))
    ((lt_mem_nhds hs.1).mono (fun k hk => capitalAtRatio_average h hk))
  rw [hs.2] at hi
  exact hi.hasDerivAt

noncomputable def steadyCapital (h : Technology f) (s m : ℝ) : ℝ := capitalAtRatio h (m / s)

theorem steadyCapital_spec (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    0 < steadyCapital h s m ∧ rate f s m (steadyCapital h s m) = 0 := by
  obtain ⟨hp, he⟩ := capitalAtRatio_spec h (div_pos hm hs)
  refine ⟨hp, ?_⟩
  have he' := (div_eq_div_iff (ne_of_gt hp) (ne_of_gt hs)).mp he
  dsimp [rate, steadyCapital]
  nlinarith

theorem steadyCapital_eq (h : Technology f) {s m k : ℝ}
    (hs : 0 < s) (hm : 0 < m) (hk : 0 < k) (he : rate f s m k = 0) :
    steadyCapital h s m = k := by
  obtain ⟨_, _, hu⟩ := existsUnique_steadyState h hs hm
  exact (hu _ (steadyCapital_spec h hs hm)).trans (hu k ⟨hk, he⟩).symm

/-- A larger saving rate strictly raises stationary capital. -/
theorem steadyCapital_strictMono_saving (h : Technology f) {m : ℝ} (hm : 0 < m) :
    StrictMonoOn (fun s => steadyCapital h s m) (Ioi 0) := by
  intro s hs t ht hst
  exact capitalAtRatio_strictAnti h (div_pos hm ht) (div_pos hm hs)
    (div_lt_div_of_pos_left hm hs hst)

/-- Greater depreciation/population dilution strictly lowers stationary capital. -/
theorem steadyCapital_strictAnti_dilution (h : Technology f) {s : ℝ} (hs : 0 < s) :
    StrictAntiOn (steadyCapital h s) (Ioi 0) := by
  intro m hm n hn hmn
  exact capitalAtRatio_strictAnti h (div_pos hm hs) (div_pos hn hs)
    ((div_lt_div_iff_of_pos_right hs).mpr hmn)

noncomputable def savingResponse (h : Technology f) (s m : ℝ) : ℝ :=
  (averageSlope f (steadyCapital h s m))⁻¹ * (-(m / s ^ 2))

noncomputable def dilutionResponse (h : Technology f) (s m : ℝ) : ℝ :=
  (averageSlope f (steadyCapital h s m))⁻¹ * (1 / s)

theorem steadyCapital_hasDerivAt_saving (h : Technology f) {s m : ℝ}
    (hs : 0 < s) (hm : 0 < m) :
    HasDerivAt (fun z => steadyCapital h z m) (savingResponse h s m) s := by
  have hr : HasDerivAt (fun z : ℝ => m / z) (-(m / s ^ 2)) s := by
    simpa only [zero_mul, mul_one, zero_sub, neg_div, id_eq] using
      (hasDerivAt_const s m).fun_div (hasDerivAt_id s) (ne_of_gt hs)
  exact (capitalAtRatio_hasDerivAt h (div_pos hm hs)).comp s hr

theorem steadyCapital_hasDerivAt_dilution (h : Technology f) {s m : ℝ}
    (hs : 0 < s) (hm : 0 < m) :
    HasDerivAt (steadyCapital h s) (dilutionResponse h s m) m :=
  (capitalAtRatio_hasDerivAt h (div_pos hm hs)).comp m ((hasDerivAt_id m).div_const s)

theorem savingResponse_pos (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    0 < savingResponse h s m :=
  mul_pos_of_neg_of_neg (inv_lt_zero.mpr (averageSlope_neg h (steadyCapital_spec h hs hm).1))
    (neg_neg_of_pos (div_pos hm (sq_pos_of_pos hs)))

theorem dilutionResponse_neg (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    dilutionResponse h s m < 0 :=
  mul_neg_of_neg_of_pos (inv_lt_zero.mpr (averageSlope_neg h (steadyCapital_spec h hs hm).1))
    (one_div_pos.mpr hs)

/-- Actual partial derivatives, not conditional implicit-differentiation rules. -/
theorem steadyCapital_derivative_signs (h : Technology f) {s m : ℝ}
    (hs : 0 < s) (hm : 0 < m) :
    0 < deriv (fun z => steadyCapital h z m) s ∧ deriv (steadyCapital h s) m < 0 := by
  rw [(steadyCapital_hasDerivAt_saving h hs hm).deriv,
    (steadyCapital_hasDerivAt_dilution h hs hm).deriv]
  exact ⟨savingResponse_pos h hs hm, dilutionResponse_neg h hs hm⟩

theorem output_derivative_signs (h : Technology f) {s m : ℝ}
    (hs : 0 < s) (hm : 0 < m) :
    0 < deriv (fun z => f (steadyCapital h z m)) s ∧
      deriv (fun z => f (steadyCapital h s z)) m < 0 := by
  have hk := (steadyCapital_spec h hs hm).1
  have hd := (h.differentiable _ hk).hasDerivAt
  change 0 < deriv (f ∘ fun z => steadyCapital h z m) s ∧
    deriv (f ∘ steadyCapital h s) m < 0
  rw [(hd.comp s (steadyCapital_hasDerivAt_saving h hs hm)).deriv,
    (hd.comp m (steadyCapital_hasDerivAt_dilution h hs hm)).deriv]
  exact ⟨mul_pos (h.marginal_positive _ hk) (savingResponse_pos h hs hm),
    mul_neg_of_pos_of_neg (h.marginal_positive _ hk) (dilutionResponse_neg h hs hm)⟩

/-- All four capital partial-derivative signs in Acemoglu Proposition 2.8,
with `f` the baseline technology and productivity entering as `A * f`. -/
theorem acemoglu_capital_partials (h : Technology f) {A s δ n : ℝ}
    (hA : 0 < A) (hs : 0 < s) (hm : 0 < δ + n) :
    0 < deriv (fun a => steadyCapital h (s * a) (δ + n)) A ∧
    0 < deriv (fun z => steadyCapital h (z * A) (δ + n)) s ∧
    deriv (fun z => steadyCapital h (s * A) (z + n)) δ < 0 ∧
    deriv (fun z => steadyCapital h (s * A) (δ + z)) n < 0 := by
  have hsave := steadyCapital_hasDerivAt_saving h (mul_pos hs hA) hm
  have hdil := steadyCapital_hasDerivAt_dilution h (mul_pos hs hA) hm
  have hAp : HasDerivAt (fun a => steadyCapital h (s * a) (δ + n))
      (savingResponse h (s * A) (δ + n) * s) A := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      hsave.comp A ((hasDerivAt_id A).const_mul s)
  have hsp : HasDerivAt (fun z => steadyCapital h (z * A) (δ + n))
      (savingResponse h (s * A) (δ + n) * A) s := by
    simpa only [Function.comp_def, id_eq, one_mul] using
      hsave.comp s ((hasDerivAt_id s).mul_const A)
  have hδp : HasDerivAt (fun z => steadyCapital h (s * A) (z + n))
      (dilutionResponse h (s * A) (δ + n)) δ := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      hdil.comp δ ((hasDerivAt_id δ).add_const n)
  have hnp : HasDerivAt (fun z => steadyCapital h (s * A) (δ + z))
      (dilutionResponse h (s * A) (δ + n)) n := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      hdil.comp n ((hasDerivAt_id n).const_add δ)
  rw [hAp.deriv, hsp.deriv, hδp.deriv, hnp.deriv]
  exact ⟨mul_pos (savingResponse_pos h (mul_pos hs hA) hm) hs,
    mul_pos (savingResponse_pos h (mul_pos hs hA) hm) hA,
    dilutionResponse_neg h (mul_pos hs hA) hm,
    dilutionResponse_neg h (mul_pos hs hA) hm⟩

/-- The output partials include productivity's direct effect on output. -/
theorem acemoglu_output_partials (h : Technology f) {A s δ n : ℝ}
    (hA : 0 < A) (hs : 0 < s) (hm : 0 < δ + n) :
    0 < deriv (fun a => a * f (steadyCapital h (s * a) (δ + n))) A ∧
    0 < deriv (fun z => A * f (steadyCapital h (z * A) (δ + n))) s ∧
    deriv (fun z => A * f (steadyCapital h (s * A) (z + n))) δ < 0 ∧
    deriv (fun z => A * f (steadyCapital h (s * A) (δ + z))) n < 0 := by
  have hk := (steadyCapital_spec h (mul_pos hs hA) hm).1
  have hf := (h.differentiable _ hk).hasDerivAt
  have hsave := steadyCapital_hasDerivAt_saving h (mul_pos hs hA) hm
  have hdil := steadyCapital_hasDerivAt_dilution h (mul_pos hs hA) hm
  have hAp := (hasDerivAt_id A).fun_mul (hf.comp A
    (hsave.comp A ((hasDerivAt_id A).const_mul s)))
  have hsp := (hf.comp s (hsave.comp s ((hasDerivAt_id s).mul_const A))).const_mul A
  have hδp := (hf.comp δ (hdil.comp δ ((hasDerivAt_id δ).add_const n))).const_mul A
  have hnp := (hf.comp n (hdil.comp n ((hasDerivAt_id n).const_add δ))).const_mul A
  simp only [Function.comp_def, id_eq, one_mul, mul_one] at hAp hsp hδp hnp
  rw [hAp.deriv, hsp.deriv, hδp.deriv, hnp.deriv]
  have hmp := h.marginal_positive _ hk
  have hpos := savingResponse_pos h (mul_pos hs hA) hm
  have hneg := dilutionResponse_neg h (mul_pos hs hA) hm
  exact ⟨add_pos (h.output_pos hk) (mul_pos hA (mul_pos hmp (mul_pos hpos hs))),
    mul_pos hA (mul_pos hmp (mul_pos hpos hA)),
    mul_neg_of_pos_of_neg hA (mul_neg_of_pos_of_neg hmp hneg),
    mul_neg_of_pos_of_neg hA (mul_neg_of_pos_of_neg hmp hneg)⟩

end Solow1956.Neoclassical
