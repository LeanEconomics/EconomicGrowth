/-
SPDX-License-Identifier: Unlicense
Original formalization by the TheoryDebugger project, developed with OpenAI Codex
under the project maintainer's direction. See UNLICENSE and THIRD_PARTY_NOTICES.md.
-/
import UzawaModern.Growth.Uzawa
import UzawaModern.Growth.UzawaElasticity
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# A repaired capital/output-coordinate proof of Uzawa representation

This is a strengthened, domain-wide theorem motivated by Jones-Scrimgeour
(2004), not a claim to prove that paper's literal assumptions. We assume
the capital/output map has the whole positive half-line as its range, and
later impose share invariance at every positive capital/output ratio.
We construct its inverse, prove continuity and differentiability, derive
the elasticity identity, and prove separation by the mean value theorem.
-/

namespace UzawaModern.UzawaSeparation

open Set Filter
open scoped Topology

/-- Intensive technologies with an explicitly specified global ratio range.
No inverse, inverse derivative, or separation identity is assumed. -/
structure Technology where
  output : ℝ → ℝ → ℝ
  marginal : ℝ → ℝ → ℝ
  output_pos : ∀ t k, 0 < k → 0 < output t k
  hasDerivAt_output : ∀ t k, 0 < k → HasDerivAt (output t) (marginal t k) k
  share_lt_one : ∀ t k, 0 < k → marginal t k * k / output t k < 1
  ratio_surjective : ∀ t x, 0 < x → ∃ k, 0 < k ∧ k / output t k = x

namespace Technology

noncomputable def ratio (T : Technology) (t k : ℝ) : ℝ := k / T.output t k

noncomputable def share (T : Technology) (t k : ℝ) : ℝ :=
  T.marginal t k * k / T.output t k

theorem ratio_pos (T : Technology) (t : ℝ) {k : ℝ} (hk : 0 < k) :
    0 < T.ratio t k := div_pos hk (T.output_pos t k hk)

theorem hasDerivAt_ratio (T : Technology) (t : ℝ) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (T.ratio t) ((1 - T.share t k) / T.output t k) k :=
  UzawaElasticity.hasDerivAt_capitalOutputRatio (T.hasDerivAt_output t k hk)
    (ne_of_gt (T.output_pos t k hk))

theorem ratio_derivative_pos (T : Technology) (t : ℝ) {k : ℝ} (hk : 0 < k) :
    0 < (1 - T.share t k) / T.output t k :=
  div_pos (sub_pos.mpr (T.share_lt_one t k hk)) (T.output_pos t k hk)

theorem ratio_strictMonoOn (T : Technology) (t : ℝ) :
    StrictMonoOn (T.ratio t) (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro k hk
    exact (T.hasDerivAt_ratio t hk).continuousAt.continuousWithinAt
  · intro k hk
    have hk' : 0 < k := by simpa only [interior_Ioi, mem_Ioi] using hk
    rw [(T.hasDerivAt_ratio t hk').deriv]
    exact T.ratio_derivative_pos t hk'

/-- Choose a positive preimage; all subsequent inverse properties are proved. -/
noncomputable def capital (T : Technology) (t x : ℝ) : ℝ :=
  if hx : 0 < x then Classical.choose (T.ratio_surjective t x hx) else 0

theorem capital_pos (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < T.capital t x := by
  simp only [capital, dite_eq_left hx]
  exact (Classical.choose_spec (T.ratio_surjective t x hx)).1

theorem ratio_capital (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    T.ratio t (T.capital t x) = x := by
  simp only [capital, dite_eq_left hx, ratio]
  exact (Classical.choose_spec (T.ratio_surjective t x hx)).2

theorem capital_ratio (T : Technology) (t : ℝ) {k : ℝ} (hk : 0 < k) :
    T.capital t (T.ratio t k) = k := by
  apply (T.ratio_strictMonoOn t).injOn (T.capital_pos t (T.ratio_pos t hk)) hk
  exact T.ratio_capital t (T.ratio_pos t hk)

theorem capital_strictMonoOn (T : Technology) (t : ℝ) :
    StrictMonoOn (T.capital t) (Ioi 0) := by
  intro x hx y hy hxy
  apply lt_of_not_ge
  intro hle
  have h := (T.ratio_strictMonoOn t).monotoneOn
    (T.capital_pos t hy) (T.capital_pos t hx) hle
  rw [T.ratio_capital t hy, T.ratio_capital t hx] at h
  exact (not_le_of_gt hxy) h

theorem capital_image (T : Technology) (t : ℝ) : T.capital t '' Ioi 0 = Ioi 0 := by
  apply Subset.antisymm
  · rintro k ⟨x, hx, rfl⟩
    exact T.capital_pos t hx
  · intro k hk
    exact ⟨T.ratio t k, T.ratio_pos t hk, T.capital_ratio t hk⟩

theorem continuousAt_capital (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (T.capital t) x := by
  apply (T.capital_strictMonoOn t).continuousAt_of_image_mem_nhds
    (isOpen_Ioi.mem_nhds hx)
  rw [T.capital_image t]
  exact isOpen_Ioi.mem_nhds (T.capital_pos t hx)

theorem hasDerivAt_capital (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (T.capital t)
      (((1 - T.share t (T.capital t x)) / T.output t (T.capital t x))⁻¹) x := by
  apply HasDerivAt.of_local_left_inverse (T.continuousAt_capital t hx)
    (T.hasDerivAt_ratio t (T.capital_pos t hx))
    (ne_of_gt (T.ratio_derivative_pos t (T.capital_pos t hx)))
  filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
  exact T.ratio_capital t hu

noncomputable def phi (T : Technology) (t x : ℝ) : ℝ := T.output t (T.capital t x)

noncomputable def phiDerivative (T : Technology) (t x : ℝ) : ℝ :=
  T.marginal t (T.capital t x) *
    (((1 - T.share t (T.capital t x)) / T.output t (T.capital t x))⁻¹)

theorem phi_pos (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    0 < T.phi t x := T.output_pos t _ (T.capital_pos t hx)

theorem hasDerivAt_phi (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (T.phi t) (T.phiDerivative t x) x :=
  (T.hasDerivAt_output t _ (T.capital_pos t hx)).comp x (T.hasDerivAt_capital t hx)

theorem capital_eq_ratio_mul_phi (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    T.capital t x = x * T.phi t x :=
  (div_eq_iff (ne_of_gt (T.phi_pos t hx))).mp (T.ratio_capital t hx)

/-- The 2004 elasticity equation, now with the inverse actually constructed. -/
theorem elasticity (T : Technology) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    T.phiDerivative t x * x / T.phi t x =
      T.share t (T.capital t x) / (1 - T.share t (T.capital t x)) := by
  apply UzawaElasticity.output_capitalOutput_elasticity (T.hasDerivAt_capital t hx)
    (T.hasDerivAt_output t _ (T.capital_pos t hx))
    (T.phi_pos t hx) (T.share_lt_one t _ (T.capital_pos t hx))
  filter_upwards [isOpen_Ioi.mem_nhds hx] with u hu
  exact T.capital_eq_ratio_mul_phi t hu

/-- The added quantifier: shares agree at every positive capital/output
coordinate, across dates. Constancy on one path is insufficient. -/
def SharesInvariant (T : Technology) (reference : ℝ) : Prop :=
  ∀ t x, 0 < x → T.share t (T.capital t x) =
    T.share reference (T.capital reference x)

/-- The separation factor is defined from the technologies, not from a path. -/
noncomputable def technology (T : Technology) (reference t : ℝ) : ℝ :=
  T.phi t 1 / T.phi reference 1

theorem technology_pos (T : Technology) (reference t : ℝ) :
    0 < T.technology reference t :=
  div_pos (T.phi_pos t zero_lt_one) (T.phi_pos reference zero_lt_one)

@[simp] theorem technology_reference (T : Technology) (reference : ℝ) :
    T.technology reference reference = 1 :=
  div_self (ne_of_gt (T.phi_pos reference zero_lt_one))

/-- Equal shares imply that the ratio of the two coordinate technologies
has derivative zero throughout the positive half-line. -/
theorem hasDerivAt_phi_ratio_zero (T : Technology) (reference : ℝ)
    (hinvariant : T.SharesInvariant reference) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun u => T.phi t u / T.phi reference u) 0 x := by
  have ht := ne_of_gt (T.phi_pos t hx)
  have hr := ne_of_gt (T.phi_pos reference hx)
  have heq : T.phiDerivative t x * x / T.phi t x =
      T.phiDerivative reference x * x / T.phi reference x := by
    rw [T.elasticity t hx, T.elasticity reference hx, hinvariant t x hx]
  have hcross : T.phiDerivative t x * T.phi reference x =
      T.phi t x * T.phiDerivative reference x := by
    apply mul_right_cancel₀ (ne_of_gt hx)
    nlinarith [(div_eq_div_iff ht hr).mp heq]
  convert! (T.hasDerivAt_phi t hx).fun_div (T.hasDerivAt_phi reference hx) hr using 1
  rw [hcross]
  simp

/-- The mean value theorem performs the separation step on a connected domain.
No integration constant or domain-wide identity is silently assumed. -/
theorem separation (T : Technology) (reference : ℝ)
    (hinvariant : T.SharesInvariant reference) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    T.phi t x = T.technology reference t * T.phi reference x := by
  have hd (u : ℝ) (hu : 0 < u) :
      HasDerivAt (fun v => T.phi t v / T.phi reference v) 0 u :=
    T.hasDerivAt_phi_ratio_zero reference hinvariant t hu
  have heq : T.phi t x / T.phi reference x = T.phi t 1 / T.phi reference 1 :=
    isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
      (fun u hu => (hd u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hd u hu).deriv) hx (by norm_num)
  exact (div_eq_iff (ne_of_gt (T.phi_pos reference hx))).mp heq

/-- Reconstruct the original intensive production function from separation.
This holds for every positive capital input, not only an observed path. -/
theorem intensive_representation (T : Technology) (reference : ℝ)
    (hinvariant : T.SharesInvariant reference) (t : ℝ) {k : ℝ} (hk : 0 < k) :
    T.output t k = T.technology reference t *
      T.output reference (k / T.technology reference t) := by
  let x := T.ratio t k
  have hx : 0 < x := T.ratio_pos t hk
  have hinv : T.capital t x = k := T.capital_ratio t hk
  have hsep := T.separation reference hinvariant t hx
  have hscaled : k / T.technology reference t = T.capital reference x := by
    apply (div_eq_iff (ne_of_gt (T.technology_pos reference t))).mpr
    calc
      k = T.capital t x := hinv.symm
      _ = x * T.phi t x := T.capital_eq_ratio_mul_phi t hx
      _ = T.capital reference x * T.technology reference t := by
        rw [hsep, T.capital_eq_ratio_mul_phi reference hx]
        ring
  calc
    T.output t k = T.phi t x := by simp only [phi, hinv]
    _ = T.technology reference t * T.phi reference x := hsep
    _ = _ := by rw [hscaled]; rfl

/-- The CRS technology associated with the intensive production function. -/
noncomputable def production (T : Technology) (t K L : ℝ) : ℝ :=
  L * T.output t (K / L)

/-- The homogenized intensive technology really is the original F whenever
F has constant returns and its labor-one slice is `T.output`. -/
theorem production_eq_original (T : Technology) {F : ℝ → ℝ → ℝ → ℝ}
    (t : ℝ) {K L : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hslice : ∀ k, 0 < k → T.output t k = F k 1 t)
    (hCRS : ∀ k l a, 0 < k → 0 < l → 0 < a →
      F (a * k) (a * l) t = a * F k l t) :
    T.production t K L = F K L t := by
  have h := hCRS (K / L) 1 L (div_pos hK hL) zero_lt_one hL
  have hdiv : L * (K / L) = K := by field_simp
  rw [hdiv, mul_one] at h
  rw [production, hslice _ (div_pos hK hL)]
  exact h.symm

/-- The repaired domain-wide representation obtained through the elasticity
proof. The reference function is the original technology at `reference`. -/
theorem production_representation (T : Technology) (reference : ℝ)
    (hinvariant : T.SharesInvariant reference) (t : ℝ) {K L : ℝ}
    (hK : 0 < K) (hL : 0 < L) :
    T.production t K L =
      T.production reference K (T.technology reference t * L) := by
  unfold production
  rw [T.intensive_representation reference hinvariant t (div_pos hK hL)]
  have harg : K / L / T.technology reference t = K / (T.technology reference t * L) := by
    rw [div_div, mul_comm L]
  rw [harg]
  ring

/-- Transfer the domain-wide representation back to the original CRS F.
The reference-date function is unchanged, preserving any additional
neoclassical properties of that function without inferring them from a path. -/
theorem original_production_representation (T : Technology) (reference : ℝ)
    (hinvariant : T.SharesInvariant reference) {F : ℝ → ℝ → ℝ → ℝ}
    (hslice : ∀ t k, 0 < k → T.output t k = F k 1 t)
    (hCRS : ∀ t k l a, 0 < k → 0 < l → 0 < a →
      F (a * k) (a * l) t = a * F k l t)
    (t : ℝ) {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    F K L t = F K (T.technology reference t * L) reference := by
  calc
    F K L t = T.production t K L :=
      (T.production_eq_original t hK hL (hslice t) (hCRS t)).symm
    _ = T.production reference K (T.technology reference t * L) :=
      T.production_representation reference hinvariant t hK hL
    _ = _ := T.production_eq_original reference hK
      (mul_pos (T.technology_pos reference t) hL) (hslice reference) (hCRS reference)

/-- Separation identifies the same technology factor at any positive ratio. -/
theorem technology_eq_phi_ratio (T : Technology) (reference : ℝ)
    (hinvariant : T.SharesInvariant reference) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    T.technology reference t = T.phi t x / T.phi reference x := by
  apply (eq_div_iff (ne_of_gt (T.phi_pos reference hx))).mpr
  exact (T.separation reference hinvariant t hx).symm

/-- Translate observed production into the capital/output coordinates. -/
theorem phi_of_production (T : Technology) (t : ℝ) {K L Y : ℝ}
    (hK : 0 < K) (hL : 0 < L) (hY : 0 < Y)
    (hproduction : Y = T.production t K L) :
    T.phi t (K / Y) = Y / L := by
  have hf : T.output t (K / L) = Y / L := by
    rw [hproduction, production]
    field_simp
  have hx : T.ratio t (K / L) = K / Y := by
    unfold ratio
    rw [hf]
    field_simp
  rw [← hx]
  simp only [phi, T.capital_ratio t (div_pos hK hL), hf]

/-- Accounting calibrates the factor derived by separation to the exponential
index. Only the rate-equality lemma is shared with the Schlicht proof;
its representation theorem is not used. -/
theorem technology_eq_balanced_growth (T : Technology) (p : Uzawa.BalancedGrowthData)
    (hinvariant : T.SharesInvariant p.start)
    (hK : 0 < p.capitalInitial) (hL : 0 < p.laborInitial)
    (hC : 0 ≤ p.consumptionInitial) (hI : 0 < p.investmentInitial)
    (hresource : ∀ t, p.start ≤ t → p.output t = p.consumption t + p.investment t)
    (haccum : ∀ t, p.start ≤ t → HasDerivAt p.capital
      (p.investment t - p.depreciation * p.capital t) t)
    (hproduction : ∀ t, p.start ≤ t →
      p.output t = T.production t (p.capital t) (p.labor t)) :
    ∀ t, p.start ≤ t → T.technology p.start t = p.technology t := by
  have hy0 : 0 < p.outputInitial := by
    have h := hresource p.start le_rfl
    simp only [Uzawa.BalancedGrowthData.output, Uzawa.BalancedGrowthData.consumption,
      Uzawa.BalancedGrowthData.investment, Uzawa.trajectory_start] at h
    linarith
  have hrates := p.outputGrowth_eq_capitalGrowth hC hI hresource haccum
  have hratio (t : ℝ) : p.capital t / p.output t = p.capitalInitial / p.outputInitial := by
    simp only [Uzawa.BalancedGrowthData.capital, Uzawa.BalancedGrowthData.output,
      Uzawa.trajectory]
    rw [← hrates]
    field_simp
  have hphi (t : ℝ) (ht : p.start ≤ t) :
      T.phi t (p.capitalInitial / p.outputInitial) = p.output t / p.labor t := by
    have h := T.phi_of_production t (Uzawa.trajectory_pos hK _ _ _)
      (Uzawa.trajectory_pos hL _ _ _) (Uzawa.trajectory_pos hy0 _ _ _) (hproduction t ht)
    change T.phi t (p.capital t / p.output t) = p.output t / p.labor t at h
    rwa [hratio t] at h
  intro t ht
  rw [T.technology_eq_phi_ratio p.start hinvariant t (div_pos hK hy0),
    hphi t ht, hphi p.start le_rfl, p.output_per_worker t, p.output_per_worker p.start,
    Uzawa.trajectory_start]
  unfold Uzawa.trajectory Uzawa.BalancedGrowthData.technology
  field_simp

/-- The repaired 2004-style theorem: separation supplies the representation;
positive-investment accounting supplies the index's specified growth rate. -/
theorem repaired_labor_augmenting_representation
    (T : Technology) (p : Uzawa.BalancedGrowthData)
    (hinvariant : T.SharesInvariant p.start)
    (hK : 0 < p.capitalInitial) (hL : 0 < p.laborInitial)
    (hC : 0 ≤ p.consumptionInitial) (hI : 0 < p.investmentInitial)
    (hresource : ∀ t, p.start ≤ t → p.output t = p.consumption t + p.investment t)
    (haccum : ∀ t, p.start ≤ t → HasDerivAt p.capital
      (p.investment t - p.depreciation * p.capital t) t)
    (hproduction : ∀ t, p.start ≤ t →
      p.output t = T.production t (p.capital t) (p.labor t)) :
    ∀ t, p.start ≤ t → p.output t =
      T.production p.start (p.capital t) (p.technology t * p.labor t) := by
  intro t ht
  have hk : 0 < p.capital t := Uzawa.trajectory_pos hK _ _ _
  have hl : 0 < p.labor t := Uzawa.trajectory_pos hL _ _ _
  rw [hproduction t ht,
    T.production_representation p.start hinvariant t hk hl,
    T.technology_eq_balanced_growth p hinvariant hK hL hC hI hresource haccum hproduction t ht]

/-- At the initial date use a within-domain derivative; no assumptions about
the technology path before the start date are needed for calibration. -/
theorem hasDerivWithinAt_technology_of_balanced_growth
    (T : Technology) (p : Uzawa.BalancedGrowthData)
    (heq : ∀ t, p.start ≤ t → T.technology p.start t = p.technology t)
    {t : ℝ} (ht : p.start ≤ t) :
    HasDerivWithinAt (T.technology p.start)
      ((p.outputGrowth - p.laborGrowth) * T.technology p.start t) (Ici p.start) t := by
  rw [heq t ht]
  apply (p.hasDerivAt_technology t).hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with u hu
    exact heq u hu
  · exact heq t ht

end Technology
end UzawaModern.UzawaSeparation
