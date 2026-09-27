/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import RamseyCassKoopmans.CassRate
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Cass comparative statics and comparative dynamics

**Statics.** The steady state solves `f'(k*) = d + m`, so `k* = g(d + m)` for the
inverse marginal product `g = marginalInverse`. We prove `g` is strictly decreasing
and, where `f''(k*) < 0`, differentiable with `g' = 1 / f''(k*)` (inverse function
theorem). Hence `∂k*/∂d = ∂k*/∂m = 1/f''(k*) < 0`, `∂c*/∂d = d/f''(k*) < 0`,
`∂c*/∂m = d/f''(k*) - k* < 0`; with productivity `A f`, `k*` rises with `A`.

**Dynamics.** `patience_rise`: starting at the old steady state, a permanent fall
in the discount rate makes capital rise strictly to the new, higher steady state;
consumption falls strictly on impact below the old steady-state level, then rises
strictly to a higher new level. `impatience_rise` is the mirror image.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

theorem CassPrimitives.existsUnique_marginal (P : CassPrimitives f U d m) {r : ℝ}
    (hr : 0 < r) : ∃! k : ℝ, 0 < k ∧ deriv f k = r :=
  existsUnique_positive_root_of_inada (deriv f) r hr P.f_prime_cont
    (production_deriv_strictAnti f P.f_conc P.f_diff) P.f_inada0 P.f_inadaTop

/-- The inverse marginal product: the unique positive capital with `f'(k) = r`. -/
noncomputable def marginalInverse (P : CassPrimitives f U d m) (r : ℝ) : ℝ :=
  if hr : 0 < r then Classical.choose (P.existsUnique_marginal hr).exists else 0

theorem marginalInverse_spec (P : CassPrimitives f U d m) {r : ℝ} (hr : 0 < r) :
    0 < marginalInverse P r ∧ deriv f (marginalInverse P r) = r := by
  simp only [marginalInverse, hr, ↓reduceDIte]
  exact Classical.choose_spec (P.existsUnique_marginal hr).exists

theorem marginalInverse_eq (P : CassPrimitives f U d m) {r k : ℝ} (hk : 0 < k)
    (he : deriv f k = r) : marginalInverse P r = k := by
  have hr : 0 < r := he ▸ P.f_prime_pos k hk
  exact (P.existsUnique_marginal hr).unique (marginalInverse_spec P hr) ⟨hk, he⟩

theorem marginalInverse_deriv (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k) :
    marginalInverse P (deriv f k) = k := marginalInverse_eq P hk rfl

/-- The steady state of any economy sharing the technology `f` is `g(δ + μ)`. -/
theorem cassSteady_eq_marginalInverse (P : CassPrimitives f U d m) {V : ℝ → ℝ} {δ μ : ℝ}
    (P' : CassPrimitives f V δ μ) : cassSteady P' = marginalInverse P (δ + μ) := by
  have hr : 0 < δ + μ := add_pos P'.d_pos P'.m_pos
  exact cassSteady_eq P' (marginalInverse_spec P hr).1 (marginalInverse_spec P hr).2

theorem marginalInverse_strictAnti (P : CassPrimitives f U d m) :
    StrictAntiOn (marginalInverse P) (Ioi 0) := by
  intro r hr s hs hrs
  have hr' : (0 : ℝ) < r := hr
  have hs' : (0 : ℝ) < s := hs
  by_contra hle
  push Not at hle
  have hanti := (production_deriv_strictAnti f P.f_conc P.f_diff).antitoneOn
    (marginalInverse_spec P hr').1 (marginalInverse_spec P hs').1 hle
  rw [(marginalInverse_spec P hr').2, (marginalInverse_spec P hs').2] at hanti
  linarith

/-- Inverse function theorem: `g' = 1 / f''(g(r))` where `f''(g(r)) ≠ 0`. -/
theorem marginalInverse_hasDerivAt (P : CassPrimitives f U d m) {r : ℝ} (hr : 0 < r)
    (hf2 : deriv (deriv f) (marginalInverse P r) ≠ 0) :
    HasDerivAt (marginalInverse P) (deriv (deriv f) (marginalInverse P r))⁻¹ r := by
  obtain ⟨hk, hkr⟩ := marginalInverse_spec P hr
  set k := marginalInverse P r
  have hstrict : HasStrictDerivAt (deriv f) (deriv (deriv f) k) k :=
    hasStrictDerivAt_of_hasDerivAt_of_continuousAt
      ((lt_mem_nhds hk).mono (fun y hy => (P.f_second y hy).hasDerivAt))
      (P.f_second_cont.continuousAt (Ioi_mem_nhds hk))
  have h := hstrict.to_local_left_inverse hf2
    ((lt_mem_nhds hk).mono (fun y hy => marginalInverse_deriv P hy))
  rw [hkr] at h
  exact h.hasDerivAt

/-- `∂k*/∂d = 1/f''(k*) < 0`. -/
theorem steady_hasDerivAt_discount (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) :
    HasDerivAt (fun δ => marginalInverse P (δ + m)) (deriv (deriv f) (cassSteady P))⁻¹ d ∧
      (deriv (deriv f) (cassSteady P))⁻¹ < 0 := by
  have hr : 0 < d + m := add_pos P.d_pos P.m_pos
  have heq := cassSteady_eq_marginalInverse P P
  rw [heq] at hf2 ⊢
  exact ⟨(marginalInverse_hasDerivAt P hr (ne_of_lt hf2)).comp_add_const d m,
    inv_lt_zero.mpr hf2⟩

/-- `∂k*/∂m = 1/f''(k*) < 0`. -/
theorem steady_hasDerivAt_dilution (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) :
    HasDerivAt (fun μ => marginalInverse P (d + μ)) (deriv (deriv f) (cassSteady P))⁻¹ m := by
  have hr : 0 < d + m := add_pos P.d_pos P.m_pos
  have heq := cassSteady_eq_marginalInverse P P
  rw [heq] at hf2 ⊢
  exact (marginalInverse_hasDerivAt P hr (ne_of_lt hf2)).comp_const_add d m

/-- `∂c*/∂d = d / f''(k*) < 0`. -/
theorem steadyConsumption_hasDerivAt_discount (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) :
    HasDerivAt (fun δ => f (marginalInverse P (δ + m)) - m * marginalInverse P (δ + m))
      (d * (deriv (deriv f) (cassSteady P))⁻¹) d ∧
      d * (deriv (deriv f) (cassSteady P))⁻¹ < 0 := by
  obtain ⟨hg, hneg⟩ := steady_hasDerivAt_discount P hf2
  have heq := cassSteady_eq_marginalInverse P P
  have hks := (cassSteady_spec P)
  have hfd : HasDerivAt f (deriv f (marginalInverse P (d + m))) (marginalInverse P (d + m)) :=
    (P.f_diff _ (heq ▸ hks.1)).hasDerivAt
  have h := (hfd.comp d hg).sub (hg.const_mul m)
  refine ⟨h.congr_deriv ?_, mul_neg_of_pos_of_neg P.d_pos hneg⟩
  rw [← heq, hks.2]
  ring

/-- `∂c*/∂m = d / f''(k*) - k* < 0`. -/
theorem steadyConsumption_hasDerivAt_dilution (P : CassPrimitives f U d m)
    (hf2 : deriv (deriv f) (cassSteady P) < 0) :
    HasDerivAt (fun μ => f (marginalInverse P (d + μ)) - μ * marginalInverse P (d + μ))
      (d * (deriv (deriv f) (cassSteady P))⁻¹ - cassSteady P) m ∧
      d * (deriv (deriv f) (cassSteady P))⁻¹ - cassSteady P < 0 := by
  have hg := steady_hasDerivAt_dilution P hf2
  have hneg := (steady_hasDerivAt_discount P hf2).2
  have heq := cassSteady_eq_marginalInverse P P
  have hks := (cassSteady_spec P)
  have hfd : HasDerivAt f (deriv f (marginalInverse P (d + m))) (marginalInverse P (d + m)) :=
    (P.f_diff _ (heq ▸ hks.1)).hasDerivAt
  have h := (hfd.comp m hg).sub ((hasDerivAt_id m).mul hg)
  refine ⟨h.congr_deriv ?_, by nlinarith [P.d_pos, hks.1]⟩
  simp only [id]
  rw [← heq, hks.2]
  ring

/-- A more impatient economy has less steady-state capital and consumption. -/
theorem steady_strictAnti_discount (P1 : CassPrimitives f U d m) {d' : ℝ}
    (P2 : CassPrimitives f U d' m) (hdd : d < d') :
    cassSteady P2 < cassSteady P1 ∧ cassSteadyConsumption P2 < cassSteadyConsumption P1 := by
  rw [cassSteady_eq_marginalInverse P1 P2, cassSteady_eq_marginalInverse P1 P1]
  have hlt : marginalInverse P1 (d' + m) < marginalInverse P1 (d + m) :=
    marginalInverse_strictAnti P1 (add_pos P1.d_pos P1.m_pos)
      (add_pos P2.d_pos P2.m_pos) (by linarith)
  refine ⟨hlt, ?_⟩
  simp only [cassSteadyConsumption]
  rw [cassSteady_eq_marginalInverse P1 P2, cassSteady_eq_marginalInverse P1 P1]
  set k1 := marginalInverse P1 (d + m)
  set k2 := marginalInverse P1 (d' + m)
  have hk1 := marginalInverse_spec P1 (add_pos P1.d_pos P1.m_pos)
  have hk2 := marginalInverse_spec P1 (add_pos P2.d_pos P2.m_pos)
  -- concavity: `f(k1) - f(k2) > f'(k1) (k1 - k2) = (d + m)(k1 - k2) > m (k1 - k2)`
  have hs := strict_concave_support P1.f_conc (mem_Ici.mpr hk1.1.le) (mem_Ici.mpr hk2.1.le)
    (P1.f_diff k1 hk1.1).hasDerivAt (ne_of_lt hlt)
  rw [hk1.2] at hs
  have := mul_pos P1.d_pos (sub_pos.mpr hlt)
  nlinarith

/-- A larger dilution rate lowers steady-state capital. -/
theorem steady_strictAnti_dilution' (P1 : CassPrimitives f U d m) {m' : ℝ}
    (P2 : CassPrimitives f U d m') (hmm : m < m') : cassSteady P2 < cassSteady P1 := by
  rw [cassSteady_eq_marginalInverse P1 P2, cassSteady_eq_marginalInverse P1 P1]
  exact marginalInverse_strictAnti P1 (add_pos P1.d_pos P1.m_pos)
    (add_pos P2.d_pos P2.m_pos) (by linarith)

/-- Higher productivity `A f` raises steady-state capital: its steady state is
`g((d + m)/A)`. -/
theorem steady_productivity (P : CassPrimitives f U d m) {A : ℝ} (hA : 0 < A)
    (PA : CassPrimitives (fun k => A * f k) U d m) :
    cassSteady PA = marginalInverse P ((d + m) / A) := by
  have hr : 0 < (d + m) / A := div_pos (add_pos P.d_pos P.m_pos) hA
  obtain ⟨hk, hkr⟩ := marginalInverse_spec P hr
  apply cassSteady_eq PA hk
  rw [deriv_const_mul A (P.f_diff _ hk), hkr]
  field_simp

theorem steady_strictMono_productivity (P : CassPrimitives f U d m) {A1 A2 : ℝ}
    (hA1 : 0 < A1) (hA : A1 < A2) (P1 : CassPrimitives (fun k => A1 * f k) U d m)
    (P2 : CassPrimitives (fun k => A2 * f k) U d m) : cassSteady P1 < cassSteady P2 := by
  rw [steady_productivity P hA1 P1, steady_productivity P (hA1.trans hA) P2]
  have hr := add_pos P.d_pos P.m_pos
  exact marginalInverse_strictAnti P (div_pos hr (hA1.trans hA)) (div_pos hr hA1)
    (div_lt_div_of_pos_left hr hA1 hA)

/-- `z(t) = (k(t) - k₀) e^{-λt}` is monotone in the direction of the sign of
`k̇ - λ (k - k₀)`: the Gronwall step behind the impact effects. -/
theorem gap_exp_hasDerivAt (a : FeasiblePath f m) (k₀ lam : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => (a.capital s - k₀) * Real.exp (-lam * s))
      ((f (a.capital t) - m * a.capital t - a.consumption t - lam * (a.capital t - k₀)) *
        Real.exp (-lam * t)) t := by
  have he : HasDerivAt (fun s => Real.exp (-lam * s)) (Real.exp (-lam * t) * (-lam)) t := by
    have := ((hasDerivAt_id t).const_mul (-lam)).exp
    simpa only [id, mul_one] using this
  refine (((a.hasDerivAt_capital' ht).sub_const k₀).mul he).congr_deriv ?_
  ring

/-- A permanent rise in patience, starting from the old steady state: capital rises
strictly to the new, higher steady state; consumption falls strictly on impact
below the old steady-state level and then rises strictly to a higher new level. -/
theorem patience_rise (P1 : CassPrimitives f U d m) {d' : ℝ} (P2 : CassPrimitives f U d' m)
    (hdd : d' < d) {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d' m a q)
    (h0 : a.capital 0 = cassSteady P1) :
    cassSteady P1 < cassSteady P2 ∧ StrictMonoOn a.capital (Ici 0) ∧
      StrictMonoOn a.consumption (Ici 0) ∧
      a.consumption 0 < cassSteadyConsumption P1 ∧
      cassSteadyConsumption P1 < cassSteadyConsumption P2 ∧
      Tendsto a.capital atTop (𝓝 (cassSteady P2)) ∧
      Tendsto a.consumption atTop (𝓝 (cassSteadyConsumption P2)) := by
  obtain ⟨hlt, hclt⟩ := steady_strictAnti_discount P2 P1 hdd
  obtain ⟨hk, hcon, hbelow, -, -⟩ := hc.dynamics P2
  obtain ⟨hmono, hcmono⟩ := hbelow (h0 ▸ hlt)
  refine ⟨hlt, hmono, hcmono, ?_, hclt, hk, hcon⟩
  by_contra hge
  push Not at hge
  set k1 := cassSteady P1
  have hk1 := cassSteady_spec P1
  -- then `k̇ ≤ d (k - k1)`, so `(k - k1) e^{-dt}` is antitone and `k ≤ k1`
  have hanti : AntitoneOn (fun s => (a.capital s - k1) * Real.exp (-d * s)) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (HasDerivAt.continuousOn (fun s hs => gap_exp_hasDerivAt a k1 d hs))
      (fun s hs => (gap_exp_hasDerivAt a k1 d (interior_subset hs)).differentiableAt
        |>.differentiableWithinAt)
    intro s hs
    have hs0 : 0 ≤ s := interior_subset hs
    rw [(gap_exp_hasDerivAt a k1 d hs0).deriv]
    apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
    have hcs : a.consumption 0 ≤ a.consumption s := hcmono.monotoneOn (mem_Ici.mpr le_rfl) hs0 hs0
    have hsup := concave_support P1.f_conc.concaveOn (mem_Ici.mpr hk1.1.le)
      (a.capital_nonneg s hs0) (P1.f_diff k1 hk1.1).hasDerivAt
    rw [hk1.2] at hsup
    simp only [cassSteadyConsumption] at hge
    nlinarith
  have h1 := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr zero_le_one) zero_le_one
  simp only [mul_zero, Real.exp_zero, mul_one, h0, sub_self] at h1
  have hk1pos : a.capital 0 < a.capital 1 := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr zero_le_one)
    zero_lt_one
  have := mul_pos (sub_pos.mpr (h0 ▸ hk1pos)) (Real.exp_pos (-d))
  linarith

/-- A permanent rise in impatience, starting from the old steady state: capital falls
strictly to the new, lower steady state; consumption jumps strictly above the old
steady-state level and then falls strictly to a lower new level. -/
theorem impatience_rise (P1 : CassPrimitives f U d m) {d' : ℝ} (P2 : CassPrimitives f U d' m)
    (hdd : d < d') {a : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d' m a q)
    (h0 : a.capital 0 = cassSteady P1) :
    cassSteady P2 < cassSteady P1 ∧ StrictAntiOn a.capital (Ici 0) ∧
      StrictAntiOn a.consumption (Ici 0) ∧
      cassSteadyConsumption P1 < a.consumption 0 ∧
      cassSteadyConsumption P2 < cassSteadyConsumption P1 ∧
      Tendsto a.capital atTop (𝓝 (cassSteady P2)) ∧
      Tendsto a.consumption atTop (𝓝 (cassSteadyConsumption P2)) := by
  obtain ⟨hlt, hclt⟩ := steady_strictAnti_discount P1 P2 hdd
  obtain ⟨hk, hcon, -, habove, -⟩ := hc.dynamics P2
  obtain ⟨hanti, hcanti⟩ := habove (h0 ▸ hlt)
  refine ⟨hlt, hanti, hcanti, ?_, hclt, hk, hcon⟩
  by_contra hle
  push Not at hle
  set k1 := cassSteady P1
  set k2 := cassSteady P2
  have hk2 := cassSteady_spec P2
  have hbnd := (hc.capital_bounds P2).2 (h0 ▸ hlt)
  -- then `k̇ ≥ d' (k - k1)`, so `(k - k1) e^{-d't}` is monotone and `k ≥ k1`
  have hmono : MonotoneOn (fun s => (a.capital s - k1) * Real.exp (-d' * s)) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (HasDerivAt.continuousOn (fun s hs => gap_exp_hasDerivAt a k1 d' hs))
      (fun s hs => (gap_exp_hasDerivAt a k1 d' (interior_subset hs)).differentiableAt
        |>.differentiableWithinAt)
    intro s hs
    have hs0 : 0 ≤ s := interior_subset hs
    rw [(gap_exp_hasDerivAt a k1 d' hs0).deriv]
    apply mul_nonneg _ (Real.exp_pos _).le
    have hcs : a.consumption s ≤ a.consumption 0 :=
      hcanti.antitoneOn (mem_Ici.mpr le_rfl) hs0 hs0
    have hks := (hbnd s hs0).1
    have hkle : a.capital s ≤ k1 := by
      rw [← h0]
      exact hanti.antitoneOn (mem_Ici.mpr le_rfl) hs0 hs0
    have hkpos : 0 < a.capital s := hk2.1.trans hks
    have hsup := concave_support P2.f_conc.concaveOn (mem_Ici.mpr hkpos.le)
      (mem_Ici.mpr (hkpos.le.trans hkle)) (P2.f_diff _ hkpos).hasDerivAt
    have hfd : deriv f (a.capital s) ≤ d' + m := by
      rw [← hk2.2]
      exact (production_deriv_strictAnti f P2.f_conc P2.f_diff).antitoneOn hk2.1 hkpos hks.le
    have hprod : deriv f (a.capital s) * (k1 - a.capital s) ≤ (d' + m) * (k1 - a.capital s) :=
      mul_le_mul_of_nonneg_right hfd (sub_nonneg.mpr hkle)
    simp only [cassSteadyConsumption] at hle
    nlinarith
  have h1 := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr zero_le_one) zero_le_one
  simp only [mul_zero, Real.exp_zero, mul_one, h0, sub_self] at h1
  have hk1lt : a.capital 1 < a.capital 0 := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr zero_le_one)
    zero_lt_one
  have := mul_pos (sub_pos.mpr (h0 ▸ hk1lt)) (Real.exp_pos (-d'))
  linarith

end RamseyCassKoopmans
