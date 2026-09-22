/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/
import Solow1956.Growth.SolowComparative

/-! # Golden Rule saving and the stationary connection to Cass

Acemoglu Chapter 2, Proposition 2.4, with depreciation replaced by effective
dilution `m`. The supporting-line proof and the modified-Golden-Rule comparison
adapt the corresponding lemmas in our Cass formalization. Matching steady states
does not assert that the Solow and Cass transition paths are identical.
-/

open Set Filter Topology

namespace Solow1956.Neoclassical

variable {f : ℝ → ℝ}

theorem existsUnique_marginal_root (h : Technology f) {r : ℝ} (hr : 0 < r) :
    ∃! k : ℝ, 0 < k ∧ deriv f k = r := by
  have hz : ∀ᶠ k : ℝ in 𝓝[>] (0 : ℝ), 0 < k := self_mem_nhdsWithin
  obtain ⟨a, ha, hma⟩ := (hz.and (h.inada_zero.eventually_gt_atTop r)).exists
  obtain ⟨b, hab, hmb⟩ := ((eventually_gt_atTop a).and
    (h.inada_top.eventually (gt_mem_nhds hr))).exists
  obtain ⟨k, hk, he⟩ := intermediate_value_Icc' hab.le
    (h.derivative_continuous.mono (fun _ hx => ha.trans_le hx.1)) ⟨hmb.le, hma.le⟩
  have hp := ha.trans_le hk.1
  exact ⟨k, ⟨hp, he⟩, fun y hy => h.marginal_strictAnti.injOn hy.1 hp (hy.2.trans he.symm)⟩

theorem golden_rule_maximizes (h : Technology f) {kg m k : ℝ}
    (hkg : 0 < kg) (hgold : deriv f kg = m) (hk : 0 ≤ k) (hne : k ≠ kg) :
    f k - m * k < f kg - m * kg := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have ht := h.concave.deriv_lt_slope hk hkg.le hlt (h.differentiable kg hkg)
    rw [hgold, slope_def_field] at ht
    have := (lt_div_iff₀ (sub_pos.mpr hlt)).mp ht
    nlinarith
  · have ht := h.concave.slope_lt_deriv hkg.le hk hgt (h.differentiable kg hkg)
    rw [hgold, slope_def_field] at ht
    have := (div_lt_iff₀ (sub_pos.mpr hgt)).mp ht
    nlinarith

noncomputable def sustainingSaving (f : ℝ → ℝ) (m k : ℝ) : ℝ := m * k / f k

theorem sustainingSaving_bounds (h : Technology f) {m k : ℝ}
    (hm : 0 < m) (hk : 0 < k) (hmp : m ≤ deriv f k) :
    0 < sustainingSaving f m k ∧ sustainingSaving f m k < 1 := by
  have hy := h.output_pos hk
  refine ⟨div_pos (mul_pos hm hk) hy, (div_lt_one hy).mpr ?_⟩
  exact (mul_le_mul_of_nonneg_right hmp hk.le).trans_lt (h.output_gap hk)

theorem sustainingSaving_equilibrium (h : Technology f) {m k : ℝ} (hk : 0 < k) :
    rate f (sustainingSaving f m k) m k = 0 := by
  simp only [rate, sustainingSaving, div_mul_cancel₀ _ (ne_of_gt (h.output_pos hk)), sub_self]

theorem sustainingSaving_stock (h : Technology f) {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    steadyCapital h (sustainingSaving f m k) m = k :=
  steadyCapital_eq h (div_pos (mul_pos hm hk) (h.output_pos hk)) hm hk
    (sustainingSaving_equilibrium h hk)

theorem sustainingSaving_strictMono (h : Technology f) {m : ℝ} (hm : 0 < m) :
    StrictMonoOn (sustainingSaving f m) (Ioi 0) := by
  intro k hk l hl hkl
  have hg := (div_lt_div_iff₀ hl hk).mp (h.average_strictAnti hk hl hkl)
  apply (div_lt_div_iff₀ (h.output_pos hk) (h.output_pos hl)).mpr
  have := mul_lt_mul_of_pos_left hg hm
  nlinarith

theorem stationary_consumption_identity (h : Technology f) {s m : ℝ}
    (hs : 0 < s) (hm : 0 < m) :
    (1 - s) * f (steadyCapital h s m) =
      f (steadyCapital h s m) - m * steadyCapital h s m := by
  have he := (steadyCapital_spec h hs hm).2
  dsimp [rate] at he
  nlinarith

/-- The Golden Rule is a unique global optimum over all saving rates in (0,1),
not only a first-order condition or a local maximum. -/
theorem exists_unique_golden_saving (h : Technology f) {m : ℝ} (hm : 0 < m) :
    ∃ kg sg : ℝ, 0 < kg ∧ deriv f kg = m ∧
      0 < sg ∧ sg < 1 ∧ sg = sustainingSaving f m kg ∧
      steadyCapital h sg m = kg ∧
      ∀ s, 0 < s → s < 1 → s ≠ sg →
        (1 - s) * f (steadyCapital h s m) < (1 - sg) * f kg := by
  obtain ⟨kg, ⟨hkg, hg⟩, _⟩ := existsUnique_marginal_root h hm
  let sg := sustainingSaving f m kg
  obtain ⟨hsg, hsg1⟩ := sustainingSaving_bounds h hm hkg hg.ge
  have hstock := sustainingSaving_stock h hm hkg
  refine ⟨kg, sg, hkg, hg, hsg, hsg1, rfl, hstock, ?_⟩
  intro s hs _ hne
  have hne' : steadyCapital h s m ≠ kg := by
    intro he
    have hsroot := (steadyCapital_spec h hs hm).2
    have hgroot := sustainingSaving_equilibrium h (m := m) hkg
    rw [he] at hsroot
    dsimp [rate] at hsroot hgroot
    have hprod : (s - sg) * f kg = 0 := by dsimp [sg]; nlinarith
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right (ne_of_gt (h.output_pos hkg))))
  rw [stationary_consumption_identity h hs hm]
  have hgoldc : (1 - sg) * f kg = f kg - m * kg := by
    simpa only [hstock] using stationary_consumption_identity h hsg hm
  rw [hgoldc]
  exact golden_rule_maximizes h hkg hg (steadyCapital_spec h hs hm).1.le hne'

/-- A Cass stationary stock satisfying `f'(kc)=d+m` is supported by a unique
constant Solow saving rate below Golden Rule saving when `d>0`. This comparison
uses the stationary equations, not an assertion about identical transition paths. -/
theorem cass_stationary_bridge (h : Technology f) {d m kc kg : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hkc : 0 < kc) (hkg : 0 < kg)
    (hc : deriv f kc = d + m) (hg : deriv f kg = m) :
    kc < kg ∧ 0 < sustainingSaving f m kc ∧
      sustainingSaving f m kc < sustainingSaving f m kg ∧
      sustainingSaving f m kg < 1 ∧
      steadyCapital h (sustainingSaving f m kc) m = kc ∧
      (1 - sustainingSaving f m kc) * f kc = f kc - m * kc := by
  have hlt : kc < kg := by
    by_contra hn
    have := h.marginal_strictAnti.antitoneOn hkg hkc (le_of_not_gt hn)
    rw [hc, hg] at this
    linarith
  refine ⟨hlt, (sustainingSaving_bounds h hm hkc (by rw [hc]; linarith)).1,
    sustainingSaving_strictMono h hm hkc hkg hlt,
    (sustainingSaving_bounds h hm hkg hg.ge).2, sustainingSaving_stock h hm hkc, ?_⟩
  have he := sustainingSaving_equilibrium h (m := m) hkc
  dsimp [rate] at he
  nlinarith

end Solow1956.Neoclassical
