/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/
import Solow1956.Growth.GeneralSolow
import Solow1956.Growth.SolowComparative
import Solow1956.Growth.SolowSwanDynamics

/-! # Stability, permanent saving changes, and effective-labour normalization -/

open Set Filter Topology

namespace Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- Global attraction for every admissible classical trajectory, not only the
constructed representative. -/
theorem every_path_converges (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k : ℝ → ℝ} (h0 : 0 < k 0) (hk : ∀ t, 0 ≤ t → 0 ≤ k t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt k (rate f s m (k t)) t) :
    Tendsto k atTop (𝓝 (steadyCapital h s m)) := by
  obtain ⟨ks, hks, he, _, l, hl0, hl, _, _, _, _, hlim, _⟩ := general_solow h hs hm h0
  have heq := path_unique h hs.le h0 hl0.symm hk (fun t ht => (hl t ht).1.le)
    hd (fun t ht => (hl t ht).2)
  rw [steadyCapital_eq h hs hm hks he]
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (heq ht).symm

/-- Quantitative Lyapunov stability: the distance from the steady stock never
exceeds its initial value. Together with attraction this gives global
asymptotic stability on the positive half-line. -/
theorem path_stable (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k : ℝ → ℝ} (h0 : 0 < k 0) (hk : ∀ t, 0 ≤ t → 0 ≤ k t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt k (rate f s m (k t)) t)
    {t : ℝ} (ht : 0 ≤ t) :
    |k t - steadyCapital h s m| ≤ |k 0 - steadyCapital h s m| := by
  obtain ⟨ks, hks, he, _, l, hl0, hl, _, _, _, hb, _, _⟩ := general_solow h hs hm h0
  have heq := path_unique h hs.le h0 hl0.symm hk (fun t ht => (hl t ht).1.le)
    hd (fun t ht => (hl t ht).2)
  rw [steadyCapital_eq h hs hm hks he, heq ht]
  obtain ⟨hlo, hhi⟩ := hb t ht
  rcases le_total (k 0) ks with h | h
  · rw [min_eq_left h] at hlo
    rw [max_eq_right h] at hhi
    rw [abs_of_nonpos (sub_nonpos.mpr hhi), abs_of_nonpos (sub_nonpos.mpr h)]
    linarith
  · rw [min_eq_right h] at hlo
    rw [max_eq_left h] at hhi
    rw [abs_of_nonneg (sub_nonneg.mpr hlo), abs_of_nonneg (sub_nonneg.mpr h)]
    linarith

/-- Section 2.8: a permanent saving increase from an old steady state produces
strict capital deepening and convergence to the higher new steady state. -/
theorem saving_increase_transition (h : Technology f) {s0 s1 m : ℝ}
    (hs0 : 0 < s0) (hs : s0 < s1) (hm : 0 < m) :
    ∃ k : ℝ → ℝ, k 0 = steadyCapital h s0 m ∧
      (∀ t, 0 ≤ t → 0 < k t ∧ HasDerivAt k (rate f s1 m (k t)) t) ∧
      StrictMonoOn k (Ici 0) ∧
      (∀ t, 0 ≤ t → k t < steadyCapital h s1 m) ∧
      Tendsto k atTop (𝓝 (steadyCapital h s1 m)) ∧
      (1 - s1) * f (k 0) < (1 - s0) * f (k 0) := by
  have hs1 := hs0.trans hs
  have h0 := (steadyCapital_spec h hs0 hm).1
  obtain ⟨ks, hks, he, _, k, hk0, hk, hlow, _, _, _, hlim, _⟩ :=
    general_solow h hs1 hm h0
  have hsks := steadyCapital_eq h hs1 hm hks he
  have hlt : steadyCapital h s0 m < ks := by
    rw [← hsks]
    exact steadyCapital_strictMono_saving h hm hs0 hs1 hs
  refine ⟨k, hk0, hk, (hlow hlt).1, ?_, ?_, ?_⟩
  · simpa only [hsks] using (hlow hlt).2
  · simpa only [hsks] using hlim
  · have hy : 0 < f (k 0) := h.output_pos (hk0 ▸ h0)
    exact mul_lt_mul_of_pos_right (by linarith) hy

/-- Proposition 2.13: effective capital converges with Harrod-neutral progress.
The quotient equation is derived from actual aggregate derivatives. -/
theorem effective_labour_convergence (h : Technology f)
    {K E Y : ℝ → ℝ} {s δ n g : ℝ} (hs : 0 < s) (hm : 0 < n + g + δ)
    (hK0 : 0 < K 0) (hK : ∀ t, 0 ≤ t → 0 ≤ K t)
    (hE : ∀ t, 0 ≤ t → 0 < E t)
    (hKd : ∀ t, 0 ≤ t → HasDerivAt K (s * Y t - δ * K t) t)
    (hEd : ∀ t, 0 ≤ t → HasDerivAt E ((n + g) * E t) t)
    (hY : ∀ t, 0 ≤ t → Y t = E t * f (K t / E t)) :
    Tendsto (fun t => K t / E t) atTop (𝓝 (steadyCapital h s (n + g + δ))) := by
  apply every_path_converges h hs hm (k := fun t => K t / E t)
    (div_pos hK0 (hE 0 le_rfl))
    (fun t ht => div_nonneg (hK t ht) (hE t ht).le)
  intro t ht
  exact SolowSwan.hasDerivAt_capitalPerEffectiveWorker (hE t ht)
    (hKd t ht) (hEd t ht) (hY t ht)

end Solow1956.Neoclassical
