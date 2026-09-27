/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import DiscreteTime.GeneralSolow
import DiscreteTime.SolowComparative

/-! # Discrete-time stability, saving shocks, effective labour, and factor prices

Discrete counterparts of `Solow1956.Growth.GeneralSolowApplications`, together with
Acemoglu Proposition 2.6: along a path from below the steady state the wage rises
and the rental rate falls every period.
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime

open Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- Global attraction for every admissible path. -/
theorem every_path_converges (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k : ℕ → ℝ} (hk : IsPath f s δ γ k) : Tendsto k atTop (𝓝 (steady h s δ γ)) :=
  hk.tendsto h P

/-- Lyapunov stability, strictly: away from `k*` the distance to `k*` falls every period. -/
theorem path_stable (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k : ℕ → ℝ} (hk : IsPath f s δ γ k) (t : ℕ) :
    |k (t + 1) - steady h s δ γ| ≤ |k t - steady h s δ γ| ∧
      (k t ≠ steady h s δ γ → |k (t + 1) - steady h s δ γ| < |k t - steady h s δ γ|) := by
  obtain ⟨hks, hfix⟩ := steady_spec h P
  have hkt := hk.pos h P t
  set ks := steady h s δ γ
  rw [hk.succ]
  rcases lt_trichotomy (k t) ks with hlt | heq | hgt
  · have h1 := next_gt_self h P hkt hlt
    have h2 : next f s δ γ (k t) < ks := hfix ▸ next_strictMono h P hkt.le hks.le hlt
    rw [abs_of_neg (sub_neg.mpr h2), abs_of_neg (sub_neg.mpr hlt)]
    exact ⟨by linarith, fun _ => by linarith⟩
  · rw [heq, hfix]
    exact ⟨le_rfl, fun hne => absurd rfl hne⟩
  · have h1 := next_lt_self h P hgt
    have h2 : ks < next f s δ γ (k t) := hfix ▸ next_strictMono h P hks.le hkt.le hgt
    rw [abs_of_pos (sub_pos.mpr h2), abs_of_pos (sub_pos.mpr hgt)]
    exact ⟨by linarith, fun _ => by linarith⟩

/-- The distance to `k*` never exceeds its initial value. -/
theorem path_stable_initial (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k : ℕ → ℝ} (hk : IsPath f s δ γ k) (t : ℕ) :
    |k t - steady h s δ γ| ≤ |k 0 - steady h s δ γ| := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (path_stable h P hk t).1.trans ih

/-- A permanent saving increase from an old steady state: strict capital deepening,
convergence to the higher new steady state, and an immediate consumption loss. -/
theorem saving_increase_transition (h : Technology f) {s0 s1 δ γ : ℝ}
    (P0 : Params s0 δ γ) (hs : s0 < s1) :
    ∃ k : ℕ → ℝ, k 0 = steady h s0 δ γ ∧ IsPath f s1 δ γ k ∧ StrictMono k ∧
      (∀ t, k t < steady h s1 δ γ) ∧ Tendsto k atTop (𝓝 (steady h s1 δ γ)) ∧
      (1 - s1) * f (k 0) < (1 - s0) * f (k 0) := by
  have P1 : Params s1 δ γ := ⟨P0.saving_pos.trans hs, P0.depreciation_le_one,
    P0.growth_pos, P0.dilution_pos⟩
  have h0 := (steady_spec h P0).1
  have hk := isPath_path (f := f) (s := s1) (δ := δ) (γ := γ) h0
  have hlt : steady h s0 δ γ < steady h s1 δ γ :=
    steady_strictMono_saving h P0.dilution_pos P0.saving_pos P1.saving_pos hs
  obtain ⟨_, hlow, _, _, _, hlim⟩ := hk.orbit h P1
  obtain ⟨hmono, hbelow⟩ := hlow hlt
  refine ⟨_, rfl, hk, hmono, hbelow, hlim, ?_⟩
  have hy : 0 < f (steady h s0 δ γ) := h.output_pos h0
  exact mul_lt_mul_of_pos_right (by linarith) hy

/-- Aggregate accumulation `K(t+1) = s Y(t) + (1 - δ) K(t)` with effective labour
`E(t+1) = γ E(t)` and `Y = E f(K/E)` gives the intensive map. -/
theorem capitalPerEffectiveWorker_succ {K E Y : ℕ → ℝ} {s δ γ : ℝ} {t : ℕ}
    (hγ : 0 < γ) (hE : 0 < E t)
    (hK : K (t + 1) = s * Y t + (1 - δ) * K t) (hEs : E (t + 1) = γ * E t)
    (hY : Y t = E t * f (K t / E t)) :
    K (t + 1) / E (t + 1) = next f s δ γ (K t / E t) := by
  rw [hK, hEs, hY]
  unfold next
  field_simp

/-- Effective capital converges with labour-augmenting progress, derived from the
aggregate equations. -/
theorem effective_labour_convergence (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {K E Y : ℕ → ℝ} (hK0 : 0 < K 0) (hE : ∀ t, 0 < E t)
    (hK : ∀ t, K (t + 1) = s * Y t + (1 - δ) * K t) (hEs : ∀ t, E (t + 1) = γ * E t)
    (hY : ∀ t, Y t = E t * f (K t / E t)) :
    Tendsto (fun t => K t / E t) atTop (𝓝 (steady h s δ γ)) :=
  IsPath.tendsto h P ⟨div_pos hK0 (hE 0), fun t =>
    capitalPerEffectiveWorker_succ P.growth_pos (hE t) (hK t) (hEs t) (hY t)⟩

/-- Competitive wage per worker, `w = f(k) - k f'(k)`. -/
noncomputable def wage (f : ℝ → ℝ) (k : ℝ) : ℝ := f k - k * deriv f k

/-- The wage is strictly increasing in capital per worker. -/
theorem wage_strictMono (h : Technology f) : StrictMonoOn (wage f) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hs := h.concave.deriv_lt_slope (show a ∈ Ici 0 from ha'.le)
    (show b ∈ Ici 0 from (ha'.trans hab).le) hab (h.differentiable b (ha'.trans hab))
  rw [slope_def_field] at hs
  have hs' := (lt_div_iff₀ (sub_pos.mpr hab)).mp hs
  have hm := h.marginal_strictAnti ha hb hab
  unfold wage
  nlinarith

/-- Acemoglu Proposition 2.6: from below the steady state the wage rises and the
rental rate `R = f'(k)` falls every period; from above the opposite holds. -/
theorem factor_prices (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k : ℕ → ℝ} (hk : IsPath f s δ γ k) :
    (k 0 < steady h s δ γ →
      StrictMono (fun t => wage f (k t)) ∧ StrictAnti (fun t => deriv f (k t))) ∧
    (steady h s δ γ < k 0 →
      StrictAnti (fun t => wage f (k t)) ∧ StrictMono (fun t => deriv f (k t))) := by
  obtain ⟨hpos, hlow, hhigh, _, _, _⟩ := hk.orbit h P
  refine ⟨fun hlt => ⟨fun a b hab => ?_, fun a b hab => ?_⟩,
    fun hgt => ⟨fun a b hab => ?_, fun a b hab => ?_⟩⟩
  · exact wage_strictMono h (hpos a) (hpos b) ((hlow hlt).1 hab)
  · exact h.marginal_strictAnti (hpos a) (hpos b) ((hlow hlt).1 hab)
  · exact wage_strictMono h (hpos b) (hpos a) ((hhigh hgt).1 hab)
  · exact h.marginal_strictAnti (hpos b) (hpos a) ((hhigh hgt).1 hab)

end Solow1956.DiscreteTime
