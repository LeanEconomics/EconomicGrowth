/-
SPDX-License-Identifier: Unlicense
Developed with OpenAI Codex under the direction of @mvazcar.
-/
import Solow1956.Analysis.AsymptoticODE
import Solow1956.Analysis.CompactExtension

/-! # Global positive scalar trajectories with a unique attracting equilibrium

The field is extended from a compact positive interval. Boundary inequalities
keep the constructed trajectory inside that interval, so the extension has no
effect on the economic solution. ODE uniqueness rules out finite-time arrival
at the equilibrium, and a nonzero limiting drift contradicts convergence.
-/

open Set Filter Topology
open scoped NNReal

namespace Solow1956.ODE

theorem exists_attracting_scalar_path {v : ℝ → ℝ} {ks x : ℝ}
    (hd : ∀ k, 0 < k → DifferentiableAt ℝ v k)
    (hc : ContinuousOn (deriv v) (Ioi 0))
    (hks : 0 < ks) (hvks : v ks = 0) (hx : 0 < x)
    (hbelow : ∀ k, 0 < k → k < ks → 0 < v k)
    (habove : ∀ k, ks < k → v k < 0) :
    ∃ γ : ℝ → ℝ, γ 0 = x ∧
      (∀ t, 0 ≤ t → 0 < γ t ∧ HasDerivAt γ (v (γ t)) t) ∧
      (x < ks → StrictMonoOn γ (Ici 0) ∧ ∀ t, 0 ≤ t → γ t < ks) ∧
      (ks < x → StrictAntiOn γ (Ici 0) ∧ ∀ t, 0 ≤ t → ks < γ t) ∧
      (x = ks → ∀ t, 0 ≤ t → γ t = ks) ∧
      (∀ t, 0 ≤ t → min x ks ≤ γ t ∧ γ t ≤ max x ks) ∧
      Tendsto γ atTop (𝓝 ks) := by
  let a := min x ks / 2
  let b := max x ks + 1
  have ha : 0 < a := half_pos (lt_min hx hks)
  have hax : a < x := by have := min_le_left x ks; dsimp [a]; linarith
  have haks : a < ks := by have := min_le_right x ks; dsimp [a]; linarith
  have hxb : x < b := by have := le_max_left x ks; dsimp [b]; linarith
  have hksb : ks < b := by have := le_max_right x ks; dsimp [b]; linarith
  have hab : a ≤ b := (hax.trans hxb).le
  obtain ⟨K, M, hK, hM⟩ := bounded_lipschitz_clip hab
    (fun k hk => hd k (ha.trans_le hk.1))
    (hc.mono (fun k hk => ha.trans_le hk.1))
  let w := v ∘ clip a b
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_solution hK hM x
  have hwa : w a = v a := by simp [w, clip_eq (show a ∈ Icc a b from ⟨le_rfl, hab⟩)]
  have hwb : w b = v b := by simp [w, clip_eq (show b ∈ Icc a b from ⟨hab, le_rfl⟩)]
  have hwks : w ks = 0 := by simp [w, clip_eq ⟨haks.le, hksb.le⟩, hvks]
  have hmem : ∀ t, 0 ≤ t → γ t ∈ Icc a b := by
    intro t ht
    constructor
    · have hr := image_le_of_deriv_right_lt_deriv_boundary
        (HasDerivAt.continuousOn (fun u _ => (hγ u).neg))
        (fun u _ => (hγ u).neg.hasDerivWithinAt)
        (B := fun _ => -a) (a := 0) (b := t)
        (by change -γ 0 ≤ -a; rw [hγ0]; linarith)
        (fun u => hasDerivAt_const u (-a))
        (fun u _ heq => by
          change -γ u = -a at heq
          have he : γ u = a := by linarith
          change -w (γ u) < 0
          rw [he, hwa]
          exact neg_neg_of_pos (hbelow a ha haks)) ⟨ht, le_rfl⟩
      change -γ t ≤ -a at hr
      linarith
    · exact image_le_of_deriv_right_lt_deriv_boundary
        (HasDerivAt.continuousOn (fun u _ => hγ u))
        (fun u _ => (hγ u).hasDerivWithinAt)
        (B := fun _ => b) (a := 0) (b := t)
        (by rw [hγ0]; exact hxb.le)
        (fun u => hasDerivAt_const u b)
        (fun u _ heq => by change w (γ u) < 0; rw [heq, hwb]; exact habove b hksb)
        ⟨ht, le_rfl⟩
  have hreal : ∀ t, 0 ≤ t → HasDerivAt γ (v (γ t)) t := by
    intro t ht
    simpa only [Function.comp_apply, clip_eq (hmem t ht)] using hγ t
  have hpos : ∀ t, 0 ≤ t → 0 < γ t := fun t ht => ha.trans_le (hmem t ht).1
  have heq (t : ℝ) (he : γ t = ks) : γ = fun _ => ks :=
    ODE_solution_unique_univ (v := fun _ => w) (s := fun _ => univ)
      (fun _ => hK.lipschitzOnWith)
      (fun u => ⟨hγ u, mem_univ _⟩)
      (fun u => ⟨by simpa only [hwks] using hasDerivAt_const u ks, mem_univ _⟩) he
  have hnot (hne : x ≠ ks) (t : ℝ) : γ t ≠ ks := by
    intro he
    have h := congrFun (heq t he) 0
    exact hne (hγ0.symm.trans h)
  have hlow (h : x < ks) : StrictMonoOn γ (Ici 0) ∧ ∀ t, 0 ≤ t → γ t < ks := by
    have hb : ∀ t, 0 ≤ t → γ t < ks := by
      intro t ht
      by_contra hn
      obtain ⟨u, hu, heu⟩ := intermediate_value_Icc ht
        (HasDerivAt.continuousOn (fun u _ => hγ u))
        (show ks ∈ Icc (γ 0) (γ t) from ⟨by rw [hγ0]; exact h.le, le_of_not_gt hn⟩)
      exact hnot h.ne u heu
    refine ⟨strictMonoOn_of_deriv_pos (convex_Ici 0)
      (HasDerivAt.continuousOn (fun t _ => hγ t)) ?_, hb⟩
    intro t ht
    have ht' : 0 ≤ t := interior_subset ht
    rw [(hreal t ht').deriv]
    exact hbelow _ (hpos t ht') (hb t ht')
  have hhigh (h : ks < x) : StrictAntiOn γ (Ici 0) ∧ ∀ t, 0 ≤ t → ks < γ t := by
    have hb : ∀ t, 0 ≤ t → ks < γ t := by
      intro t ht
      by_contra hn
      obtain ⟨u, hu, heu⟩ := intermediate_value_Icc' ht
        (HasDerivAt.continuousOn (fun u _ => hγ u))
        (show ks ∈ Icc (γ t) (γ 0) from ⟨le_of_not_gt hn, by rw [hγ0]; exact h.le⟩)
      exact hnot h.ne' u heu
    refine ⟨strictAntiOn_of_deriv_neg (convex_Ici 0)
      (HasDerivAt.continuousOn (fun t _ => hγ t)) ?_, hb⟩
    intro t ht
    have ht' : 0 ≤ t := interior_subset ht
    rw [(hreal t ht').deriv]
    exact habove _ (hb t ht')
  have hconstant (h : x = ks) : ∀ t, γ t = ks :=
    fun t => congrFun (heq 0 (hγ0.trans h)) t
  have htight : ∀ t, 0 ≤ t → min x ks ≤ γ t ∧ γ t ≤ max x ks := by
    intro t ht
    rcases lt_trichotomy x ks with h | h | h
    · obtain ⟨hm, hb⟩ := hlow h
      rw [min_eq_left h.le, max_eq_right h.le]
      exact ⟨by rw [← hγ0]; exact hm.monotoneOn (by simp) ht ht, (hb t ht).le⟩
    · simp [h, hconstant h t]
    · obtain ⟨hm, hb⟩ := hhigh h
      rw [min_eq_right h.le, max_eq_left h.le]
      exact ⟨(hb t ht).le, by rw [← hγ0]; exact hm.antitoneOn (by simp) ht ht⟩
  have hlimit : ∃ l, Tendsto γ atTop (𝓝 l) := by
    rcases lt_trichotomy x ks with h | h | h
    · exact exists_limit_of_monotone_bounded (hlow h).1.monotoneOn
        (fun t ht => (hlow h).2 t ht |>.le)
    · refine ⟨ks, ?_⟩
      have he : γ = fun _ => ks := funext (hconstant h)
      rw [he]
      exact tendsto_const_nhds
    · exact exists_limit_of_antitone_bounded (hhigh h).1.antitoneOn
        (fun t ht => (hhigh h).2 t ht |>.le)
  obtain ⟨l, hl⟩ := hlimit
  have hlmem : l ∈ Icc a b := isClosed_Icc.mem_of_tendsto hl
    ((eventually_ge_atTop (0 : ℝ)).mono (fun t ht => hmem t ht))
  have hleq : v l = 0 := by
    have := derivative_limit_zero hγ hl (hK.continuous.continuousAt.tendsto.comp hl)
    simpa only [Function.comp_apply, clip_eq hlmem] using this
  have hlks : l = ks := by
    rcases lt_trichotomy l ks with h | h | h
    · exact False.elim ((ne_of_gt (hbelow l (ha.trans_le hlmem.1) h)) hleq)
    · exact h
    · exact False.elim ((ne_of_lt (habove l h)) hleq)
  exact ⟨γ, hγ0, fun t ht => ⟨hpos t ht, hreal t ht⟩, hlow, hhigh,
    fun h t _ => hconstant h t, htight, hlks ▸ hl⟩

end Solow1956.ODE
