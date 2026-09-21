import RamseyCassKoopmans.GlobalFlow
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Simultaneous comparison barriers for two state coordinates -/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.ODE

theorem eventually_lt_right_of_deriv_neg {f : ℝ → ℝ} {v t : ℝ}
    (hd : HasDerivAt f v t) (hv : v < 0) :
    ∀ᶠ u in 𝓝[>] t, f u < f t := by
  have hs := (hd.hasDerivWithinAt (s := Ioi t)).limsup_slope_le' (lt_irrefl t) hv
  filter_upwards [hs, self_mem_nhdsWithin] with u hu htu
  rw [slope_def_field] at hu
  have := (div_lt_iff₀ (sub_pos.mpr htu)).mp hu
  linarith

theorem eventually_below_right {f B : ℝ → ℝ} {df dB t : ℝ}
    (hf : HasDerivAt f df t) (hB : HasDerivAt B dB t)
    (hle : f t ≤ B t) (hstrict : f t = B t → df < dB) :
    ∀ᶠ u in 𝓝[>] t, f u ≤ B u := by
  rcases hle.lt_or_eq with hlt | heq
  · have hn : ∀ᶠ u in 𝓝 t, f u < B u :=
      (hf.continuousAt.sub hB.continuousAt).eventually (gt_mem_nhds (sub_neg.mpr hlt))
        |>.mono (fun _ h => sub_neg.mp h)
    exact (hn.filter_mono nhdsWithin_le_nhds).mono (fun _ h => h.le)
  · have hn := eventually_lt_right_of_deriv_neg (hf.sub hB) (sub_neg.mpr (hstrict heq))
    filter_upwards [hn] with u hu
    change f u - B u < f t - B t at hu
    linarith

/-- Each coordinate may depend on the other. At a first contact with the
barrier, both coordinates are known to be below it simultaneously. -/
theorem pair_le_barrier {f g df dg B dB : ℝ → ℝ} {T : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t)
    (hg : ∀ t, HasDerivAt g (dg t) t)
    (hB : ∀ t, HasDerivAt B (dB t) t)
    (hf0 : f 0 ≤ B 0) (hg0 : g 0 ≤ B 0)
    (hb1 : ∀ t ∈ Ico 0 T, f t = B t → g t ≤ B t → df t < dB t)
    (hb2 : ∀ t ∈ Ico 0 T, g t = B t → f t ≤ B t → dg t < dB t) :
    ∀ t ∈ Icc 0 T, f t ≤ B t ∧ g t ≤ B t := by
  let S : Set ℝ := {t | f t ≤ B t ∧ g t ≤ B t}
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hf t).continuousAt)
  have hgc : Continuous g := continuous_iff_continuousAt.mpr (fun t => (hg t).continuousAt)
  have hBc : Continuous B := continuous_iff_continuousAt.mpr (fun t => (hB t).continuousAt)
  have hclosed : IsClosed S := (isClosed_le hfc hBc).inter (isClosed_le hgc hBc)
  apply (hclosed.inter isClosed_Icc).Icc_subset_of_forall_exists_gt ⟨hf0, hg0⟩
  rintro t ⟨htS, ht⟩ y hy
  have h1 := eventually_below_right (hf t) (hB t) htS.1 (fun heq => hb1 t ht heq htS.2)
  have h2 := eventually_below_right (hg t) (hB t) htS.2 (fun heq => hb2 t ht heq htS.1)
  obtain ⟨u, hu1, hu2, huy⟩ := (h1.and (h2.and (Ioc_mem_nhdsGT hy))).exists
  exact ⟨u, ⟨hu1, hu2⟩, huy⟩

end RamseyCassKoopmans.ODE
