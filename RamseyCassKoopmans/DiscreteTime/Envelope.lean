/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import DiscreteTime.Dynamics
import RamseyCassKoopmans.CassEnvelope

/-!
# The envelope theorem and steady-state comparative statics in discrete time

* `value_hasDerivAt`: `V'(x) = u'(c₀) (f'(x) + 1 - δ)` at every `x > 0`, where
  `c₀ = F(x) - g(x)`. As in continuous time the proof is the Clausen–Strub sandwich
  (`clausen_strub_sandwich`): the lower support is `u(F(z) - g(x)) + β V(g(x))`
  (keep next period's capital), and the upper support is the tangent line, which
  bounds `V` from above by concavity (`concave_le_tangent_of_lower_support`).
* `steady_strictMono_patience`, `steady_strictAnti_depreciation`: the steady state
  rises with patience `β` and falls with depreciation `δ`.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.DiscreteTime

variable {f u : ℝ → ℝ} {β δ : ℝ}

/-- A concave function with a lower support touching it at an interior point, and
differentiable there, lies below the support's tangent line. -/
theorem concave_le_tangent_of_lower_support {V L : ℝ → ℝ} {x D : ℝ}
    (hV : ConcaveOn ℝ (Ici 0) V) (hx : 0 < x) (hL : HasDerivAt L D x)
    (hLV : ∀ᶠ z in 𝓝 x, L z ≤ V z) (hLx : L x = V x) {z : ℝ} (hz : 0 ≤ z) :
    V z ≤ V x + D * (z - x) := by
  rw [hasDerivAt_iff_tendsto_slope, ← nhdsLT_sup_nhdsGT, tendsto_sup] at hL
  rcases lt_trichotomy z x with hzx | hzx | hzx
  · -- slopes to the right of `x` are at most the slope over `[z, x]`
    have hbound : D ≤ (V x - V z) / (x - z) := by
      refine le_of_tendsto hL.2 ?_
      filter_upwards [nhdsWithin_le_nhds hLV, self_mem_nhdsWithin] with w hw hwx
      have hwx' : x < w := hwx
      have hslope := hV.slope_anti_adjacent (x := z) (y := x) (z := w) (mem_Ici.mpr hz)
        (mem_Ici.mpr (hx.le.trans hwx'.le)) hzx hwx'
      rw [slope_def_field]
      calc (L w - L x) / (w - x) ≤ (V w - V x) / (w - x) :=
            div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hwx'.le)
        _ ≤ (V x - V z) / (x - z) := hslope
    rw [le_div_iff₀ (sub_pos.mpr hzx)] at hbound
    linarith
  · rw [hzx]; simp
  · -- slopes to the left of `x` are at least the slope over `[x, z]`
    have hbound : (V z - V x) / (z - x) ≤ D := by
      refine ge_of_tendsto hL.1 ?_
      filter_upwards [nhdsWithin_le_nhds hLV, self_mem_nhdsWithin,
        nhdsWithin_le_nhds (lt_mem_nhds hx)] with w hw hwx hw0
      have hwx' : w < x := hwx
      have hslope := hV.slope_anti_adjacent (x := w) (y := x) (z := z) (mem_Ici.mpr hw0.le)
        (mem_Ici.mpr hz) hwx' hzx
      rw [slope_def_field]
      calc (V z - V x) / (z - x) ≤ (V x - V w) / (x - w) := hslope
        _ ≤ (L x - L w) / (x - w) :=
            div_le_div_of_nonneg_right (by linarith) (sub_nonneg.mpr hwx'.le)
        _ = (L w - L x) / (w - x) := by
            rw [show L x - L w = -(L w - L x) by ring, show x - w = -(w - x) by ring,
              neg_div_neg_eq]
    rw [div_le_iff₀ (sub_pos.mpr hzx)] at hbound
    linarith

/-- The envelope theorem: `V'(x) = u'(c₀) (f'(x) + 1 - δ)`. -/
theorem value_hasDerivAt (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (value P) (deriv u (resources f δ x - policy P x) * (deriv f x + (1 - δ))) x := by
  obtain ⟨hy, hyF, -⟩ := policy_interior P hx
  set y := policy P x
  have hc : 0 < resources f δ x - y := by linarith
  set D := deriv u (resources f δ x - y) * (deriv f x + (1 - δ))
  set L : ℝ → ℝ := fun z => u (resources f δ z - y) + β * value P y
  have hL : HasDerivAt L D x := by
    exact ((P.u_diff _ hc).hasDerivAt.comp x
      ((hasDerivAt_resources P hx).sub_const y)).add_const (β * value P y)
  have hLx : L x = value P x := (bellman_policy P hx.le).1.symm
  have hLV : ∀ᶠ z in 𝓝 x, L z ≤ value P z := by
    have hFc : ContinuousAt (resources f δ) x := (hasDerivAt_resources P hx).continuousAt
    filter_upwards [lt_mem_nhds hx, hFc.eventually (lt_mem_nhds hyF)] with z hz hzF
    exact (bellman P hz.le).2 y hy.le hzF.le
  have hH : HasDerivAt (fun z => value P x + D * (z - x)) D x := by
    have := ((hasDerivAt_id x).sub_const x).const_mul D |>.const_add (value P x)
    simpa only [id, mul_one] using this
  refine clausen_strub_sandwich hL hH hLV ?_ hLx (by ring)
  filter_upwards [lt_mem_nhds hx] with z hz
  exact concave_le_tangent_of_lower_support (value_strictConcave P).concaveOn hx hL hLV hLx hz.le

/-- A more patient economy has a larger steady state. -/
theorem steady_strictMono_patience {β' : ℝ} (P : Primitives f u β δ)
    (P' : Primitives f u β' δ) (hββ : β < β') : steady P < steady P' := by
  obtain ⟨hk, hd⟩ := steady_spec P
  obtain ⟨hk', hd'⟩ := steady_spec P'
  by_contra hle
  push Not at hle
  have hanti := (production_deriv_strictAnti f P.f_conc P.f_diff).antitoneOn hk' hk hle
  rw [hd, hd'] at hanti
  have : 1 / β' < 1 / β := one_div_lt_one_div_of_lt P.β_pos hββ
  linarith

/-- Faster depreciation lowers the steady state. -/
theorem steady_strictAnti_depreciation {δ' : ℝ} (P : Primitives f u β δ)
    (P' : Primitives f u β δ') (hδδ : δ < δ') : steady P' < steady P := by
  obtain ⟨hk, hd⟩ := steady_spec P
  obtain ⟨hk', hd'⟩ := steady_spec P'
  by_contra hle
  push Not at hle
  have hanti := (production_deriv_strictAnti f P.f_conc P.f_diff).antitoneOn hk hk' hle
  rw [hd, hd'] at hanti
  linarith

end RamseyCassKoopmans.DiscreteTime
