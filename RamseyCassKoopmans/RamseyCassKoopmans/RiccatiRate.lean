/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Analysis lemmas for the local convergence rate

* `hasDerivAt_of_comp_eq`: if `μ ∘ g = q` near `t`, `μ'(g t) ≠ 0` and `g` is
  continuous and locally injective at `t`, then `g' = q' / μ'`.
* `tendsto_div_of_deriv_tendsto`: if `φ' → L` then `φ t / t → L`.
* `riccati_tendsto`: a positive solution of `S' = S² - D S + B` with `D → d > 0` and
  `B → -A < 0` converges to the positive root `(d + √(d² + 4A)) / 2`. Solutions
  above that root blow up in finite time and solutions below it turn negative, so
  a positive solution defined for all large times has no other option.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

theorem hasDerivAt_of_comp_eq {g μ q : ℝ → ℝ} {t μ' q' : ℝ}
    (hg : ContinuousAt g t) (hμ : HasDerivAt μ μ' (g t)) (hμ' : μ' ≠ 0)
    (hq : HasDerivAt q q' t) (heq : ∀ᶠ s in 𝓝 t, μ (g s) = q s)
    (hinj : ∀ᶠ s in 𝓝[≠] t, g s ≠ g t) : HasDerivAt g (q' / μ') t := by
  rw [hasDerivAt_iff_tendsto_slope] at hq hμ ⊢
  have hgt : Tendsto g (𝓝[≠] t) (𝓝[≠] (g t)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hg.tendsto.mono_left nhdsWithin_le_nhds) hinj
  have hslope := hμ.comp hgt
  have hdiv := hq.div hslope hμ'
  have heqt : μ (g t) = q t := heq.self_of_nhds
  refine hdiv.congr' ?_
  filter_upwards [hinj, nhdsWithin_le_nhds heq, self_mem_nhdsWithin,
    hslope.eventually (eventually_ne_nhds hμ')] with s hs hμs hst hsl
  change slope q t s / slope μ (g t) (g s) = slope g t s
  change slope μ (g t) (g s) ≠ 0 at hsl
  rw [slope_def_field] at hsl
  rw [slope_def_field, slope_def_field, slope_def_field, ← hμs, ← heqt]
  have hst' : s - t ≠ 0 := sub_ne_zero.mpr hst
  have hgs : g s - g t ≠ 0 := sub_ne_zero.mpr hs
  have hnum : μ (g s) - μ (g t) ≠ 0 := by
    intro h0
    apply hsl
    rw [h0, zero_div]
  field_simp

/-- If the derivative of `φ` tends to `L`, then `φ t / t → L`. -/
theorem tendsto_div_of_deriv_tendsto {φ φ' : ℝ → ℝ} {L T0 : ℝ}
    (hφ : ∀ t, T0 ≤ t → HasDerivAt φ (φ' t) t) (hlim : Tendsto φ' atTop (𝓝 L)) :
    Tendsto (fun t => φ t / t) atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨T1, hT1⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) (half_pos hε)
  set T := max (max T0 T1) 1
  have hT0 : T0 ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have hT1' : T1 ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  have hTpos : 0 < T := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ψ : ℝ → ℝ := fun t => φ t - L * t
  have hmvt : ∀ t, T ≤ t → |ψ t - ψ T| ≤ ε / 2 * (t - T) := by
    intro t ht
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := ψ) (f' := fun s => φ' s - L)
      (fun s hs => (((hφ s (hT0.trans hs.1)).sub ((hasDerivAt_id s).const_mul L)).congr_deriv
        (by simp)).hasDerivWithinAt)
      (fun s hs => by
        rw [Real.norm_eq_abs]
        exact (hT1 s (hT1'.trans hs.1)).le) t ⟨ht, le_rfl⟩
    simpa only [Real.norm_eq_abs] using h
  obtain ⟨T2, hT2⟩ : ∃ T2, ∀ t, T2 ≤ t → |ψ T| / t < ε / 2 := by
    obtain ⟨T2, hT2⟩ := Metric.tendsto_atTop.mp
      (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun t : ℝ => |ψ T| / t) atTop (𝓝 0))
      (ε / 2) (half_pos hε)
    refine ⟨T2, fun t ht => ?_⟩
    have := hT2 t ht
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans_lt this
  refine ⟨max T T2, fun t ht => ?_⟩
  have htT : T ≤ t := (le_max_left _ _).trans ht
  have htpos : 0 < t := hTpos.trans_le htT
  have hb := hmvt t htT
  have hc := hT2 t ((le_max_right _ _).trans ht)
  rw [Real.dist_eq]
  have hrewrite : φ t / t - L = (ψ T + (ψ t - ψ T)) / t := by
    simp only [ψ]
    field_simp
    ring
  rw [hrewrite, abs_div, abs_of_pos htpos, div_lt_iff₀ htpos]
  have h1 : |ψ T + (ψ t - ψ T)| ≤ |ψ T| + |ψ t - ψ T| := abs_add_le _ _
  have h2 : |ψ T| < ε / 2 * t := by rwa [div_lt_iff₀ htpos] at hc
  nlinarith

/-- The quotient rule for `S = v/u` with `u' = u D - v` and `v' = u B` gives the
Riccati right-hand side. -/
theorem riccati_algebra {u v D B u' v' : ℝ} (hu : u ≠ 0) (hu' : u' = u * D - v)
    (hv' : v' = u * B) : (v' * u - v * u') / u ^ 2 = (v / u) ^ 2 - D * (v / u) + B := by
  subst hu' hv'
  field_simp
  ring

/-- A positive solution of the Riccati equation `S' = S² - D S + B`, with `D → d > 0`
and `B → -A < 0`, converges to the positive root `(d + √(d² + 4A)) / 2`. -/
theorem riccati_tendsto {S D B : ℝ → ℝ} {d A T0 : ℝ} (hd : 0 < d) (hA : 0 < A)
    (hS : ∀ t, T0 ≤ t → HasDerivAt S (S t ^ 2 - D t * S t + B t) t)
    (hpos : ∀ t, T0 ≤ t → 0 < S t)
    (hD : Tendsto D atTop (𝓝 d)) (hB : Tendsto B atTop (𝓝 (-A))) :
    Tendsto S atTop (𝓝 ((d + Real.sqrt (d ^ 2 + 4 * A)) / 2)) := by
  set r := Real.sqrt (d ^ 2 + 4 * A) with hr_def
  have hr2 : r ^ 2 = d ^ 2 + 4 * A := Real.sq_sqrt (by positivity)
  have hr : d < r := by
    rw [hr_def]
    exact (Real.lt_sqrt hd.le).mpr (by linarith)
  set x := (d + r) / 2 with hx_def
  set y := (d - r) / 2 with hy_def
  have hy : y < 0 := by rw [hy_def]; linarith
  have hx : 0 < x := by rw [hx_def]; linarith
  have hfac : ∀ s : ℝ, s ^ 2 - d * s - A = (s - x) * (s - y) := by
    intro s
    rw [hx_def, hy_def]
    linear_combination (1 / 4 : ℝ) * hr2
  have hcont : ∀ a b, T0 ≤ a → ContinuousOn S (Icc a b) := fun a b ha =>
    HasDerivAt.continuousOn (fun t ht => hS t (ha.trans ht.1))
  rw [Metric.tendsto_atTop]
  intro ε hε
  set e := min (ε / 2) (x / 2) with he_def
  have he : 0 < e := lt_min (half_pos hε) (half_pos hx)
  have heε : e < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hex : e ≤ x / 2 := min_le_right _ _
  set η := min 1 (min (e / 2) (min (e * x / 8) (-(e * y) / (4 * (x + 1))))) with hη_def
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηe : η ≤ e / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηex : η ≤ e * x / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hηy : η ≤ -(e * y) / (4 * (x + 1)) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hηpos : 0 < η := by
    apply lt_min one_pos (lt_min (half_pos he) (lt_min (by positivity) ?_))
    apply div_pos (by nlinarith) (by linarith)
  have hηy' : η * (x + 1) ≤ -(e * y) / 4 := by
    have := (le_div_iff₀ (by linarith : (0 : ℝ) < 4 * (x + 1))).mp hηy
    nlinarith
  obtain ⟨N1, hN1⟩ := Metric.tendsto_atTop.mp hD η hηpos
  obtain ⟨N2, hN2⟩ := Metric.tendsto_atTop.mp hB η hηpos
  set N := max T0 (max N1 N2)
  have hNT0 : T0 ≤ N := le_max_left _ _
  have hDN : ∀ t, N ≤ t → |D t - d| < η := fun t ht => by
    have := hN1 t ((le_max_left _ _).trans ((le_max_right _ _).trans ht))
    rwa [Real.dist_eq] at this
  have hBN : ∀ t, N ≤ t → |B t + A| < η := fun t ht => by
    have := hN2 t ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
    rwa [Real.dist_eq, sub_neg_eq_add] at this
  -- the right-hand side, rewritten around the limiting quadratic
  have hF : ∀ t, S t ^ 2 - D t * S t + B t =
      (S t - x) * (S t - y) + (d - D t) * S t + (B t + A) := by
    intro t
    have := hfac (S t)
    linarith
  -- lower bound: once below `x - e`, a positive solution is driven to zero
  have hlower : ∀ t, N ≤ t → x - e ≤ S t := by
    intro t1 ht1
    by_contra hlt
    push Not at hlt
    set c0 := -(e * y) / 4 with hc0
    have hc0pos : 0 < c0 := by rw [hc0]; nlinarith
    set b := t1 + S t1 / c0 + 1
    have htb : t1 ≤ b := by
      have := div_pos (hpos t1 (hNT0.trans ht1)) hc0pos
      linarith
    have hcmp := image_le_of_deriv_right_lt_deriv_boundary' (a := t1) (b := b)
      (f := S) (f' := fun t => S t ^ 2 - D t * S t + B t)
      (hcont t1 b (hNT0.trans ht1))
      (fun t ht => (hS t (hNT0.trans (ht1.trans ht.1))).hasDerivWithinAt)
      (B := fun t => S t1 - c0 * (t - t1)) (B' := fun _ => -c0)
      (by simp) (by fun_prop)
      (fun t _ => ((((hasDerivAt_id t).sub_const t1).const_mul c0).const_sub (S t1)).congr_deriv
        (by simp) |>.hasDerivWithinAt)
      (by
        intro t ht hSB
        have htN : N ≤ t := ht1.trans ht.1
        have hSpos := hpos t (hNT0.trans htN)
        have hSle : S t ≤ S t1 := by
          rw [hSB]
          have : 0 ≤ c0 * (t - t1) := mul_nonneg hc0pos.le (sub_nonneg.mpr ht.1)
          linarith
        have hSx : S t - x ≤ -e := by linarith
        have hSy : 0 ≤ S t - y := by linarith
        have hprod : (S t - x) * (S t - y) ≤ -e * (S t - y) :=
          mul_le_mul_of_nonneg_right hSx hSy
        have h1 : (d - D t) * S t ≤ η * S t :=
          mul_le_mul_of_nonneg_right (by linarith [abs_lt.mp (hDN t htN)]) hSpos.le
        have h2 : B t + A ≤ η := (le_abs_self _).trans (hBN t htN).le
        have h5 : η * S t ≤ η * x := mul_le_mul_of_nonneg_left (by linarith) hηpos.le
        have h6 : 0 ≤ e * S t := mul_nonneg he.le hSpos.le
        change S t ^ 2 - D t * S t + B t < -c0
        rw [hF t]
        linarith)
    have hb : S b ≤ S t1 - c0 * (b - t1) := hcmp ⟨htb, le_rfl⟩
    have hbpos := hpos b (hNT0.trans (ht1.trans htb))
    have : S t1 - c0 * (b - t1) = -c0 := by
      simp only [b]
      field_simp
      ring
    linarith
  -- upper bound: once above `x + e`, a solution grows, then blows up in finite time
  have hupper : ∀ t, N ≤ t → S t ≤ x + e := by
    intro t1 ht1
    by_contra hgt
    push Not at hgt
    have hT1 : T0 ≤ t1 := hNT0.trans ht1
    set c1 := e * x / 4 with hc1
    have hc1pos : 0 < c1 := by rw [hc1]; positivity
    set M := 4 * (d + A + 2) with hM
    have hMpos : 1 ≤ M := by rw [hM]; linarith
    set b1 := t1 + M / c1
    have htb1 : t1 ≤ b1 := by have := div_pos (by linarith : (0 : ℝ) < M) hc1pos; linarith
    -- stage A: linear growth at rate `c1`
    have hgrow := image_le_of_deriv_right_lt_deriv_boundary' (a := t1) (b := b1)
      (f := fun t => S t1 + c1 * (t - t1)) (f' := fun _ => c1)
      (by fun_prop)
      (fun t _ => ((((hasDerivAt_id t).sub_const t1).const_mul c1).const_add (S t1)).congr_deriv
        (by simp) |>.hasDerivWithinAt)
      (B := S) (B' := fun t => S t ^ 2 - D t * S t + B t) (by simp) (hcont t1 b1 hT1)
      (fun t ht => (hS t (hT1.trans ht.1)).hasDerivWithinAt)
      (by
        intro t ht hSB
        have htN : N ≤ t := ht1.trans ht.1
        have hge : S t1 ≤ S t := by
          rw [← hSB]
          have : 0 ≤ c1 * (t - t1) := mul_nonneg hc1pos.le (sub_nonneg.mpr ht.1)
          linarith
        have hSx : e ≤ S t - x := by linarith
        have hSy : S t ≤ S t - y := by linarith
        have hSpos : 0 < S t := by linarith
        have hprod : e * S t ≤ (S t - x) * (S t - y) :=
          mul_le_mul hSx hSy hSpos.le (by linarith)
        have h1 : -η * S t ≤ (d - D t) * S t :=
          mul_le_mul_of_nonneg_right (by linarith [abs_lt.mp (hDN t htN)]) hSpos.le
        have h2 : -η ≤ B t + A := by linarith [abs_lt.mp (hBN t htN)]
        have hxS : x ≤ S t := by linarith
        have h3 : (e - η) * x ≤ (e - η) * S t := mul_le_mul_of_nonneg_left hxS (by linarith)
        have h4 : η * x ≤ e / 2 * x := mul_le_mul_of_nonneg_right hηe hx.le
        change c1 < S t ^ 2 - D t * S t + B t
        rw [hF t, hc1]
        linarith)
    have hSb1 : M < S b1 := by
      have h : S t1 + c1 * (b1 - t1) ≤ S b1 := hgrow ⟨htb1, le_rfl⟩
      have : c1 * (b1 - t1) = M := by simp only [b1]; field_simp; ring
      linarith
    -- stage B: `1/S` falls at rate at least `1/2`, so it reaches zero in finite time
    have hb1T : T0 ≤ b1 := hT1.trans htb1
    have hSb1pos : 0 < S b1 := by linarith
    set φ0 := (S b1)⁻¹
    have hφ0 : 0 < φ0 := inv_pos.mpr hSb1pos
    have hφ0M : φ0 < M⁻¹ := inv_strictAnti₀ (by linarith) hSb1
    set b2 := b1 + 2 * φ0 + 1
    have htb2 : b1 ≤ b2 := by linarith
    have hinvd : ∀ t, T0 ≤ t → HasDerivAt (fun s => (S s)⁻¹)
        (-(S t ^ 2 - D t * S t + B t) / S t ^ 2) t := fun t ht =>
      (hS t ht).inv (ne_of_gt (hpos t ht))
    have hdecay := image_le_of_deriv_right_lt_deriv_boundary' (a := b1) (b := b2)
      (f := fun s => (S s)⁻¹) (f' := fun t => -(S t ^ 2 - D t * S t + B t) / S t ^ 2)
      (HasDerivAt.continuousOn (fun t ht => hinvd t (hb1T.trans ht.1)))
      (fun t ht => (hinvd t (hb1T.trans ht.1)).hasDerivWithinAt)
      (B := fun t => φ0 - (t - b1) / 2) (B' := fun _ => -(1 / 2))
      (by simp [φ0]) (by fun_prop)
      (fun t _ => (((hasDerivAt_id t).sub_const b1).div_const 2).const_sub φ0 |>.congr_deriv
        (by simp) |>.hasDerivWithinAt)
      (by
        intro t ht hφB
        have htN : N ≤ t := ht1.trans (htb1.trans ht.1)
        have hSpos := hpos t (hb1T.trans ht.1)
        have hφB' : (S t)⁻¹ = φ0 - (t - b1) / 2 := hφB
        have hφle : (S t)⁻¹ ≤ φ0 := by
          rw [hφB']
          have : 0 ≤ (t - b1) / 2 := div_nonneg (sub_nonneg.mpr ht.1) (by norm_num)
          linarith
        have hSM : M < S t := by
          have h := hφle.trans_lt hφ0M
          rwa [inv_lt_inv₀ hSpos (by linarith)] at h
        have h1 : -η * S t ≤ (d - D t) * S t :=
          mul_le_mul_of_nonneg_right (by linarith [abs_lt.mp (hDN t htN)]) hSpos.le
        have h2 : -η ≤ B t + A := by linarith [abs_lt.mp (hBN t htN)]
        have hS1 : 1 ≤ S t := hMpos.trans hSM.le
        have hMS : M * S t ≤ S t * S t := mul_le_mul_of_nonneg_right hSM.le hSpos.le
        have hAS : (A + 1) * 1 ≤ (A + 1) * S t := mul_le_mul_of_nonneg_left hS1 (by linarith)
        have hηS : η * S t ≤ 1 * S t := mul_le_mul_of_nonneg_right hη1 hSpos.le
        have hquad : 3 / 4 * S t ^ 2 ≤ S t ^ 2 - D t * S t + B t := by
          rw [hF t, ← hfac (S t), hM] at *
          nlinarith
        have hsq : 0 < S t ^ 2 := by positivity
        change -(S t ^ 2 - D t * S t + B t) / S t ^ 2 < -(1 / 2)
        rw [div_lt_iff₀ hsq]
        linarith)
    have hb2 : (S b2)⁻¹ ≤ φ0 - (b2 - b1) / 2 := hdecay ⟨htb2, le_rfl⟩
    have hb2pos := inv_pos.mpr (hpos b2 (hb1T.trans htb2))
    have : φ0 - (b2 - b1) / 2 = -(1 / 2) := by simp only [b2]; ring
    linarith
  refine ⟨N, fun t ht => ?_⟩
  rw [Real.dist_eq, abs_lt]
  have h1 := hlower t ht
  have h2 := hupper t ht
  constructor <;> linarith

end RamseyCassKoopmans
