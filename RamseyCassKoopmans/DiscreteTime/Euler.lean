/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import DiscreteTime.Bellman

/-!
# Interiority and the Euler equation

* `IsOptimal.shift`: every tail of an optimal path is optimal from the stock reached,
  and `IsOptimal.bellman_eq` gives the Bellman equation along the path.
* `interior_choice`: by the Inada conditions a maximizer of `u(F(x) - y) + β V(y)` over
  `0 ≤ y ≤ F(x)` is interior: saving and consumption are both strictly positive.
* `IsOptimal.capital_pos`, `IsOptimal.consumption_pos`: an optimal path from positive
  capital keeps capital and consumption strictly positive.
* `IsOptimal.euler`: `u'(c t) = β u'(c (t+1)) F'(k (t+1))`, `F' = f' + 1 - δ`.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.DiscreteTime

variable {f u : ℝ → ℝ} {β δ : ℝ}

/-- A feasible path attaining the maximal welfare from `x`. -/
def IsOptimal (f u : ℝ → ℝ) (β δ x : ℝ) (k : ℕ → ℝ) : Prop :=
  Feasible f δ x k ∧ ∀ k', Feasible f δ x k' → welfare f u β δ k' ≤ welfare f u β δ k

theorem isOptimal_optimalPath (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) :
    IsOptimal f u β δ x (optimalPath P hx) := optimalPath_spec P hx

theorem IsOptimal.welfare_eq (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) : welfare f u β δ k = value P x := by
  apply le_antisymm (welfare_le_value P hx hk.1)
  rw [value_eq P hx]
  exact hk.2 _ (optimalPath_spec P hx).1

theorem IsOptimal.tail (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) : IsOptimal f u β δ (k 1) (DiscreteTime.tail k) := by
  refine ⟨hk.1.tail, fun k' hk' => ?_⟩
  rw [tail_optimal P hx hk.1 hk.2]
  exact welfare_le_value P (hk.1.2 0).1 hk'

theorem IsOptimal.shift (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    IsOptimal f u β δ (k t) (fun s => k (t + s)) := by
  induction t with
  | zero => simpa only [zero_add, hk.1.1] using hk
  | succ t ih =>
    have h := ih.tail P (hk.1.nonneg hx t)
    have heq : DiscreteTime.tail (fun s => k (t + s)) = fun s => k (t + 1 + s) := by
      funext s
      simp only [DiscreteTime.tail]
      congr 1
      ring
    rw [heq] at h
    simpa only [add_zero] using h

/-- The Bellman equation along an optimal path. -/
theorem IsOptimal.bellman_eq (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    value P (k t) = u (resources f δ (k t) - k (t + 1)) + β * value P (k (t + 1)) := by
  have hs := hk.shift P hx t
  have hkt := hk.1.nonneg hx t
  rw [← hs.welfare_eq P hkt, welfare_eq_head_add P hs.1 hkt, tail_optimal P hkt hs.1 hs.2]
  simp only [consumption, add_zero]

theorem value_zero (P : Primitives f u β δ) : value P 0 = u 0 + β * value P 0 := by
  obtain ⟨hk, -⟩ := optimalPath_spec P (le_refl (0 : ℝ))
  have h1 : optimalPath P (le_refl (0 : ℝ)) 1 = 0 := by
    have := hk.2 0
    rw [hk.1, resources_zero P] at this
    linarith [this.1, this.2]
  have := (bellman P (le_refl (0 : ℝ))).1
  rwa [h1, resources_zero P, sub_zero] at this

theorem Primitives.u_prime_anti (P : Primitives f u β δ) : StrictAntiOn (deriv u) (Ioi 0) :=
  (P.u_conc.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictAntiOn_deriv P.u_diff

/-- A maximizer of `u(F(x) - y) + β V(y)` is interior. -/
theorem interior_choice (P : Primitives f u β δ) {x y : ℝ} (hx : 0 < x) (hy0 : 0 ≤ y)
    (hyF : y ≤ resources f δ x)
    (hmax : ∀ z, 0 ≤ z → z ≤ resources f δ x →
      u (resources f δ x - z) + β * value P z ≤ u (resources f δ x - y) + β * value P y) :
    0 < y ∧ y < resources f δ x := by
  have hFx : 0 < resources f δ x := by
    have h := P.resources_strictMono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx.le) hx
    rwa [resources_zero P] at h
  have hVmono := value_strictMono P
  have hVconc := value_strictConcave P
  constructor
  · -- saving is positive
    by_contra hle
    push Not at hle
    have hy : y = 0 := le_antisymm hle hy0
    subst hy
    set a := resources f δ x / 2 with ha
    have hapos : 0 < a := half_pos hFx
    have hua : 0 < deriv u a := P.u_prime_pos a hapos
    -- small `ε` with `F(ε) ≤ a` and `β f'(ε) > 1`
    have hFcont : Tendsto (resources f δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (P.resources_cont (0 : ℝ) (mem_Ici.mpr le_rfl)).tendsto
      rw [resources_zero P] at this
      exact this.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
    obtain ⟨ε, hε⟩ := ((eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0).and
      ((hFcont.eventually (gt_mem_nhds hapos)).and
      ((P.f_inada0.eventually (eventually_gt_atTop (1 / β))).and
      (Ioo_mem_nhdsGT hapos : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo 0 a)))).exists
    obtain ⟨hεpos, hFε, hfε, hεa⟩ := hε
    have hεpos' : (0 : ℝ) < ε := hεpos
    have hεF : ε ≤ resources f δ x := by linarith [hεa.2]
    have hcmp := hmax ε hεpos'.le hεF
    -- `u(F x) - u(F x - ε) ≤ u'(a) ε`
    have hu1 : u (resources f δ x) - u (resources f δ x - ε) ≤ deriv u a * ε := by
      have hpos : 0 < resources f δ x - ε := by linarith [hεa.2]
      have hs := concave_support P.u_conc.concaveOn (mem_Ici.mpr hpos.le) (mem_Ici.mpr hFx.le)
        (P.u_diff _ hpos).hasDerivAt
      have hmono : deriv u (resources f δ x - ε) ≤ deriv u a :=
        P.u_prime_anti.antitoneOn hapos hpos (by linarith [hεa.2])
      have : u (resources f δ x) - u (resources f δ x - ε) ≤
          deriv u (resources f δ x - ε) * ε := by
        have := hs
        rw [show resources f δ x - (resources f δ x - ε) = ε by ring] at this
        exact this
      exact this.trans (mul_le_mul_of_nonneg_right hmono hεpos'.le)
    -- `V(ε) - V(0) ≥ u(F ε) - u(0) ≥ u'(a) f'(ε) ε`
    have hFεpos : 0 < resources f δ ε := by
      have h := P.resources_strictMono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hεpos'.le) hεpos'
      rwa [resources_zero P] at h
    have hV1 : u (resources f δ ε) - u 0 ≤ value P ε - value P 0 := by
      have hb := (bellman P hεpos'.le).2 0 le_rfl hFεpos.le
      rw [sub_zero] at hb
      have hz := value_zero P
      have : value P 0 * (1 - β) = u 0 := by linarith
      have hV0 : value P 0 = u 0 + β * value P 0 := hz
      nlinarith [P.β_pos, P.β_lt_one]
    have hu2 : deriv u a * (deriv f ε * ε) ≤ u (resources f δ ε) - u 0 := by
      have hs := concave_support P.u_conc.concaveOn (mem_Ici.mpr hFεpos.le) (mem_Ici.mpr le_rfl)
        (P.u_diff _ hFεpos).hasDerivAt
      have hmono : deriv u a ≤ deriv u (resources f δ ε) :=
        P.u_prime_anti.antitoneOn hFεpos hapos hFε.le
      have hfε' : deriv f ε * ε ≤ resources f δ ε := by
        have hs' := concave_support P.f_conc.concaveOn (mem_Ici.mpr hεpos'.le) (mem_Ici.mpr le_rfl)
          (P.f_diff _ hεpos').hasDerivAt
        rw [P.f_zero] at hs'
        have := mul_nonneg (sub_nonneg.mpr P.δ_le_one) hεpos'.le
        simp only [resources]
        linarith
      have hfpos : 0 ≤ deriv f ε * ε := mul_nonneg (P.f_prime_pos ε hεpos').le hεpos'.le
      have h1 : deriv u a * (deriv f ε * ε) ≤ deriv u (resources f δ ε) * resources f δ ε :=
        mul_le_mul hmono hfε' hfpos (P.u_prime_pos _ hFεpos).le
      linarith
    have hbf : 1 < β * deriv f ε := by
      have := (div_lt_iff₀' P.β_pos).mp hfε
      linarith
    have hgain : deriv u a * ε < β * (deriv u a * (deriv f ε * ε)) := by
      have := mul_lt_mul_of_pos_left hbf (mul_pos hua hεpos')
      nlinarith
    simp only [sub_zero] at hcmp
    have := mul_le_mul_of_nonneg_left (hu2.trans hV1) P.β_pos.le
    linarith
  · -- consumption is positive
    by_contra hle
    push Not at hle
    have hy : y = resources f δ x := le_antisymm hyF hle
    subst hy
    set Y := resources f δ x
    set S := 2 * (value P Y - value P 0) / Y
    obtain ⟨ε, hε⟩ := ((eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi 0).and
      ((P.u_inada0.eventually (eventually_gt_atTop (β * S))).and
      (Ioo_mem_nhdsGT (half_pos hFx) : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioo 0 (Y / 2)))).exists
    obtain ⟨hεpos, huε, hεY⟩ := hε
    have hεpos' : (0 : ℝ) < ε := hεpos
    have hYε : Y / 2 < Y - ε := by linarith [hεY.2]
    have hcmp := hmax (Y - ε) (by linarith) (by linarith)
    rw [sub_self, show Y - (Y - ε) = ε by ring] at hcmp
    -- `u(ε) - u(0) ≥ u'(ε) ε`
    have hu : deriv u ε * ε ≤ u ε - u 0 := by
      have hs := concave_support P.u_conc.concaveOn (mem_Ici.mpr hεpos'.le) (mem_Ici.mpr le_rfl)
        (P.u_diff _ hεpos').hasDerivAt
      linarith
    -- `V(Y) - V(Y - ε) ≤ S ε` by concavity and monotonicity
    have hV : value P Y - value P (Y - ε) ≤ S * ε := by
      have hslope := hVconc.concaveOn.slope_anti_adjacent (x := 0) (y := Y - ε) (z := Y)
        (mem_Ici.mpr le_rfl) (mem_Ici.mpr hFx.le) (by linarith) (by linarith)
      rw [show Y - (Y - ε) = ε by ring, div_le_div_iff₀ hεpos' (by linarith : (0 : ℝ) < Y - ε - 0),
        sub_zero] at hslope
      have hmono : value P (Y - ε) ≤ value P Y :=
        hVmono.monotoneOn (mem_Ici.mpr (by linarith)) (mem_Ici.mpr hFx.le) (by linarith)
      have hV0 : value P 0 ≤ value P (Y - ε) :=
        hVmono.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr (by linarith)) (by linarith)
      have hS : (value P (Y - ε) - value P 0) / (Y - ε) ≤ S := by
        rw [div_le_iff₀ (by linarith)]
        simp only [S]
        rw [div_mul_eq_mul_div, le_div_iff₀ hFx]
        nlinarith
      have h2 : (value P Y - value P (Y - ε)) * (Y - ε) ≤
          (value P (Y - ε) - value P 0) * ε := hslope
      have h3 := (div_le_iff₀ (by linarith : (0 : ℝ) < Y - ε)).mp hS
      nlinarith
    have hgain : β * S * ε < deriv u ε * ε := mul_lt_mul_of_pos_right huε hεpos'
    have := mul_le_mul_of_nonneg_left hV P.β_pos.le
    linarith

theorem Primitives.resources_pos (P : Primitives f u β δ) {k : ℝ} (hk : 0 < k) :
    0 < resources f δ k := by
  have h := P.resources_strictMono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hk.le) hk
  rwa [resources_zero P] at h

/-- An optimal path from positive capital keeps capital strictly positive and
consumption strictly positive. -/
theorem IsOptimal.interior (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    0 < k t ∧ 0 < k (t + 1) ∧ 0 < consumption f δ k t := by
  have hpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => rw [hk.1.1]; exact hx
    | succ t ih =>
      have hbell := hk.bellman_eq P hx.le t
      exact (interior_choice P ih (hk.1.2 t).1 (hk.1.2 t).2 (fun z hz0 hzF => by
        rw [← hbell]; exact (bellman P (hk.1.nonneg hx.le t)).2 z hz0 hzF)).1
  refine ⟨hpos t, hpos (t + 1), ?_⟩
  have hbell := hk.bellman_eq P hx.le t
  have h := (interior_choice P (hpos t) (hk.1.2 t).1 (hk.1.2 t).2 (fun z hz0 hzF => by
    rw [← hbell]; exact (bellman P (hk.1.nonneg hx.le t)).2 z hz0 hzF)).2
  simp only [consumption]
  linarith

theorem hasDerivAt_resources (P : Primitives f u β δ) {k : ℝ} (hk : 0 < k) :
    HasDerivAt (resources f δ) (deriv f k + (1 - δ)) k := by
  have h1 : HasDerivAt (fun y => f y + (1 - δ) * y) (deriv f k + (1 - δ) * 1) k :=
    (P.f_diff k hk).hasDerivAt.add ((hasDerivAt_id' k).const_mul (1 - δ))
  rw [mul_one] at h1
  exact h1

/-- The Euler equation along an optimal path. -/
theorem IsOptimal.euler (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    deriv u (consumption f δ k t) =
      β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ)) := by
  obtain ⟨hkt, hkt1, hct⟩ := hk.interior P hx t
  obtain ⟨-, -, hct1⟩ := hk.interior P hx (t + 1)
  set ψ : ℝ → ℝ := fun y => u (resources f δ (k t) - y) +
    β * (u (resources f δ y - k (t + 2)) + β * value P (k (t + 2)))
  have hct' : 0 < resources f δ (k t) - k (t + 1) := hct
  have hct1' : 0 < resources f δ (k (t + 1)) - k (t + 2) := hct1
  -- `ψ` has a local maximum at `k (t + 1)`
  have hloc : IsLocalMax ψ (k (t + 1)) := by
    have hFc : ContinuousAt (resources f δ) (k (t + 1)) :=
      (hasDerivAt_resources P hkt1).continuousAt
    have hnear : ∀ᶠ y in 𝓝 (k (t + 1)), 0 < y ∧ y < resources f δ (k t) ∧
        k (t + 2) < resources f δ y := by
      refine (lt_mem_nhds hkt1).and
        ((gt_mem_nhds (by linarith : k (t + 1) < resources f δ (k t))).and ?_)
      exact hFc.eventually (lt_mem_nhds (by linarith : k (t + 2) < resources f δ (k (t + 1))))
    filter_upwards [hnear] with y hy
    obtain ⟨hypos, hyF, hy2⟩ := hy
    have hbt := hk.bellman_eq P hx.le t
    have hbt1 := hk.bellman_eq P hx.le (t + 1)
    have hin1 := (bellman P hypos.le).2 (k (t + 2)) (hk.1.2 (t + 1)).1 hy2.le
    have hin0 := (bellman P (hk.1.nonneg hx.le t)).2 y hypos.le hyF.le
    have := mul_le_mul_of_nonneg_left hin1 P.β_pos.le
    simp only [ψ]
    rw [show t + 1 + 1 = t + 2 by ring] at hbt1
    have hbt1' : β * value P (k (t + 1)) = β * (u (resources f δ (k (t + 1)) - k (t + 2)) +
        β * value P (k (t + 2))) := by rw [hbt1]
    linarith
  -- its derivative at `k (t + 1)`
  have hd1 : HasDerivAt (fun y => u (resources f δ (k t) - y))
      (deriv u (resources f δ (k t) - k (t + 1)) * (-1)) (k (t + 1)) :=
    (P.u_diff _ hct').hasDerivAt.comp (k (t + 1)) ((hasDerivAt_id (k (t + 1))).const_sub _)
  have hd2 : HasDerivAt (fun y => u (resources f δ y - k (t + 2)))
      (deriv u (resources f δ (k (t + 1)) - k (t + 2)) * (deriv f (k (t + 1)) + (1 - δ)))
      (k (t + 1)) :=
    (P.u_diff _ hct1').hasDerivAt.comp (k (t + 1)) ((hasDerivAt_resources P hkt1).sub_const _)
  have hd := hd1.add ((hd2.add_const (β * value P (k (t + 2)))).const_mul β)
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hc0 : consumption f δ k t = resources f δ (k t) - k (t + 1) := rfl
  have hc1 : consumption f δ k (t + 1) = resources f δ (k (t + 1)) - k (t + 2) := rfl
  rw [hc0, hc1]
  linarith

end RamseyCassKoopmans.DiscreteTime
