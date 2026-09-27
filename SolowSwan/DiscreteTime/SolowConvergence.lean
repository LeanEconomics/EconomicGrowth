/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import DiscreteTime.GeneralSolowApplications
import Solow1956.Growth.SolowConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Absolute convergence among identical discrete-time Solow economies, and its speed

The discrete counterpart of `Solow1956.Growth.SolowConvergence`. Two economies share
`s`, `δ`, `γ` and `f` and differ only in initial capital. We prove:

* `path_eq_of_meet`, `paths_ordered`: paths that meet at a date agree at every
  earlier date (the map is injective), so paths never cross.
* `poorer_grows_faster`: the poorer economy's gross growth factor `k(t+1)/k(t)` is
  strictly higher every period.
* `log_gap_strictAnti`, `absolute_convergence`: the log gap `D t = log l t - log k t`
  strictly decreases, and the level gap, log gap and ratio converge to `0`, `0`, `1`.
* `log_gap_le_of_contraction_bound`, `exists_uniform_rate`,
  `absolute_convergence_rate`, `level_gap_le`: geometric convergence. The local
  contraction `κ(k) = k G'(k) / G(k)` (the elasticity of the map) lies in `(0, 1)`;
  an upper bound `ρ` for it on the range of the paths gives `D t ≤ ρ^t D 0`.
* `sharp_convergence_rate`, `log_gap_ratio_tendsto`, `log_gap_rate_tendsto`: the exact
  asymptotic factor is `ρ* = κ(k*) = G'(k*) = (s f'(k*) + 1 - δ) / γ`:
  `D (t+1) / D t → ρ*` and `log (D t) / t → log ρ*`.
* `contraction_steady_eq`: `ρ* = 1 - β*/γ`, with `β* = m - s f'(k*)` the
  continuous-time speed; `cobbDouglas_contraction`: `ρ* = 1 - (1 - α) m / γ`
  (`= α` under full depreciation and `γ = 1`).

The constant steady-state path is admissible, so every result also bounds a single
economy's convergence to its steady state (`log_gap_steady_le`).
-/

open Set Filter Topology

namespace Solow1956.DiscreteTime

open Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- Gross growth factor of capital, `k(t+1)/k(t) = (s f(k)/k + 1 - δ)/γ`. -/
noncomputable def growthFactor (f : ℝ → ℝ) (s δ γ k : ℝ) : ℝ := (s * (f k / k) + (1 - δ)) / γ

/-- Local contraction `κ(k) = k G'(k)/G(k)`: the elasticity of the map, the slope of
`log k(t+1)` against `log k(t)`. -/
noncomputable def contraction (f : ℝ → ℝ) (s δ k : ℝ) : ℝ :=
  k * (s * deriv f k + (1 - δ)) / (s * f k + (1 - δ) * k)

theorem next_div_eq_growthFactor (s δ γ : ℝ) {k : ℝ} (hk : 0 < k) :
    next f s δ γ k / k = growthFactor f s δ γ k := by
  unfold next growthFactor
  field_simp

theorem growthFactor_strictAnti (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    StrictAntiOn (growthFactor f s δ γ) (Ioi 0) := by
  intro a ha b hb hab
  have := mul_lt_mul_of_pos_left (h.average_strictAnti ha hb hab) P.saving_pos
  exact div_lt_div_of_pos_right (by linarith) P.growth_pos

theorem gross_pos (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ) (hk : 0 < k) :
    0 < s * f k + (1 - δ) * k := by
  have := mul_pos P.saving_pos (h.output_pos hk)
  have := mul_nonneg (sub_nonneg.mpr P.depreciation_le_one) hk.le
  linarith

theorem contraction_pos (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ) (hk : 0 < k) :
    0 < contraction f s δ k := by
  have := mul_pos P.saving_pos (h.marginal_positive k hk)
  have := sub_nonneg.mpr P.depreciation_le_one
  exact div_pos (mul_pos hk (by linarith)) (gross_pos h P hk)

theorem contraction_lt_one (h : Technology f) {s δ γ k : ℝ} (P : Params s δ γ) (hk : 0 < k) :
    contraction f s δ k < 1 := by
  have hg := mul_lt_mul_of_pos_left (h.output_gap hk) P.saving_pos
  apply (div_lt_one (gross_pos h P hk)).mpr
  nlinarith

theorem contraction_continuousOn (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    ContinuousOn (contraction f s δ) (Ioi 0) := by
  have hf : ContinuousOn f (Ioi 0) := fun k hk =>
    (h.differentiable k hk).continuousAt.continuousWithinAt
  exact (continuousOn_id.mul ((h.derivative_continuous.const_mul s).add continuousOn_const)).div
    ((hf.const_mul s).add (continuousOn_id.const_mul (1 - δ)))
    (fun k hk => ne_of_gt (gross_pos h P hk))

/-- At the steady state the contraction is the slope of the map, `G'(k*)`. -/
theorem contraction_steady (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    contraction f s δ (steady h s δ γ) = (s * deriv f (steady h s δ γ) + (1 - δ)) / γ := by
  obtain ⟨hk, hfix⟩ := steady_spec h P
  set ks := steady h s δ γ
  have hgross : s * f ks + (1 - δ) * ks = γ * ks := by
    unfold next at hfix
    field_simp [ne_of_gt P.growth_pos] at hfix
    linarith
  unfold contraction
  rw [hgross]
  field_simp [ne_of_gt P.growth_pos, ne_of_gt hk]

/-- The discrete factor and the continuous speed: `ρ* = 1 - β*/γ`. -/
theorem contraction_steady_eq (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    contraction f s δ (steady h s δ γ) =
      1 - convergenceSpeed f s (steady h s δ γ) / γ := by
  rw [contraction_steady h P, steady,
    convergenceSpeed_steady h P.saving_pos P.dilution_pos]
  field_simp [ne_of_gt P.growth_pos]
  ring

/-- Cobb–Douglas: `ρ* = 1 - (1 - α)(γ - 1 + δ)/γ`. -/
theorem cobbDouglas_contraction {α b δ γ : ℝ} (hα : 0 < α) (hα1 : α < 1) (P : Params b δ γ) :
    contraction (fun k : ℝ => k ^ α) b δ (steady (technology_rpow hα hα1) b δ γ) =
      1 - (1 - α) * (γ - 1 + δ) / γ := by
  rw [contraction_steady_eq _ P, steady, cobbDouglas_speed hα hα1 P.saving_pos P.dilution_pos]

/-- The constant path at `k*` is admissible. -/
theorem isPath_steady (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) :
    IsPath f s δ γ (fun _ => steady h s δ γ) :=
  ⟨(steady_spec h P).1, fun _ => (steady_spec h P).2.symm⟩

/-- Backward uniqueness: paths that meet at a date agree at every earlier date. -/
theorem path_eq_of_meet (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l)
    {T : ℕ} (hmeet : k T = l T) {t : ℕ} (ht : t ≤ T) : k t = l t := by
  induction T with
  | zero => rwa [Nat.le_zero.mp ht]
  | succ T ih =>
    rcases Nat.lt_or_eq_of_le ht with hlt | heq
    · apply ih _ (Nat.lt_succ_iff.mp hlt)
      rw [hk.succ, hl.succ] at hmeet
      exact (next_strictMono h P).injOn (hk.pos h P T).le (hl.pos h P T).le hmeet
    · rw [heq]; exact hmeet

/-- Paths never cross: the initially poorer economy is strictly poorer every period. -/
theorem paths_ordered (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0)
    (t : ℕ) : k t < l t := by
  induction t with
  | zero => exact h0
  | succ t ih =>
    rw [hk.succ, hl.succ]
    exact next_strictMono h P (hk.pos h P t).le (hl.pos h P t).le ih

/-- The poorer economy grows by a strictly larger factor every period. -/
theorem poorer_grows_faster (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0)
    (t : ℕ) : l (t + 1) / l t < k (t + 1) / k t := by
  rw [hk.succ, hl.succ, next_div_eq_growthFactor s δ γ (hk.pos h P t),
    next_div_eq_growthFactor s δ γ (hl.pos h P t)]
  exact growthFactor_strictAnti h P (hk.pos h P t) (hl.pos h P t) (paths_ordered h P hk hl h0 t)

theorem log_gap_pos (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0)
    (t : ℕ) : 0 < Real.log (l t) - Real.log (k t) :=
  sub_pos.mpr (Real.log_lt_log (hk.pos h P t) (paths_ordered h P hk hl h0 t))

/-- The proportional gap shrinks strictly every period. -/
theorem log_gap_strictAnti (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) :
    StrictAnti (fun t => Real.log (l t) - Real.log (k t)) := by
  apply strictAnti_nat_of_succ_lt
  intro t
  have hkt := hk.pos h P t
  have hlt := hl.pos h P t
  have hfast := poorer_grows_faster h P hk hl h0 t
  have hk1 := hk.pos h P (t + 1)
  have hl1 := hl.pos h P (t + 1)
  have hlog := Real.log_lt_log (div_pos hl1 hlt) hfast
  rw [Real.log_div hl1.ne' hlt.ne', Real.log_div hk1.ne' hkt.ne'] at hlog
  linarith

/-- Absolute convergence: identical economies converge to each other in levels, in
logs, and in ratio. -/
theorem absolute_convergence (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) :
    Tendsto (fun t => l t - k t) atTop (𝓝 0) ∧
      Tendsto (fun t => Real.log (l t) - Real.log (k t)) atTop (𝓝 0) ∧
      Tendsto (fun t => l t / k t) atTop (𝓝 1) := by
  have hks := (steady_spec h P).1
  have hkl := hk.tendsto h P
  have hll := hl.tendsto h P
  refine ⟨by simpa only [sub_self] using hll.sub hkl, ?_, ?_⟩
  · have hlog := (Real.continuousAt_log (ne_of_gt hks)).tendsto
    have := (hlog.comp hll).sub (hlog.comp hkl)
    rw [sub_self] at this
    exact this
  · have := hll.div hkl (ne_of_gt hks)
    rw [div_self (ne_of_gt hks)] at this
    exact this

theorem hasDerivAt_log_next_sub (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ) (r : ℝ)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z => Real.log (next f s δ γ z) - r * Real.log z)
      ((contraction f s δ z - r) / z) z := by
  have hg := gross_pos h P hz
  have h1 := (next_hasDerivAt h s δ γ hz).log (ne_of_gt (next_pos h P hz))
  have h2 := (Real.hasDerivAt_log (ne_of_gt hz)).const_mul r
  refine (h1.sub h2).congr_deriv ?_
  unfold contraction next
  field_simp [ne_of_gt P.growth_pos, ne_of_gt hg, ne_of_gt hz]

/-- An upper bound `ρ` on the contraction over `[a, b]` bounds the one-period log gap. -/
theorem log_next_gap_le (h : Technology f) {s δ γ a b r : ℝ} (P : Params s δ γ) (ha : 0 < a)
    (hr : ∀ z ∈ Icc a b, contraction f s δ z ≤ r)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    Real.log (next f s δ γ y) - Real.log (next f s δ γ x) ≤ r * (Real.log y - Real.log x) := by
  have hanti : AntitoneOn (fun z => Real.log (next f s δ γ z) - r * Real.log z) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (HasDerivAt.continuousOn (fun z hz => hasDerivAt_log_next_sub h P r (ha.trans_le hz.1)))
      (fun z hz => (hasDerivAt_log_next_sub h P r (ha.trans_le
        (interior_subset hz : z ∈ Icc a b).1)).differentiableAt.differentiableWithinAt)
    intro z hz
    have hz' : z ∈ Icc a b := interior_subset hz
    rw [(hasDerivAt_log_next_sub h P r (ha.trans_le hz'.1)).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hr z hz')) (ha.trans_le hz'.1).le
  have := hanti hx hy hxy
  simp only at this
  linarith

/-- A lower bound `ρ'` on the contraction over `[a, b]` bounds the one-period log gap below. -/
theorem log_next_gap_ge (h : Technology f) {s δ γ a b r : ℝ} (P : Params s δ γ) (ha : 0 < a)
    (hr : ∀ z ∈ Icc a b, r ≤ contraction f s δ z)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    r * (Real.log y - Real.log x) ≤ Real.log (next f s δ γ y) - Real.log (next f s δ γ x) := by
  have hmono : MonotoneOn (fun z => Real.log (next f s δ γ z) - r * Real.log z) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (HasDerivAt.continuousOn (fun z hz => hasDerivAt_log_next_sub h P r (ha.trans_le hz.1)))
      (fun z hz => (hasDerivAt_log_next_sub h P r (ha.trans_le
        (interior_subset hz : z ∈ Icc a b).1)).differentiableAt.differentiableWithinAt)
    intro z hz
    have hz' : z ∈ Icc a b := interior_subset hz
    rw [(hasDerivAt_log_next_sub h P r (ha.trans_le hz'.1)).deriv]
    exact div_nonneg (sub_nonneg.mpr (hr z hz')) (ha.trans_le hz'.1).le
  have := hmono hx hy hxy
  simp only at this
  linarith

/-- Geometric bound from above: from any date `T` after which both ordered paths stay
in `[a, b]`, an upper bound `ρ ≥ 0` on the contraction gives `D (T + n) ≤ ρ^n D T`. -/
theorem log_gap_upper (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0)
    {a b r : ℝ} {T : ℕ} (ha : 0 < a) (hr0 : 0 ≤ r)
    (hkw : ∀ t, T ≤ t → k t ∈ Icc a b) (hlw : ∀ t, T ≤ t → l t ∈ Icc a b)
    (hr : ∀ z ∈ Icc a b, contraction f s δ z ≤ r) (n : ℕ) :
    Real.log (l (T + n)) - Real.log (k (T + n)) ≤
      r ^ n * (Real.log (l T) - Real.log (k T)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hT : T ≤ T + n := Nat.le_add_right T n
    have hstep := log_next_gap_le (γ := γ) h P ha hr (hkw _ hT) (hlw _ hT)
      (paths_ordered h P hk hl h0 (T + n)).le
    rw [← hk.succ, ← hl.succ] at hstep
    rw [← add_assoc, pow_succ]
    calc Real.log (l (T + n + 1)) - Real.log (k (T + n + 1))
        ≤ r * (Real.log (l (T + n)) - Real.log (k (T + n))) := hstep
      _ ≤ r * (r ^ n * (Real.log (l T) - Real.log (k T))) :=
          mul_le_mul_of_nonneg_left ih hr0
      _ = _ := by ring

/-- Geometric bound from below: a lower bound `ρ' ≥ 0` on the contraction gives
`ρ'^n D T ≤ D (T + n)`. -/
theorem log_gap_lower (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0)
    {a b r : ℝ} {T : ℕ} (ha : 0 < a) (hr0 : 0 ≤ r)
    (hkw : ∀ t, T ≤ t → k t ∈ Icc a b) (hlw : ∀ t, T ≤ t → l t ∈ Icc a b)
    (hr : ∀ z ∈ Icc a b, r ≤ contraction f s δ z) (n : ℕ) :
    r ^ n * (Real.log (l T) - Real.log (k T)) ≤
      Real.log (l (T + n)) - Real.log (k (T + n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hT : T ≤ T + n := Nat.le_add_right T n
    have hstep := log_next_gap_ge (γ := γ) h P ha hr (hkw _ hT) (hlw _ hT)
      (paths_ordered h P hk hl h0 (T + n)).le
    rw [← hk.succ, ← hl.succ] at hstep
    rw [← add_assoc, pow_succ]
    calc r ^ n * r * (Real.log (l T) - Real.log (k T))
        = r * (r ^ n * (Real.log (l T) - Real.log (k T))) := by ring
      _ ≤ r * (Real.log (l (T + n)) - Real.log (k (T + n))) :=
          mul_le_mul_of_nonneg_left ih hr0
      _ ≤ _ := hstep

/-- Both ordered paths lie between the lower initial stock (or `k*`) and the higher
initial stock (or `k*`). -/
theorem paths_window (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) (t : ℕ) :
    k t ∈ Icc (min (k 0) (steady h s δ γ)) (max (l 0) (steady h s δ γ)) ∧
      l t ∈ Icc (min (k 0) (steady h s δ γ)) (max (l 0) (steady h s δ γ)) := by
  obtain ⟨hk1, hk2⟩ := hk.bounds h P t
  obtain ⟨hl1, hl2⟩ := hl.bounds h P t
  have h1 : min (k 0) (steady h s δ γ) ≤ min (l 0) (steady h s δ γ) :=
    min_le_min_right _ h0.le
  have h2 : max (k 0) (steady h s δ γ) ≤ max (l 0) (steady h s δ γ) :=
    max_le_max_right _ h0.le
  exact ⟨⟨hk1, hk2.trans h2⟩, ⟨h1.trans hl1, hl2⟩⟩

/-- Global geometric convergence at an explicit factor: any bound `ρ` for the
contraction over the range of the two paths satisfies `D t ≤ ρ^t D 0`. -/
theorem log_gap_le_of_contraction_bound (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) {r : ℝ}
    (hr0 : 0 ≤ r)
    (hr : ∀ z ∈ Icc (min (k 0) (steady h s δ γ)) (max (l 0) (steady h s δ γ)),
      contraction f s δ z ≤ r) (t : ℕ) :
    Real.log (l t) - Real.log (k t) ≤ r ^ t * (Real.log (l 0) - Real.log (k 0)) := by
  have ha : 0 < min (k 0) (steady h s δ γ) := lt_min hk.initial_pos (steady_spec h P).1
  simpa only [zero_add] using log_gap_upper h P hk hl h0 (T := 0) ha hr0
    (fun u _ => (paths_window h P hk hl h0 u).1) (fun u _ => (paths_window h P hk hl h0 u).2)
    hr t

/-- A uniform geometric factor `ρ < 1` exists. -/
theorem exists_uniform_rate (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ t,
      Real.log (l t) - Real.log (k t) ≤ r ^ t * (Real.log (l 0) - Real.log (k 0)) := by
  set a := min (k 0) (steady h s δ γ)
  set b := max (l 0) (steady h s δ γ)
  have ha : 0 < a := lt_min hk.initial_pos (steady_spec h P).1
  have hab : a ≤ b := (min_le_right _ _).trans (le_max_right _ _)
  obtain ⟨z, hz, hzmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab)
    ((contraction_continuousOn h P).mono (fun _ hx => ha.trans_le hx.1))
  have hzpos := ha.trans_le hz.1
  exact ⟨contraction f s δ z, contraction_pos h P hzpos, contraction_lt_one h P hzpos,
    log_gap_le_of_contraction_bound h P hk hl h0 (contraction_pos h P hzpos).le
      (fun y hy => hzmax hy)⟩

/-- Absolute convergence at a geometric rate for any two identical economies. -/
theorem absolute_convergence_rate (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ t,
      |Real.log (l t) - Real.log (k t)| ≤ r ^ t * |Real.log (l 0) - Real.log (k 0)| := by
  rcases lt_trichotomy (k 0) (l 0) with h0 | h0 | h0
  · obtain ⟨r, hr, hr1, hb⟩ := exists_uniform_rate h P hk hl h0
    refine ⟨r, hr, hr1, fun t => ?_⟩
    rw [abs_of_pos (log_gap_pos h P hk hl h0 t), abs_of_pos (log_gap_pos h P hk hl h0 0)]
    exact hb t
  · refine ⟨1 / 2, by norm_num, by norm_num, fun t => ?_⟩
    have he := path_unique hk.succ hl.succ h0
    rw [he, sub_self, sub_self, abs_zero, mul_zero]
  · obtain ⟨r, hr, hr1, hb⟩ := exists_uniform_rate h P hl hk h0
    refine ⟨r, hr, hr1, fun t => ?_⟩
    rw [abs_sub_comm, abs_sub_comm (Real.log (l 0)), abs_of_pos (log_gap_pos h P hl hk h0 t),
      abs_of_pos (log_gap_pos h P hl hk h0 0)]
    exact hb t

/-- A single economy converges geometrically to its steady state. -/
theorem log_gap_steady_le (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k : ℕ → ℝ} (hk : IsPath f s δ γ k) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ t,
      |Real.log (k t) - Real.log (steady h s δ γ)| ≤
        r ^ t * |Real.log (k 0) - Real.log (steady h s δ γ)| :=
  absolute_convergence_rate h P (isPath_steady h P) hk

/-- The level gap also closes geometrically:
`l t - k t ≤ max (l 0) k* · log (l 0 / k 0) · ρ^t`. -/
theorem level_gap_le (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) :
    ∃ r, 0 < r ∧ r < 1 ∧ ∀ t, 0 < l t - k t ∧
      l t - k t ≤ max (l 0) (steady h s δ γ) * (Real.log (l 0) - Real.log (k 0)) * r ^ t := by
  obtain ⟨r, hr, hr1, hb⟩ := exists_uniform_rate h P hk hl h0
  refine ⟨r, hr, hr1, fun t => ⟨sub_pos.mpr (paths_ordered h P hk hl h0 t), ?_⟩⟩
  have hkt := hk.pos h P t
  have hlt := hl.pos h P t
  have hlog : l t - k t ≤ l t * (Real.log (l t) - Real.log (k t)) := by
    have he := Real.add_one_le_exp (Real.log (k t) - Real.log (l t))
    rw [Real.exp_sub, Real.exp_log hkt, Real.exp_log hlt, le_div_iff₀ hlt] at he
    nlinarith
  have hD := log_gap_pos h P hk hl h0 t
  have hup := (paths_window h P hk hl h0 t).2.2
  calc l t - k t ≤ l t * (Real.log (l t) - Real.log (k t)) := hlog
    _ ≤ max (l 0) (steady h s δ γ) * (Real.log (l t) - Real.log (k t)) :=
        mul_le_mul_of_nonneg_right hup hD.le
    _ ≤ max (l 0) (steady h s δ γ) * (r ^ t * (Real.log (l 0) - Real.log (k 0))) :=
        mul_le_mul_of_nonneg_left (hb t) (hlt.le.trans hup)
    _ = _ := by ring

/-- Near the steady state the one-period ratio of log gaps is within `ε` of `ρ*`:
there is a date after which both paths lie in a window where `ρ* - ε ≤ κ ≤ ρ* + ε`. -/
theorem eventually_contraction_window (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) {ε : ℝ} (hε : 0 < ε) :
    ∃ a b : ℝ, 0 < a ∧ ∃ T : ℕ,
      (∀ t, T ≤ t → k t ∈ Icc a b) ∧ (∀ t, T ≤ t → l t ∈ Icc a b) ∧
      ∀ z ∈ Icc a b, |contraction f s δ z - contraction f s δ (steady h s δ γ)| < ε := by
  have hks := (steady_spec h P).1
  set ks := steady h s δ γ
  obtain ⟨d, hd, hdb⟩ := Metric.continuousAt_iff.mp
    ((contraction_continuousOn h P).continuousAt (Ioi_mem_nhds hks)) ε hε
  set r := min (d / 2) (ks / 2)
  have hr : 0 < r := lt_min (half_pos hd) (half_pos hks)
  have ha : 0 < ks - r := by have := min_le_right (d / 2) (ks / 2); linarith
  have hnhds : Icc (ks - r) (ks + r) ∈ 𝓝 ks := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((hk.tendsto h P).eventually hnhds).and ((hl.tendsto h P).eventually hnhds))
  refine ⟨ks - r, ks + r, ha, T, fun t ht => (hT t ht).1, fun t ht => (hT t ht).2, ?_⟩
  intro z hz
  have : dist z ks < d := by
    rw [Real.dist_eq, abs_lt]
    have := min_le_left (d / 2) (ks / 2)
    constructor <;> linarith [hz.1, hz.2]
  have := hdb this
  rwa [Real.dist_eq] at this

/-- The exact asymptotic factor: `D (t+1) / D t → ρ* = κ(k*) = G'(k*)`. -/
theorem log_gap_ratio_tendsto (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) :
    Tendsto (fun t => (Real.log (l (t + 1)) - Real.log (k (t + 1))) /
      (Real.log (l t) - Real.log (k t))) atTop (𝓝 (contraction f s δ (steady h s δ γ))) := by
  set ρ := contraction f s δ (steady h s δ γ)
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨a, b, ha, T, hkw, hlw, hwin⟩ :=
    eventually_contraction_window h P hk hl (half_pos hε)
  refine ⟨T, fun t ht => ?_⟩
  have hD := log_gap_pos h P hk hl h0 t
  have hord := (paths_ordered h P hk hl h0 t).le
  have hup := log_next_gap_le (γ := γ) h P ha
    (fun z hz => (by linarith [(abs_lt.mp (hwin z hz)).2] : contraction f s δ z ≤ ρ + ε / 2))
    (hkw t ht) (hlw t ht) hord
  have hlo := log_next_gap_ge (γ := γ) h P ha
    (fun z hz => (by linarith [(abs_lt.mp (hwin z hz)).1] : ρ - ε / 2 ≤ contraction f s δ z))
    (hkw t ht) (hlw t ht) hord
  rw [← hk.succ, ← hl.succ] at hup hlo
  rw [Real.dist_eq, abs_lt]
  constructor
  · rw [lt_sub_iff_add_lt, lt_div_iff₀ hD]; nlinarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ hD]; nlinarith

/-- Sharp geometric sandwich: for `0 < ε < ρ*` with `ρ* + ε ≤ 1`, the log gap lies
between multiples of `(ρ* - ε)^t` and `(ρ* + ε)^t`. -/
theorem sharp_convergence_rate (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0)
    {ε : ℝ} (hε : 0 < ε) (hερ : ε < contraction f s δ (steady h s δ γ))
    (hρ1 : contraction f s δ (steady h s δ γ) + ε ≤ 1) :
    ∃ c, 0 < c ∧ ∃ C, 0 < C ∧ ∀ t,
      c * (contraction f s δ (steady h s δ γ) - ε) ^ t ≤ Real.log (l t) - Real.log (k t) ∧
        Real.log (l t) - Real.log (k t) ≤ C * (contraction f s δ (steady h s δ γ) + ε) ^ t := by
  set ρ := contraction f s δ (steady h s δ γ)
  set D : ℕ → ℝ := fun u => Real.log (l u) - Real.log (k u) with hD
  obtain ⟨a, b, ha, T, hkw, hlw, hwin⟩ := eventually_contraction_window h P hk hl hε
  have hDpos : ∀ t, 0 < D t := log_gap_pos h P hk hl h0
  have hanti := log_gap_strictAnti h P hk hl h0
  have hlo0 : 0 ≤ ρ - ε := by linarith
  have hhi0 : 0 < ρ + ε := by linarith
  have hlo1 : ρ - ε ≤ 1 := by linarith
  have hupT := log_gap_upper h P hk hl h0 ha hhi0.le hkw hlw
    (fun z hz => (by linarith [(abs_lt.mp (hwin z hz)).2] : contraction f s δ z ≤ ρ + ε))
  have hloT := log_gap_lower h P hk hl h0 ha hlo0 hkw hlw
    (fun z hz => (by linarith [(abs_lt.mp (hwin z hz)).1] : ρ - ε ≤ contraction f s δ z))
  have hpowT := pow_pos hhi0 T
  refine ⟨D T, hDpos T, D 0 / (ρ + ε) ^ T, div_pos (hDpos 0) hpowT, fun t => ⟨?_, ?_⟩⟩
  · rcases le_total T t with hTt | htT
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hTt
      have h1 : (ρ - ε) ^ (T + n) ≤ (ρ - ε) ^ n := by
        rw [pow_add]
        exact mul_le_of_le_one_left (pow_nonneg hlo0 _) (pow_le_one₀ hlo0 hlo1)
      calc D T * (ρ - ε) ^ (T + n) ≤ D T * (ρ - ε) ^ n :=
            mul_le_mul_of_nonneg_left h1 (hDpos T).le
        _ = (ρ - ε) ^ n * D T := by ring
        _ ≤ D (T + n) := hloT n
    · have hmono : D T ≤ D t := hanti.antitone htT
      calc D T * (ρ - ε) ^ t ≤ D T * 1 :=
            mul_le_mul_of_nonneg_left (pow_le_one₀ hlo0 hlo1) (hDpos T).le
        _ ≤ D t := by rw [mul_one]; exact hmono
  · rcases le_total T t with hTt | htT
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hTt
      have hmono : D T ≤ D 0 := hanti.antitone (Nat.zero_le T)
      calc D (T + n) ≤ (ρ + ε) ^ n * D T := hupT n
        _ ≤ (ρ + ε) ^ n * D 0 := mul_le_mul_of_nonneg_left hmono (pow_nonneg hhi0.le _)
        _ = D 0 / (ρ + ε) ^ T * (ρ + ε) ^ (T + n) := by
            rw [pow_add]; field_simp
    · have hmono : D t ≤ D 0 := hanti.antitone (Nat.zero_le t)
      have hp : (ρ + ε) ^ T ≤ (ρ + ε) ^ t := pow_le_pow_of_le_one hhi0.le hρ1 htT
      calc D t ≤ D 0 := hmono
        _ = D 0 / (ρ + ε) ^ T * (ρ + ε) ^ T := by field_simp
        _ ≤ D 0 / (ρ + ε) ^ T * (ρ + ε) ^ t :=
            mul_le_mul_of_nonneg_left hp (div_pos (hDpos 0) hpowT).le

/-- The exact asymptotic rate in logarithms: `log (D t) / t → log ρ*`. -/
theorem log_gap_rate_tendsto (h : Technology f) {s δ γ : ℝ} (P : Params s δ γ)
    {k l : ℕ → ℝ} (hk : IsPath f s δ γ k) (hl : IsPath f s δ γ l) (h0 : k 0 < l 0) :
    Tendsto (fun t : ℕ => Real.log (Real.log (l t) - Real.log (k t)) / t) atTop
      (𝓝 (Real.log (contraction f s δ (steady h s δ γ)))) := by
  set ρ := contraction f s δ (steady h s δ γ)
  have hρ := contraction_pos h P (steady_spec h P).1
  have hρ1 := contraction_lt_one h P (steady_spec h P).1
  rw [Metric.tendsto_nhds]
  intro e he
  -- choose `ε` so that `log (ρ ± ε)` is within `e / 4` of `log ρ`
  obtain ⟨d, hd, hdb⟩ := Metric.continuousAt_iff.mp (Real.continuousAt_log (ne_of_gt hρ))
    (e / 4) (by linarith)
  set ε := min (d / 2) (min (ρ / 2) ((1 - ρ) / 2))
  have hε : 0 < ε := lt_min (half_pos hd) (lt_min (half_pos hρ) (by linarith))
  have hεd : ε < d := (min_le_left _ _).trans_lt (half_lt_self hd)
  have hερ : ε < ρ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self hρ)
  have hε1 : ρ + ε ≤ 1 := by
    have := (min_le_right (d / 2) _).trans (min_le_right (ρ / 2) ((1 - ρ) / 2)); linarith
  have hlogm : |Real.log (ρ - ε) - Real.log ρ| < e / 4 := by
    have := hdb (x := ρ - ε) (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
    rwa [Real.dist_eq] at this
  have hlogp : |Real.log (ρ + ε) - Real.log ρ| < e / 4 := by
    have := hdb (x := ρ + ε) (by rw [Real.dist_eq]; rw [abs_lt]; constructor <;> linarith)
    rwa [Real.dist_eq] at this
  obtain ⟨c, hc, C, hC, hb⟩ := sharp_convergence_rate h P hk hl h0 hε hερ hε1
  have hz : ∀ a : ℝ, Tendsto (fun t : ℕ => a / (t : ℝ)) atTop (𝓝 0) :=
    fun a => tendsto_const_div_atTop_nhds_zero_nat a
  filter_upwards [eventually_gt_atTop 0,
    (hz (Real.log c)).eventually (Metric.ball_mem_nhds 0 (by linarith : 0 < e / 4)),
    (hz (Real.log C)).eventually (Metric.ball_mem_nhds 0 (by linarith : 0 < e / 4))]
    with t ht hct hCt
  rw [Real.dist_eq, sub_zero] at hct hCt
  have htr : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  obtain ⟨hlo, hhi⟩ := hb t
  have hlpos : 0 < ρ - ε := by linarith
  have hlo' := Real.log_le_log (mul_pos hc (pow_pos hlpos t)) hlo
  have hhi' := Real.log_le_log ((mul_pos hc (pow_pos hlpos t)).trans_le hlo) hhi
  rw [Real.log_mul (ne_of_gt hc) (pow_pos hlpos t).ne', Real.log_pow] at hlo'
  rw [Real.log_mul (ne_of_gt hC) (pow_pos (by linarith) t).ne', Real.log_pow] at hhi'
  have h1 : Real.log c / t + Real.log (ρ - ε) ≤
      Real.log (Real.log (l t) - Real.log (k t)) / t := by
    rw [div_add' _ _ _ (ne_of_gt htr), div_le_div_iff_of_pos_right htr]; linarith
  have h2 : Real.log (Real.log (l t) - Real.log (k t)) / t ≤
      Real.log C / t + Real.log (ρ + ε) := by
    rw [div_add' _ _ _ (ne_of_gt htr), div_le_div_iff_of_pos_right htr]; linarith
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [(abs_lt.mp hct).1, (abs_lt.mp hlogm).1]
  · linarith [(abs_lt.mp hCt).2, (abs_lt.mp hlogp).2]

end Solow1956.DiscreteTime
