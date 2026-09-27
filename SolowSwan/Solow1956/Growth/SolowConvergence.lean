/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import Solow1956.Growth.GeneralSolowApplications
import Solow1956.Growth.GeneralSolowExamples
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Absolute convergence among identical Solow economies, and its speed

Two economies share the saving rate `s`, the effective dilution `m`, and the
intensive technology `f`, and differ only in their initial capital. We prove:

* `path_eq_of_meet`, `paths_ordered`: two paths that meet at some date coincide
  at every earlier date (backward uniqueness), so paths never cross; the
  poorer economy stays poorer.
* `poorer_grows_faster`: at every date the poorer economy's capital grows at a
  strictly higher proportional rate (the `β`-convergence sign).
* `log_gap_strictAnti`, `absolute_convergence`: the proportional gap
  `log l - log k` is strictly decreasing, and the level gap, log gap and ratio all
  converge (to `0`, `0`, `1`).
* `log_gap_le_of_speed_bound`, `exists_uniform_rate`, `absolute_convergence_rate`,
  `level_gap_le`: a global
  exponential rate. If `λ` bounds the local speed
  `σ(k) = s (f(k)/k - f'(k))` from below on the range of the two paths, the log
  gap is at most its initial value times `exp(-λ t)`. Such a `λ > 0` exists.
* `sharp_convergence_rate`: the exact asymptotic rate is
  `β* = σ(k*) = m - s f'(k*) = m (1 - capital share at k*)`; for every
  `ε`, the log gap lies between two exponentials with rates `β* ± ε`.
  `log_gap_rate_tendsto` states it as `log (gap t) / t → -β*`.
* `cobbDouglas_speed`: with `f(k) = k^α`, `β* = (1 - α) m`.

Since the constant path at `k*` is itself an admissible path, every result also
gives the rate of convergence of a single economy to its steady state
(`log_gap_steady_le`).

The level gap `l - k` need not be monotone, because `s f(k) - m k` is increasing
at low capital; the monotone quantity is the proportional (log) gap.
-/

open Set Filter Topology

namespace Solow1956.Neoclassical

variable {f : ℝ → ℝ}

/-- An admissible classical future path of `k' = s f(k) - m k` from positive capital. -/
structure IsPath (f : ℝ → ℝ) (s m : ℝ) (k : ℝ → ℝ) : Prop where
  initial_pos : 0 < k 0
  nonneg : ∀ t, 0 ≤ t → 0 ≤ k t
  hasDerivAt : ∀ t, 0 ≤ t → HasDerivAt k (rate f s m (k t)) t

/-- Proportional growth rate `k'/k = s f(k)/k - m` of capital at the stock `k`. -/
noncomputable def growthRate (f : ℝ → ℝ) (s m k : ℝ) : ℝ := s * (f k / k) - m

/-- Local speed of convergence `σ(k) = s (f(k)/k - f'(k))`: minus the slope of the
growth rate with respect to `log k`. -/
noncomputable def convergenceSpeed (f : ℝ → ℝ) (s k : ℝ) : ℝ := s * (f k / k - deriv f k)

theorem rate_div_eq_growthRate (s m : ℝ) {k : ℝ} (hk : 0 < k) :
    rate f s m k / k = growthRate f s m k := by
  unfold rate growthRate
  field_simp

theorem growthRate_strictAnti (h : Technology f) {s : ℝ} (hs : 0 < s) (m : ℝ) :
    StrictAntiOn (growthRate f s m) (Ioi 0) := by
  intro a ha b hb hab
  have := mul_lt_mul_of_pos_left (h.average_strictAnti ha hb hab) hs
  unfold growthRate
  linarith

theorem convergenceSpeed_pos (h : Technology f) {s k : ℝ} (hs : 0 < s) (hk : 0 < k) :
    0 < convergenceSpeed f s k := by
  have hg := h.output_gap hk
  have : deriv f k < f k / k := (lt_div_iff₀ hk).mpr hg
  exact mul_pos hs (sub_pos.mpr this)

theorem convergenceSpeed_continuousOn (h : Technology f) (s : ℝ) :
    ContinuousOn (convergenceSpeed f s) (Ioi 0) := by
  have hf : ContinuousOn f (Ioi 0) := fun k hk =>
    (h.differentiable k hk).continuousAt.continuousWithinAt
  exact continuousOn_const.mul
    ((hf.div continuousOn_id (fun k hk => ne_of_gt hk)).sub h.derivative_continuous)

/-- The asymptotic speed is `m - s f'(k*)`. -/
theorem convergenceSpeed_steady (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    convergenceSpeed f s (steadyCapital h s m) = m - s * deriv f (steadyCapital h s m) := by
  obtain ⟨hk, he⟩ := steadyCapital_spec h hs hm
  set ks := steadyCapital h s m
  have hfk : s * (f ks / ks) = m := by
    unfold rate at he
    field_simp
    linarith
  unfold convergenceSpeed
  rw [mul_sub, hfk]

/-- The asymptotic speed is dilution times the labour share at the steady state. -/
theorem convergenceSpeed_steady_share (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    convergenceSpeed f s (steadyCapital h s m) =
      m * (1 - deriv f (steadyCapital h s m) * steadyCapital h s m /
        f (steadyCapital h s m)) := by
  obtain ⟨hk, he⟩ := steadyCapital_spec h hs hm
  set ks := steadyCapital h s m
  have hy := h.output_pos hk
  have hfk : s * f ks = m * ks := by unfold rate at he; linarith
  unfold convergenceSpeed
  field_simp
  linear_combination (f ks - deriv f ks * ks) * hfk

theorem IsPath.pos (h : Technology f) {s m : ℝ} (hs : 0 ≤ s) {k : ℝ → ℝ}
    (hk : IsPath f s m k) {t : ℝ} (ht : 0 ≤ t) : 0 < k t :=
  capital_positive h hs hk.initial_pos hk.nonneg hk.hasDerivAt ht

/-- The constant path at the steady state is admissible. -/
theorem isPath_steady (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m) :
    IsPath f s m (fun _ => steadyCapital h s m) := by
  obtain ⟨hk, he⟩ := steadyCapital_spec h hs hm
  exact ⟨hk, fun _ _ => hk.le, fun t _ => by rw [he]; exact hasDerivAt_const t _⟩

/-- Every admissible path stays between its initial stock and the steady state. -/
theorem IsPath.bounds (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k : ℝ → ℝ} (hk : IsPath f s m k) {t : ℝ} (ht : 0 ≤ t) :
    min (k 0) (steadyCapital h s m) ≤ k t ∧ k t ≤ max (k 0) (steadyCapital h s m) := by
  obtain ⟨ks, hks, he, _, l, hl0, hl, _, _, _, hb, _, _⟩ :=
    general_solow h hs hm hk.initial_pos
  have heq := path_unique h hs.le hk.initial_pos hl0.symm hk.nonneg
    (fun t ht => (hl t ht).1.le) hk.hasDerivAt (fun t ht => (hl t ht).2)
  rw [steadyCapital_eq h hs hm hks he, heq ht]
  exact hb t ht

theorem IsPath.tendsto (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k : ℝ → ℝ} (hk : IsPath f s m k) :
    Tendsto k atTop (𝓝 (steadyCapital h s m)) :=
  every_path_converges h hs hm hk.initial_pos hk.nonneg hk.hasDerivAt

/-- Backward uniqueness: two paths that meet at a date agree at every earlier date. -/
theorem path_eq_of_meet (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l)
    {T : ℝ} (hT : 0 ≤ T) (hmeet : k T = l T) : EqOn k l (Icc 0 T) := by
  have hkp : ∀ t, 0 ≤ t → 0 < k t := fun t ht => hk.pos h hs ht
  have hlp : ∀ t, 0 ≤ t → 0 < l t := fun t ht => hl.pos h hs ht
  have hkc : ContinuousOn k (Icc 0 T) :=
    HasDerivAt.continuousOn (fun t ht => hk.hasDerivAt t ht.1)
  have hlc : ContinuousOn l (Icc 0 T) :=
    HasDerivAt.continuousOn (fun t ht => hl.hasDerivAt t ht.1)
  obtain ⟨ta, hta, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT) (hkc.inf hlc)
  obtain ⟨tb, htb, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) (hkc.sup hlc)
  let a := min (k ta) (l ta)
  let b := max (k tb) (l tb)
  have ha : 0 < a := lt_min (hkp ta hta.1) (hlp ta hta.1)
  have hkm : ∀ t ∈ Icc 0 T, k t ∈ Icc a b := fun t ht =>
    ⟨(hmin ht).trans (min_le_left _ _), (le_max_left _ _).trans (hmax ht)⟩
  have hlm : ∀ t ∈ Icc 0 T, l t ∈ Icc a b := fun t ht =>
    ⟨(hmin ht).trans (min_le_right _ _), (le_max_right _ _).trans (hmax ht)⟩
  have hab : a ≤ b := (hkm 0 ⟨le_rfl, hT⟩).1.trans (hkm 0 ⟨le_rfl, hT⟩).2
  have hdc : ContinuousOn (deriv (rate f s m)) (Icc a b) :=
    (rate_derivative_continuous h s m).mono (fun _ hx => ha.trans_le hx.1)
  obtain ⟨z, hz, hzmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab) hdc.norm
  have hLip : LipschitzOnWith ‖deriv (rate f s m) z‖₊ (rate f s m) (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le
      (fun k hk => (rate_hasDerivAt h s m (ha.trans_le hk.1)).differentiableAt)
      (fun k hk => hzmax hk)
  exact ODE_solution_unique_of_mem_Icc_left
    (v := fun _ => rate f s m) (s := fun _ => Icc a b)
    (fun _ _ => hLip) hkc (fun t ht => (hk.hasDerivAt t ht.1.le).hasDerivWithinAt)
    (fun t ht => hkm t (Ioc_subset_Icc_self ht))
    hlc (fun t ht => (hl.hasDerivAt t ht.1.le).hasDerivWithinAt)
    (fun t ht => hlm t (Ioc_subset_Icc_self ht)) hmeet

/-- Paths of identical economies never cross: the initially poorer economy is
strictly poorer at every future date. -/
theorem paths_ordered (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {t : ℝ} (ht : 0 ≤ t) : k t < l t := by
  by_contra hle
  push Not at hle
  have hc : ContinuousOn (fun u => l u - k u) (Icc 0 t) :=
    (HasDerivAt.continuousOn (fun u hu => hl.hasDerivAt u hu.1)).sub
      (HasDerivAt.continuousOn (fun u hu => hk.hasDerivAt u hu.1))
  obtain ⟨τ, hτ, hτeq⟩ := intermediate_value_Icc' ht hc
    ⟨sub_nonpos.mpr hle, (sub_pos.mpr h0).le⟩
  have hmeet : k τ = l τ := by simp only at hτeq; linarith
  have := path_eq_of_meet h hs hk hl hτ.1 hmeet ⟨le_rfl, hτ.1⟩
  exact (ne_of_lt h0) this

/-- `β`-convergence sign: the poorer economy grows strictly faster at every date. -/
theorem poorer_grows_faster (h : Technology f) {s m : ℝ} (hs : 0 < s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {t : ℝ} (ht : 0 ≤ t) : growthRate f s m (l t) < growthRate f s m (k t) :=
  growthRate_strictAnti h hs m (hk.pos h hs.le ht) (hl.pos h hs.le ht)
    (paths_ordered h hs.le hk hl h0 ht)

theorem hasDerivAt_log_gap (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun u => Real.log (l u) - Real.log (k u))
      (growthRate f s m (l t) - growthRate f s m (k t)) t := by
  have hkt := hk.pos h hs ht
  have hlt := hl.pos h hs ht
  have := ((hl.hasDerivAt t ht).log (ne_of_gt hlt)).sub
    ((hk.hasDerivAt t ht).log (ne_of_gt hkt))
  rwa [rate_div_eq_growthRate s m hlt, rate_div_eq_growthRate s m hkt] at this

/-- The proportional gap between the two economies shrinks strictly. -/
theorem log_gap_strictAnti (h : Technology f) {s m : ℝ} (hs : 0 < s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0) :
    StrictAntiOn (fun u => Real.log (l u) - Real.log (k u)) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
    (HasDerivAt.continuousOn (fun u hu => hasDerivAt_log_gap h hs.le hk hl hu))
  intro t ht
  have ht' : 0 ≤ t := (by simpa only [interior_Ici, mem_Ioi] using ht : 0 < t).le
  rw [(hasDerivAt_log_gap h hs.le hk hl ht').deriv]
  exact sub_neg.mpr (poorer_grows_faster h hs hk hl h0 ht')

/-- Absolute convergence: identical economies converge to each other in levels,
in logs, and in ratio, whatever their initial capital. -/
theorem absolute_convergence (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) :
    Tendsto (fun t => l t - k t) atTop (𝓝 0) ∧
      Tendsto (fun t => Real.log (l t) - Real.log (k t)) atTop (𝓝 0) ∧
      Tendsto (fun t => l t / k t) atTop (𝓝 1) := by
  have hks := (steadyCapital_spec h hs hm).1
  have hkl := hk.tendsto h hs hm
  have hll := hl.tendsto h hs hm
  refine ⟨by simpa only [sub_self] using hll.sub hkl, ?_, ?_⟩
  · have hlog := (Real.continuousAt_log (ne_of_gt hks)).tendsto
    have := (hlog.comp hll).sub (hlog.comp hkl)
    rw [sub_self] at this
    exact this
  · have := hll.div hkl (ne_of_gt hks)
    rw [div_self (ne_of_gt hks)] at this
    exact this

/-- A lower bound `λ` on the local speed turns into a lower bound on how fast the
growth-rate gap closes, measured against the log gap. -/
theorem growthRate_gap_ge {s m a b lam : ℝ} (h : Technology f) (ha : 0 < a)
    (hlam : ∀ z ∈ Icc a b, lam ≤ convergenceSpeed f s z)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    lam * (Real.log y - Real.log x) ≤ growthRate f s m x - growthRate f s m y := by
  have hd : ∀ z, 0 < z → HasDerivAt (fun z => growthRate f s m z + lam * Real.log z)
      ((lam - convergenceSpeed f s z) / z) z := by
    intro z hz
    have h1 : HasDerivAt (fun z => s * (f z / z) - m)
        (s * ((deriv f z * z - f z * 1) / z ^ 2)) z :=
      (((h.differentiable z hz).hasDerivAt.div (hasDerivAt_id' z)
        (ne_of_gt hz)).const_mul s).sub_const m
    have h2 := (Real.hasDerivAt_log (ne_of_gt hz)).const_mul lam
    exact (h1.add h2).congr_deriv (by unfold convergenceSpeed; field_simp; ring)
  have hanti : AntitoneOn (fun z => growthRate f s m z + lam * Real.log z) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (HasDerivAt.continuousOn (fun z hz => hd z (ha.trans_le hz.1)))
      (fun z hz => (hd z (ha.trans_le
        (interior_subset hz : z ∈ Icc a b).1)).differentiableAt.differentiableWithinAt)
    intro z hz
    have hz' : z ∈ Icc a b := interior_subset hz
    rw [(hd z (ha.trans_le hz'.1)).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hlam z hz'))
      (ha.trans_le hz'.1).le
  have := hanti hx hy hxy
  simp only at this
  linarith

/-- An upper bound `μ` on the local speed bounds how fast the growth-rate gap closes. -/
theorem growthRate_gap_le {s m a b mu : ℝ} (h : Technology f) (ha : 0 < a)
    (hmu : ∀ z ∈ Icc a b, convergenceSpeed f s z ≤ mu)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    growthRate f s m x - growthRate f s m y ≤ mu * (Real.log y - Real.log x) := by
  have hd : ∀ z, 0 < z → HasDerivAt (fun z => growthRate f s m z + mu * Real.log z)
      ((mu - convergenceSpeed f s z) / z) z := by
    intro z hz
    have h1 : HasDerivAt (fun z => s * (f z / z) - m)
        (s * ((deriv f z * z - f z * 1) / z ^ 2)) z :=
      (((h.differentiable z hz).hasDerivAt.div (hasDerivAt_id' z)
        (ne_of_gt hz)).const_mul s).sub_const m
    have h2 := (Real.hasDerivAt_log (ne_of_gt hz)).const_mul mu
    exact (h1.add h2).congr_deriv (by unfold convergenceSpeed; field_simp; ring)
  have hmono : MonotoneOn (fun z => growthRate f s m z + mu * Real.log z) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (HasDerivAt.continuousOn (fun z hz => hd z (ha.trans_le hz.1)))
      (fun z hz => (hd z (ha.trans_le
        (interior_subset hz : z ∈ Icc a b).1)).differentiableAt.differentiableWithinAt)
    intro z hz
    have hz' : z ∈ Icc a b := interior_subset hz
    rw [(hd z (ha.trans_le hz'.1)).deriv]
    exact div_nonneg (sub_nonneg.mpr (hmu z hz')) (ha.trans_le hz'.1).le
  have := hmono hx hy hxy
  simp only at this
  linarith

/-- Gronwall bound from above: from any date `T` after which both ordered paths stay
in `[a, b]`, a lower bound `λ` for the local speed on `[a, b]` makes the log gap
decay at least at rate `λ`. -/
theorem log_gap_upper (h : Technology f) {s m : ℝ} (hs : 0 < s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {a b lam T : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    (hkw : ∀ t, T ≤ t → k t ∈ Icc a b) (hlw : ∀ t, T ≤ t → l t ∈ Icc a b)
    (hlam : ∀ z ∈ Icc a b, lam ≤ convergenceSpeed f s z) {t : ℝ} (ht : T ≤ t) :
    Real.log (l t) - Real.log (k t) ≤
      (Real.log (l T) - Real.log (k T)) * Real.exp (-lam * (t - T)) := by
  set D : ℝ → ℝ := fun u => Real.log (l u) - Real.log (k u) with hD
  have hint : ∀ u, u ∈ interior (Ici T) → T ≤ u := fun u hu =>
    (by simpa only [interior_Ici, mem_Ioi] using hu : T < u).le
  have hex : ∀ u, HasDerivAt (fun u => Real.exp (lam * (u - T)))
      (Real.exp (lam * (u - T)) * lam) u := by
    intro u
    have := ((hasDerivAt_id u).sub_const T).const_mul lam
    simpa only [id, mul_one] using this.exp
  have hE : ∀ u, T ≤ u → HasDerivAt (fun u => D u * Real.exp (lam * (u - T)))
      ((growthRate f s m (l u) - growthRate f s m (k u)) * Real.exp (lam * (u - T)) +
        D u * (Real.exp (lam * (u - T)) * lam)) u :=
    fun u hu => (hasDerivAt_log_gap h hs.le hk hl (hT.trans hu)).mul (hex u)
  have hanti : AntitoneOn (fun u => D u * Real.exp (lam * (u - T))) (Ici T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici T)
      (HasDerivAt.continuousOn (fun u hu => hE u hu))
      (fun u hu => (hE u (hint u hu)).differentiableAt.differentiableWithinAt)
    intro u hu
    have hu' := hint u hu
    rw [(hE u hu').deriv]
    have hg := growthRate_gap_ge (m := m) h ha hlam (hkw u hu') (hlw u hu')
      (paths_ordered h hs.le hk hl h0 (hT.trans hu')).le
    have hpos := Real.exp_pos (lam * (u - T))
    have : (growthRate f s m (l u) - growthRate f s m (k u)) + D u * lam ≤ 0 := by
      simp only [hD]; linarith
    nlinarith
  have := hanti (mem_Ici.mpr le_rfl) (show t ∈ Ici T from ht) ht
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at this
  have he : Real.exp (lam * (t - T)) * Real.exp (-lam * (t - T)) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc D t = D t * Real.exp (lam * (t - T)) * Real.exp (-lam * (t - T)) := by
        rw [mul_assoc, he, mul_one]
    _ ≤ D T * Real.exp (-lam * (t - T)) :=
        mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

/-- Gronwall bound from below: an upper bound `μ` for the local speed on `[a, b]`
means the log gap decays no faster than rate `μ`. -/
theorem log_gap_lower (h : Technology f) {s m : ℝ} (hs : 0 < s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {a b mu T : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    (hkw : ∀ t, T ≤ t → k t ∈ Icc a b) (hlw : ∀ t, T ≤ t → l t ∈ Icc a b)
    (hmu : ∀ z ∈ Icc a b, convergenceSpeed f s z ≤ mu) {t : ℝ} (ht : T ≤ t) :
    (Real.log (l T) - Real.log (k T)) * Real.exp (-mu * (t - T)) ≤
      Real.log (l t) - Real.log (k t) := by
  set D : ℝ → ℝ := fun u => Real.log (l u) - Real.log (k u) with hD
  have hint : ∀ u, u ∈ interior (Ici T) → T ≤ u := fun u hu =>
    (by simpa only [interior_Ici, mem_Ioi] using hu : T < u).le
  have hex : ∀ u, HasDerivAt (fun u => Real.exp (mu * (u - T)))
      (Real.exp (mu * (u - T)) * mu) u := by
    intro u
    have := ((hasDerivAt_id u).sub_const T).const_mul mu
    simpa only [id, mul_one] using this.exp
  have hE : ∀ u, T ≤ u → HasDerivAt (fun u => D u * Real.exp (mu * (u - T)))
      ((growthRate f s m (l u) - growthRate f s m (k u)) * Real.exp (mu * (u - T)) +
        D u * (Real.exp (mu * (u - T)) * mu)) u :=
    fun u hu => (hasDerivAt_log_gap h hs.le hk hl (hT.trans hu)).mul (hex u)
  have hmono : MonotoneOn (fun u => D u * Real.exp (mu * (u - T))) (Ici T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici T)
      (HasDerivAt.continuousOn (fun u hu => hE u hu))
      (fun u hu => (hE u (hint u hu)).differentiableAt.differentiableWithinAt)
    intro u hu
    have hu' := hint u hu
    rw [(hE u hu').deriv]
    have hg := growthRate_gap_le (m := m) h ha hmu (hkw u hu') (hlw u hu')
      (paths_ordered h hs.le hk hl h0 (hT.trans hu')).le
    have hpos := Real.exp_pos (mu * (u - T))
    have : 0 ≤ (growthRate f s m (l u) - growthRate f s m (k u)) + D u * mu := by
      simp only [hD]; linarith
    nlinarith
  have := hmono (mem_Ici.mpr le_rfl) (show t ∈ Ici T from ht) ht
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at this
  have he : Real.exp (-mu * (t - T)) * Real.exp (mu * (t - T)) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc D T * Real.exp (-mu * (t - T))
      ≤ D t * Real.exp (mu * (t - T)) * Real.exp (-mu * (t - T)) :=
        mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    _ = D t := by rw [mul_assoc, mul_comm (Real.exp _), he, mul_one]

/-- Both ordered paths lie, at every date, between the lower initial stock (or the
steady state) and the higher initial stock (or the steady state). -/
theorem paths_window (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {t : ℝ} (ht : 0 ≤ t) :
    k t ∈ Icc (min (k 0) (steadyCapital h s m)) (max (l 0) (steadyCapital h s m)) ∧
      l t ∈ Icc (min (k 0) (steadyCapital h s m)) (max (l 0) (steadyCapital h s m)) := by
  obtain ⟨hk1, hk2⟩ := hk.bounds h hs hm ht
  obtain ⟨hl1, hl2⟩ := hl.bounds h hs hm ht
  have h1 : min (k 0) (steadyCapital h s m) ≤ min (l 0) (steadyCapital h s m) :=
    min_le_min_right _ h0.le
  have h2 : max (k 0) (steadyCapital h s m) ≤ max (l 0) (steadyCapital h s m) :=
    max_le_max_right _ h0.le
  exact ⟨⟨hk1, hk2.trans h2⟩, ⟨h1.trans hl1, hl2⟩⟩

/-- Global exponential convergence at an explicit rate: any lower bound `λ` for the
local speed over the range of the two paths is a rate for the log gap. -/
theorem log_gap_le_of_speed_bound (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0) {lam : ℝ}
    (hlam : ∀ z ∈ Icc (min (k 0) (steadyCapital h s m)) (max (l 0) (steadyCapital h s m)),
      lam ≤ convergenceSpeed f s z)
    {t : ℝ} (ht : 0 ≤ t) :
    Real.log (l t) - Real.log (k t) ≤
      (Real.log (l 0) - Real.log (k 0)) * Real.exp (-lam * t) := by
  have ha : 0 < min (k 0) (steadyCapital h s m) :=
    lt_min hk.initial_pos (steadyCapital_spec h hs hm).1
  simpa only [sub_zero] using log_gap_upper h hs hk hl h0 ha le_rfl
    (fun u hu => (paths_window h hs hm hk hl h0 hu).1)
    (fun u hu => (paths_window h hs hm hk hl h0 hu).2) hlam ht

/-- The log gap of ordered paths is strictly positive. -/
theorem log_gap_pos (h : Technology f) {s m : ℝ} (hs : 0 ≤ s)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {t : ℝ} (ht : 0 ≤ t) : 0 < Real.log (l t) - Real.log (k t) :=
  sub_pos.mpr (Real.log_lt_log (hk.pos h hs ht) (paths_ordered h hs hk hl h0 ht))

/-- A uniform exponential rate exists: some `λ > 0` bounds the local speed over the
whole range of the two paths. -/
theorem exists_uniform_rate (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0) :
    ∃ lam, 0 < lam ∧ ∀ t, 0 ≤ t →
      Real.log (l t) - Real.log (k t) ≤
        (Real.log (l 0) - Real.log (k 0)) * Real.exp (-lam * t) := by
  set a := min (k 0) (steadyCapital h s m)
  set b := max (l 0) (steadyCapital h s m)
  have ha : 0 < a := lt_min hk.initial_pos (steadyCapital_spec h hs hm).1
  have hab : a ≤ b := (min_le_right _ _).trans (le_max_right _ _)
  obtain ⟨z, hz, hzmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
    ((convergenceSpeed_continuousOn h s).mono (fun _ hx => ha.trans_le hx.1))
  exact ⟨convergenceSpeed f s z, convergenceSpeed_pos h hs (ha.trans_le hz.1),
    fun t ht => log_gap_le_of_speed_bound h hs hm hk hl h0 (fun y hy => hzmin hy) ht⟩

/-- Absolute convergence at an exponential rate for any two identical economies,
stated symmetrically in absolute value. -/
theorem absolute_convergence_rate (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) :
    ∃ lam, 0 < lam ∧ ∀ t, 0 ≤ t →
      |Real.log (l t) - Real.log (k t)| ≤
        |Real.log (l 0) - Real.log (k 0)| * Real.exp (-lam * t) := by
  rcases lt_trichotomy (k 0) (l 0) with h0 | h0 | h0
  · obtain ⟨lam, hlam, hb⟩ := exists_uniform_rate h hs hm hk hl h0
    refine ⟨lam, hlam, fun t ht => ?_⟩
    rw [abs_of_pos (log_gap_pos h hs.le hk hl h0 ht),
      abs_of_pos (log_gap_pos h hs.le hk hl h0 le_rfl)]
    exact hb t ht
  · refine ⟨1, one_pos, fun t ht => ?_⟩
    have he := path_unique h hs.le hk.initial_pos h0 hk.nonneg hl.nonneg
      hk.hasDerivAt hl.hasDerivAt (mem_Ici.mpr ht)
    rw [he, h0, sub_self, sub_self, abs_zero, zero_mul]
  · obtain ⟨lam, hlam, hb⟩ := exists_uniform_rate h hs hm hl hk h0
    refine ⟨lam, hlam, fun t ht => ?_⟩
    rw [abs_sub_comm, abs_sub_comm (Real.log (l 0)),
      abs_of_pos (log_gap_pos h hs.le hl hk h0 ht),
      abs_of_pos (log_gap_pos h hs.le hl hk h0 le_rfl)]
    exact hb t ht

/-- A single economy converges to its steady state at an exponential rate: the
constant steady-state path is an admissible comparison economy. -/
theorem log_gap_steady_le (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k : ℝ → ℝ} (hk : IsPath f s m k) :
    ∃ lam, 0 < lam ∧ ∀ t, 0 ≤ t →
      |Real.log (k t) - Real.log (steadyCapital h s m)| ≤
        |Real.log (k 0) - Real.log (steadyCapital h s m)| * Real.exp (-lam * t) := by
  obtain ⟨lam, hlam, hb⟩ :=
    absolute_convergence_rate h hs hm (isPath_steady h hs hm) hk
  exact ⟨lam, hlam, hb⟩

/-- The level gap is bounded by the richer stock times the log gap, so it also
closes exponentially: `l t - k t ≤ max (l 0) k* · log (l 0 / k 0) · exp (-λ t)`. -/
theorem level_gap_le (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0) :
    ∃ lam, 0 < lam ∧ ∀ t, 0 ≤ t →
      0 < l t - k t ∧
      l t - k t ≤ max (l 0) (steadyCapital h s m) *
        (Real.log (l 0) - Real.log (k 0)) * Real.exp (-lam * t) := by
  obtain ⟨lam, hlam, hb⟩ := exists_uniform_rate h hs hm hk hl h0
  refine ⟨lam, hlam, fun t ht => ⟨sub_pos.mpr (paths_ordered h hs.le hk hl h0 ht), ?_⟩⟩
  have hkt := hk.pos h hs.le ht
  have hlt := hl.pos h hs.le ht
  have hlog : l t - k t ≤ l t * (Real.log (l t) - Real.log (k t)) := by
    have he := Real.add_one_le_exp (Real.log (k t) - Real.log (l t))
    rw [Real.exp_sub, Real.exp_log hkt, Real.exp_log hlt, le_div_iff₀ hlt] at he
    nlinarith
  have hD := log_gap_pos h hs.le hk hl h0 ht
  have hup := (paths_window h hs hm hk hl h0 ht).2.2
  calc l t - k t ≤ l t * (Real.log (l t) - Real.log (k t)) := hlog
    _ ≤ max (l 0) (steadyCapital h s m) * (Real.log (l t) - Real.log (k t)) :=
        mul_le_mul_of_nonneg_right hup hD.le
    _ ≤ max (l 0) (steadyCapital h s m) *
          ((Real.log (l 0) - Real.log (k 0)) * Real.exp (-lam * t)) :=
        mul_le_mul_of_nonneg_left (hb t ht) (hlt.le.trans hup)
    _ = _ := by ring

/-- Sharp rate. Let `β* = σ(k*) = m - s f'(k*)`. For every `0 < ε < β*` the log gap
between two identical economies is squeezed between exponentials with rates
`β* + ε` and `β* - ε`. -/
theorem sharp_convergence_rate (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0)
    {ε : ℝ} (hε : 0 < ε) (hεβ : ε < convergenceSpeed f s (steadyCapital h s m)) :
    ∃ c, 0 < c ∧ ∃ C, 0 < C ∧ ∀ t, 0 ≤ t →
      c * Real.exp (-(convergenceSpeed f s (steadyCapital h s m) + ε) * t) ≤
          Real.log (l t) - Real.log (k t) ∧
        Real.log (l t) - Real.log (k t) ≤
          C * Real.exp (-(convergenceSpeed f s (steadyCapital h s m) - ε) * t) := by
  set ks := steadyCapital h s m with hks_def
  set β := convergenceSpeed f s ks
  set D : ℝ → ℝ := fun u => Real.log (l u) - Real.log (k u) with hD
  have hks := (steadyCapital_spec h hs hm).1
  -- a window around `k*` on which the local speed is within `ε` of `β`
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.mp
    ((convergenceSpeed_continuousOn h s).continuousAt (Ioi_mem_nhds hks)) ε hε
  set r := min (δ / 2) (ks / 2)
  have hr : 0 < r := lt_min (half_pos hδ) (half_pos hks)
  have ha : 0 < ks - r := by have := min_le_right (δ / 2) (ks / 2); linarith
  have hwin : ∀ z ∈ Icc (ks - r) (ks + r), |convergenceSpeed f s z - β| < ε := by
    intro z hz
    have : dist z ks < δ := by
      rw [Real.dist_eq, abs_lt]
      have := min_le_left (δ / 2) (ks / 2)
      constructor <;> linarith [hz.1, hz.2]
    have := hδb this
    rwa [Real.dist_eq] at this
  have hlam : ∀ z ∈ Icc (ks - r) (ks + r), β - ε ≤ convergenceSpeed f s z :=
    fun z hz => by linarith [(abs_lt.mp (hwin z hz)).1]
  have hmu : ∀ z ∈ Icc (ks - r) (ks + r), convergenceSpeed f s z ≤ β + ε :=
    fun z hz => by linarith [(abs_lt.mp (hwin z hz)).2]
  have hnhds : Icc (ks - r) (ks + r) ∈ 𝓝 ks := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨T0, hT0⟩ := eventually_atTop.mp
    (((hk.tendsto h hs hm).eventually hnhds).and ((hl.tendsto h hs hm).eventually hnhds))
  set T := max T0 0
  have hT : 0 ≤ T := le_max_right _ _
  have hkw : ∀ t, T ≤ t → k t ∈ Icc (ks - r) (ks + r) :=
    fun t ht => (hT0 t ((le_max_left _ _).trans ht)).1
  have hlw : ∀ t, T ≤ t → l t ∈ Icc (ks - r) (ks + r) :=
    fun t ht => (hT0 t ((le_max_left _ _).trans ht)).2
  have hanti := log_gap_strictAnti h hs hk hl h0
  have hDpos : ∀ t, 0 ≤ t → 0 < D t := fun t ht => log_gap_pos h hs.le hk hl h0 ht
  have hlamp : 0 < β - ε := sub_pos.mpr hεβ
  have hmup : 0 < β + ε := by linarith
  refine ⟨D T, hDpos T hT, D 0 * Real.exp ((β - ε) * T),
    mul_pos (hDpos 0 le_rfl) (Real.exp_pos _), fun t ht => ⟨?_, ?_⟩⟩
  · rcases le_total T t with hTt | htT
    · have hlow := log_gap_lower h hs hk hl h0 ha hT hkw hlw hmu hTt
      have : Real.exp (-(β + ε) * t) ≤ Real.exp (-(β + ε) * (t - T)) :=
        Real.exp_le_exp.mpr (by nlinarith)
      calc D T * Real.exp (-(β + ε) * t) ≤ D T * Real.exp (-(β + ε) * (t - T)) :=
            mul_le_mul_of_nonneg_left this (hDpos T hT).le
        _ ≤ D t := by simpa only [neg_mul] using hlow
    · have hmono : D T ≤ D t := hanti.antitoneOn (mem_Ici.mpr ht) (mem_Ici.mpr hT) htT
      have : Real.exp (-(β + ε) * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      calc D T * Real.exp (-(β + ε) * t) ≤ D T * 1 :=
            mul_le_mul_of_nonneg_left this (hDpos T hT).le
        _ ≤ D t := by rw [mul_one]; exact hmono
  · have hsplit : Real.exp ((β - ε) * T) * Real.exp (-(β - ε) * t) =
        Real.exp (-(β - ε) * (t - T)) := by rw [← Real.exp_add]; ring_nf
    rcases le_total T t with hTt | htT
    · have hup := log_gap_upper h hs hk hl h0 ha hT hkw hlw hlam hTt
      have hmono : D T ≤ D 0 := hanti.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hT) hT
      calc D t ≤ D T * Real.exp (-(β - ε) * (t - T)) := hup
        _ ≤ D 0 * Real.exp (-(β - ε) * (t - T)) :=
            mul_le_mul_of_nonneg_right hmono (Real.exp_pos _).le
        _ = D 0 * Real.exp ((β - ε) * T) * Real.exp (-(β - ε) * t) := by
            rw [mul_assoc, hsplit]
    · have hmono : D t ≤ D 0 := hanti.antitoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
      have : 1 ≤ Real.exp (-(β - ε) * (t - T)) := Real.one_le_exp (by nlinarith)
      calc D t ≤ D 0 * 1 := by rw [mul_one]; exact hmono
        _ ≤ D 0 * Real.exp (-(β - ε) * (t - T)) :=
            mul_le_mul_of_nonneg_left this (hDpos 0 le_rfl).le
        _ = D 0 * Real.exp ((β - ε) * T) * Real.exp (-(β - ε) * t) := by
            rw [mul_assoc, hsplit]

/-- The exact asymptotic rate of convergence: `log (log-gap) / t → -β*`, where
`β* = σ(k*) = m - s f'(k*)`. -/
theorem log_gap_rate_tendsto (h : Technology f) {s m : ℝ} (hs : 0 < s) (hm : 0 < m)
    {k l : ℝ → ℝ} (hk : IsPath f s m k) (hl : IsPath f s m l) (h0 : k 0 < l 0) :
    Tendsto (fun t => Real.log (Real.log (l t) - Real.log (k t)) / t) atTop
      (𝓝 (-convergenceSpeed f s (steadyCapital h s m))) := by
  set β := convergenceSpeed f s (steadyCapital h s m)
  have hβ : 0 < β := convergenceSpeed_pos h hs (steadyCapital_spec h hs hm).1
  rw [Metric.tendsto_nhds]
  intro e he
  set ε := min (e / 4) (β / 2)
  have hε : 0 < ε := lt_min (by linarith) (half_pos hβ)
  have hεβ : ε < β := (min_le_right _ _).trans_lt (half_lt_self hβ)
  have hεe : ε ≤ e / 4 := min_le_left _ _
  obtain ⟨c, hc, C, hC, hb⟩ := sharp_convergence_rate h hs hm hk hl h0 hε hεβ
  have hz : ∀ a : ℝ, Tendsto (fun t : ℝ => a / t) atTop (𝓝 0) :=
    fun a => tendsto_const_nhds.div_atTop tendsto_id
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (hz (Real.log c)).eventually (Metric.ball_mem_nhds 0 (by linarith : 0 < e / 2)),
    (hz (Real.log C)).eventually (Metric.ball_mem_nhds 0 (by linarith : 0 < e / 2))]
    with t ht hct hCt
  rw [Real.dist_eq, sub_zero] at hct hCt
  obtain ⟨hlo, hhi⟩ := hb t ht.le
  have hlo' := Real.log_le_log (mul_pos hc (Real.exp_pos _)) hlo
  have hhi' := Real.log_le_log ((mul_pos hc (Real.exp_pos _)).trans_le hlo) hhi
  rw [Real.log_mul (ne_of_gt hc) (Real.exp_pos _).ne', Real.log_exp] at hlo'
  rw [Real.log_mul (ne_of_gt hC) (Real.exp_pos _).ne', Real.log_exp] at hhi'
  have h1 : Real.log c / t - (β + ε) ≤
      Real.log (Real.log (l t) - Real.log (k t)) / t := by
    rw [div_sub' (ne_of_gt ht), div_le_div_iff_of_pos_right ht]; linarith
  have h2 : Real.log (Real.log (l t) - Real.log (k t)) / t ≤
      Real.log C / t - (β - ε) := by
    rw [div_sub' (ne_of_gt ht), div_le_div_iff_of_pos_right ht]; linarith
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [(abs_lt.mp hct).1]
  · linarith [(abs_lt.mp hCt).2]

/-- Cobb–Douglas: with `f(k) = k^α` the asymptotic rate is `β* = (1 - α) m`. -/
theorem cobbDouglas_speed {α s m : ℝ} (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s) (hm : 0 < m) :
    convergenceSpeed (fun k : ℝ => k ^ α) s
      (steadyCapital (technology_rpow hα hα1) s m) = (1 - α) * m := by
  have ht := technology_rpow hα hα1
  obtain ⟨hk, he⟩ := steadyCapital_spec ht hs hm
  set ks := steadyCapital ht s m
  have hd : deriv (fun k : ℝ => k ^ α) ks = α * (ks ^ α / ks) := by
    rw [(Real.hasDerivAt_rpow_const (p := α) (Or.inl (ne_of_gt hk))).deriv,
      Real.rpow_sub_one (ne_of_gt hk)]
  unfold convergenceSpeed
  rw [hd]
  unfold rate at he
  field_simp
  linear_combination (1 - α) * he

end Solow1956.Neoclassical
