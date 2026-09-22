import RamseyCassKoopmans.AsymptoticODE
import RamseyCassKoopmans.CooperativeShooting
import Mathlib.Topology.Order.IntermediateValue

/-! # Monotonicity of the trajectory selected by shooting

The escape condition is used to exclude an incorrectly directed vector at an
ordinary point of the trajectory. The comparison theorem traps such a vector's
future in a rectangle; a uniform drift would then force escape in finite time.
-/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.ODE

def Avoids (γ : ℝ → ℝ × ℝ) (a : ℝ × ℝ) : Prop :=
  ∀ t, 0 ≤ t → γ t ∉ lowerQuadrant a ∪ upperQuadrant a

theorem trajectory_shift {v : ℝ × ℝ → ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (v (γ t)) t) (s : ℝ) :
    ∀ t, HasDerivAt (fun u => γ (u + s)) (v (γ (t + s))) t := by
  intro t
  convert (hd (t + s)).scomp t ((hasDerivAt_id t).add_const s) using 1
  · rfl
  · simp only [one_smul]

theorem avoids_shift {γ : ℝ → ℝ × ℝ} {a : ℝ × ℝ} (h : Avoids γ a)
    {s : ℝ} (hs : 0 ≤ s) : Avoids (fun u => γ (u + s)) a :=
  fun t ht => h (t + s) (add_nonneg ht hs)

theorem never_reaches_equilibrium {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hl : LipschitzWith K v) {a : ℝ × ℝ} (ha : v a = 0)
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : γ 0 ≠ a) : ∀ t, γ t ≠ a := by
  intro t ht
  have heq : γ = fun _ => a := by
    apply ODE_solution_unique_univ (v := fun (_ : ℝ) => v)
      (s := fun _ => univ) (t₀ := t) (fun _ => hl.lipschitzOnWith)
      (fun u => ⟨hd u, mem_univ _⟩)
      (fun u => ⟨by simpa only [ha] using hasDerivAt_const u a, mem_univ _⟩) ht
  exact h0 (congrFun heq 0)

theorem enters_lower_at_first_boundary {γ : ℝ → ℝ × ℝ} {a w : ℝ × ℝ}
    (hd : HasDerivAt γ w 0) (hk : (γ 0).1 = a.1) (hq : (γ 0).2 < a.2)
    (hv : w.1 < 0) : ∃ t, 0 < t ∧ γ t ∈ lowerQuadrant a := by
  have hswap : HasDerivAt (fun t => ((γ t).2, (γ t).1)) (w.2, w.1) 0 :=
    (hasDerivAt_snd hd).prodMk (hasDerivAt_fst hd)
  obtain ⟨t, ht, hmem⟩ := enters_lower_at_boundary (a := (a.2, a.1)) hswap hq hk hv
  exact ⟨t, ht, hmem.2, hmem.1⟩

theorem enters_upper_at_first_boundary {γ : ℝ → ℝ × ℝ} {a w : ℝ × ℝ}
    (hd : HasDerivAt γ w 0) (hk : (γ 0).1 = a.1) (hq : a.2 < (γ 0).2)
    (hv : 0 < w.1) : ∃ t, 0 < t ∧ γ t ∈ upperQuadrant a := by
  have hswap : HasDerivAt (fun t => ((γ t).2, (γ t).1)) (w.2, w.1) 0 :=
    (hasDerivAt_snd hd).prodMk (hasDerivAt_fst hd)
  obtain ⟨t, ht, hmem⟩ := enters_upper_at_boundary (a := (a.2, a.1)) hswap hq hk hv
  exact ⟨t, ht, hmem.2, hmem.1⟩

theorem avoids_first_ne {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hl : LipschitzWith K v) {a : ℝ × ℝ} (ha : v a = 0)
    (haxis : ∀ x : ℝ × ℝ, x.1 = a.1 →
      (x.2 < a.2 → (v x).1 < 0) ∧ (a.2 < x.2 → 0 < (v x).1))
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : γ 0 ≠ a) (havoid : Avoids γ a) :
    ∀ T, 0 ≤ T → (γ T).1 ≠ a.1 := by
  intro T hT hk
  have hdshift := trajectory_shift hd T 0
  simp only [zero_add] at hdshift
  rcases lt_trichotomy (γ T).2 a.2 with hq | hq | hq
  · obtain ⟨s, hs, hmem⟩ := enters_lower_at_first_boundary (a := a) hdshift
      (by simpa only [zero_add] using hk) (by simpa only [zero_add] using hq) ((haxis _ hk).1 hq)
    exact havoid (s + T) (add_nonneg hs.le hT) (Or.inl hmem)
  · exact never_reaches_equilibrium hl ha hd h0 T (Prod.ext hk hq)
  · obtain ⟨s, hs, hmem⟩ := enters_upper_at_first_boundary (a := a) hdshift
      (by simpa only [zero_add] using hk) (by simpa only [zero_add] using hq) ((haxis _ hk).2 hq)
    exact havoid (s + T) (add_nonneg hs.le hT) (Or.inr hmem)

theorem first_stays_below {γ : ℝ → ℝ × ℝ} {a : ℝ × ℝ}
    (hc : Continuous γ) (h0 : (γ 0).1 < a.1)
    (hne : ∀ t, 0 ≤ t → (γ t).1 ≠ a.1) : ∀ t, 0 ≤ t → (γ t).1 < a.1 := by
  intro t ht
  by_contra hn
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc ht hc.fst.continuousOn
    (show a.1 ∈ Icc (γ 0).1 (γ t).1 from ⟨h0.le, le_of_not_gt hn⟩)
  exact hne s hs.1 heq

theorem first_stays_above {γ : ℝ → ℝ × ℝ} {a : ℝ × ℝ}
    (hc : Continuous γ) (h0 : a.1 < (γ 0).1)
    (hne : ∀ t, 0 ≤ t → (γ t).1 ≠ a.1) : ∀ t, 0 ≤ t → a.1 < (γ t).1 := by
  intro t ht
  by_contra hn
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc' ht hc.fst.continuousOn
    (show a.1 ∈ Icc (γ t).1 (γ 0).1 from ⟨le_of_not_gt hn, h0.le⟩)
  exact hne s hs.1 heq

/-- On the lower-capital branch, a nonpositive capital velocity would force
the price below the steady price. The drift bound concerns finite rectangles
of points, not an assumed property of a selected solution. -/
theorem lower_branch_velocity {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ}
    (hprice : ∀ x : ℝ × ℝ, x.1 < a.1 → a.2 ≤ x.2 → (v x).2 < 0)
    (hdrift : ∀ b : ℝ × ℝ, b.1 < a.1 → a.2 ≤ b.2 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ × ℝ,
        x.1 ≤ b.1 → a.2 ≤ x.2 → x.2 ≤ b.2 → (v x).2 ≤ -ε)
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hk : ∀ t, 0 ≤ t → (γ t).1 < a.1) (havoid : Avoids γ a) :
    ∀ t, 0 ≤ t → 0 < (v (γ t)).1 ∧ (v (γ t)).2 < 0 := by
  have hq : ∀ t, 0 ≤ t → a.2 ≤ (γ t).2 := by
    intro t ht
    by_contra hn
    exact havoid t ht (Or.inl ⟨hk t ht, lt_of_not_ge hn⟩)
  intro t ht
  have hv2 := hprice (γ t) (hk t ht) (hq t ht)
  refine ⟨?_, hv2⟩
  by_contra hn
  have hs := trajectory_shift hd t
  have hle := solution_le_supersolution hc hl
    (a := γ t) ⟨le_of_not_gt hn, hv2.le⟩ hs
    (by simp only [zero_add]; exact ⟨le_rfl, le_rfl⟩)
  obtain ⟨ε, hε, he⟩ := hdrift (γ t) (hk t ht) (hq t ht)
  exact not_bounded_below_of_negative_drift (fun s => hasDerivAt_snd (hs s)) hε
    (fun s hs0 => he _ (hle s hs0).1 (hq _ (add_nonneg hs0 ht)) (hle s hs0).2)
    (fun s hs0 => hq _ (add_nonneg hs0 ht))

theorem lower_branch_monotone {v : ℝ × ℝ → ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hv : ∀ t, 0 ≤ t → 0 < (v (γ t)).1 ∧ (v (γ t)).2 < 0) :
    StrictMonoOn (fun t => (γ t).1) (Ici 0) ∧
      StrictAntiOn (fun t => (γ t).2) (Ici 0) := by
  constructor
  · apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (HasDerivAt.continuousOn (fun t _ => hasDerivAt_fst (hd t)))
    intro t ht
    rw [(hasDerivAt_fst (hd t)).deriv]
    exact (hv t (interior_subset ht)).1
  · apply strictAntiOn_of_deriv_neg (convex_Ici 0)
      (HasDerivAt.continuousOn (fun t _ => hasDerivAt_snd (hd t)))
    intro t ht
    rw [(hasDerivAt_snd (hd t)).deriv]
    exact (hv t (interior_subset ht)).2

/-- On the upper-capital branch, the two possible incorrect directions are
excluded separately. The second drift condition includes an investment corner:
it can force capital down even when the price equation is not the Euler equation. -/
theorem upper_branch_velocity {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ}
    (hcross : ∀ b : ℝ × ℝ, a.1 < b.1 → b.2 ≤ a.2 →
      0 ≤ (v b).1 → 0 < (v b).2)
    (hup : ∀ b : ℝ × ℝ, a.1 < b.1 → b.2 ≤ a.2 → 0 ≤ (v b).1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ × ℝ,
        b.1 ≤ x.1 → b.2 ≤ x.2 → x.2 ≤ a.2 → ε ≤ (v x).2)
    (hdown : ∀ b : ℝ × ℝ, a.1 < b.1 → b.2 ≤ a.2 → (v b).2 ≤ 0 →
      (v b).1 ≤ 0 ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ × ℝ,
        a.1 ≤ x.1 → x.1 ≤ b.1 → x.2 ≤ b.2 → (v x).1 ≤ -ε)
    {γ : ℝ → ℝ × ℝ} (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hk : ∀ t, 0 ≤ t → a.1 < (γ t).1) (havoid : Avoids γ a) :
    ∀ t, 0 ≤ t → (v (γ t)).1 < 0 ∧ 0 < (v (γ t)).2 := by
  have hq : ∀ t, 0 ≤ t → (γ t).2 ≤ a.2 := by
    intro t ht
    by_contra hn
    exact havoid t ht (Or.inr ⟨hk t ht, lt_of_not_ge hn⟩)
  intro t ht
  have hs := trajectory_shift hd t
  constructor
  · by_contra hn
    have hv1 : 0 ≤ (v (γ t)).1 := le_of_not_gt hn
    have hv2 := hcross (γ t) (hk t ht) (hq t ht) hv1
    have hge := solution_ge_subsolution hc hl (a := γ t) ⟨hv1, hv2.le⟩ hs
      (by simp only [zero_add]; exact ⟨le_rfl, le_rfl⟩)
    obtain ⟨ε, hε, he⟩ := hup (γ t) (hk t ht) (hq t ht) hv1
    exact not_bounded_above_of_positive_drift (fun s => hasDerivAt_snd (hs s)) hε
      (fun s hs0 => he _ (hge s hs0).1 (hge s hs0).2 (hq _ (add_nonneg hs0 ht)))
      (fun s hs0 => hq _ (add_nonneg hs0 ht))
  · by_contra hn
    have hv2 : (v (γ t)).2 ≤ 0 := le_of_not_gt hn
    obtain ⟨hv1, ε, hε, he⟩ := hdown (γ t) (hk t ht) (hq t ht) hv2
    have hle := solution_le_supersolution hc hl (a := γ t) ⟨hv1, hv2⟩ hs
      (by simp only [zero_add]; exact ⟨le_rfl, le_rfl⟩)
    exact not_bounded_below_of_negative_drift (fun s => hasDerivAt_fst (hs s)) hε
      (fun s hs0 => he _ (hk _ (add_nonneg hs0 ht)).le (hle s hs0).1 (hle s hs0).2)
      (fun s hs0 => (hk _ (add_nonneg hs0 ht)).le)

theorem upper_branch_monotone {v : ℝ × ℝ → ℝ × ℝ} {γ : ℝ → ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hv : ∀ t, 0 ≤ t → (v (γ t)).1 < 0 ∧ 0 < (v (γ t)).2) :
    StrictAntiOn (fun t => (γ t).1) (Ici 0) ∧
      StrictMonoOn (fun t => (γ t).2) (Ici 0) := by
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Ici 0)
      (HasDerivAt.continuousOn (fun t _ => hasDerivAt_fst (hd t)))
    intro t ht
    rw [(hasDerivAt_fst (hd t)).deriv]
    exact (hv t (interior_subset ht)).1
  · apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (HasDerivAt.continuousOn (fun t _ => hasDerivAt_snd (hd t)))
    intro t ht
    rw [(hasDerivAt_snd (hd t)).deriv]
    exact (hv t (interior_subset ht)).2

theorem lower_branch_limit {v : ℝ × ℝ → ℝ × ℝ} (hc : Continuous v)
    {γ : ℝ → ℝ × ℝ} {a : ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hk : ∀ t, 0 ≤ t → (γ t).1 ≤ a.1)
    (hq : ∀ t, 0 ≤ t → a.2 ≤ (γ t).2)
    (hm : MonotoneOn (fun t => (γ t).1) (Ici 0))
    (ha : AntitoneOn (fun t => (γ t).2) (Ici 0)) :
    ∃ b : ℝ × ℝ, Tendsto γ atTop (𝓝 b) ∧ v b = 0 ∧
      b.1 ∈ Icc (γ 0).1 a.1 ∧ b.2 ∈ Icc a.2 (γ 0).2 := by
  obtain ⟨k, hklim⟩ := exists_limit_of_monotone_bounded hm hk
  obtain ⟨q, hqlim⟩ := exists_limit_of_antitone_bounded ha hq
  have hlim : Tendsto γ atTop (𝓝 (k, q)) := hklim.prodMk_nhds hqlim
  refine ⟨(k, q), hlim, limit_is_equilibrium hc hd hlim, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ge_of_tendsto hklim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht)
  · exact le_of_tendsto hklim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hk t ht)
  · exact ge_of_tendsto hqlim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hq t ht)
  · exact le_of_tendsto hqlim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact ha (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht)

theorem upper_branch_limit {v : ℝ × ℝ → ℝ × ℝ} (hc : Continuous v)
    {γ : ℝ → ℝ × ℝ} {a : ℝ × ℝ}
    (hd : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hk : ∀ t, 0 ≤ t → a.1 ≤ (γ t).1)
    (hq : ∀ t, 0 ≤ t → (γ t).2 ≤ a.2)
    (ha : AntitoneOn (fun t => (γ t).1) (Ici 0))
    (hm : MonotoneOn (fun t => (γ t).2) (Ici 0)) :
    ∃ b : ℝ × ℝ, Tendsto γ atTop (𝓝 b) ∧ v b = 0 ∧
      b.1 ∈ Icc a.1 (γ 0).1 ∧ b.2 ∈ Icc (γ 0).2 a.2 := by
  obtain ⟨k, hklim⟩ := exists_limit_of_antitone_bounded ha hk
  obtain ⟨q, hqlim⟩ := exists_limit_of_monotone_bounded hm hq
  have hlim : Tendsto γ atTop (𝓝 (k, q)) := hklim.prodMk_nhds hqlim
  refine ⟨(k, q), hlim, limit_is_equilibrium hc hd hlim, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact ge_of_tendsto hklim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hk t ht)
  · exact le_of_tendsto hklim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact ha (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht)
  · exact ge_of_tendsto hqlim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hm (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht)
  · exact le_of_tendsto hqlim (by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hq t ht)

end RamseyCassKoopmans.ODE
