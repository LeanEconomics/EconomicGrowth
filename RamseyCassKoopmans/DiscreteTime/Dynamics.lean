/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import DiscreteTime.Euler
import RamseyCassKoopmans.Stationary

/-!
# The policy function and global dynamics of the discrete Ramsey–Cass model

* `policy`: next period's capital `g(x)` on the optimal path from `x`;
  `IsOptimal.succ_eq_policy`: every optimal path follows `k(t+1) = g(k(t))`.
* `policy_strictMono`: `g` is strictly increasing (increasing differences of
  `u(F(x) - y)` in `(x, y)`; strictness from the Euler equation).
* `existsUnique_steady`, `steady`: the unique positive `k*` with
  `β (f'(k*) + 1 - δ) = 1`.
* `IsOptimal.tendsto`: every optimal path from positive capital converges to `k*`;
  `IsOptimal.dynamics_below`, `IsOptimal.dynamics_above`: strictly monotonically,
  with consumption moving in the same direction, and never crossing `k*`.
* `consumptionPolicy_strictMono`, `IsOptimal.capital_lt`, `IsOptimal.consumption_lt`,
  `IsOptimal.absolute_convergence`: consumption is strictly increasing in capital,
  optimal paths of identical economies never cross, and they converge to each other.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.DiscreteTime

variable {f u : ℝ → ℝ} {β δ : ℝ}

/-- Shifting an interval right lowers the increment of a strictly concave function. -/
theorem shift_increment_lt (P : Primitives f u β δ) {a b Δ : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hΔ : 0 < Δ) : u (b + Δ) - u (a + Δ) < u b - u a := by
  have hs1 := P.u_conc.secant_strict_mono (a := a) (x := b) (y := b + Δ) (mem_Ici.mpr ha)
    (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) (ne_of_gt hab)
    (by linarith) (by linarith)
  have hs2 := P.u_conc.secant_strict_mono (a := b + Δ) (x := a) (y := a + Δ)
    (mem_Ici.mpr (by linarith)) (mem_Ici.mpr ha) (mem_Ici.mpr (by linarith)) (by linarith)
    (by linarith) (by linarith)
  have hL : 0 < b - a := sub_pos.mpr hab
  have e1 : (u (a + Δ) - u (b + Δ)) / (a + Δ - (b + Δ)) = (u (b + Δ) - u (a + Δ)) / (b - a) := by
    rw [show a + Δ - (b + Δ) = -(b - a) by ring, div_neg, ← neg_div]
    ring_nf
  have e2 : (u a - u (b + Δ)) / (a - (b + Δ)) = (u (b + Δ) - u a) / (b + Δ - a) := by
    rw [show a - (b + Δ) = -(b + Δ - a) by ring, div_neg, ← neg_div]
    ring_nf
  rw [e1, e2] at hs2
  have h := hs2.trans hs1
  rwa [div_lt_div_iff_of_pos_right hL] at h

/-- Next period's capital chosen from `x`. -/
noncomputable def policy (P : Primitives f u β δ) (x : ℝ) : ℝ :=
  if hx : 0 ≤ x then optimalPath P hx 1 else 0

theorem policy_eq (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) :
    policy P x = optimalPath P hx 1 := by
  simp only [policy, hx, ↓reduceDIte]

/-- Every optimal path follows the policy. -/
theorem IsOptimal.succ_eq_policy (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) : k (t + 1) = policy P (k t) := by
  have hkt := hk.1.nonneg hx t
  have hs := hk.shift P hx t
  have heq := optimal_unique P hkt hs.1 hs.2
  rw [policy_eq P hkt]
  exact congrFun heq 1

/-- The Bellman equation at the policy, with its feasibility. -/
theorem bellman_policy (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) :
    value P x = u (resources f δ x - policy P x) + β * value P (policy P x) ∧
      0 ≤ policy P x ∧ policy P x ≤ resources f δ x := by
  obtain ⟨hk, -⟩ := optimalPath_spec P hx
  rw [policy_eq P hx]
  exact ⟨(bellman P hx).1, (hk.2 0).1, (hk.2 0).2.trans_eq (congrArg (resources f δ) hk.1)⟩

/-- From `x > 0`, next capital is interior and the Euler equation holds at date zero. -/
theorem policy_interior (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) :
    0 < policy P x ∧ policy P x < resources f δ x ∧
      deriv u (resources f δ x - policy P x) =
        β * deriv u (resources f δ (policy P x) - policy P (policy P x)) *
          (deriv f (policy P x) + (1 - δ)) := by
  have hk := isOptimal_optimalPath P hx.le
  obtain ⟨-, h1, hc⟩ := hk.interior P hx 0
  have he := hk.euler P hx 0
  have hs0 := hk.succ_eq_policy P hx.le 0
  have hs1 := hk.succ_eq_policy P hx.le 1
  have h0 : optimalPath P hx.le 0 = x := hk.1.1
  simp only [consumption, zero_add] at hc he h1 hs0 hs1
  rw [h0] at hs0 hc he
  rw [hs0] at h1 hc he hs1
  rw [hs1] at he
  exact ⟨h1, by linarith, he⟩

/-- The policy is strictly increasing. -/
theorem policy_strictMono (P : Primitives f u β δ) : StrictMonoOn (policy P) (Ioi 0) := by
  intro x hx x' hx' hxx
  have hx0 : (0 : ℝ) < x := hx
  have hx0' : (0 : ℝ) < x' := hx'
  obtain ⟨-, hy0, hyF⟩ := bellman_policy P hx0.le
  obtain ⟨-, hy0', hyF'⟩ := bellman_policy P hx0'.le
  have hFF := P.resources_strictMono (mem_Ici.mpr hx0.le) (mem_Ici.mpr hx0'.le) hxx
  have hweak : policy P x ≤ policy P x' := by
    by_contra hlt
    push Not at hlt
    have h1 := (bellman P hx0.le).2 (policy P x') hy0' (hlt.le.trans hyF)
    have h2 := (bellman P hx0'.le).2 (policy P x) hy0 (hyF.trans hFF.le)
    have hb1 := (bellman_policy P hx0.le).1
    have hb2 := (bellman_policy P hx0'.le).1
    have hinc := shift_increment_lt P (a := resources f δ x - policy P x)
      (b := resources f δ x - policy P x') (Δ := resources f δ x' - resources f δ x)
      (sub_nonneg.mpr hyF) (by linarith) (by linarith)
    rw [show resources f δ x - policy P x' + (resources f δ x' - resources f δ x) =
        resources f δ x' - policy P x' by ring,
      show resources f δ x - policy P x + (resources f δ x' - resources f δ x) =
        resources f δ x' - policy P x by ring] at hinc
    linarith
  rcases lt_or_eq_of_le hweak with hlt | heq
  · exact hlt
  · -- equal choices contradict the two Euler equations
    exfalso
    obtain ⟨hp, hpF, he⟩ := policy_interior P hx0
    obtain ⟨-, hpF', he'⟩ := policy_interior P hx0'
    rw [← heq] at he' hpF'
    have hu : deriv u (resources f δ x - policy P x) = deriv u (resources f δ x' - policy P x) := by
      rw [he, he']
    have hc : 0 < resources f δ x - policy P x := by linarith
    have hc' : 0 < resources f δ x' - policy P x := by linarith
    have := P.u_prime_anti.injOn hc hc' hu
    linarith

theorem Primitives.target_pos (P : Primitives f u β δ) : 0 < 1 / β - (1 - δ) := by
  have h1 : 1 < 1 / β := by rw [lt_div_iff₀ P.β_pos]; linarith [P.β_lt_one]
  linarith [P.δ_pos]

theorem Primitives.existsUnique_steady (P : Primitives f u β δ) :
    ∃! k : ℝ, 0 < k ∧ deriv f k = 1 / β - (1 - δ) :=
  existsUnique_positive_root_of_inada (deriv f) _ P.target_pos P.f_prime_cont
    (production_deriv_strictAnti f P.f_conc P.f_diff) P.f_inada0 P.f_inadaTop

/-- The steady state: `β (f'(k*) + 1 - δ) = 1`. -/
noncomputable def steady (P : Primitives f u β δ) : ℝ :=
  Classical.choose P.existsUnique_steady.exists

theorem steady_spec (P : Primitives f u β δ) :
    0 < steady P ∧ deriv f (steady P) = 1 / β - (1 - δ) :=
  Classical.choose_spec P.existsUnique_steady.exists

theorem steady_euler (P : Primitives f u β δ) : β * (deriv f (steady P) + (1 - δ)) = 1 := by
  rw [(steady_spec P).2]
  field_simp [P.β_pos.ne']
  ring

/-- Steady-state consumption `c* = F(k*) - k*` is positive. -/
theorem steady_consumption_pos (P : Primitives f u β δ) :
    0 < resources f δ (steady P) - steady P := by
  obtain ⟨hk, hd⟩ := steady_spec P
  have hgap := marginal_product_times_capital_lt_output f _ P.f_conc P.f_zero hk (P.f_diff _ hk)
  rw [hd] at hgap
  have h1 : 1 < 1 / β := by rw [lt_div_iff₀ P.β_pos]; linarith [P.β_lt_one]
  have : (1 - (1 - δ)) * steady P < (1 / β - (1 - δ)) * steady P :=
    mul_lt_mul_of_pos_right (by linarith) hk
  simp only [resources]
  nlinarith

theorem hasDerivAt_resources_pos (P : Primitives f u β δ) {k : ℝ} (hk : 0 < k) :
    0 < deriv f k + (1 - δ) := by
  have := P.f_prime_pos k hk
  linarith [P.δ_le_one]

/-- An optimal path is monotone. -/
theorem IsOptimal.monotone_or_antitone (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : IsOptimal f u β δ x k) :
    (k 0 ≤ k 1 → Monotone k) ∧ (k 1 ≤ k 0 → Antitone k) := by
  have hpos : ∀ t, 0 < k t := fun t => (hk.interior P hx t).1
  have hsucc := hk.succ_eq_policy P hx.le
  constructor
  · intro h01
    apply monotone_nat_of_le_succ
    intro t
    induction t with
    | zero => exact h01
    | succ t ih =>
      calc k (t + 1) = policy P (k t) := hsucc t
        _ ≤ policy P (k (t + 1)) := (policy_strictMono P).monotoneOn (hpos t) (hpos (t + 1)) ih
        _ = k (t + 1 + 1) := (hsucc (t + 1)).symm
  · intro h10
    apply antitone_nat_of_succ_le
    intro t
    induction t with
    | zero => exact h10
    | succ t ih =>
      calc k (t + 1 + 1) = policy P (k (t + 1)) := hsucc (t + 1)
        _ ≤ policy P (k t) := (policy_strictMono P).monotoneOn (hpos (t + 1)) (hpos t) ih
        _ = k (t + 1) := (hsucc t).symm

/-- Every optimal path from positive capital converges to the steady state. -/
theorem IsOptimal.tendsto (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) : Tendsto k atTop (𝓝 (steady P)) := by
  have hpos : ∀ t, 0 < k t := fun t => (hk.interior P hx t).1
  have hcpos : ∀ t, 0 < consumption f δ k t := fun t => (hk.interior P hx t).2.2
  have hbd : ∀ t, k t ≤ bound P x := fun t => hk.1.le_bound P hx.le t
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  -- the limit
  obtain ⟨L, hL⟩ : ∃ L, Tendsto k atTop (𝓝 L) := by
    rcases le_total (k 0) (k 1) with h | h
    · exact ⟨_, tendsto_atTop_ciSup (hmono h) ⟨bound P x, by rintro _ ⟨t, rfl⟩; exact hbd t⟩⟩
    · exact ⟨_, tendsto_atTop_ciInf (hanti h) ⟨0, by rintro _ ⟨t, rfl⟩; exact (hpos t).le⟩⟩
  have hL0 : 0 ≤ L := ge_of_tendsto' hL (fun t => (hpos t).le)
  have hshift : Tendsto (fun t => k (t + 1)) atTop (𝓝 L) := hL.comp (tendsto_add_atTop_nat 1)
  have hFcont : ContinuousWithinAt (resources f δ) (Ici 0) L := P.resources_cont L hL0
  have hFk : Tendsto (fun t => resources f δ (k t)) atTop (𝓝 (resources f δ L)) :=
    hFcont.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hL, Eventually.of_forall
      (fun t => mem_Ici.mpr (hpos t).le)⟩)
  have hc : Tendsto (consumption f δ k) atTop (𝓝 (resources f δ L - L)) := hFk.sub hshift
  have hLF : L ≤ resources f δ L := by
    have h := le_of_tendsto_of_tendsto hshift hFk (Eventually.of_forall (fun t => (hk.1.2 t).2))
    exact h
  obtain ⟨hks, hkd⟩ := steady_spec P
  have hr := P.target_pos
  -- case `L = 0` is impossible
  rcases hL0.eq_or_lt with hL00 | hLpos
  · exfalso
    subst hL00
    have hk0 : Tendsto (fun t => k (t + 1)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hshift, Eventually.of_forall (fun t => hpos (t + 1))⟩
    have hbig := (P.f_inada0.comp hk0).eventually (eventually_gt_atTop (1 / β - (1 - δ)))
    obtain ⟨T, hT⟩ := eventually_atTop.mp hbig
    -- consumption rises from `T` on
    have hrise : ∀ t, T ≤ t → consumption f δ k t < consumption f δ k (t + 1) := by
      intro t ht
      have he := hk.euler P hx t
      have hg : 1 < β * (deriv f (k (t + 1)) + (1 - δ)) := by
        have h := hT t ht
        simp only [Function.comp_apply] at h
        have := mul_lt_mul_of_pos_left h P.β_pos
        rw [mul_sub, mul_div_cancel₀ _ P.β_pos.ne'] at this
        nlinarith
      by_contra hle
      push Not at hle
      have hu := P.u_prime_anti.antitoneOn (hcpos (t + 1)) (hcpos t) hle
      have hup := P.u_prime_pos _ (hcpos (t + 1))
      have : deriv u (consumption f δ k (t + 1)) <
          β * deriv u (consumption f δ k (t + 1)) * (deriv f (k (t + 1)) + (1 - δ)) := by
        nlinarith
      linarith
    have hge : ∀ n, consumption f δ k T ≤ consumption f δ k (T + n) := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih => exact ih.trans (hrise (T + n) (by omega)).le
    rw [resources_zero P, sub_zero] at hc
    have hev := (hc.eventually (gt_mem_nhds (hcpos T)))
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    have := hN (T + N) (by omega)
    have := hge N
    linarith
  -- case `F(L) = L`: consumption vanishes, contradicted by jumping to `k*`
  rcases lt_or_eq_of_le hLF with hFL | hFL
  · -- `F(L) > L`: the Euler equation in the limit pins down `L = k*`
    have hcL : 0 < resources f δ L - L := sub_pos.mpr hFL
    have huc : ContinuousAt (deriv u) (resources f δ L - L) :=
      P.u_prime_cont.continuousAt (Ioi_mem_nhds hcL)
    have hfc : ContinuousAt (deriv f) L := P.f_prime_cont.continuousAt (Ioi_mem_nhds hLpos)
    have hlhs := huc.tendsto.comp hc
    have hrhs := ((huc.tendsto.comp (hc.comp (tendsto_add_atTop_nat 1))).const_mul β).mul
      ((hfc.tendsto.comp hshift).add_const (1 - δ))
    have heq : deriv u (resources f δ L - L) =
        β * deriv u (resources f δ L - L) * (deriv f L + (1 - δ)) :=
      tendsto_nhds_unique hlhs (hrhs.congr (fun t => by
        simp only [Function.comp_apply]
        exact (hk.euler P hx t).symm))
    have hup := P.u_prime_pos _ hcL
    have hβ : β * (deriv f L + (1 - δ)) = 1 := by
      have : deriv u (resources f δ L - L) * (β * (deriv f L + (1 - δ)) - 1) = 0 := by
        linear_combination -heq
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (ne_of_gt hup)
      · linarith
    have hfL : deriv f L = 1 / β - (1 - δ) := by
      field_simp [P.β_pos.ne']
      linarith
    have := P.existsUnique_steady.unique ⟨hLpos, hfL⟩ ⟨hks, hkd⟩
    rw [this] at hL
    exact hL
  · exfalso
    -- consumption tends to zero and `L > k*`
    rw [← hFL, sub_self] at hc
    have hLks : steady P < L := by
      have hfL : f L = δ * L := by simp only [resources] at hFL; linarith
      have hgap := marginal_product_times_capital_lt_output f L P.f_conc P.f_zero hLpos
        (P.f_diff L hLpos)
      rw [hfL] at hgap
      have hdL : deriv f L < δ := by nlinarith
      by_contra hle
      push Not at hle
      have := (production_deriv_strictAnti f P.f_conc P.f_diff).antitoneOn hLpos hks hle
      rw [hkd] at this
      have h1 : 1 < 1 / β := by rw [lt_div_iff₀ P.β_pos]; linarith [P.β_lt_one]
      linarith
    have hcs0 := steady_consumption_pos P
    set cs := resources f δ (steady P) - steady P with hcs_def
    have hcs : 0 < cs := hcs0
    obtain ⟨T, hT⟩ := eventually_atTop.mp ((hL.eventually (lt_mem_nhds hLks)).and
      (hc.eventually (gt_mem_nhds (half_pos hcs))))
    -- the alternative path from `k T`: move to `k*` and stay there
    set z : ℕ → ℝ := fun s => if s = 0 then k T else steady P
    have hFmono : resources f δ (steady P) ≤ resources f δ (k T) :=
      P.resources_strictMono.monotoneOn (mem_Ici.mpr hks.le) (mem_Ici.mpr (hpos T).le)
        (hT T le_rfl).1.le
    have hFT : steady P < resources f δ (k T) := by linarith
    have hz : Feasible f δ (k T) z := by
      refine ⟨rfl, fun s => ⟨?_, ?_⟩⟩
      · simp only [z, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]; exact hks.le
      · rcases s with _ | s
        · simp only [z, zero_add, one_ne_zero, ↓reduceIte]; exact hFT.le
        · simp only [z, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]; linarith
    have hzc : ∀ s, cs ≤ consumption f δ z s := by
      intro s
      rcases s with _ | s
      · simp only [consumption, z, zero_add, one_ne_zero, ↓reduceIte]
        linarith
      · simp only [consumption, z, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        exact le_rfl
    have hsT := hk.shift P hx.le T
    have hle := hsT.2 z hz
    -- compare welfare termwise
    have hshc : ∀ s, consumption f δ (fun s => k (T + s)) s ≤ cs / 2 := by
      intro s
      have := (hT (T + s) (by omega)).2
      exact this.le
    have hshnn : ∀ s, 0 ≤ consumption f δ (fun s => k (T + s)) s :=
      fun s => (hsT.1.consumption_mem P (hpos T).le s).1
    have hgeo := summable_geometric_of_lt_one P.β_pos.le P.β_lt_one
    have h1 : welfare f u β δ (fun s => k (T + s)) ≤ ∑' s, β ^ s * u (cs / 2) :=
      (hsT.1.summable P (hpos T).le).tsum_le_tsum (fun s => mul_le_mul_of_nonneg_left
        (P.u_strictMono.monotoneOn (hshnn s) (mem_Ici.mpr (half_pos hcs).le) (hshc s))
        (pow_pos P.β_pos s).le) (hgeo.mul_right _)
    have h2 : ∑' s, β ^ s * u (cs / 2) < ∑' s, β ^ s * u cs :=
      (hgeo.mul_right _).tsum_lt_tsum (i := 0) (fun s => mul_le_mul_of_nonneg_left
        (P.u_strictMono.monotoneOn (mem_Ici.mpr (half_pos hcs).le) (mem_Ici.mpr hcs.le)
          (half_le_self hcs.le)) (pow_pos P.β_pos s).le)
        (by
          simp only [pow_zero, one_mul]
          exact P.u_strictMono (mem_Ici.mpr (half_pos hcs).le) (mem_Ici.mpr hcs.le)
            (half_lt_self hcs))
        (hgeo.mul_right _)
    have h3 : ∑' s, β ^ s * u cs ≤ welfare f u β δ z :=
      (hgeo.mul_right _).tsum_le_tsum (fun s => mul_le_mul_of_nonneg_left
        (P.u_strictMono.monotoneOn (mem_Ici.mpr hcs.le)
          (mem_Ici.mpr (hcs.le.trans (hzc s))) (hzc s)) (pow_pos P.β_pos s).le)
        (hz.summable P (hpos T).le)
    linarith

/-- Consumption converges to `c* = F(k*) - k*`. -/
theorem IsOptimal.consumption_tendsto (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x)
    {k : ℕ → ℝ} (hk : IsOptimal f u β δ x k) :
    Tendsto (consumption f δ k) atTop (𝓝 (resources f δ (steady P) - steady P)) := by
  have hL := hk.tendsto P hx
  have hks := (steady_spec P).1
  have hFk : Tendsto (fun t => resources f δ (k t)) atTop (𝓝 (resources f δ (steady P))) :=
    (P.resources_cont _ (mem_Ici.mpr hks.le)).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hL, Eventually.of_forall (fun t => mem_Ici.mpr (hk.interior P hx t).1.le)⟩)
  exact hFk.sub (hL.comp (tendsto_add_atTop_nat 1))

/-- Below the steady state an optimal path rises strictly toward `k*`, with rising
consumption. -/
theorem IsOptimal.dynamics_below (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (hlt : x < steady P) :
    StrictMono k ∧ (∀ t, k t < steady P) ∧ StrictMono (consumption f δ k) := by
  have hpos : ∀ t, 0 < k t := fun t => (hk.interior P hx t).1
  have hL := hk.tendsto P hx
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  have hsucc := hk.succ_eq_policy P hx.le
  have h01 : k 0 < k 1 := by
    by_contra hle
    push Not at hle
    have hlim := le_of_tendsto' hL (fun t => (hanti hle) (Nat.zero_le t))
    rw [hk.1.1] at hlim
    linarith
  have hsm : StrictMono k := by
    apply strictMono_nat_of_lt_succ
    intro t
    induction t with
    | zero => exact h01
    | succ t ih =>
      calc k (t + 1) = policy P (k t) := hsucc t
        _ < policy P (k (t + 1)) := policy_strictMono P (hpos t) (hpos (t + 1)) ih
        _ = k (t + 1 + 1) := (hsucc (t + 1)).symm
  have hbelow : ∀ t, k t < steady P := fun t =>
    (hsm (Nat.lt_succ_self t)).trans_le (ge_of_tendsto hL (eventually_atTop.mpr
      ⟨t + 1, fun s hs => hsm.monotone hs⟩))
  refine ⟨hsm, hbelow, strictMono_nat_of_lt_succ (fun t => ?_)⟩
  have he := hk.euler P hx t
  have hks := steady_spec P
  have hfd : deriv f (steady P) < deriv f (k (t + 1)) :=
    (production_deriv_strictAnti f P.f_conc P.f_diff) (hpos (t + 1)) hks.1 (hbelow (t + 1))
  have hg : 1 < β * (deriv f (k (t + 1)) + (1 - δ)) := by
    have := steady_euler P
    nlinarith [P.β_pos]
  have hcpos := fun t => (hk.interior P hx t).2.2
  by_contra hle
  push Not at hle
  have hu := P.u_prime_anti.antitoneOn (hcpos (t + 1)) (hcpos t) hle
  have hup := P.u_prime_pos _ (hcpos (t + 1))
  nlinarith

/-- Above the steady state an optimal path falls strictly toward `k*`, with falling
consumption. -/
theorem IsOptimal.dynamics_above (P : Primitives f u β δ) {x : ℝ} (hx : 0 < x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (hgt : steady P < x) :
    StrictAnti k ∧ (∀ t, steady P < k t) ∧ StrictAnti (consumption f δ k) := by
  have hpos : ∀ t, 0 < k t := fun t => (hk.interior P hx t).1
  have hL := hk.tendsto P hx
  obtain ⟨hmono, hanti⟩ := hk.monotone_or_antitone P hx
  have hsucc := hk.succ_eq_policy P hx.le
  have h10 : k 1 < k 0 := by
    by_contra hle
    push Not at hle
    have hlim := ge_of_tendsto' hL (fun t => (hmono hle) (Nat.zero_le t))
    rw [hk.1.1] at hlim
    linarith
  have hsa : StrictAnti k := by
    apply strictAnti_nat_of_succ_lt
    intro t
    induction t with
    | zero => exact h10
    | succ t ih =>
      calc k (t + 1 + 1) = policy P (k (t + 1)) := hsucc (t + 1)
        _ < policy P (k t) := policy_strictMono P (hpos (t + 1)) (hpos t) ih
        _ = k (t + 1) := (hsucc t).symm
  have habove : ∀ t, steady P < k t := fun t =>
    lt_of_le_of_lt (le_of_tendsto hL (eventually_atTop.mpr
      ⟨t + 1, fun s hs => hsa.antitone hs⟩)) (hsa (Nat.lt_succ_self t))
  refine ⟨hsa, habove, strictAnti_nat_of_succ_lt (fun t => ?_)⟩
  have he := hk.euler P hx t
  have hks := steady_spec P
  have hfd : deriv f (k (t + 1)) < deriv f (steady P) :=
    (production_deriv_strictAnti f P.f_conc P.f_diff) hks.1 (hpos (t + 1)) (habove (t + 1))
  have hg : β * (deriv f (k (t + 1)) + (1 - δ)) < 1 := by
    have := steady_euler P
    nlinarith [P.β_pos]
  have hcpos := fun t => (hk.interior P hx t).2.2
  by_contra hle
  push Not at hle
  have hu := P.u_prime_anti.antitoneOn (hcpos t) (hcpos (t + 1)) hle
  have hup := P.u_prime_pos _ (hcpos (t + 1))
  have hFp := hasDerivAt_resources_pos P (hpos (t + 1))
  nlinarith

/-- Optimal paths of identical economies never cross. -/
theorem IsOptimal.capital_lt (P : Primitives f u β δ) {x x' : ℝ} (hx : 0 < x)
    {k k' : ℕ → ℝ} (hk : IsOptimal f u β δ x k) (hk' : IsOptimal f u β δ x' k') (hxx : x < x')
    (t : ℕ) : k t < k' t := by
  have hx' : 0 < x' := hx.trans hxx
  induction t with
  | zero => rw [hk.1.1, hk'.1.1]; exact hxx
  | succ t ih =>
    rw [hk.succ_eq_policy P hx.le t, hk'.succ_eq_policy P hx'.le t]
    exact policy_strictMono P (hk.interior P hx t).1 (hk'.interior P hx' t).1 ih

/-- Consumption as a function of capital. -/
noncomputable def consumptionPolicy (P : Primitives f u β δ) (x : ℝ) : ℝ :=
  resources f δ x - policy P x

theorem IsOptimal.consumption_eq (P : Primitives f u β δ) {x : ℝ} (hx : 0 ≤ x) {k : ℕ → ℝ}
    (hk : IsOptimal f u β δ x k) (t : ℕ) :
    consumption f δ k t = consumptionPolicy P (k t) := by
  simp only [consumption, consumptionPolicy, hk.succ_eq_policy P hx t]

/-- Consumption is strictly increasing in capital. -/
theorem consumptionPolicy_strictMono (P : Primitives f u β δ) :
    StrictMonoOn (consumptionPolicy P) (Ioi 0) := by
  intro x hx x' hx' hxx
  have hx0 : (0 : ℝ) < x := hx
  have hx0' : (0 : ℝ) < x' := hx'
  set k := optimalPath P hx0.le
  set k' := optimalPath P hx0'.le
  have hk := isOptimal_optimalPath P hx0.le
  have hk' := isOptimal_optimalPath P hx0'.le
  have hc0 : consumption f δ k 0 = consumptionPolicy P x := by
    rw [hk.consumption_eq P hx0.le 0, hk.1.1]
  have hc0' : consumption f δ k' 0 = consumptionPolicy P x' := by
    rw [hk'.consumption_eq P hx0'.le 0, hk'.1.1]
  rw [← hc0, ← hc0']
  by_contra hle
  push Not at hle
  have hcp := fun t => (hk.interior P hx0 t).2.2
  have hcp' := fun t => (hk'.interior P hx0' t).2.2
  have hkp := fun t => (hk.interior P hx0 t).1
  have hkp' := fun t => (hk'.interior P hx0' t).1
  -- the marginal-utility ratio `R t = u'(c'_t)/u'(c_t)` rises strictly
  set R : ℕ → ℝ := fun t => deriv u (consumption f δ k' t) / deriv u (consumption f δ k t)
  have hup := fun t => P.u_prime_pos _ (hcp t)
  have hup' := fun t => P.u_prime_pos _ (hcp' t)
  have hstep : ∀ t, R t < R (t + 1) := by
    intro t
    have he := hk.euler P hx0 t
    have he' := hk'.euler P hx0' t
    have hlt := hk.capital_lt P hx0 hk' hxx (t + 1)
    have hfd : deriv f (k' (t + 1)) < deriv f (k (t + 1)) :=
      (production_deriv_strictAnti f P.f_conc P.f_diff) (hkp (t + 1)) (hkp' (t + 1)) hlt
    have hF := hasDerivAt_resources_pos P (hkp' (t + 1))
    simp only [R]
    rw [div_lt_div_iff₀ (hup t) (hup (t + 1)), he, he']
    have := mul_pos (mul_pos P.β_pos (hup' (t + 1))) (hup (t + 1))
    nlinarith
  have hR0 : 1 ≤ R 0 := by
    simp only [R]
    rw [le_div_iff₀ (hup 0), one_mul]
    exact P.u_prime_anti.antitoneOn (hcp' 0) (hcp 0) hle
  have hR1 : ∀ t, R 1 ≤ R (t + 1) := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih => exact ih.trans (hstep (t + 1)).le
  -- but `R t → 1`
  have hcs := steady_consumption_pos P
  have huc : ContinuousAt (deriv u) (resources f δ (steady P) - steady P) :=
    P.u_prime_cont.continuousAt (Ioi_mem_nhds hcs)
  have hlim : Tendsto R atTop (𝓝 1) := by
    have h := (huc.tendsto.comp (hk'.consumption_tendsto P hx0')).div
      (huc.tendsto.comp (hk.consumption_tendsto P hx0)) (ne_of_gt (P.u_prime_pos _ hcs))
    rw [div_self (ne_of_gt (P.u_prime_pos _ hcs))] at h
    exact h
  have hge : R 1 ≤ 1 := ge_of_tendsto' (hlim.comp (tendsto_add_atTop_nat 1))
    (fun t => hR1 t)
  have := hstep 0
  linarith

/-- The poorer economy consumes strictly less at every date. -/
theorem IsOptimal.consumption_lt (P : Primitives f u β δ) {x x' : ℝ} (hx : 0 < x)
    {k k' : ℕ → ℝ} (hk : IsOptimal f u β δ x k) (hk' : IsOptimal f u β δ x' k') (hxx : x < x')
    (t : ℕ) : consumption f δ k t < consumption f δ k' t := by
  have hx' : 0 < x' := hx.trans hxx
  rw [hk.consumption_eq P hx.le t, hk'.consumption_eq P hx'.le t]
  exact consumptionPolicy_strictMono P (hk.interior P hx t).1 (hk'.interior P hx' t).1
    (hk.capital_lt P hx hk' hxx t)

/-- Absolute convergence of identical economies. -/
theorem IsOptimal.absolute_convergence (P : Primitives f u β δ) {x x' : ℝ} (hx : 0 < x)
    (hx' : 0 < x') {k k' : ℕ → ℝ} (hk : IsOptimal f u β δ x k)
    (hk' : IsOptimal f u β δ x' k') :
    Tendsto (fun t => k' t - k t) atTop (𝓝 0) ∧
      Tendsto (fun t => consumption f δ k' t - consumption f δ k t) atTop (𝓝 0) := by
  constructor
  · simpa only [sub_self] using (hk'.tendsto P hx').sub (hk.tendsto P hx)
  · simpa only [sub_self] using (hk'.consumption_tendsto P hx').sub (hk.consumption_tendsto P hx)

end RamseyCassKoopmans.DiscreteTime
