/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import DiscreteTime.Model

/-!
# The principle of optimality, uniqueness, and the shape of the value function

* `welfare_eq_head_add`: `W(k) = u(c₀) + β W(tail k)`.
* `tail_optimal`, `bellman`: the tail of an optimal path is optimal from the stock
  it reaches, and `V(k₀) = max_{0 ≤ y ≤ F(k₀)} u(F(k₀) - y) + β V(y)`.
* `optimal_unique`: the optimal path is unique (strict concavity of `u`).
* `value_strictMono`, `value_strictConcave`: `V` is strictly increasing and strictly
  concave.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.DiscreteTime

variable {f u : ℝ → ℝ} {β δ : ℝ}

/-- The path from date one on. -/
def tail (k : ℕ → ℝ) : ℕ → ℝ := fun t => k (t + 1)

/-- Prepend a stock to a path. -/
def prepend (k₀ : ℝ) (k : ℕ → ℝ) : ℕ → ℝ := fun t => if t = 0 then k₀ else k (t - 1)

theorem Feasible.tail {k₀ : ℝ} {k : ℕ → ℝ} (hk : Feasible f δ k₀ k) :
    Feasible f δ (k 1) (DiscreteTime.tail k) :=
  ⟨rfl, fun t => hk.2 (t + 1)⟩

theorem Feasible.prepend {k₀ y : ℝ} {k : ℕ → ℝ} (hk : Feasible f δ y k) (hy0 : 0 ≤ y)
    (hy : y ≤ resources f δ k₀) : Feasible f δ k₀ (DiscreteTime.prepend k₀ k) := by
  refine ⟨rfl, fun t => ?_⟩
  rcases t with _ | t
  · have h1 : DiscreteTime.prepend k₀ k (0 + 1) = y := by simp [DiscreteTime.prepend, hk.1]
    have h0 : DiscreteTime.prepend k₀ k 0 = k₀ := by simp [DiscreteTime.prepend]
    rw [h1, h0]
    exact ⟨hy0, hy⟩
  · have h1 : DiscreteTime.prepend k₀ k (t + 1 + 1) = k (t + 1) := by
      simp [DiscreteTime.prepend]
    have h0 : DiscreteTime.prepend k₀ k (t + 1) = k t := by simp [DiscreteTime.prepend]
    rw [h1, h0]
    exact hk.2 t

theorem consumption_tail (k : ℕ → ℝ) (t : ℕ) :
    consumption f δ (tail k) t = consumption f δ k (t + 1) := rfl

theorem welfare_eq_head_add (P : Primitives f u β δ) {k₀ : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) :
    welfare f u β δ k = u (consumption f δ k 0) + β * welfare f u β δ (tail k) := by
  unfold welfare
  rw [(hk.summable P hk₀).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, pow_succ, consumption_tail]
  congr 1
  congr 1
  funext t
  ring

theorem consumption_prepend_zero (k₀ : ℝ) (k : ℕ → ℝ) :
    consumption f δ (prepend k₀ k) 0 = resources f δ k₀ - k 0 := by
  simp [consumption, prepend]

theorem tail_prepend (k₀ : ℝ) (k : ℕ → ℝ) : tail (prepend k₀ k) = k := by
  funext t
  simp [tail, prepend]

theorem welfare_prepend (P : Primitives f u β δ) {k₀ y : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ y k) (hy0 : 0 ≤ y) (hy : y ≤ resources f δ k₀) (hk₀ : 0 ≤ k₀) :
    welfare f u β δ (prepend k₀ k) = u (resources f δ k₀ - y) + β * welfare f u β δ k := by
  rw [welfare_eq_head_add P (hk.prepend hy0 hy) hk₀, consumption_prepend_zero, tail_prepend, hk.1]

/-- The tail of an optimal path is optimal. -/
theorem tail_optimal (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k)
    (hopt : ∀ k', Feasible f δ k₀ k' → welfare f u β δ k' ≤ welfare f u β δ k) :
    welfare f u β δ (tail k) = value P (k 1) := by
  have hk1 : 0 ≤ k 1 := (hk.2 0).1
  apply le_antisymm (welfare_le_value P hk1 hk.tail)
  by_contra hlt
  push Not at hlt
  obtain ⟨hopt1, _⟩ := optimalPath_spec P hk1
  have hbetter := hopt _ (hopt1.prepend hk1 (by rw [← hk.1]; exact (hk.2 0).2))
  rw [welfare_prepend P hopt1 hk1 (by rw [← hk.1]; exact (hk.2 0).2) hk₀,
    welfare_eq_head_add P hk hk₀, ← value_eq P hk1] at hbetter
  have hc0 : consumption f δ k 0 = resources f δ k₀ - k 1 := by
    simp [consumption, hk.1]
  rw [hc0] at hbetter
  have := mul_lt_mul_of_pos_left hlt P.β_pos
  linarith

/-- The Bellman equation along the optimal path, and the Bellman inequality for
every feasible choice of next period's capital. -/
theorem bellman (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    value P k₀ = u (resources f δ k₀ - optimalPath P hk₀ 1) +
        β * value P (optimalPath P hk₀ 1) ∧
      ∀ y, 0 ≤ y → y ≤ resources f δ k₀ →
        u (resources f δ k₀ - y) + β * value P y ≤ value P k₀ := by
  obtain ⟨hk, hopt⟩ := optimalPath_spec P hk₀
  refine ⟨?_, fun y hy0 hy => ?_⟩
  · rw [value_eq P hk₀, welfare_eq_head_add P hk hk₀, tail_optimal P hk₀ hk hopt]
    simp [consumption, hk.1]
  · obtain ⟨hy', _⟩ := optimalPath_spec P hy0
    have := welfare_le_value P hk₀ (hy'.prepend hy0 hy)
    rwa [welfare_prepend P hy' hy0 hy hk₀, ← value_eq P hy0] at this

/-- Concavity of resources: mixed resources dominate the mixture, strictly at
distinct stocks. -/
theorem resources_mix (P : Primitives f u β δ) {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    θ * resources f δ a + (1 - θ) * resources f δ b ≤ resources f δ (θ * a + (1 - θ) * b) ∧
      (a ≠ b → θ * resources f δ a + (1 - θ) * resources f δ b <
        resources f δ (θ * a + (1 - θ) * b)) := by
  have hc := P.f_conc.concaveOn.2 ha hb hθ.le (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hc
  refine ⟨by simp only [resources]; nlinarith, fun hne => ?_⟩
  have hs := P.f_conc.2 ha hb hne hθ (by linarith : (0 : ℝ) < 1 - θ) (by ring)
  simp only [smul_eq_mul] at hs
  simp only [resources]
  nlinarith

/-- The mixture of two feasible paths is feasible, with consumption at least the
mixture of consumptions. -/
theorem Feasible.mix (P : Primitives f u β δ) {k₀ k₀' θ : ℝ} {k k' : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk' : Feasible f δ k₀' k') (hk₀ : 0 ≤ k₀) (hk₀' : 0 ≤ k₀')
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    Feasible f δ (θ * k₀ + (1 - θ) * k₀') (fun t => θ * k t + (1 - θ) * k' t) ∧
      ∀ t, θ * consumption f δ k t + (1 - θ) * consumption f δ k' t ≤
        consumption f δ (fun t => θ * k t + (1 - θ) * k' t) t := by
  have hmix := fun t => (resources_mix P (hk.nonneg hk₀ t) (hk'.nonneg hk₀' t) hθ hθ1).1
  refine ⟨⟨by simp only [hk.1, hk'.1], fun t => ⟨?_, ?_⟩⟩, fun t => ?_⟩
  · have := mul_nonneg hθ.le (hk.2 t).1
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - θ) (hk'.2 t).1
    linarith
  · have h1 := mul_le_mul_of_nonneg_left (hk.2 t).2 hθ.le
    have h2 := mul_le_mul_of_nonneg_left (hk'.2 t).2 (by linarith : (0 : ℝ) ≤ 1 - θ)
    linarith [hmix t]
  · simp only [consumption]
    linarith [hmix t]

/-- Termwise comparison of discounted utility for a mixture. -/
theorem utility_mix (P : Primitives f u β δ) {c c' c'' θ : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hθ : 0 < θ) (hθ1 : θ < 1) (hle : θ * c + (1 - θ) * c' ≤ c'') :
    θ * u c + (1 - θ) * u c' ≤ u c'' ∧
      (c ≠ c' → θ * u c + (1 - θ) * u c' < u c'') := by
  have hmixnn : 0 ≤ θ * c + (1 - θ) * c' := by nlinarith
  have hmono := P.u_strictMono.monotoneOn hmixnn (hmixnn.trans hle) hle
  have hconc := P.u_conc.concaveOn.2 hc hc' hθ.le (by linarith : (0 : ℝ) ≤ 1 - θ) (by ring)
  simp only [smul_eq_mul] at hconc
  refine ⟨hconc.trans hmono, fun hne => ?_⟩
  have hs := P.u_conc.2 hc hc' hne hθ (by linarith : (0 : ℝ) < 1 - θ) (by ring)
  simp only [smul_eq_mul] at hs
  exact hs.trans_le hmono

/-- The mixture's welfare dominates the mixture of welfares. -/
theorem welfare_mix (P : Primitives f u β δ) {k₀ k₀' θ : ℝ} {k k' : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk' : Feasible f δ k₀' k') (hk₀ : 0 ≤ k₀) (hk₀' : 0 ≤ k₀')
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    θ * welfare f u β δ k + (1 - θ) * welfare f u β δ k' ≤
        welfare f u β δ (fun t => θ * k t + (1 - θ) * k' t) ∧
      ((∃ t, consumption f δ k t ≠ consumption f δ k' t ∨
          θ * consumption f δ k t + (1 - θ) * consumption f δ k' t <
            consumption f δ (fun t => θ * k t + (1 - θ) * k' t) t) →
        θ * welfare f u β δ k + (1 - θ) * welfare f u β δ k' <
          welfare f u β δ (fun t => θ * k t + (1 - θ) * k' t)) := by
  obtain ⟨hmixf, hcons⟩ := hk.mix P hk' hk₀ hk₀' hθ hθ1
  have hmix0 : 0 ≤ θ * k₀ + (1 - θ) * k₀' := by nlinarith
  have hs := hk.summable P hk₀
  have hs' := hk'.summable P hk₀'
  have hsm := hmixf.summable P hmix0
  have hlhs : θ * welfare f u β δ k + (1 - θ) * welfare f u β δ k' =
      ∑' t, (θ * (β ^ t * u (consumption f δ k t)) +
        (1 - θ) * (β ^ t * u (consumption f δ k' t))) := by
    unfold welfare
    rw [(hs.mul_left θ).tsum_add (hs'.mul_left (1 - θ)), tsum_mul_left, tsum_mul_left]
  have hterm : ∀ t, θ * (β ^ t * u (consumption f δ k t)) +
      (1 - θ) * (β ^ t * u (consumption f δ k' t)) ≤
        β ^ t * u (consumption f δ (fun t => θ * k t + (1 - θ) * k' t) t) := by
    intro t
    have h := (utility_mix P (hk.consumption_mem P hk₀ t).1 (hk'.consumption_mem P hk₀' t).1 hθ
      hθ1 (hcons t)).1
    have := mul_le_mul_of_nonneg_left h (pow_pos P.β_pos t).le
    linarith
  have hsum := (hs.mul_left θ).add (hs'.mul_left (1 - θ))
  refine ⟨?_, fun ⟨t, ht⟩ => ?_⟩
  · rw [hlhs]
    exact hsum.tsum_le_tsum hterm hsm
  · rw [hlhs]
    refine hsum.tsum_lt_tsum (i := t) hterm ?_ hsm
    have hct := (hk.consumption_mem P hk₀ t).1
    have hct' := (hk'.consumption_mem P hk₀' t).1
    have hstrict : θ * u (consumption f δ k t) + (1 - θ) * u (consumption f δ k' t) <
        u (consumption f δ (fun t => θ * k t + (1 - θ) * k' t) t) := by
      rcases ht with hne | hlt
      · exact (utility_mix P hct hct' hθ hθ1 (hcons t)).2 hne
      · have hmixc : 0 ≤ θ * consumption f δ k t + (1 - θ) * consumption f δ k' t := by
          nlinarith
        have h1 := (utility_mix P hct hct' hθ hθ1 le_rfl).1
        exact h1.trans_lt (P.u_strictMono hmixc (hmixc.trans hlt.le) hlt)
    have := mul_lt_mul_of_pos_left hstrict (pow_pos P.β_pos t)
    linarith

/-- The optimal path is unique. -/
theorem optimal_unique (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k)
    (hopt : ∀ k', Feasible f δ k₀ k' → welfare f u β δ k' ≤ welfare f u β δ k) :
    k = optimalPath P hk₀ := by
  obtain ⟨ho, hoopt⟩ := optimalPath_spec P hk₀
  set o := optimalPath P hk₀
  by_contra hne
  -- two distinct feasible paths from the same stock differ in some consumption
  have hcne : ∃ t, consumption f δ k t ≠ consumption f δ o t := by
    by_contra hall
    push Not at hall
    apply hne
    funext t
    induction t with
    | zero => rw [hk.1, ho.1]
    | succ t ih =>
      have := hall t
      simp only [consumption, ih] at this
      linarith
  have hθ : (0 : ℝ) < 1 / 2 := by norm_num
  have hθ1 : (1 : ℝ) / 2 < 1 := by norm_num
  obtain ⟨hmixf, -⟩ := hk.mix P ho hk₀ hk₀ hθ hθ1
  have hstrict := (welfare_mix P hk ho hk₀ hk₀ hθ hθ1).2
    (by obtain ⟨t, ht⟩ := hcne; exact ⟨t, Or.inl ht⟩)
  have hmix0 : 1 / 2 * k₀ + (1 - 1 / 2) * k₀ = k₀ := by ring
  rw [hmix0] at hmixf
  have h1 := hopt _ hmixf
  have h2 := hoopt k hk
  have h3 := hopt o ho
  linarith

/-- The value function is strictly increasing. -/
theorem value_strictMono (P : Primitives f u β δ) : StrictMonoOn (value P) (Ici 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) ≤ a := ha
  have hb' : (0 : ℝ) ≤ b := hb
  obtain ⟨hk, hopt⟩ := optimalPath_spec P ha'
  have hk1 : 0 ≤ optimalPath P ha' 1 := (hk.2 0).1
  have hFa : optimalPath P ha' 1 ≤ resources f δ a :=
    (hk.2 0).2.trans_eq (congrArg (resources f δ) hk.1)
  have hFab := P.resources_strictMono ha hb hab
  obtain ⟨hb1, _⟩ := bellman P hb'
  have hbell := (bellman P hb').2 (optimalPath P ha' 1) hk1 (hFa.trans hFab.le)
  rw [(bellman P ha').1]
  have hc : 0 ≤ resources f δ a - optimalPath P ha' 1 := sub_nonneg.mpr hFa
  have hu := P.u_strictMono hc (by linarith : (0 : ℝ) ≤ resources f δ b - optimalPath P ha' 1)
    (by linarith)
  linarith

/-- The value function is strictly concave. -/
theorem value_strictConcave (P : Primitives f u β δ) : StrictConcaveOn ℝ (Ici 0) (value P) := by
  refine ⟨convex_Ici 0, fun a ha b hb hne θ θ' hθ hθ' hsum => ?_⟩
  have ha' : (0 : ℝ) ≤ a := ha
  have hb' : (0 : ℝ) ≤ b := hb
  have hθ'' : θ' = 1 - θ := by linarith
  subst hθ''
  have hθ1 : θ < 1 := by linarith
  obtain ⟨hka, _⟩ := optimalPath_spec P ha'
  obtain ⟨hkb, _⟩ := optimalPath_spec P hb'
  obtain ⟨hmixf, -⟩ := hka.mix P hkb ha' hb' hθ hθ1
  have hstrict := (welfare_mix P hka hkb ha' hb' hθ hθ1).2 ⟨0, Or.inr (by
    have hne' : optimalPath P ha' 0 ≠ optimalPath P hb' 0 := by rw [hka.1, hkb.1]; exact hne
    have h := (resources_mix P (hka.nonneg ha' 0) (hkb.nonneg hb' 0) hθ hθ1).2 hne'
    simp only [consumption]
    linarith)⟩
  have hmix0 : 0 ≤ θ * a + (1 - θ) * b := by nlinarith
  have hle := welfare_le_value P hmix0 hmixf
  simp only [smul_eq_mul]
  rw [value_eq P ha', value_eq P hb']
  linarith

end RamseyCassKoopmans.DiscreteTime
