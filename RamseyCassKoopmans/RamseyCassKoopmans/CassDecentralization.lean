/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import RamseyCassKoopmans.CassValue
import RamseyCassKoopmans.AsymptoticOptimality

/-!
# Competitive decentralization of the Cass optimum

Households own the capital stock (per effective worker), rent it to firms at the
rental rate `R(t)`, supply labour for the wage `w(t)`, and choose consumption and
gross investment subject to the budget `c + z = R k + w`, accumulation
`k̇ = z - m k`, nonnegative assets, and irreversible investment `z ≥ 0`, the
household counterpart of Cass's constraint. Competitive firms rent capital until
`R = f'(k)`, and pay `w = f(k) - k f'(k)` (`firm_optimal`: this maximizes profit,
which is zero).

* `second_welfare_theorem`: the certified Cass optimum, with these prices, is a
  competitive equilibrium: no household plan asymptotically improves on it.
  Household assets may grow without bound; the comparison still closes because
  the boundary term is at most the discounted value of the planner's capital.
* `first_welfare_theorem`: every competitive-equilibrium allocation is Cass
  optimal, hence equals the unique optimum (`equilibrium_eq_optimum`).
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

/-- A household plan given rental and wage paths. -/
structure HouseholdPlan (R w : ℝ → ℝ) (m : ℝ) where
  capital : ℝ → ℝ
  consumption : ℝ → ℝ
  investment : ℝ → ℝ
  capital_nonneg : ∀ t, 0 ≤ t → 0 ≤ capital t
  consumption_pos : ∀ t, 0 ≤ t → 0 < consumption t
  consumption_continuous : ContinuousOn consumption (Ici 0)
  investment_continuous : ContinuousOn investment (Ici 0)
  investment_nonneg : ∀ t, 0 ≤ t → 0 ≤ investment t
  budget : ∀ t, 0 ≤ t → consumption t + investment t = R t * capital t + w t
  dynamics : ∀ t, 0 ≤ t → HasDerivAt capital (investment t - m * capital t) t

/-- A competitive equilibrium: firm optimality, feasibility, and household
optimality against every household plan from the same initial assets. -/
structure CompetitiveEquilibrium (f U R w : ℝ → ℝ) (d m : ℝ) (a : FeasiblePath f m) : Prop where
  capital_pos : ∀ t, 0 ≤ t → 0 < a.capital t
  rental : ∀ t, 0 ≤ t → R t = deriv f (a.capital t)
  wage : ∀ t, 0 ≤ t → w t = f (a.capital t) - a.capital t * deriv f (a.capital t)
  investment_nonneg : a.NonnegativeInvestment
  welfare : ∃ J, HasWelfare U (discount d) a.consumption J
  household_optimal : ∀ b : HouseholdPlan R w m, b.capital 0 = a.capital 0 →
    AsymptoticallyDominates U (discount d) a.consumption b.consumption

/-- Competitive firms: at `R = f'(k)` and `w = f(k) - k f'(k)` the capital stock
`k` maximizes profit `f(x) - R x - w`, and maximal profit is zero. -/
theorem firm_optimal (P : CassPrimitives f U d m) {k x : ℝ} (hk : 0 < k) (hx : 0 ≤ x) :
    f x - deriv f k * x - (f k - k * deriv f k) ≤ 0 ∧
      f k - deriv f k * k - (f k - k * deriv f k) = 0 := by
  have h := concave_support P.f_conc.concaveOn (mem_Ici.mpr hk.le) (mem_Ici.mpr hx)
    (P.f_diff k hk).hasDerivAt
  constructor <;> nlinarith

/-- Second welfare theorem: the certified Cass optimum with competitive prices is a
competitive equilibrium. -/
theorem second_welfare_theorem (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) :
    CompetitiveEquilibrium f U (fun t => deriv f (a.capital t))
      (fun t => f (a.capital t) - a.capital t * deriv f (a.capital t)) d m a := by
  refine ⟨hc.capital_pos, fun _ _ => rfl, fun _ _ => rfl, hc.investment_nonneg, hc.welfare, ?_⟩
  intro b hb0 ε hε
  set p : ℝ → ℝ := fun t => discount d t * q t
  -- the boundary term `B = p (k_a - k_b)` and its derivative
  set B : ℝ → ℝ := fun t => p t * (a.capital t - b.capital t)
  have hp : ∀ t, 0 ≤ t → HasDerivAt p
      (m * p t - discount d t * deriv U (a.consumption t) * deriv f (a.capital t)) t :=
    fun t ht => hasDerivAt_discounted_costate (hc.costate t ht)
  set B' : ℝ → ℝ := fun t =>
    (m * p t - discount d t * deriv U (a.consumption t) * deriv f (a.capital t)) *
      (a.capital t - b.capital t) +
    p t * ((a.investment t - m * a.capital t) - (b.investment t - m * b.capital t))
  have hB : ∀ t, 0 ≤ t → HasDerivAt B (B' t) t := fun t ht =>
    (hp t ht).mul ((a.dynamics t ht).sub (b.dynamics t ht))
  have hpc : ContinuousOn p (Ici 0) := fun t ht => (hp t ht).continuousAt.continuousWithinAt
  have hkac := a.capital_continuous
  have hkbc : ContinuousOn b.capital (Ici 0) := fun t ht =>
    (b.dynamics t ht).continuousAt.continuousWithinAt
  have hRc : ContinuousOn (fun t => deriv f (a.capital t)) (Ici 0) :=
    P.f_prime_cont.comp hkac hc.capital_pos
  have hmuc : ContinuousOn (fun t => deriv U (a.consumption t)) (Ici 0) :=
    P.U_prime_cont.comp a.consumption_continuous a.consumption_pos
  have hB'c : ContinuousOn B' (Ici 0) :=
    (((continuousOn_const.mul hpc).sub (((discount_continuous d).continuousOn.mul hmuc).mul
      hRc)).mul (hkac.sub hkbc)).add (hpc.mul ((a.investment_continuous.sub
      (continuousOn_const.mul hkac)).sub (b.investment_continuous.sub
      (continuousOn_const.mul hkbc))))
  have hUa : ContinuousOn (fun t => discount d t * U (a.consumption t)) (Ici 0) :=
    (discount_continuous d).continuousOn.mul (P.U_cont.comp a.consumption_continuous
      a.consumption_pos)
  have hUb : ContinuousOn (fun t => discount d t * U (b.consumption t)) (Ici 0) :=
    (discount_continuous d).continuousOn.mul (P.U_cont.comp b.consumption_continuous
      b.consumption_pos)
  -- pointwise comparison
  have hpoint : ∀ t, 0 ≤ t →
      0 ≤ discount d t * U (a.consumption t) - discount d t * U (b.consumption t) + B' t := by
    intro t ht
    have hca := a.consumption_pos t ht
    have hcb := b.consumption_pos t ht
    have hU := concave_support P.U_conc.concaveOn hca hcb (P.U_diff _ hca).hasDerivAt
    have hra := a.resource t ht
    have hbb := b.budget t ht
    have hw := hc.wedge t ht
    have hs := hc.slack t ht
    have hzb := b.investment_nonneg t ht
    have hdisc := discount_pos d t
    -- `c_a - c_b = R (k_a - k_b) - (z_a - z_b)` by the Euler identity
    have hcdiff : a.consumption t - b.consumption t =
        deriv f (a.capital t) * (a.capital t - b.capital t) -
          (a.investment t - b.investment t) := by
      linarith
    have hkey : B' t = discount d t * (-(deriv U (a.consumption t) * deriv f (a.capital t) *
        (a.capital t - b.capital t)) + q t * (a.investment t - b.investment t)) := by
      simp only [B', p]
      ring
    rw [hkey]
    have hslack' :
        0 ≤ (q t - deriv U (a.consumption t)) * (a.investment t - b.investment t) := by
      have : (q t - deriv U (a.consumption t)) * (a.investment t - b.investment t) =
          -((q t - deriv U (a.consumption t)) * b.investment t) := by linarith
      rw [this]
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hzb)
    have h1 : deriv U (a.consumption t) * (b.consumption t - a.consumption t) =
        -(deriv U (a.consumption t) * (deriv f (a.capital t) * (a.capital t - b.capital t) -
          (a.investment t - b.investment t))) := by
      rw [show b.consumption t - a.consumption t = -(a.consumption t - b.consumption t) by ring,
        hcdiff]
      ring
    have hmain : 0 ≤ U (a.consumption t) - U (b.consumption t) +
        (-(deriv U (a.consumption t) * deriv f (a.capital t) * (a.capital t - b.capital t)) +
          q t * (a.investment t - b.investment t)) := by
      linarith
    have := mul_nonneg hdisc.le hmain
    linarith
  -- the finite-horizon comparison
  have hfinite : ∀ T, 0 ≤ T → welfare U (discount d) b.consumption T -
      welfare U (discount d) a.consumption T ≤ p T * a.capital T := by
    intro T hT
    have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
    have hai := (hUa.mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
    have hbi := (hUb.mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
    have hBi := (hB'c.mono hsub).intervalIntegrable_of_Icc (μ := volume) hT
    have hFTC : (∫ t in (0 : ℝ)..T, B' t) = B T - B 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => by
        rw [uIcc_of_le hT] at ht; exact hB t ht.1) hBi
    have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..T,
        (discount d t * U (a.consumption t) - discount d t * U (b.consumption t)) + B' t :=
      intervalIntegral.integral_nonneg hT (fun t ht => hpoint t ht.1)
    rw [intervalIntegral.integral_add (hai.sub hbi) hBi, intervalIntegral.integral_sub hai hbi,
      hFTC] at hnonneg
    have hB0 : B 0 = 0 := by simp only [B, hb0, sub_self, mul_zero]
    have hBT : B T ≤ p T * a.capital T := by
      have := mul_nonneg (mul_nonneg (discount_pos d T).le (hc.price_nonneg T hT))
        (b.capital_nonneg T hT)
      simp only [B, p] at this ⊢
      nlinarith
    change welfare U (discount d) a.consumption T - welfare U (discount d) b.consumption T +
      (B T - B 0) ≥ 0 at hnonneg
    linarith
  -- the discounted value of the planner's capital vanishes
  obtain ⟨K, hK, hcap⟩ := P.exists_capacity (a.capital 0)
  have hvanish : Tendsto (fun T => p T * a.capital T) atTop (𝓝 0) :=
    Terminal.terminal_tendsto_zero_of_bounded_capital (k₁ := fun _ => 0) hc.transversality
      (fun t ht => ⟨a.capital_nonneg t ht, a.capital_le_capacity hcap hK t ht⟩)
      (fun _ _ => ⟨le_rfl, le_trans (a.capital_nonneg 0 le_rfl) hK⟩) |>.congr
      (fun T => by simp only [sub_zero]; rfl)
  filter_upwards [eventually_ge_atTop (0 : ℝ), hvanish.eventually (gt_mem_nhds hε)] with T hT hv
  exact (hfinite T hT).trans_lt hv

/-- First welfare theorem: a competitive-equilibrium allocation is Cass optimal. -/
theorem first_welfare_theorem (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {R w : ℝ → ℝ} (he : CompetitiveEquilibrium f U R w d m a) {J : ℝ}
    (hJ : HasWelfare U (discount d) a.consumption J) : IsCassOptimal U d a J := by
  refine ⟨he.investment_nonneg, hJ, fun b hb hinit Jb hJb => ?_⟩
  -- the planner's competitor is affordable to the household, with more consumption
  have hRc : ContinuousOn R (Ici 0) := (P.f_prime_cont.comp a.capital_continuous
    he.capital_pos).congr (fun t ht => he.rental t ht)
  have hwc : ContinuousOn w (Ici 0) := ((P.f_cont.comp a.capital_continuous he.capital_pos).sub
    (a.capital_continuous.mul (P.f_prime_cont.comp a.capital_continuous he.capital_pos))).congr
    (fun t ht => he.wage t ht)
  have hkbc : ContinuousOn b.capital (Ici 0) := b.capital_continuous
  have hafford : ∀ t, 0 ≤ t → b.consumption t ≤ R t * b.capital t + w t - b.investment t := by
    intro t ht
    have hs := concave_support P.f_conc.concaveOn (mem_Ici.mpr (he.capital_pos t ht).le)
      (b.capital_nonneg t ht) (P.f_diff _ (he.capital_pos t ht)).hasDerivAt
    have hr := b.resource t ht
    rw [he.rental t ht, he.wage t ht]
    nlinarith
  let b' : HouseholdPlan R w m := {
    capital := b.capital
    consumption := fun t => R t * b.capital t + w t - b.investment t
    investment := b.investment
    capital_nonneg := b.capital_nonneg
    consumption_pos := fun t ht => (b.consumption_pos t ht).trans_le (hafford t ht)
    consumption_continuous := ((hRc.mul hkbc).add hwc).sub b.investment_continuous
    investment_continuous := b.investment_continuous
    investment_nonneg := hb
    budget := fun t _ => by ring
    dynamics := b.dynamics }
  have hdom := he.household_optimal b' hinit.symm
  -- the household's welfare dominates the planner competitor's at every horizon
  have hle : ∀ T, 0 ≤ T → welfare U (discount d) b.consumption T ≤
      welfare U (discount d) b'.consumption T := by
    intro T hT
    have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
    apply intervalIntegral.integral_mono_on hT
    · exact (((discount_continuous d).continuousOn.mul (P.U_cont.comp b.consumption_continuous
        b.consumption_pos)).mono hsub).intervalIntegrable_of_Icc hT
    · exact (((discount_continuous d).continuousOn.mul (P.U_cont.comp
        b'.consumption_continuous b'.consumption_pos)).mono hsub).intervalIntegrable_of_Icc hT
    · intro t ht
      exact mul_le_mul_of_nonneg_left (P.U_strictMono.monotoneOn (b.consumption_pos t ht.1)
        (b'.consumption_pos t ht.1) (hafford t ht.1)) (discount_pos d t).le
  have hdomb : AsymptoticallyDominates U (discount d) a.consumption b.consumption := by
    intro ε hε
    filter_upwards [hdom ε hε, eventually_ge_atTop (0 : ℝ)] with T hT hT0
    linarith [hle T hT0]
  exact hdomb.finite_welfare_le hJ hJb

/-- Every competitive-equilibrium allocation is the unique Cass optimum. -/
theorem equilibrium_eq_optimum (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {R w : ℝ → ℝ} (he : CompetitiveEquilibrium f U R w d m a) :
    ∀ t, 0 ≤ t → a.capital t = (optimalPath P (he.capital_pos 0 le_rfl)).capital t ∧
      a.consumption t = (optimalPath P (he.capital_pos 0 le_rfl)).consumption t := by
  obtain ⟨J, hJ⟩ := he.welfare
  obtain ⟨qo, ho0, hoc⟩ := optimalPath_spec P (he.capital_pos 0 le_rfl)
  obtain ⟨Jo, hJo⟩ := hoc.welfare
  intro t ht
  have h := (hoc.eq_of_isCassOptimal P hJo (first_welfare_theorem P he hJ) ho0).2 t ht
  exact ⟨h.1, h.2.1⟩

end RamseyCassKoopmans
