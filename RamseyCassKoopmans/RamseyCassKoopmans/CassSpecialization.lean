import RamseyCassKoopmans.GlobalCass
import RamseyCassKoopmans.BoundedWelfare

/-!
# Cass's dynamic conclusions for a fully specified economy

Production and utility are `2 * sqrt`, and `d = m = 1`. For every `k₀ > 0`,
we construct the unique optimal path, prove monotone convergence, and prove that
all admissible competitors have finite welfare. Above `k₀ = 4/9` the construction
includes a zero-investment phase ending at `log (9*k₀/4)`.

The admissible class has continuous controls and strictly positive consumption.
These theorems do not assert the general-function Cass existence theorem, nor
Koopmans's full published characterization under his distinct utility hypotheses.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.ClosedForm

/-- Monotone capital and consumption adjustment, with a constant path precisely
at the modified golden rule. Strictness is for all nonnegative times. -/
def MonotoneTransition (a : FeasiblePath Examples.production 1) (k₀ : ℝ) : Prop :=
  (k₀ < 1 / 4 → StrictMonoOn a.capital (Ici 0) ∧
    StrictMonoOn a.consumption (Ici 0)) ∧
  (1 / 4 < k₀ → StrictAntiOn a.capital (Ici 0) ∧
    StrictAntiOn a.consumption (Ici 0)) ∧
  (k₀ = 1 / 4 → ∀ t, 0 ≤ t → a.capital t = 1 / 4 ∧ a.consumption t = 3 / 4)

theorem path_monotoneTransition (x₀ : ℝ) (hx : 0 < x₀) :
    MonotoneTransition (path x₀ hx) (x₀ ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hs : x₀ < 1 / 2 := by nlinarith
    exact ⟨capital_strictMonoOn hx hs, consumption_strictMonoOn hx hs⟩
  · intro h
    have hs : 1 / 2 < x₀ := by nlinarith
    exact ⟨capital_strictAntiOn hx hs, consumption_strictAntiOn hx hs⟩
  · intro h t _
    have hs : x₀ = 1 / 2 := by nlinarith
    subst x₀
    norm_num [path, capital, consumption, state]

theorem Corner.cornerPath_monotoneTransition {k₀ : ℝ} (hk : 4 / 9 ≤ k₀) (τ : ℝ) :
    MonotoneTransition (cornerPath τ) k₀ := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    linarith
  · intro _
    exact ⟨(joinedCapital_strictAnti τ).strictAntiOn _,
      (joinedConsumption_strictAnti τ).strictAntiOn _⟩
  · intro h
    linarith

noncomputable def optimalPath (k₀ : ℝ) (hk : 0 < k₀) : FeasiblePath Examples.production 1 :=
  if k₀ ≤ 4 / 9 then path (Real.sqrt k₀) (Real.sqrt_pos.mpr hk)
  else Corner.cornerPath (Real.log (9 * k₀ / 4))

noncomputable def optimalValue (k₀ : ℝ) : ℝ :=
  if k₀ ≤ 4 / 9 then 2 * Real.sqrt 3 * (1 + Real.sqrt k₀) / 3
  else Corner.cornerValue (Real.log (9 * k₀ / 4))

theorem optimalPath_initial (k₀ : ℝ) (hk : 0 < k₀) :
    (optimalPath k₀ hk).capital 0 = k₀ := by
  unfold optimalPath
  split_ifs with h
  · rw [path_initial, Real.sq_sqrt hk.le]
  · exact (Corner.cornerPath_initial_from_stock (le_of_not_ge h)).2

theorem optimalPath_isCassOptimal (k₀ : ℝ) (hk : 0 < k₀) :
    IsCassOptimal utility 1 (optimalPath k₀ hk) (optimalValue k₀) := by
  unfold optimalPath optimalValue
  split_ifs with h
  · apply path_isCassOptimal
    have hs := Real.sq_sqrt hk.le
    have hp := Real.sqrt_nonneg k₀
    nlinarith
  · exact Corner.cornerPath_isCassOptimal _
      (Corner.cornerPath_initial_from_stock (le_of_not_ge h)).1

theorem optimalPath_converges (k₀ : ℝ) (hk : 0 < k₀) :
    Tendsto (optimalPath k₀ hk).capital atTop (𝓝 (1 / 4)) ∧
    Tendsto (optimalPath k₀ hk).consumption atTop (𝓝 (3 / 4)) := by
  unfold optimalPath
  split_ifs
  · exact ⟨capital_tendsto _, consumption_tendsto _⟩
  · exact ⟨Corner.joinedCapital_tendsto _, Corner.joinedConsumption_tendsto _⟩

theorem optimalPath_monotone (k₀ : ℝ) (hk : 0 < k₀) :
    MonotoneTransition (optimalPath k₀ hk) k₀ := by
  unfold optimalPath
  split_ifs with h
  · simpa only [Real.sq_sqrt hk.le] using
      path_monotoneTransition (Real.sqrt k₀) (Real.sqrt_pos.mpr hk)
  · exact Corner.cornerPath_monotoneTransition (le_of_not_ge h) _

theorem optimalPath_unique (k₀ : ℝ) (hk : 0 < k₀)
    (b : FeasiblePath Examples.production 1) (hb : b.NonnegativeInvestment)
    (hinit : b.capital 0 = k₀)
    (hJ : HasWelfare utility (discount 1) b.consumption (optimalValue k₀)) :
    ∀ t, 0 ≤ t → b.capital t = (optimalPath k₀ hk).capital t ∧
      b.consumption t = (optimalPath k₀ hk).consumption t ∧
      b.investment t = (optimalPath k₀ hk).investment t := by
  unfold optimalPath optimalValue at *
  split_ifs at * with h
  · apply path_unique _ (Real.sqrt_pos.mpr hk) b _ hJ
    rw [path_initial, Real.sq_sqrt hk.le, hinit]
  · obtain ⟨hτ, hi⟩ := Corner.cornerPath_initial_from_stock (le_of_not_ge h)
    exact Corner.cornerPath_unique _ hτ b hb (hi.trans hinit.symm) hJ

/-- Complete optimal-path conclusion for this economy. Welfare existence is
proved for every competitor, rather than required from the user of the theorem.
Equality with the optimal value forces equality of the entire feasible path. -/
theorem cass_dynamic_theorem (k₀ : ℝ) (hk : 0 < k₀) :
    (optimalPath k₀ hk).capital 0 = k₀ ∧
    IsCassOptimal utility 1 (optimalPath k₀ hk) (optimalValue k₀) ∧
    MonotoneTransition (optimalPath k₀ hk) k₀ ∧
    Tendsto (optimalPath k₀ hk).capital atTop (𝓝 (1 / 4)) ∧
    Tendsto (optimalPath k₀ hk).consumption atTop (𝓝 (3 / 4)) ∧
    (∀ b : FeasiblePath Examples.production 1, b.NonnegativeInvestment →
      b.capital 0 = k₀ → ∃ Jb,
        HasWelfare utility (discount 1) b.consumption Jb ∧ Jb ≤ optimalValue k₀ ∧
        (Jb = optimalValue k₀ → ∀ t, 0 ≤ t →
          b.capital t = (optimalPath k₀ hk).capital t ∧
          b.consumption t = (optimalPath k₀ hk).consumption t ∧
          b.investment t = (optimalPath k₀ hk).investment t)) := by
  have ho := optimalPath_isCassOptimal k₀ hk
  refine ⟨optimalPath_initial k₀ hk, ho, optimalPath_monotone k₀ hk,
    (optimalPath_converges k₀ hk).1, (optimalPath_converges k₀ hk).2, ?_⟩
  intro b hb hi
  obtain ⟨Jb, hJb⟩ := cass_path_hasWelfare b hb
  refine ⟨Jb, hJb, ho.2.2 b hb ((optimalPath_initial k₀ hk).trans hi.symm) Jb hJb, ?_⟩
  intro heq
  exact optimalPath_unique k₀ hk b hb hi (heq ▸ hJb)

/-- Necessity of the constructed path follows from welfare optimality itself;
no Euler equation, transversality, or convergence is assumed of `b`. -/
theorem every_optimum_eq (k₀ : ℝ) (hk : 0 < k₀)
    (b : FeasiblePath Examples.production 1) (Jb : ℝ)
    (hb : IsCassOptimal utility 1 b Jb) (hi : b.capital 0 = k₀) :
    Jb = optimalValue k₀ ∧ ∀ t, 0 ≤ t →
      b.capital t = (optimalPath k₀ hk).capital t ∧
      b.consumption t = (optimalPath k₀ hk).consumption t ∧
      b.investment t = (optimalPath k₀ hk).investment t := by
  have ha := optimalPath_isCassOptimal k₀ hk
  have hinit := (optimalPath_initial k₀ hk).trans hi.symm
  have heq : Jb = optimalValue k₀ := le_antisymm
    (ha.2.2 b hb.1 hinit Jb hb.2.1)
    (hb.2.2 _ ha.1 hinit.symm _ ha.2.1)
  exact ⟨heq, optimalPath_unique k₀ hk b hb.1 hi (heq ▸ hb.2.1)⟩

theorem every_optimum_converges (k₀ : ℝ) (hk : 0 < k₀)
    (b : FeasiblePath Examples.production 1) (Jb : ℝ)
    (hb : IsCassOptimal utility 1 b Jb) (hi : b.capital 0 = k₀) :
    Tendsto b.capital atTop (𝓝 (1 / 4)) ∧
      Tendsto b.consumption atTop (𝓝 (3 / 4)) := by
  have heq := (every_optimum_eq k₀ hk b Jb hb hi).2
  have hlim := optimalPath_converges k₀ hk
  constructor
  · apply hlim.1.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (heq t ht).1.symm
  · apply hlim.2.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (heq t ht).2.1.symm

end RamseyCassKoopmans.ClosedForm
