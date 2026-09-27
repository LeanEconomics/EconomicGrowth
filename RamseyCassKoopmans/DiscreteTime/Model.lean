/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import RamseyCassKoopmans.CapacityFromInada
import RamseyCassKoopmans.Stationary
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The discrete-time Ramsey–Cass–Koopmans model: feasibility and existence

Capital per worker obeys `k(t+1) = F(k(t)) - c(t)` with gross resources
`F(k) = f(k) + (1 - δ) k`, and a path is feasible when `0 ≤ k(t+1) ≤ F(k(t))`.
Welfare is `∑ βᵗ u(c(t))` with `0 < β < 1`.

Utility is continuous at zero consumption (`u` is continuous on `[0, ∞)`), so
welfare is a convergent series on the compact set of feasible paths; logarithmic
utility is not covered. Feasible paths are bounded (`Feasible.le_bound`), the
feasible set is compact in the product topology, and welfare is continuous on it,
so an optimal path exists (`exists_optimal`).
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.DiscreteTime

/-- Primitive assumptions of the discrete-time model. -/
structure Primitives (f u : ℝ → ℝ) (β δ : ℝ) : Prop where
  β_pos : 0 < β
  β_lt_one : β < 1
  δ_pos : 0 < δ
  δ_le_one : δ ≤ 1
  f_cont : ContinuousOn f (Ici 0)
  f_zero : f 0 = 0
  f_conc : StrictConcaveOn ℝ (Ici 0) f
  f_diff : ∀ k, 0 < k → DifferentiableAt ℝ f k
  f_prime_pos : ∀ k, 0 < k → 0 < deriv f k
  f_prime_cont : ContinuousOn (deriv f) (Ioi 0)
  f_inada0 : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop
  f_inadaTop : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))
  u_cont : ContinuousOn u (Ici 0)
  u_conc : StrictConcaveOn ℝ (Ici 0) u
  u_diff : ∀ c, 0 < c → DifferentiableAt ℝ u c
  u_prime_pos : ∀ c, 0 < c → 0 < deriv u c
  u_prime_cont : ContinuousOn (deriv u) (Ioi 0)
  u_inada0 : Tendsto (deriv u) (𝓝[>] (0 : ℝ)) atTop

variable {f u : ℝ → ℝ} {β δ : ℝ}

/-- Gross resources: output plus undepreciated capital. -/
def resources (f : ℝ → ℝ) (δ k : ℝ) : ℝ := f k + (1 - δ) * k

/-- A feasible capital path from `k₀`. -/
def Feasible (f : ℝ → ℝ) (δ k₀ : ℝ) (k : ℕ → ℝ) : Prop :=
  k 0 = k₀ ∧ ∀ t, 0 ≤ k (t + 1) ∧ k (t + 1) ≤ resources f δ (k t)

/-- Consumption along a capital path. -/
def consumption (f : ℝ → ℝ) (δ : ℝ) (k : ℕ → ℝ) (t : ℕ) : ℝ :=
  resources f δ (k t) - k (t + 1)

/-- Discounted lifetime welfare. -/
noncomputable def welfare (f u : ℝ → ℝ) (β δ : ℝ) (k : ℕ → ℝ) : ℝ :=
  ∑' t, β ^ t * u (consumption f δ k t)

theorem Primitives.f_strictMono (P : Primitives f u β δ) : StrictMonoOn f (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) P.f_cont
    (fun k hk => by rw [interior_Ici] at hk; exact P.f_prime_pos k hk)

theorem Primitives.u_strictMono (P : Primitives f u β δ) : StrictMonoOn u (Ici 0) :=
  strictMonoOn_of_deriv_pos (convex_Ici 0) P.u_cont
    (fun c hc => by rw [interior_Ici] at hc; exact P.u_prime_pos c hc)

theorem Primitives.resources_strictMono (P : Primitives f u β δ) :
    StrictMonoOn (resources f δ) (Ici 0) := by
  intro a ha b hb hab
  have h1 := P.f_strictMono ha hb hab
  have h2 := mul_le_mul_of_nonneg_left hab.le (sub_nonneg.mpr P.δ_le_one)
  simp only [resources]
  linarith

theorem Primitives.resources_cont (P : Primitives f u β δ) :
    ContinuousOn (resources f δ) (Ici 0) :=
  P.f_cont.add (continuousOn_const.mul continuousOn_id)

theorem resources_zero (P : Primitives f u β δ) : resources f δ 0 = 0 := by
  simp [resources, P.f_zero]

theorem Primitives.resources_nonneg (P : Primitives f u β δ) {k : ℝ} (hk : 0 ≤ k) :
    0 ≤ resources f δ k := by
  rw [← resources_zero P]
  exact P.resources_strictMono.monotoneOn (mem_Ici.mpr le_rfl) hk hk

/-- A capacity beyond which resources do not exceed capital. -/
theorem Primitives.exists_capacity (P : Primitives f u β δ) :
    ∃ K, 0 < K ∧ ∀ k, K ≤ k → resources f δ k ≤ k := by
  obtain ⟨K, hK1, hK⟩ := exists_capacity_of_marginal_tendsto_zero f (k0 := 1) P.δ_pos
    P.f_conc.concaveOn P.f_diff (fun k hk => (P.f_prime_pos k hk).le) P.f_inadaTop
  refine ⟨K, lt_of_lt_of_le one_pos hK1, fun k hk => ?_⟩
  have := hK k hk
  simp only [resources]
  linarith

/-- The capital bound used for paths from `k₀`. -/
noncomputable def bound (P : Primitives f u β δ) (k₀ : ℝ) : ℝ :=
  max k₀ (Classical.choose P.exists_capacity)

theorem bound_spec (P : Primitives f u β δ) (k₀ : ℝ) :
    k₀ ≤ bound P k₀ ∧ 0 < bound P k₀ ∧ resources f δ (bound P k₀) ≤ bound P k₀ := by
  obtain ⟨hK, hcap⟩ := Classical.choose_spec P.exists_capacity
  exact ⟨le_max_left _ _, lt_of_lt_of_le hK (le_max_right _ _),
    hcap _ (le_max_right _ _)⟩

theorem Feasible.nonneg {k₀ : ℝ} {k : ℕ → ℝ} (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) (t : ℕ) :
    0 ≤ k t := by
  cases t with
  | zero => rw [hk.1]; exact hk₀
  | succ t => exact (hk.2 t).1

/-- Every feasible path stays below the bound. -/
theorem Feasible.le_bound (P : Primitives f u β δ) {k₀ : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) (t : ℕ) : k t ≤ bound P k₀ := by
  obtain ⟨h1, h2, h3⟩ := bound_spec P k₀
  induction t with
  | zero => rw [hk.1]; exact h1
  | succ t ih =>
    exact (hk.2 t).2.trans ((P.resources_strictMono.monotoneOn (hk.nonneg hk₀ t)
      h2.le ih).trans h3)

theorem Feasible.consumption_mem (P : Primitives f u β δ) {k₀ : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) (t : ℕ) :
    consumption f δ k t ∈ Icc 0 (bound P k₀) := by
  obtain ⟨-, h2, h3⟩ := bound_spec P k₀
  refine ⟨sub_nonneg.mpr (hk.2 t).2, ?_⟩
  have := (P.resources_strictMono.monotoneOn (hk.nonneg hk₀ t) h2.le
    (hk.le_bound P hk₀ t)).trans h3
  have := (hk.2 t).1
  simp only [consumption]
  linarith

/-- A uniform bound on utility over the consumption range of paths from `k₀`. -/
theorem exists_utility_bound (P : Primitives f u β δ) (k₀ : ℝ) :
    ∃ M, ∀ c ∈ Icc 0 (bound P k₀), |u c| ≤ M := by
  obtain ⟨x, _, hx⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (bound_spec P k₀).2.1.le) ((P.u_cont.mono Icc_subset_Ici_self).norm)
  exact ⟨‖u x‖, fun c hc => hx hc⟩

theorem Feasible.summable (P : Primitives f u β δ) {k₀ : ℝ} {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) (hk₀ : 0 ≤ k₀) :
    Summable (fun t => β ^ t * u (consumption f δ k t)) := by
  obtain ⟨M, hM⟩ := exists_utility_bound P k₀
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one P.β_pos.le P.β_lt_one).mul_right M) (fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos P.β_pos t)]
  exact mul_le_mul_of_nonneg_left (hM _ (hk.consumption_mem P hk₀ t)) (pow_pos P.β_pos t).le

/-- The path that consumes everything after the first period is feasible. -/
theorem feasible_consume_all (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    Feasible f δ k₀ (fun t => if t = 0 then k₀ else 0) := by
  refine ⟨rfl, fun t => ⟨le_rfl, ?_⟩⟩
  cases t with
  | zero => exact P.resources_nonneg hk₀
  | succ t => simp [resources_zero P]

/-- The feasible set from `k₀` as a subset of the sequence space. -/
def feasibleSet (f : ℝ → ℝ) (δ k₀ : ℝ) : Set (ℕ → ℝ) := {k | Feasible f δ k₀ k}

theorem isCompact_feasibleSet (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    IsCompact (feasibleSet f δ k₀) := by
  -- the continuous extension of `f` to the whole line
  set fe : ℝ → ℝ := fun x => f (max x 0)
  have hfe : Continuous fe := P.f_cont.comp_continuous (continuous_id.max continuous_const)
    (fun x => le_max_right x 0)
  have heq : feasibleSet f δ k₀ = {k | k 0 = k₀} ∩ ⋂ t, ({k : ℕ → ℝ | 0 ≤ k (t + 1)} ∩
      {k | k (t + 1) ≤ fe (k t) + (1 - δ) * k t}) := by
    ext k
    simp only [feasibleSet, Feasible, mem_ofPred_eq, mem_inter_iff, mem_iInter]
    constructor
    · rintro ⟨h0, h⟩
      refine ⟨h0, fun t => ⟨(h t).1, ?_⟩⟩
      have hnn : 0 ≤ k t := Feasible.nonneg ⟨h0, h⟩ hk₀ t
      simp only [fe, max_eq_left hnn]
      exact (h t).2
    · rintro ⟨h0, h⟩
      have hnn : ∀ t, 0 ≤ k t := by
        intro t
        cases t with
        | zero => rw [h0]; exact hk₀
        | succ t => exact (h t).1
      refine ⟨h0, fun t => ⟨(h t).1, ?_⟩⟩
      have := (h t).2
      simp only [fe, max_eq_left (hnn t)] at this
      exact this
  have hclosed : IsClosed (feasibleSet f δ k₀) := by
    rw [heq]
    refine (isClosed_eq (continuous_apply 0) continuous_const).inter (isClosed_iInter fun t => ?_)
    exact (isClosed_le continuous_const (continuous_apply (t + 1))).inter
      (isClosed_le (continuous_apply (t + 1)) ((hfe.comp (continuous_apply t)).add
        (continuous_const.mul (continuous_apply t))))
  have hbox : feasibleSet f δ k₀ ⊆ Set.pi univ (fun _ => Icc 0 (bound P k₀)) := by
    intro k hk _ _
    exact ⟨Feasible.nonneg hk hk₀ _, Feasible.le_bound P hk hk₀ _⟩
  exact (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset hclosed hbox

theorem continuousOn_welfare (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    ContinuousOn (welfare f u β δ) (feasibleSet f δ k₀) := by
  obtain ⟨M, hM⟩ := exists_utility_bound P k₀
  apply continuousOn_tsum (u := fun t => β ^ t * M)
  · intro t
    apply continuousOn_const.mul
    apply P.u_cont.comp
    · apply ContinuousOn.sub _ (continuous_apply (t + 1)).continuousOn
      exact (P.resources_cont.comp (continuous_apply t).continuousOn
        (fun k hk => Feasible.nonneg hk hk₀ t))
    · exact fun k hk => (Feasible.consumption_mem P hk hk₀ t).1
  · exact (summable_geometric_of_lt_one P.β_pos.le P.β_lt_one).mul_right M
  · intro t k hk
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos P.β_pos t)]
    exact mul_le_mul_of_nonneg_left (hM _ (Feasible.consumption_mem P hk hk₀ t))
      (pow_pos P.β_pos t).le

/-- An optimal path exists from every nonnegative stock. -/
theorem exists_optimal (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    ∃ k, Feasible f δ k₀ k ∧
      ∀ k', Feasible f δ k₀ k' → welfare f u β δ k' ≤ welfare f u β δ k := by
  obtain ⟨k, hk, hmax⟩ := (isCompact_feasibleSet P hk₀).exists_isMaxOn
    ⟨fun t => if t = 0 then k₀ else 0, (feasible_consume_all P hk₀ : _)⟩
    (continuousOn_welfare P hk₀)
  exact ⟨k, hk, fun k' hk' => hmax hk'⟩

/-- The optimal path from `k₀ ≥ 0` (chosen). -/
noncomputable def optimalPath (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) : ℕ → ℝ :=
  Classical.choose (exists_optimal P hk₀)

theorem optimalPath_spec (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    Feasible f δ k₀ (optimalPath P hk₀) ∧ ∀ k', Feasible f δ k₀ k' →
      welfare f u β δ k' ≤ welfare f u β δ (optimalPath P hk₀) :=
  Classical.choose_spec (exists_optimal P hk₀)

/-- The value function. -/
noncomputable def value (P : Primitives f u β δ) (k₀ : ℝ) : ℝ :=
  if hk₀ : 0 ≤ k₀ then welfare f u β δ (optimalPath P hk₀) else 0

theorem value_eq (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) :
    value P k₀ = welfare f u β δ (optimalPath P hk₀) := by
  simp only [value, hk₀, ↓reduceDIte]

theorem welfare_le_value (P : Primitives f u β δ) {k₀ : ℝ} (hk₀ : 0 ≤ k₀) {k : ℕ → ℝ}
    (hk : Feasible f δ k₀ k) : welfare f u β δ k ≤ value P k₀ := by
  rw [value_eq P hk₀]
  exact (optimalPath_spec P hk₀).2 k hk

end RamseyCassKoopmans.DiscreteTime
