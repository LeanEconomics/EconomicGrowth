import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Tactic.Linarith

/-!
# Global flows for bounded Lipschitz vector fields

This analytic helper constructs trajectories and continuous dependence, rather
than placing their existence in the assumptions of a shooting theorem. Economic
vector fields will be extended from compact rectangles before it is applied.
-/

open Set Filter Metric
open scoped Topology NNReal

namespace RamseyCassKoopmans.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem exists_global_solution {v : E → E} {L K : ℝ≥0}
    (hlip : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (v (γ t)) t := by
  have hlocal (T : ℝ) : ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Ioo (-(|T| + 1)) (|T| + 1), HasDerivAt γ (v (γ t)) t := by
    let a : ℝ≥0 := ⟨L * (|T| + 1), mul_nonneg L.coe_nonneg (by positivity)⟩
    have hpl : IsPicardLindelof (fun (_ : ℝ) => v)
        (⟨0, by constructor <;> linarith [abs_nonneg T]⟩ : Icc (-(|T| + 1)) (|T| + 1))
        x a 0 L K := by
      refine ⟨fun _ _ => hlip.lipschitzOnWith, fun _ _ => continuousOn_const,
        fun _ _ y _ => hbound y, ?_⟩
      change (L : ℝ) * max ((|T| + 1) - 0) (0 - -(|T| + 1)) ≤
        (L : ℝ) * (|T| + 1) - 0
      simp
    obtain ⟨γ, hγ0, hγ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨γ, hγ0, fun t ht => (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)⟩
  choose γ hγ0 hγ using hlocal
  have hagree (S T t : ℝ) (hs : |t| < |S| + 1) (ht : |t| < |T| + 1) :
      γ S t = γ T t := by
    let R := min (|S| + 1) (|T| + 1)
    have hR : 0 < R := lt_min (by positivity) (by positivity)
    apply ODE_solution_unique_of_mem_Ioo
      (v := fun (_ : ℝ) => v) (s := fun _ => univ)
      (a := -R) (b := R) (t₀ := 0) (fun _ _ => hlip.lipschitzOnWith)
      ⟨by linarith, hR⟩
      (fun u hu => ⟨hγ S u ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hu.1,
        lt_of_lt_of_le hu.2 (min_le_left _ _)⟩, mem_univ _⟩)
      (fun u hu => ⟨hγ T u ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hu.1,
        lt_of_lt_of_le hu.2 (min_le_right _ _)⟩, mem_univ _⟩)
      ((hγ0 S).trans (hγ0 T).symm)
    exact abs_lt.mp (lt_min hs ht)
  refine ⟨fun t => γ t t, hγ0 0, ?_⟩
  intro t
  apply (hγ t t (abs_lt.mp (by linarith : |t| < |t| + 1))).congr_of_eventuallyEq
  have hn : {u : ℝ | |u| < |t| + 1} ∈ 𝓝 t :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simp)
  filter_upwards [hn] with u hu
  exact hagree u t u (by linarith) hu

omit [CompleteSpace E] in
theorem flow_lipschitz_initial {v : E → E} {K : ℝ≥0}
    (hlip : LipschitzWith K v) (φ : E → ℝ → E)
    (h0 : ∀ x, φ x 0 = x)
    (hφ : ∀ x t, HasDerivAt (φ x) (v (φ x t)) t)
    {t : ℝ} (ht : 0 ≤ t) :
    LipschitzWith ⟨Real.exp (K * t), (Real.exp_pos _).le⟩ (fun x => φ x t) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have h := dist_le_of_trajectories_ODE (v := fun (_ : ℝ) => v)
    (a := 0) (b := t) (δ := dist x y) (fun _ => hlip)
    (HasDerivAt.continuousOn (fun u _ => hφ x u))
    (fun u _ => (hφ x u).hasDerivWithinAt)
    (HasDerivAt.continuousOn (fun u _ => hφ y u))
    (fun u _ => (hφ y u).hasDerivWithinAt)
    (by rw [h0, h0]) t ⟨ht, le_rfl⟩
  change dist (φ x t) (φ y t) ≤ Real.exp ((K : ℝ) * t) * dist x y
  simpa only [sub_zero, mul_comm] using h

/-- A bounded globally Lipschitz field has a globally defined family of actual
solutions, continuous in the initial point at each nonnegative time. -/
theorem exists_global_flow {v : E → E} {L K : ℝ≥0}
    (hlip : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L) :
    ∃ φ : E → ℝ → E, (∀ x, φ x 0 = x) ∧
      (∀ x t, HasDerivAt (φ x) (v (φ x t)) t) ∧
      (∀ t, 0 ≤ t → Continuous (fun x => φ x t)) := by
  choose φ h0 hφ using exists_global_solution hlip hbound
  exact ⟨φ, h0, hφ, fun _ ht => (flow_lipschitz_initial hlip φ h0 hφ ht).continuous⟩

omit [CompleteSpace E] in
theorem flow_add {v : E → E} {K : ℝ≥0}
    (hlip : LipschitzWith K v) (φ : E → ℝ → E)
    (h0 : ∀ x, φ x 0 = x)
    (hφ : ∀ x t, HasDerivAt (φ x) (v (φ x t)) t)
    (x : E) (s t : ℝ) : φ (φ x s) t = φ x (t + s) := by
  have heq : φ (φ x s) = fun u => φ x (u + s) := by
    apply ODE_solution_unique_univ (v := fun (_ : ℝ) => v)
      (s := fun _ => univ) (t₀ := 0) (fun _ => hlip.lipschitzOnWith)
      (fun u => ⟨hφ _ u, mem_univ _⟩)
    · intro u
      refine ⟨?_, mem_univ _⟩
      convert (hφ x (u + s)).scomp u ((hasDerivAt_id u).add_const s) using 1
      · rfl
      · simp only [one_smul]
    · simp only [h0, zero_add]
  exact congrFun heq t

end RamseyCassKoopmans.ODE
