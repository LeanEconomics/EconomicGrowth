import RamseyCassKoopmans.GlobalFlow
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.Basic

/-!
# A connected shooting interval contains a trajectory avoiding both exits

Two disjoint, open, forward-invariant exit regions cannot exhaust a connected
interval of initial conditions if its endpoints enter different exit regions.
This gives an existence argument; no selected trajectory is an assumption.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans.ODE

variable {E : Type*} [TopologicalSpace E]

def hits (φ : E → ℝ → E) (initial : ℝ → E) (U : Set E) : Set ℝ :=
  {a | ∃ t, 0 ≤ t ∧ φ (initial a) t ∈ U}

theorem isOpen_hits (φ : E → ℝ → E) (initial : ℝ → E)
    (hφ : ∀ t, 0 ≤ t → Continuous (fun x => φ x t))
    (hi : Continuous initial) {U : Set E} (hU : IsOpen U) :
    IsOpen (hits φ initial U) := by
  rw [isOpen_iff_mem_nhds]
  rintro a ⟨t, ht, ha⟩
  have hn := (hU.preimage ((hφ t ht).comp hi)).mem_nhds ha
  apply Filter.mem_of_superset hn
  intro b hb
  exact ⟨t, ht, hb⟩

omit [TopologicalSpace E] in
theorem disjoint_hits (φ : E → ℝ → E) (initial : ℝ → E)
    (hadd : ∀ x s t, φ (φ x s) t = φ x (t + s))
    {U V : Set E} (hUV : Disjoint U V)
    (hU : ∀ x ∈ U, ∀ t, 0 ≤ t → φ x t ∈ U)
    (hV : ∀ x ∈ V, ∀ t, 0 ≤ t → φ x t ∈ V) :
    Disjoint (hits φ initial U) (hits φ initial V) := by
  apply Set.disjoint_left.mpr
  rintro a ⟨s, _, hs⟩ ⟨t, _, ht⟩
  rcases le_total s t with hst | hts
  · have h := hU _ hs (t - s) (sub_nonneg.mpr hst)
    rw [hadd, sub_add_cancel] at h
    exact Set.disjoint_left.mp hUV h ht
  · have h := hV _ ht (s - t) (sub_nonneg.mpr hts)
    rw [hadd, sub_add_cancel] at h
    exact Set.disjoint_left.mp hUV hs h

/-- Shooting theorem for a continuous family of global trajectories. All exit
times are finite; the conclusion avoids both open exit regions at every time. -/
theorem exists_avoiding_exits (φ : E → ℝ → E) (initial : ℝ → E)
    (hφ : ∀ t, 0 ≤ t → Continuous (fun x => φ x t))
    (hadd : ∀ x s t, φ (φ x s) t = φ x (t + s))
    (hi : Continuous initial) {U V : Set E}
    (hUopen : IsOpen U) (hVopen : IsOpen V) (hUV : Disjoint U V)
    (hU : ∀ x ∈ U, ∀ t, 0 ≤ t → φ x t ∈ U)
    (hV : ∀ x ∈ V, ∀ t, 0 ≤ t → φ x t ∈ V)
    {a b : ℝ} (hab : a ≤ b)
    (ha : a ∈ hits φ initial U) (hb : b ∈ hits φ initial V) :
    ∃ c ∈ Icc a b, ∀ t, 0 ≤ t → φ (initial c) t ∉ U ∪ V := by
  have hdis := disjoint_hits φ initial hadd hUV hU hV
  have hncover : ¬ Icc a b ⊆ hits φ initial U ∪ hits φ initial V := by
    intro hcover
    have hleft := isPreconnected_Icc.subset_left_of_subset_union
      (isOpen_hits φ initial hφ hi hUopen) (isOpen_hits φ initial hφ hi hVopen)
      hdis hcover ⟨a, ⟨⟨le_rfl, hab⟩, ha⟩⟩
    exact Set.disjoint_left.mp hdis (hleft ⟨hab, le_rfl⟩) hb
  obtain ⟨c, hc, hnot⟩ := Set.not_subset.mp hncover
  refine ⟨c, hc, ?_⟩
  intro t ht hmem
  apply hnot
  rcases hmem with hu | hv
  · exact Or.inl ⟨t, ht, hu⟩
  · exact Or.inr ⟨t, ht, hv⟩

end RamseyCassKoopmans.ODE
