import RamseyCassKoopmans.CooperativeFlow
import RamseyCassKoopmans.Shooting

/-! # Constructing a trajectory between the two equilibrium escape quadrants -/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.ODE

def lowerQuadrant (a : ℝ × ℝ) : Set (ℝ × ℝ) := {x | x.1 < a.1 ∧ x.2 < a.2}
def upperQuadrant (a : ℝ × ℝ) : Set (ℝ × ℝ) := {x | a.1 < x.1 ∧ a.2 < x.2}

theorem isOpen_lowerQuadrant (a : ℝ × ℝ) : IsOpen (lowerQuadrant a) :=
  (isOpen_lt continuous_fst continuous_const).inter (isOpen_lt continuous_snd continuous_const)

theorem isOpen_upperQuadrant (a : ℝ × ℝ) : IsOpen (upperQuadrant a) :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_const continuous_snd)

theorem disjoint_quadrants (a : ℝ × ℝ) : Disjoint (lowerQuadrant a) (upperQuadrant a) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact lt_asymm hx.1 hy.1

/-- The two endpoint hypotheses concern escape of ordinary initial-value
solutions. The nonescaping trajectory in the conclusion is constructed. -/
theorem exists_solution_avoiding_quadrants
    {v : ℝ × ℝ → ℝ × ℝ} {L K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) (hbound : ∀ x, ‖v x‖ ≤ L)
    {a : ℝ × ℝ} (ha : v a = 0)
    (initial : ℝ → ℝ × ℝ) (hi : Continuous initial) {l r : ℝ} (hlr : l ≤ r)
    (hleft : ∀ γ : ℝ → ℝ × ℝ, γ 0 = initial l →
      (∀ t, HasDerivAt γ (v (γ t)) t) → ∃ t, 0 ≤ t ∧ γ t ∈ lowerQuadrant a)
    (hright : ∀ γ : ℝ → ℝ × ℝ, γ 0 = initial r →
      (∀ t, HasDerivAt γ (v (γ t)) t) → ∃ t, 0 ≤ t ∧ γ t ∈ upperQuadrant a) :
    ∃ q ∈ Icc l r, ∃ γ : ℝ → ℝ × ℝ,
      γ 0 = initial q ∧ (∀ t, HasDerivAt γ (v (γ t)) t) ∧
      ∀ t, 0 ≤ t → γ t ∉ lowerQuadrant a ∪ upperQuadrant a := by
  obtain ⟨φ, h0, hφ, hcont⟩ := exists_global_flow hl hbound
  have hlow : ∀ x ∈ lowerQuadrant a, ∀ t, 0 ≤ t → φ x t ∈ lowerQuadrant a := by
    intro x hx
    apply solution_lt_equilibrium hc hl ha (hφ x)
    simpa only [h0 x] using (show x.1 < a.1 ∧ x.2 < a.2 from hx)
  have hupp : ∀ x ∈ upperQuadrant a, ∀ t, 0 ≤ t → φ x t ∈ upperQuadrant a := by
    intro x hx
    apply solution_gt_equilibrium hc hl ha (hφ x)
    simpa only [h0 x] using (show a.1 < x.1 ∧ a.2 < x.2 from hx)
  obtain ⟨q, hq, havoid⟩ := exists_avoiding_exits φ initial hcont
    (flow_add hl φ h0 hφ) hi (isOpen_lowerQuadrant a) (isOpen_upperQuadrant a)
    (disjoint_quadrants a) hlow hupp hlr
    (hleft _ (h0 _) (hφ _)) (hright _ (h0 _) (hφ _))
  exact ⟨q, hq, φ (initial q), h0 _, hφ _, havoid⟩

theorem enters_lower_at_boundary {γ : ℝ → ℝ × ℝ} {a w : ℝ × ℝ}
    (hd : HasDerivAt γ w 0) (hk : (γ 0).1 < a.1) (hq : (γ 0).2 = a.2)
    (hv : w.2 < 0) : ∃ t, 0 < t ∧ γ t ∈ lowerQuadrant a := by
  have hknear : ∀ᶠ t in 𝓝 0, (γ t).1 < a.1 :=
    (hasDerivAt_fst hd).continuousAt.eventually (gt_mem_nhds hk)
  have hqnear := eventually_lt_right_of_deriv_neg (hasDerivAt_snd hd) hv
  have htnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hkt, hqt⟩ :=
    (htnear.and ((hknear.filter_mono nhdsWithin_le_nhds).and hqnear)).exists
  exact ⟨t, ht, hkt, hq ▸ hqt⟩

theorem enters_upper_at_boundary {γ : ℝ → ℝ × ℝ} {a w : ℝ × ℝ}
    (hd : HasDerivAt γ w 0) (hk : a.1 < (γ 0).1) (hq : (γ 0).2 = a.2)
    (hv : 0 < w.2) : ∃ t, 0 < t ∧ γ t ∈ upperQuadrant a := by
  have hneg : HasDerivAt (fun t => -γ t) (-w) 0 := hd.neg
  obtain ⟨t, ht, hmem⟩ := enters_lower_at_boundary (a := -a) hneg
    (neg_lt_neg hk) (congrArg Neg.neg hq) (neg_neg_of_pos hv)
  refine ⟨t, ht, ?_⟩
  simpa only [lowerQuadrant, upperQuadrant, mem_ofPred_eq, Prod.fst_neg,
    Prod.snd_neg, neg_lt_neg_iff] using hmem

end RamseyCassKoopmans.ODE
