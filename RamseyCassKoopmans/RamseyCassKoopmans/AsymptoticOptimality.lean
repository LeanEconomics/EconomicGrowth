import RamseyCassKoopmans.Verification

/-! # Welfare dominance without assuming competitor welfare convergence

The comparison is defined using finite-horizon integrals: for every positive
epsilon, the competitor's welfare advantage is eventually less than epsilon.
This includes competitors whose lifetime utility diverges or has no real limit.
It is not an assertion that each competitor has finite lifetime welfare.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

def AsymptoticallyDominates (U w ca cb : ℝ → ℝ) : Prop :=
  ∀ ε, 0 < ε → ∀ᶠ T in atTop, welfare U w cb T - welfare U w ca T < ε

theorem asymptotic_dominance_of_terminal_limit
    {f U w : ℝ → ℝ} {m : ℝ} {a : FeasiblePath f m}
    (v : SupportingPrices f U w m a) (b : FeasiblePath f m)
    (halloc : AllocationComparison v b) (hinit : a.capital 0 = b.capital 0)
    (hterminal : Tendsto (boundary v.price a.capital b.capital) atTop (𝓝 0)) :
    AsymptoticallyDominates U w a.consumption b.consumption := by
  intro ε hε
  filter_upwards [eventually_ge_atTop (0 : ℝ), hterminal.eventually (gt_mem_nhds hε)] with T hT hB
  exact (finite_horizon_comparison v b halloc hinit hT).trans_lt hB

theorem AsymptoticallyDominates.finite_welfare_le {U w ca cb : ℝ → ℝ} {Ja Jb : ℝ}
    (h : AsymptoticallyDominates U w ca cb) (ha : HasWelfare U w ca Ja)
    (hb : HasWelfare U w cb Jb) : Jb ≤ Ja := by
  by_contra hn
  have hp : 0 < (Jb - Ja) / 2 := half_pos (sub_pos.mpr (lt_of_not_ge hn))
  have hh : Jb - Ja ≤ (Jb - Ja) / 2 :=
    le_of_tendsto (hb.sub ha) ((h _ hp).mono (fun _ hx => hx.le))
  linarith

end RamseyCassKoopmans
