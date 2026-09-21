import RamseyCassKoopmans.Koopmans

/-! # Hamiltonian identities along regular interior Euler paths

These are identities for actual derivatives and finite integrals. They provide
an independent diagnostic for a proposed infinite-horizon Euler trajectory.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace RamseyCassKoopmans

noncomputable def currentHamiltonian (U g k c q : ℝ → ℝ) (t : ℝ) : ℝ :=
  U (c t) + q t * (g (k t) - c t)

theorem hasDerivAt_currentHamiltonian {U g k c q : ℝ → ℝ} {d gp cd t : ℝ}
    (hU : HasDerivAt U (q t) (c t)) (hg : HasDerivAt g gp (k t))
    (hk : HasDerivAt k (g (k t) - c t) t) (hc : HasDerivAt c cd t)
    (hq : HasDerivAt q ((d - gp) * q t) t) :
    HasDerivAt (currentHamiltonian U g k c q)
      (d * q t * (g (k t) - c t)) t := by
  convert (hU.comp t hc).add (hq.mul ((hg.comp t hk).sub hc)) using 1
  · rfl
  · dsimp
    ring

theorem hasDerivAt_discountedHamiltonian {U g k c q : ℝ → ℝ} {d gp cd t : ℝ}
    (hU : HasDerivAt U (q t) (c t)) (hg : HasDerivAt g gp (k t))
    (hk : HasDerivAt k (g (k t) - c t) t) (hc : HasDerivAt c cd t)
    (hq : HasDerivAt q ((d - gp) * q t) t) :
    HasDerivAt (fun s => discount d s * currentHamiltonian U g k c q s)
      (-d * (discount d t * U (c t))) t := by
  convert (hasDerivAt_discount d t).mul
    (hasDerivAt_currentHamiltonian hU hg hk hc hq) using 1
  dsimp [currentHamiltonian]
  ring

/-- A vanishing discounted primitive determines the welfare limit, rather than
assuming that the improper objective exists. -/
theorem hasWelfare_of_primitive {U c F : ℝ → ℝ} {d : ℝ}
    (hcont : ContinuousOn (fun t => U (c t)) (Ici 0))
    (hF : ∀ t, 0 ≤ t → HasDerivAt F (-(discount d t * U (c t))) t)
    (hlim : Tendsto F atTop (𝓝 0)) : HasWelfare U (discount d) c (F 0) := by
  have hid : ∀ T, 0 ≤ T → welfare U (discount d) c T = F 0 - F T := by
    intro T hT
    have hi : IntervalIntegrable (fun t => discount d t * U (c t)) volume 0 T :=
      (((discount_continuous d).continuousOn.mul hcont).mono
        (fun _ ht => ht.1)).intervalIntegrable_of_Icc hT
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hF t (by rw [uIcc_of_le hT] at ht; exact ht.1)) hi.neg
    rw [intervalIntegral.integral_neg] at heq
    change -welfare U (discount d) c T = F T - F 0 at heq
    linarith
  have h := (tendsto_const_nhds (x := F 0) (f := atTop)).sub hlim
  simp only [sub_zero] at h
  exact h.congr' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    exact (hid T hT).symm)

end RamseyCassKoopmans
