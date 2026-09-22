import RamseyCassKoopmans.PairBarrier
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Invariant quadrants for cooperative two-dimensional dynamics

Only monotonicity in the other coordinate is assumed. A coordinate need not
increase with itself, and the vector field need not be differentiable at an
investment switch. Lipschitz continuity suffices for the comparison argument.
-/

open Set Filter
open scoped Topology NNReal

namespace RamseyCassKoopmans.ODE

def Cooperative (v : ℝ × ℝ → ℝ × ℝ) : Prop :=
  (∀ k, Monotone (fun q => (v (k, q)).1)) ∧
  (∀ q, Monotone (fun k => (v (k, q)).2))

theorem hasDerivAt_fst {γ : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {t : ℝ}
    (h : HasDerivAt γ v t) : HasDerivAt (fun s => (γ s).1) v.1 t := by
  simpa using h.hasFDerivAt.fst.hasDerivAt

theorem hasDerivAt_snd {γ : ℝ → ℝ × ℝ} {v : ℝ × ℝ} {t : ℝ}
    (h : HasDerivAt γ v t) : HasDerivAt (fun s => (γ s).2) v.2 t := by
  simpa using h.hasFDerivAt.snd.hasDerivAt

theorem Cooperative.fst_le_boundary {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {x a : ℝ × ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hx : x.1 = a.1 + B) (hy : x.2 ≤ a.2 + B) :
    (v x).1 ≤ (v a).1 + K * B := by
  let b : ℝ × ℝ := (a.1 + B, a.2 + B)
  have hdist : dist b a = B := by
    simp [b, Prod.dist_eq, abs_of_nonneg hB]
  have hcomp : dist (v b).1 (v a).1 ≤ dist (v b) (v a) := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hbound := hcomp.trans (hl.dist_le_mul b a)
  rw [hdist, Real.dist_eq] at hbound
  have hfirst : (v x).1 ≤ (v b).1 := by
    dsimp only [b]
    rw [← hx]
    exact hc.1 x.1 hy
  have hdiff := (le_abs_self ((v b).1 - (v a).1)).trans hbound
  linarith

theorem Cooperative.snd_le_boundary {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {x a : ℝ × ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hx : x.1 ≤ a.1 + B) (hy : x.2 = a.2 + B) :
    (v x).2 ≤ (v a).2 + K * B := by
  let b : ℝ × ℝ := (a.1 + B, a.2 + B)
  have hdist : dist b a = B := by
    simp [b, Prod.dist_eq, abs_of_nonneg hB]
  have hcomp : dist (v b).2 (v a).2 ≤ dist (v b) (v a) := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hbound := hcomp.trans (hl.dist_le_mul b a)
  rw [hdist, Real.dist_eq] at hbound
  have hsecond : (v x).2 ≤ (v b).2 := by
    dsimp only [b]
    rw [← hy]
    exact hc.2 x.2 hx
  have hdiff := (le_abs_self ((v b).2 - (v a).2)).trans hbound
  linarith

/-- A constant supersolution bounds a trajectory. The proof uses simultaneous
strict exponential barriers and lets their size vanish. -/
theorem solution_le_supersolution {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ}
    (ha : (v a).1 ≤ 0 ∧ (v a).2 ≤ 0)
    {γ : ℝ → ℝ × ℝ} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : (γ 0).1 ≤ a.1 ∧ (γ 0).2 ≤ a.2) :
    ∀ T, 0 ≤ T → (γ T).1 ≤ a.1 ∧ (γ T).2 ≤ a.2 := by
  intro T hT
  have hbarrier (ε : ℝ) (hε : 0 < ε) :
      (γ T).1 - a.1 ≤ ε * Real.exp (((K : ℝ) + 1) * T) ∧
      (γ T).2 - a.2 ≤ ε * Real.exp (((K : ℝ) + 1) * T) := by
    let B : ℝ → ℝ := fun t => ε * Real.exp (((K : ℝ) + 1) * t)
    have hB t : HasDerivAt B (((K : ℝ) + 1) * B t) t := by
      convert (((hasDerivAt_id t).const_mul ((K : ℝ) + 1)).exp).const_mul ε using 1
      · rfl
      · dsimp [B]
        ring
    have hpos t : 0 < B t := mul_pos hε (Real.exp_pos _)
    have h := pair_le_barrier
      (fun t => (hasDerivAt_fst (hγ t)).sub_const a.1)
      (fun t => (hasDerivAt_snd (hγ t)).sub_const a.2) hB
      (by dsimp [B]; simp only [mul_zero, Real.exp_zero, mul_one]; linarith [h0.1])
      (by dsimp [B]; simp only [mul_zero, Real.exp_zero, mul_one]; linarith [h0.2])
      (T := T) ?_ ?_ T ⟨hT, le_rfl⟩
    · exact h
    · intro t _ heq hle
      have hb := hc.fst_le_boundary hl (a := a) (hpos t).le
        (show (γ t).1 = a.1 + B t by linarith)
        (show (γ t).2 ≤ a.2 + B t by linarith)
      nlinarith [hpos t, ha.1]
    · intro t _ heq hle
      have hb := hc.snd_le_boundary hl (a := a) (hpos t).le
        (show (γ t).1 ≤ a.1 + B t by linarith)
        (show (γ t).2 = a.2 + B t by linarith)
      nlinarith [hpos t, ha.2]
  have hsmall (ε : ℝ) (hε : 0 < ε) :
      (γ T).1 ≤ a.1 + ε ∧ (γ T).2 ≤ a.2 + ε := by
    have h := hbarrier (ε / Real.exp (((K : ℝ) + 1) * T)) (div_pos hε (Real.exp_pos _))
    rw [div_mul_cancel₀ ε (Real.exp_ne_zero _)] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  exact ⟨le_of_forall_pos_le_add (fun ε hε => (hsmall ε hε).1),
    le_of_forall_pos_le_add (fun ε hε => (hsmall ε hε).2)⟩

theorem solution_le_equilibrium {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ} (ha : v a = 0)
    {γ : ℝ → ℝ × ℝ} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : (γ 0).1 ≤ a.1 ∧ (γ 0).2 ≤ a.2) :
    ∀ T, 0 ≤ T → (γ T).1 ≤ a.1 ∧ (γ T).2 ≤ a.2 :=
  solution_le_supersolution hc hl (by simp [ha]) hγ h0

theorem Cooperative.fst_le_gap {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {x a : ℝ × ℝ}
    (hx : x.1 ≤ a.1) (hy : x.2 ≤ a.2) :
    (v x).1 ≤ (v a).1 + K * (a.1 - x.1) := by
  have hdist : dist (x.1, a.2) a = a.1 - x.1 := by
    simp [Prod.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx), hx]
  have hcomp : dist (v (x.1, a.2)).1 (v a).1 ≤ dist (v (x.1, a.2)) (v a) := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hbound := hcomp.trans (hl.dist_le_mul (x.1, a.2) a)
  rw [hdist, Real.dist_eq] at hbound
  have hm := hc.1 x.1 hy
  have hd := (le_abs_self ((v (x.1, a.2)).1 - (v a).1)).trans hbound
  change (v x).1 ≤ (v (x.1, a.2)).1 at hm
  linarith

theorem Cooperative.snd_le_gap {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {x a : ℝ × ℝ}
    (hx : x.1 ≤ a.1) (hy : x.2 ≤ a.2) :
    (v x).2 ≤ (v a).2 + K * (a.2 - x.2) := by
  have hdist : dist (a.1, x.2) a = a.2 - x.2 := by
    simp [Prod.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hy), hy]
  have hcomp : dist (v (a.1, x.2)).2 (v a).2 ≤ dist (v (a.1, x.2)) (v a) := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have hbound := hcomp.trans (hl.dist_le_mul (a.1, x.2) a)
  rw [hdist, Real.dist_eq] at hbound
  have hm := hc.2 x.2 hx
  have hd := (le_abs_self ((v (a.1, x.2)).2 - (v a).2)).trans hbound
  change (v x).2 ≤ (v (a.1, x.2)).2 at hm
  linarith

theorem strict_neg_of_deriv_le_mul {f df : ℝ → ℝ} {K : ℝ}
    (hf : ∀ t, HasDerivAt f (df t) t) (h0 : f 0 < 0)
    (hb : ∀ t, 0 ≤ t → df t ≤ K * f t) : ∀ T, 0 ≤ T → f T < 0 := by
  intro T hT
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (a := 0) (b := T) (δ := f 0) (K := K) (ε := 0)
    (HasDerivAt.continuousOn (fun t _ => hf t))
    (fun t _ r hr => by
      simpa only [slope_def_field, div_eq_mul_inv, mul_comm] using
        (hf t).hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl (fun t ht => by simpa only [add_zero] using hb t ht.1) T ⟨hT, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at h
  exact h.trans_lt (mul_neg_of_neg_of_pos h0 (Real.exp_pos _))

/-- The strict lower quadrant is also invariant; the Lipschitz estimate rules
out reaching a coordinate boundary in finite time. -/
theorem solution_lt_equilibrium {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ} (ha : v a = 0)
    {γ : ℝ → ℝ × ℝ} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : (γ 0).1 < a.1 ∧ (γ 0).2 < a.2) :
    ∀ T, 0 ≤ T → (γ T).1 < a.1 ∧ (γ T).2 < a.2 := by
  have hle := solution_le_equilibrium hc hl ha hγ ⟨h0.1.le, h0.2.le⟩
  have h1 := strict_neg_of_deriv_le_mul (K := -(K : ℝ))
    (fun t => (hasDerivAt_fst (hγ t)).sub_const a.1) (sub_neg.mpr h0.1)
    (fun t ht => by
      have hb := hc.fst_le_gap hl (hle t ht).1 (hle t ht).2
      rw [ha] at hb
      change (v (γ t)).1 ≤ 0 + K * (a.1 - (γ t).1) at hb
      nlinarith)
  have h2 := strict_neg_of_deriv_le_mul (K := -(K : ℝ))
    (fun t => (hasDerivAt_snd (hγ t)).sub_const a.2) (sub_neg.mpr h0.2)
    (fun t ht => by
      have hb := hc.snd_le_gap hl (hle t ht).1 (hle t ht).2
      rw [ha] at hb
      change (v (γ t)).2 ≤ 0 + K * (a.2 - (γ t).2) at hb
      nlinarith)
  exact fun T hT => ⟨sub_neg.mp (h1 T hT), sub_neg.mp (h2 T hT)⟩

def reflected (v : ℝ × ℝ → ℝ × ℝ) (x : ℝ × ℝ) : ℝ × ℝ := -v (-x)

theorem Cooperative.reflected {v : ℝ × ℝ → ℝ × ℝ} (hc : Cooperative v) :
    Cooperative (reflected v) := by
  constructor
  · intro k q₁ q₂ hq
    change -(v (-k, -q₁)).1 ≤ -(v (-k, -q₂)).1
    exact neg_le_neg (hc.1 (-k) (neg_le_neg hq))
  · intro q k₁ k₂ hk
    change -(v (-k₁, -q)).2 ≤ -(v (-k₂, -q)).2
    exact neg_le_neg (hc.2 (-q) (neg_le_neg hk))

theorem lipschitz_reflected {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hl : LipschitzWith K v) : LipschitzWith K (reflected v) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [reflected, dist_neg_neg] using hl.dist_le_mul (-x) (-y)

theorem solution_gt_equilibrium {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ} (ha : v a = 0)
    {γ : ℝ → ℝ × ℝ} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : a.1 < (γ 0).1 ∧ a.2 < (γ 0).2) :
    ∀ T, 0 ≤ T → a.1 < (γ T).1 ∧ a.2 < (γ T).2 := by
  have hr : reflected v (-a) = 0 := by simp only [reflected, neg_neg, ha, neg_zero]
  have hd : ∀ t, HasDerivAt (fun t => -γ t) (reflected v (-γ t)) t := by
    intro t
    convert (hγ t).neg using 1
    simp only [reflected, neg_neg]
  have hh := solution_lt_equilibrium hc.reflected (lipschitz_reflected hl) hr hd
    (show (-γ 0).1 < (-a).1 ∧ (-γ 0).2 < (-a).2 from
      ⟨neg_lt_neg h0.1, neg_lt_neg h0.2⟩)
  intro T hT
  simpa only [Prod.fst_neg, Prod.snd_neg, neg_lt_neg_iff] using hh T hT

theorem solution_ge_subsolution {v : ℝ × ℝ → ℝ × ℝ} {K : ℝ≥0}
    (hc : Cooperative v) (hl : LipschitzWith K v) {a : ℝ × ℝ}
    (ha : 0 ≤ (v a).1 ∧ 0 ≤ (v a).2)
    {γ : ℝ → ℝ × ℝ} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (h0 : a.1 ≤ (γ 0).1 ∧ a.2 ≤ (γ 0).2) :
    ∀ T, 0 ≤ T → a.1 ≤ (γ T).1 ∧ a.2 ≤ (γ T).2 := by
  have hr : (reflected v (-a)).1 ≤ 0 ∧ (reflected v (-a)).2 ≤ 0 := by
    simpa only [reflected, neg_neg, Prod.fst_neg, Prod.snd_neg, neg_nonpos] using ha
  have hd : ∀ t, HasDerivAt (fun t => -γ t) (reflected v (-γ t)) t := by
    intro t
    convert (hγ t).neg using 1
    simp only [reflected, neg_neg]
  have hh := solution_le_supersolution hc.reflected (lipschitz_reflected hl) hr hd
    (show (-γ 0).1 ≤ (-a).1 ∧ (-γ 0).2 ≤ (-a).2 from
      ⟨neg_le_neg h0.1, neg_le_neg h0.2⟩)
  intro T hT
  simpa only [Prod.fst_neg, Prod.snd_neg, neg_le_neg_iff] using hh T hT

end RamseyCassKoopmans.ODE
