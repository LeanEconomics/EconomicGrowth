/-
SPDX-License-Identifier: Unlicense
Developed with Claude (Anthropic).
-/
import RamseyCassKoopmans.CassGeneral
import RamseyCassKoopmans.TailWelfare

/-!
# Certified Cass optima, time shifts, and time consistency

`CassPrimitives` bundles the Inada and curvature assumptions of
`cass_general_dynamic`. `CassCertificate` records a current-value costate with
the wedge, complementary slackness and transversality conditions. We prove:

* `exists_certified`: from every positive stock the constructed optimum carries
  a certificate;
* `CassCertificate.isCassOptimal`, `CassCertificate.eq_of_isCassOptimal`: a
  certificate makes a path optimal, and every optimum with the same initial stock
  coincides with it;
* `FeasiblePath.shift`, `CassCertificate.shift`: the tail of a certified path
  after any date is a certified path from the stock it has reached;
* `CassCertificate.dynamics`: every certified path converges monotonically to the
  steady state (transferred from the construction by uniqueness);
* `CassCertificate.tail_eq`: time consistency, the tail of an optimum is the
  optimum from the stock reached.
-/

open Set Filter
open scoped Topology

namespace RamseyCassKoopmans

variable {f U : ℝ → ℝ} {d m : ℝ}

/-- The primitive assumptions of `cass_general_dynamic`. -/
structure CassPrimitives (f U : ℝ → ℝ) (d m : ℝ) : Prop where
  d_pos : 0 < d
  m_pos : 0 < m
  f_conc : StrictConcaveOn ℝ (Ici 0) f
  f_zero : f 0 = 0
  f_diff : ∀ k, 0 < k → DifferentiableAt ℝ f k
  f_prime_cont : ContinuousOn (deriv f) (Ioi 0)
  f_prime_pos : ∀ k, 0 < k → 0 < deriv f k
  f_second : ∀ k, 0 < k → DifferentiableAt ℝ (deriv f) k
  f_second_cont : ContinuousOn (deriv (deriv f)) (Ioi 0)
  f_inada0 : Tendsto (deriv f) (𝓝[>] (0 : ℝ)) atTop
  f_inadaTop : Tendsto (deriv f) atTop (𝓝 (0 : ℝ))
  U_conc : StrictConcaveOn ℝ (Ioi 0) U
  U_diff : ∀ c, 0 < c → DifferentiableAt ℝ U c
  U_prime_pos : ∀ c, 0 < c → 0 < deriv U c
  U_second : ∀ c, 0 < c → DifferentiableAt ℝ (deriv U) c
  U_second_cont : ContinuousOn (deriv (deriv U)) (Ioi 0)
  U_second_neg : ∀ c, 0 < c → deriv (deriv U) c < 0
  U_inada0 : Tendsto (deriv U) (𝓝[>] (0 : ℝ)) atTop

theorem CassPrimitives.U_cont (P : CassPrimitives f U d m) : ContinuousOn U (Ioi 0) :=
  fun c hc => (P.U_diff c hc).continuousAt.continuousWithinAt

theorem CassPrimitives.U_prime_cont (P : CassPrimitives f U d m) :
    ContinuousOn (deriv U) (Ioi 0) :=
  fun c hc => (P.U_second c hc).continuousAt.continuousWithinAt

theorem CassPrimitives.existsUnique_steady (P : CassPrimitives f U d m) :
    ∃! k : ℝ, 0 < k ∧ deriv f k = d + m :=
  existsUnique_stationary_capital_of_inada f d m (add_pos P.d_pos P.m_pos) P.f_conc
    P.f_diff P.f_prime_cont P.f_inada0 P.f_inadaTop

/-- The modified-Golden-Rule steady state, `f'(k*) = d + m`. -/
noncomputable def cassSteady (P : CassPrimitives f U d m) : ℝ :=
  Classical.choose P.existsUnique_steady.exists

theorem cassSteady_spec (P : CassPrimitives f U d m) :
    0 < cassSteady P ∧ deriv f (cassSteady P) = d + m :=
  Classical.choose_spec P.existsUnique_steady.exists

theorem cassSteady_eq (P : CassPrimitives f U d m) {k : ℝ} (hk : 0 < k)
    (he : deriv f k = d + m) : cassSteady P = k :=
  P.existsUnique_steady.unique (cassSteady_spec P) ⟨hk, he⟩

theorem CassPrimitives.exists_capacity (P : CassPrimitives f U d m) (k0 : ℝ) :
    ∃ K, k0 ≤ K ∧ ∀ k, K ≤ k → f k ≤ m * k :=
  exists_capacity_of_marginal_tendsto_zero f P.m_pos P.f_conc.concaveOn P.f_diff
    (fun k hk => (P.f_prime_pos k hk).le) P.f_inadaTop

/-- A current-value costate certifying a Cass path: the costate equation, the
investment wedge, complementary slackness, transversality and finite welfare. -/
structure CassCertificate (f U : ℝ → ℝ) (d m : ℝ) (a : FeasiblePath f m) (q : ℝ → ℝ) : Prop where
  capital_pos : ∀ t, 0 ≤ t → 0 < a.capital t
  investment_nonneg : a.NonnegativeInvestment
  price_nonneg : ∀ t, 0 ≤ t → 0 ≤ q t
  costate : ∀ t, 0 ≤ t → HasDerivAt q
    ((d + m) * q t - deriv U (a.consumption t) * deriv f (a.capital t)) t
  wedge : ∀ t, 0 ≤ t → q t ≤ deriv U (a.consumption t)
  slack : ∀ t, 0 ≤ t → (q t - deriv U (a.consumption t)) * a.investment t = 0
  transversality : Tendsto (fun t => discount d t * q t) atTop (𝓝 0)
  welfare : ∃ J, HasWelfare U (discount d) a.consumption J

/-- From every positive stock, the constructed optimum carries a certificate. -/
theorem exists_certified (P : CassPrimitives f U d m) {k0 : ℝ} (hk0 : 0 < k0) :
    ∃ a : FeasiblePath f m, ∃ q : ℝ → ℝ, a.capital 0 = k0 ∧ CassCertificate f U d m a q := by
  obtain ⟨ks, _, _, ⟨D⟩⟩ := exists_cass_data_of_inada f U d m k0 P.d_pos P.m_pos hk0
    P.f_conc P.f_zero P.f_diff P.f_prime_cont P.f_prime_pos P.f_second P.f_second_cont
    P.f_inada0 P.f_inadaTop P.U_conc P.U_diff P.U_prime_pos P.U_second P.U_second_cont
    P.U_second_neg P.U_inada0
  let p := D.phase
  obtain ⟨_, _, hCLip, _⟩ := D.demand_bounded
  obtain ⟨_, _, hFLip, _⟩ := D.production_bounded
  obtain ⟨γ, h0, hd, hclipq, hlim, -, -, -⟩ := p.exists_convergent_trajectory
    D.bounded D.net_mono D.consumption_mem D.net_gap D.time_nonneg D.price_large
    D.time_large D.initial_mem
  have hclip := fun t ht => (hclipq t ht).1
  have hmul : p.μ = deriv U := D.marginalUtility_eq
  have hmp : p.mp = deriv p.f := by rw [D.production_eq]; exact D.marginalProduct_eq
  have hres : ∃ a : FeasiblePath p.f p.m, ∃ q : ℝ → ℝ, a.capital 0 = k0 ∧
      CassCertificate p.f U p.d p.m a q := by
    let a := p.feasiblePath γ hCLip.continuous hFLip.continuous hd hclip
    have hcostate := p.path_costate hd hclip
    rw [hmp, hmul] at hcostate
    have hwedge := p.path_wedge_slack hclip
    rw [hmul] at hwedge
    refine ⟨a, fun t => (γ t).2, h0, ⟨p.path_capital_pos γ hclip,
      fun t _ => cass_investment_nonneg p.f p.C (p.point (γ t)), ?_, hcostate,
      fun t ht => (hwedge t ht).1, fun t ht => (hwedge t ht).2,
      Terminal.discounted_price_tendsto_zero p.d_pos hlim.snd_nhds, ?_⟩⟩
    · intro t ht
      have hq := congrArg Prod.snd (hclip t ht)
      exact hq ▸ (p.price_mem (γ t).2).1
    · exact exists_hasWelfare_of_compact_consumption U a.consumption p.d_pos p.ca_le_cb
        (P.U_cont.mono (fun _ hx => p.ca_pos.trans_le hx.1)) a.consumption_continuous
        (fun t _ => p.consumption_mem (γ t))
  rw [D.production_eq, D.dilution_eq, D.discount_eq] at hres
  exact hres

/-- A certificate makes the path optimal in the library's Cass class. -/
theorem CassCertificate.isCassOptimal (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) {J : ℝ}
    (hJ : HasWelfare U (discount d) a.consumption J) : IsCassOptimal U d a J := by
  obtain ⟨K, hK, hcap⟩ := P.exists_capacity (a.capital 0)
  exact cass_certificate_is_optimal f U q d m K J a P.f_conc.concaveOn P.U_conc.concaveOn
    P.U_cont P.f_diff P.U_diff P.f_prime_cont P.U_prime_cont hc.capital_pos hc.price_nonneg
    hc.costate hc.wedge hc.slack hc.investment_nonneg hcap hK hJ hc.transversality

/-- Every optimum with the same initial stock coincides with a certified path. -/
theorem CassCertificate.eq_of_isCassOptimal (P : CassPrimitives f U d m)
    {a b : FeasiblePath f m} {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) {Ja Jb : ℝ}
    (ha : HasWelfare U (discount d) a.consumption Ja) (hb : IsCassOptimal U d b Jb)
    (hi : a.capital 0 = b.capital 0) :
    Jb = Ja ∧ ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
      b.consumption t = a.consumption t ∧ b.investment t = a.investment t := by
  obtain ⟨K, hK, hcap⟩ := P.exists_capacity (a.capital 0)
  have hopt := hc.isCassOptimal P ha
  have heq : Jb = Ja := le_antisymm (hopt.2.2 b hb.1 hi Jb hb.2.1)
    (hb.2.2 a hc.investment_nonneg hi.symm Ja ha)
  refine ⟨heq, cass_certificate_unique f U q d m K Ja Jb a b P.f_conc P.U_conc P.U_cont
    P.f_diff P.U_diff P.f_prime_cont P.U_prime_cont hc.capital_pos ?_ hc.costate hc.wedge
    hc.slack hb.1 hi hcap hK ha hb.2.1 hc.transversality heq⟩
  exact fun t ht => P.U_prime_pos _ (a.consumption_pos t ht)

/-- Two certified paths from the same stock coincide at every nonnegative time. -/
theorem CassCertificate.eq (P : CassPrimitives f U d m) {a b : FeasiblePath f m}
    {qa qb : ℝ → ℝ} (ha : CassCertificate f U d m a qa) (hb : CassCertificate f U d m b qb)
    (hi : a.capital 0 = b.capital 0) :
    ∀ t, 0 ≤ t → b.capital t = a.capital t ∧
      b.consumption t = a.consumption t ∧ b.investment t = a.investment t := by
  obtain ⟨Ja, hJa⟩ := ha.welfare
  obtain ⟨Jb, hJb⟩ := hb.welfare
  exact (ha.eq_of_isCassOptimal P hJa (hb.isCassOptimal P hJb) hi).2

/-- The path from date `T` on, re-indexed to start at time zero. -/
noncomputable def FeasiblePath.shift (a : FeasiblePath f m) (T : ℝ) (hT : 0 ≤ T) :
    FeasiblePath f m where
  capital := fun t => a.capital (T + t)
  consumption := fun t => a.consumption (T + t)
  investment := fun t => a.investment (T + t)
  capital_nonneg := fun _ ht => a.capital_nonneg _ (add_nonneg hT ht)
  consumption_pos := fun _ ht => a.consumption_pos _ (add_nonneg hT ht)
  consumption_continuous := a.consumption_continuous.comp
    (continuous_const.add continuous_id).continuousOn
    (fun _ ht => add_nonneg hT (mem_Ici.mp ht))
  investment_continuous := a.investment_continuous.comp
    (continuous_const.add continuous_id).continuousOn
    (fun _ ht => add_nonneg hT (mem_Ici.mp ht))
  resource := fun _ ht => a.resource _ (add_nonneg hT ht)
  dynamics := fun t ht => (a.dynamics _ (add_nonneg hT ht)).comp_const_add T t

@[simp] theorem FeasiblePath.shift_capital (a : FeasiblePath f m) {T : ℝ} (hT : 0 ≤ T)
    (t : ℝ) : (a.shift T hT).capital t = a.capital (T + t) := rfl

@[simp] theorem FeasiblePath.shift_consumption (a : FeasiblePath f m) {T : ℝ} (hT : 0 ≤ T)
    (t : ℝ) : (a.shift T hT).consumption t = a.consumption (T + t) := rfl

@[simp] theorem FeasiblePath.shift_investment (a : FeasiblePath f m) {T : ℝ} (hT : 0 ≤ T)
    (t : ℝ) : (a.shift T hT).investment t = a.investment (T + t) := rfl

/-- Welfare of the tail: `W_tail = (J - W(T)) / discount T`. -/
theorem hasWelfare_shift (P : CassPrimitives f U d m) (a : FeasiblePath f m) {T J : ℝ}
    (hT : 0 ≤ T) (hJ : HasWelfare U (discount d) a.consumption J) :
    HasWelfare U (discount d) (a.shift T hT).consumption
      ((J - welfare U (discount d) a.consumption T) / discount d T) := by
  have hcont : ContinuousOn (fun t => discount d t * U (a.consumption t)) (Ici 0) :=
    (discount_continuous d).continuousOn.mul
      (P.U_cont.comp a.consumption_continuous (fun t ht => a.consumption_pos t ht))
  have hsplit : ∀ s, 0 ≤ s → welfare U (discount d) (a.shift T hT).consumption s =
      (welfare U (discount d) a.consumption (T + s) -
        welfare U (discount d) a.consumption T) / discount d T := by
    intro s hs
    have h := welfare_of_tail_eq (tail := (a.shift T hT).consumption) (T := T + s) hT
      (by linarith) hcont (fun t ht => by
        simp only [FeasiblePath.shift_consumption]
        congr 1
        ring)
    rw [show T + s - T = s by ring] at h
    rw [h]
    field_simp [(discount_pos d T).ne']
    ring
  have hlim : Tendsto (fun s => (welfare U (discount d) a.consumption (T + s) -
      welfare U (discount d) a.consumption T) / discount d T) atTop
      (𝓝 ((J - welfare U (discount d) a.consumption T) / discount d T)) :=
    ((hJ.comp (tendsto_atTop_add_const_left atTop T tendsto_id)).sub_const _).div_const _
  exact hlim.congr' (by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact (hsplit s hs).symm)

/-- The tail of a certified path is certified from the stock it has reached. -/
theorem CassCertificate.shift (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) {T : ℝ} (hT : 0 ≤ T) :
    CassCertificate f U d m (a.shift T hT) (fun t => q (T + t)) := by
  obtain ⟨J, hJ⟩ := hc.welfare
  refine ⟨fun t ht => hc.capital_pos _ (add_nonneg hT ht),
    fun t ht => hc.investment_nonneg _ (add_nonneg hT ht),
    fun t ht => hc.price_nonneg _ (add_nonneg hT ht),
    fun t ht => (hc.costate _ (add_nonneg hT ht)).comp_const_add T t,
    fun t ht => hc.wedge _ (add_nonneg hT ht), fun t ht => hc.slack _ (add_nonneg hT ht),
    ?_, ⟨_, hasWelfare_shift P a hT hJ⟩⟩
  have h := (hc.transversality.comp (tendsto_atTop_add_const_left atTop T tendsto_id)).const_mul
    (Real.exp (d * T))
  rw [mul_zero] at h
  refine h.congr (fun t => ?_)
  simp only [Function.comp_apply, discount, id]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Every certified path converges monotonically to the steady state; the facts are
transferred from the construction of `cass_general_dynamic` by uniqueness. -/
theorem CassCertificate.dynamics (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) :
    Tendsto a.capital atTop (𝓝 (cassSteady P)) ∧
      Tendsto a.consumption atTop
        (𝓝 (f (cassSteady P) - m * cassSteady P)) ∧
      (a.capital 0 < cassSteady P →
        StrictMonoOn a.capital (Ici 0) ∧ StrictMonoOn a.consumption (Ici 0)) ∧
      (cassSteady P < a.capital 0 →
        StrictAntiOn a.capital (Ici 0) ∧ StrictAntiOn a.consumption (Ici 0)) ∧
      (a.capital 0 = cassSteady P → ∀ t, 0 ≤ t → a.capital t = cassSteady P ∧
        a.consumption t = f (cassSteady P) - m * cassSteady P) := by
  obtain ⟨ks, hks, hstat, b, Jb, hb0, hbopt, hbk, hbc, hbmk, hbak, hbmc, hbac, -, hbconst,
    -, -, -⟩ := cass_general_dynamic f U d m (a.capital 0) P.d_pos P.m_pos (hc.capital_pos 0 le_rfl)
    P.f_conc P.f_zero P.f_diff P.f_prime_cont P.f_prime_pos P.f_second P.f_second_cont
    P.f_inada0 P.f_inadaTop P.U_conc P.U_diff P.U_prime_pos P.U_second P.U_second_cont
    P.U_second_neg P.U_inada0
  have hks' : cassSteady P = ks := cassSteady_eq P hks hstat
  obtain ⟨Ja, hJa⟩ := hc.welfare
  have heq := (hc.eq_of_isCassOptimal P hJa hbopt hb0.symm).2
  have hk : EqOn a.capital b.capital (Ici 0) := fun t ht => ((heq t ht).1).symm
  have hcon : EqOn a.consumption b.consumption (Ici 0) := fun t ht => ((heq t ht).2.1).symm
  have hev : ∀ᶠ t in atTop, t ∈ Ici (0 : ℝ) := eventually_ge_atTop 0
  rw [hks']
  refine ⟨hbk.congr' (hev.mono fun t ht => (hk ht).symm),
    hbc.congr' (hev.mono fun t ht => (hcon ht).symm), fun h => ?_, fun h => ?_, fun h t ht => ?_⟩
  · exact ⟨(hbmk h).congr hk.symm, (hbmc h).congr hcon.symm⟩
  · exact ⟨(hbak h).congr hk.symm, (hbac h).congr hcon.symm⟩
  · obtain ⟨h1, h2, -⟩ := hbconst h t
    exact ⟨(hk ht).trans h1, (hcon ht).trans h2⟩

/-- Below the steady state a certified path stays strictly below it; above, strictly
above. -/
theorem CassCertificate.capital_bounds (P : CassPrimitives f U d m) {a : FeasiblePath f m}
    {q : ℝ → ℝ} (hc : CassCertificate f U d m a q) :
    (a.capital 0 < cassSteady P → ∀ t, 0 ≤ t → a.capital t < cassSteady P ∧
      a.consumption t < f (cassSteady P) - m * cassSteady P) ∧
    (cassSteady P < a.capital 0 → ∀ t, 0 ≤ t → cassSteady P < a.capital t ∧
      f (cassSteady P) - m * cassSteady P < a.consumption t) := by
  obtain ⟨hk, hcon, hbelow, habove, -⟩ := hc.dynamics P
  have hev : ∀ t : ℝ, 0 ≤ t → ∀ᶠ s : ℝ in atTop, t + 1 ≤ s := fun t _ =>
    eventually_ge_atTop (t + 1)
  have hm1 : ∀ t, 0 ≤ t → t + 1 ∈ Ici (0 : ℝ) := fun t ht => by
    simp only [mem_Ici]; linarith
  have hms : ∀ t s : ℝ, 0 ≤ t → t + 1 ≤ s → s ∈ Ici (0 : ℝ) := fun t s ht hs => by
    simp only [mem_Ici]; linarith
  have hlt : ∀ t : ℝ, t < t + 1 := fun t => by linarith
  refine ⟨fun h t ht => ⟨?_, ?_⟩, fun h t ht => ⟨?_, ?_⟩⟩
  · have hmono := (hbelow h).1
    exact (hmono (show t ∈ Ici 0 from ht) (hm1 t ht) (hlt t)).trans_le (ge_of_tendsto hk
      ((hev t ht).mono fun s hs => hmono.monotoneOn (hm1 t ht) (hms t s ht hs) hs))
  · have hmono := (hbelow h).2
    exact (hmono (show t ∈ Ici 0 from ht) (hm1 t ht) (hlt t)).trans_le (ge_of_tendsto hcon
      ((hev t ht).mono fun s hs => hmono.monotoneOn (hm1 t ht) (hms t s ht hs) hs))
  · have hanti := (habove h).1
    exact lt_of_le_of_lt (le_of_tendsto hk ((hev t ht).mono fun s hs =>
      hanti.antitoneOn (hm1 t ht) (hms t s ht hs) hs))
      (hanti (show t ∈ Ici 0 from ht) (hm1 t ht) (hlt t))
  · have hanti := (habove h).2
    exact lt_of_le_of_lt (le_of_tendsto hcon ((hev t ht).mono fun s hs =>
      hanti.antitoneOn (hm1 t ht) (hms t s ht hs) hs))
      (hanti (show t ∈ Ici 0 from ht) (hm1 t ht) (hlt t))

end RamseyCassKoopmans
