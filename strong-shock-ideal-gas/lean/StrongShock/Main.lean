/-
  Main results: limiting spectral stability on the region `ℛ` of Theorem 1.1, and the
  passage to sufficiently strong finite shocks (Corollary 1.2).
  External inputs from [HLZ] appear as explicit hypotheses (see README).
-/
import StrongShock.WeightedDecay
import StrongShock.Endpoint
import StrongShock.ZeroFrequency
import StrongShock.Finite

open Filter Topology Set

namespace StrongShock

noncomputable section

namespace LimitingProfile
variable {g n : ℝ} (P : LimitingProfile g n)

lemma s_bot (hg : 0 < g) : Tendsto P.s atBot (𝓝 1) := by
  have := ((P.V_bot.const_mul (g + 2)).sub_const g).div_const 2
  have e : ((g + 2) * 1 - g) / 2 = 1 := by ring
  rw [e] at this; exact this

lemma z_top' : Tendsto P.z atTop (𝓝 P.zlim) := by
  have := P.z_top; unfold z s; exact this

lemma slope (hg : 0 < g) (hn : 0 < n) (x : ℝ) : InSlope g n ((P.toSZ hg hn).z x) :=
  SZTraj.slope_interval hg hn (P.toSZ hg hn) P.zlim_pos P.z_top' (P.s_top hg) x

lemma z_pos (hg : 0 < g) (hn : 0 < n) (x : ℝ) : 0 < (P.toSZ hg hn).z x :=
  lt_of_lt_of_le (lt_min (by positivity) (by positivity)) (P.slope hg hn x).1

end LimitingProfile

/-- The trivial-solution conclusion. -/
def Trivial {g n : ℝ} {T : SZTraj g n} {lam : ℂ} (S : EigenSol T lam) : Prop :=
  ∀ x, S.v x = 0 ∧ S.u x = 0 ∧ S.ε x = 0

/-! ### The two weights -/

/-- The constant weight `W = a_*` (Section 6.1). -/
def constWeight {g n : ℝ} (T : SZTraj g n) (hg : 0 < g) : Weight T where
  W := fun _ => 2 / (g + 2)
  W1 := fun _ => 0
  hW := fun x => hasDerivAt_const x _
  pos := fun _ => by positivity

/-- The variable weight `W = a + 4c/3` of (6.9), when `z ≤ 1`. -/
def varWeight {g n : ℝ} (T : SZTraj g n) (hg : 0 < g) (hn : 0 < n) (hz1 : ∀ x, T.z x ≤ 1) :
    Weight T where
  W := fun x => Wv g (T.s x) (T.z x)
  W1 := fun x => W1v g n (T.s x) (T.z x)
  hW := fun x => by
    have h := (T.hasDerivAt_A hg hn x).add ((T.hasDerivAt_c hg hn x).const_mul (4 / 3))
    refine hasDerivAt_of_eq h (fun y => by simp [Wv]) ?_
    simp [W1v]
  pos := fun x => by
    unfold Wv
    have := T.As_pos hg hn x
    have : 0 ≤ cS g (T.s x) (T.z x) := by
      unfold cS; apply div_nonneg _ hg.le
      have := T.s_pos x; have := hz1 x; nlinarith
    positivity

lemma cS_nonneg {g n : ℝ} (hg : 0 < g) (T : SZTraj g n) {x : ℝ} (hz1 : T.z x ≤ 1) :
    0 ≤ cS g (T.s x) (T.z x) := by
  unfold cS; apply div_nonneg _ hg.le
  have := T.s_pos x; nlinarith

/-- `c/W ≤ 3/4` for the variable weight. -/
lemma cW_bound {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (T : SZTraj g n) (hz1 : ∀ x, T.z x ≤ 1)
    (x : ℝ) : |cS g (T.s x) (T.z x) / (varWeight T hg hn hz1).W x| ≤ 3 / 4 := by
  have hc := cS_nonneg hg T (hz1 x)
  have hW := (varWeight T hg hn hz1).pos x
  have hA := T.As_pos hg hn x
  rw [abs_of_nonneg (div_nonneg hc hW.le), div_le_iff₀ hW]
  show cS g (T.s x) (T.z x) ≤ 3 / 4 * Wv g (T.s x) (T.z x)
  unfold Wv; linarith

/-- `W ≥ a ≥ a(0)` downstream for the variable weight. -/
lemma varW_top {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (T : SZTraj g n) (hz1 : ∀ x, T.z x ≤ 1)
    (hz : ∀ x, 0 < T.z x) (x : ℝ) (hx : 0 ≤ x) :
    As g (T.s 0) ≤ (varWeight T hg hn hz1).W x := by
  have hs := T.s_antitone hz hx
  have hc := cS_nonneg hg T (hz1 x)
  show As g (T.s 0) ≤ Wv g (T.s x) (T.z x)
  unfold Wv As
  have : 2 * (1 - T.s 0) / (g + 2) ≤ 2 * (1 - T.s x) / (g + 2) :=
    div_le_div_of_nonneg_right (by linarith) (by linarith)
  linarith

/-! ### Nonzero frequencies, case by case -/

section
variable {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (T : SZTraj g n) {L : ℝ} (hL : 0 < L)
  (hzL : Tendsto T.z atTop (𝓝 L)) (hs0 : Tendsto T.s atTop (𝓝 0))
  (hs1 : Tendsto T.s atBot (𝓝 1))
include hg hn hL hzL hs0

lemma z_pos_of (x : ℝ) : 0 < T.z x :=
  lt_of_lt_of_le (lt_min (by positivity) (by positivity)) (T.slope_interval hg hn hL hzL hs0 x).1

/-- Below the reference line, `1 ≤ ν ≤ Γ + 1`, with the constant weight. -/
theorem nonzero_lower (hg2 : g < 2) (hn1 : 1 ≤ n) (hng : n ≤ g + 1)
    {lam : ℂ} (hlam : lam ≠ 0) (hre : 0 ≤ lam.re) (S : EigenSol T lam)
    (hS : Admissible S) : Trivial S := by
  have hsl := T.slope_interval hg hn hL hzL hs0
  have h1 : 1 / (g + 1) ≤ 1 / n := one_div_le_one_div_of_le hn hng
  have hz : ∀ x, 1 / (g + 1) ≤ T.z x ∧ T.z x ≤ 1 / n := fun x => by
    have := hsl x; unfold InSlope at this; rwa [min_eq_left h1, max_eq_right h1] at this
  have hzpos := z_pos_of hg hn T hL hzL hs0
  set R := constWeight T hg
  have hk : ∀ x, 0 < dS (T.s x) (T.z x) * (2 - dS (T.s x) (T.z x)) / 16 := by
    intro x
    have hd0 : 0 < dS (T.s x) (T.z x) := by unfold dS; exact mul_pos (T.s_pos x) (hzpos x)
    have hd1 : dS (T.s x) (T.z x) < 1 := by
      unfold dS
      have := T.s_lt x
      have : T.z x ≤ 1 := le_trans (hz x).2 (by rw [div_le_one hn]; exact hn1)
      nlinarith [T.s_pos x]
    have : 0 < 2 - dS (T.s x) (T.z x) := by linarith
    positivity
  have hcoer : ∀ x X Y, dS (T.s x) (T.z x) * (2 - dS (T.s x) (T.z x)) / 16 * Y ^ 2 ≤
      pairW g n (T.s x) (T.z x) (R.W x) (R.W1 x) X Y := fun x X Y =>
    lower_coercive hg hg2 hn1 hng (T.s_pos x) (T.s_lt x) (hz x).1 (hz x).2 X Y
  -- the flux vanishes at both ends
  have hcW : ∀ x, |cS g (T.s x) (T.z x) / R.W x| ≤ (g + 2) / (2 * g) := by
    intro x
    have hc := cS_nonneg hg T (le_trans (hz x).2 (by rw [div_le_one hn]; exact hn1))
    show |cS g (T.s x) (T.z x) / (2 / (g + 2))| ≤ (g + 2) / (2 * g)
    rw [abs_of_nonneg (by positivity)]
    have : cS g (T.s x) (T.z x) ≤ 1 / g := by
      unfold cS; rw [div_le_div_iff_of_pos_right hg]
      have := T.s_pos x; have := T.s_lt x; have := hzpos x; nlinarith
    calc cS g (T.s x) (T.z x) / (2 / (g + 2)) ≤ 1 / g / (2 / (g + 2)) :=
          div_le_div_of_nonneg_right this (by positivity)
      _ = (g + 2) / (2 * g) := by field_simp
  have hdM : ∀ x ≤ (0:ℝ), dS (T.s x) (T.z x) ≤ 1 / n := by
    intro x _; unfold dS
    have := T.s_lt x; have := T.s_pos x; have := (hz x).2; have := hzpos x
    nlinarith
  obtain ⟨hbot, htop⟩ := fluxW_tendsto hg hn T R hz (by positivity) hs0 hcW
    (k1 := 2 / (g + 2)) (by positivity) (fun x _ => le_refl _) (X := 0) (μ := 0)
    (kW := 2 / (g + 2)) (by positivity) le_rfl hdM (fun x _ => by simp [R, constWeight])
    (by rw [min_eq_right (by rw [div_le_one hn]; exact hn1)]
        have : 0 < 1 / n := by positivity
        linarith) S hS
  exact exclusionW hg hg2 hn T hzpos R hk hcoer hlam hre S hbot htop

include hs1 in
/-- Above the reference line, `Γ + 1 < ν < 5`, with the variable weight and the endpoint
    condition. -/
theorem nonzero_above (hg2 : g < 2) (hgn : g + 1 < n) (hn5 : n < 5) (hE : GammaE n ≤ g)
    {lam : ℂ} (hlam : lam ≠ 0) (hre : 0 ≤ lam.re) (S : EigenSol T lam)
    (hS : Admissible S) : Trivial S := by
  obtain ⟨hL1, hL0, hz⟩ := T.sharp_above hg hn hgn hL hzL hs0
  have hzpos := z_pos_of hg hn T hL hzL hs0
  have hg1 : 1 / (g + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hz1 : ∀ x, T.z x ≤ 1 := fun x => by linarith [(hz x).2]
  set R := varWeight T hg hn hz1
  -- the endpoint condition along the profile
  have hPi : ∀ x, 0 ≤ PiP n (g * cS g (T.s x) (T.z x) / dS (T.s x) (T.z x)) := by
    intro x
    have hρ : g * cS g (T.s x) (T.z x) / dS (T.s x) (T.z x) = (1 - T.z x) / T.z x := by
      unfold cS dS
      have := T.s_pos x; have := hzpos x
      field_simp
    rw [hρ]
    have hLpos := hL
    have hρ0 : 0 ≤ (1 - T.z x) / T.z x := div_nonneg (by linarith [(hz x).2]) (hzpos x).le
    rcases le_or_gt n (9 / 5) with h9 | h9
    · exact PiP_strip (by linarith) h9 hρ0
    · have hρr0 : 0 ≤ (1 - L) / L := div_nonneg (by linarith) hLpos.le
      have hρrt : (1 - L) / L ≤ n - 1 := by
        rw [div_le_iff₀ hLpos]
        have : 1 / n * n = 1 := by field_simp
        nlinarith
      have hend := endpoint hg h9 hn5 hρr0 hρrt
        (SZTraj.rho_root hg hn hLpos (T.zlim_root hg hn hzL hs0)) hE
      have hle : (1 - L) / L ≤ (1 - T.z x) / T.z x := by
        rw [div_le_div_iff₀ hLpos (hzpos x)]; nlinarith [(hz x).2]
      have hρt : (1 - T.z x) / T.z x ≤ n - 1 := by
        rw [div_le_iff₀ (hzpos x)]
        have h1 := (hz x).1
        have : 1 ≤ n * T.z x := by rw [div_le_iff₀ hn] at h1; linarith
        nlinarith
      exact le_trans hend (PiP_mono (by linarith) hn5 hρr0 hle hρt)
  have hk : ∀ x, 0 < As g (T.s x) * dS (T.s x) (T.z x) := by
    intro x
    have := T.As_pos hg hn x
    have : 0 < dS (T.s x) (T.z x) := by unfold dS; exact mul_pos (T.s_pos x) (hzpos x)
    positivity
  have hcoer : ∀ x X Y, As g (T.s x) * dS (T.s x) (T.z x) * Y ^ 2 ≤
      pairW g n (T.s x) (T.z x) (R.W x) (R.W1 x) X Y := fun x X Y =>
    var_coercive hg hg2 (by linarith) hn5 (T.s_pos x) (T.s_lt x) (hzpos x) (hz1 x) (hPi x) X Y
  -- upstream: z → 1/ν, so d ≤ 3/(2ν) far upstream
  have hbot := T.z_bot_above hg hn hgn hL hzL hs0 hs1
  have ev : ∀ᶠ x in atBot, T.z x < 3 / (2 * n) := hbot.eventually (gt_mem_nhds (by
    rw [div_lt_div_iff₀ hn (by positivity)]; linarith))
  obtain ⟨X, hX⟩ := eventually_atBot.mp ev
  have hdM : ∀ x ≤ X, dS (T.s x) (T.z x) ≤ 3 / (2 * n) := by
    intro x hx; unfold dS
    have := T.s_lt x; have := T.s_pos x; have := (hX x hx).le; have := hzpos x
    nlinarith
  -- the weight is bounded below
  set kW := min (2 / (g + 2)) (4 / (3 * (g + 1)))
  have hkW : 0 < kW := lt_min (by positivity) (by positivity)
  have hWlow : ∀ x, kW ≤ R.W x := by
    intro x
    show kW ≤ Wv g (T.s x) (T.z x)
    unfold Wv As
    have hs := T.s_pos x; have hs1 := T.s_lt x
    have hc : T.s x / (g + 1) ≤ cS g (T.s x) (T.z x) := by
      unfold cS
      have : T.z x ≤ 1 / (g + 1) := le_trans (hz x).2 hL0.le
      have : g / (g + 1) ≤ 1 - T.z x := by
        have e : 1 - 1 / (g + 1) = g / (g + 1) := by field_simp; ring
        linarith
      rw [div_le_div_iff₀ (by linarith) hg]
      have := mul_le_mul_of_nonneg_left this hs.le
      have e2 : T.s x * (g / (g + 1)) * (g + 1) = T.s x * g := by field_simp
      nlinarith
    have h1 : kW * (1 - T.s x) ≤ 2 / (g + 2) * (1 - T.s x) :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith)
    have h2 : kW * T.s x ≤ 4 / (3 * (g + 1)) * T.s x :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hs.le
    have e3 : 4 / (3 * (g + 1)) * T.s x = 4 / 3 * (T.s x / (g + 1)) := by field_simp
    have e4 : 2 * (1 - T.s x) / (g + 2) = 2 / (g + 2) * (1 - T.s x) := by ring
    nlinarith
  have hn1 : 1 < n := by linarith
  obtain ⟨hfbot, hftop⟩ := fluxW_tendsto hg hn T R hz (by positivity) hs0
    (cW_bound hg hn T hz1) (k1 := kW) hkW (fun x _ => hWlow x) (X := X) (μ := 0) (kW := kW)
    hkW le_rfl hdM (fun x _ => by simp; exact hWlow x)
    (by rw [min_eq_right (by rw [div_le_one hn]; linarith)]
        have : 3 / (2 * n) / 2 = 3 / (4 * n) := by field_simp; ring
        rw [this, add_zero, div_lt_div_iff₀ (by positivity) hn]; linarith) S hS
  exact exclusionW hg hg2 hn T hzpos R hk hcoer hlam hre S hfbot hftop

include hs1 in
/-- Below `ν = 1`, `2/3 < ν < 1`, with the variable weight, which degenerates upstream. -/
theorem nonzero_below (hg2 : g < 2) (hn23 : 2 / 3 < n) (hn1 : n < 1)
    {lam : ℂ} (hlam : lam ≠ 0) (hre : 0 ≤ lam.re) (S : EigenSol T lam)
    (hS : Admissible S) : Trivial S := by
  obtain ⟨hL1, hz⟩ := T.sharp_below hg hn hn1 hL hzL hs0
  have hzpos := z_pos_of hg hn T hL hzL hs0
  have hz1 : ∀ x, T.z x ≤ 1 := fun x => (hz x).2
  set R := varWeight T hg hn hz1
  have hPi : ∀ x, 0 ≤ PiP n (g * cS g (T.s x) (T.z x) / dS (T.s x) (T.z x)) := by
    intro x
    have : 0 ≤ g * cS g (T.s x) (T.z x) / dS (T.s x) (T.z x) := by
      have := cS_nonneg hg T (hz1 x)
      have : 0 < dS (T.s x) (T.z x) := by unfold dS; exact mul_pos (T.s_pos x) (hzpos x)
      positivity
    exact PiP_strip hn23 (by linarith) this
  have hk : ∀ x, 0 < As g (T.s x) * dS (T.s x) (T.z x) := by
    intro x
    have := T.As_pos hg hn x
    have : 0 < dS (T.s x) (T.z x) := by unfold dS; exact mul_pos (T.s_pos x) (hzpos x)
    positivity
  have hcoer : ∀ x X Y, As g (T.s x) * dS (T.s x) (T.z x) * Y ^ 2 ≤
      pairW g n (T.s x) (T.z x) (R.W x) (R.W1 x) X Y := fun x X Y =>
    var_coercive hg hg2 hn23 (by linarith) (T.s_pos x) (T.s_lt x) (hzpos x) (hz1 x) (hPi x) X Y
  -- upstream rate of degeneration of the weight
  set κ := 1 / n - 1 + (3 / 2 - 1 / n) / 2 with hκdef
  have hn' : 1 / n < 3 / 2 := by rw [div_lt_iff₀ hn]; linarith
  have hκ : 1 / n - 1 < κ := by rw [hκdef]; linarith
  have hκ0 : 0 ≤ κ := by
    have : 1 < 1 / n := by rw [lt_div_iff₀ hn]; linarith
    rw [hκdef]; linarith
  obtain ⟨X, C, hC, hw⟩ := T.one_sub_z_lower hg hn hn1 hL hzL hs0 hs1 hκ
  have hsX : ∀ x ≤ X, T.s X ≤ T.s x := fun x hx => T.s_antitone hzpos hx
  have hWup : ∀ x ≤ X, (4 / 3 * (T.s X * C / g)) * Real.exp (κ * x) ≤ R.W x := by
    intro x hx
    show (4 / 3 * (T.s X * C / g)) * Real.exp (κ * x) ≤ Wv g (T.s x) (T.z x)
    unfold Wv cS
    have h1 := hw x hx
    have h2 := hsX x hx
    have hA := T.As_pos hg hn x
    have hsXp := T.s_pos X
    have : T.s X * (C * Real.exp (κ * x)) ≤ T.s x * (1 - T.z x) :=
      mul_le_mul h2 h1 (by positivity) (T.s_pos x).le
    have e : 4 / 3 * (T.s X * C / g) * Real.exp (κ * x) = 4 / 3 * (T.s X * (C * Real.exp (κ * x)) / g) := by
      ring
    rw [e]
    have : T.s X * (C * Real.exp (κ * x)) / g ≤ T.s x * (1 - T.z x) / g :=
      div_le_div_of_nonneg_right this hg.le
    have : 0 < As g (T.s x) := hA
    unfold As at this
    linarith
  have hdM : ∀ x ≤ X, dS (T.s x) (T.z x) ≤ 1 := by
    intro x _; unfold dS
    have := T.s_lt x; have := T.s_pos x; have := hz1 x; have := hzpos x
    nlinarith
  obtain ⟨hfbot, hftop⟩ := fluxW_tendsto hg hn T R hz hL hs0
    (cW_bound hg hn T hz1) (k1 := As g (T.s 0)) (T.As_pos hg hn 0)
    (fun x hx => varW_top hg hn T hz1 hzpos x hx) (X := X) (μ := κ)
    (kW := 4 / 3 * (T.s X * C / g)) (by have := T.s_pos X; positivity) hκ0 hdM hWup
    (by rw [min_eq_left (by rw [le_div_iff₀ hn]; linarith), hκdef]; linarith) S hS
  exact exclusionW hg hg2 hn T hzpos R hk hcoer hlam hre S hfbot hftop

end

/-! ### Theorem 1.1 -/

/-- **Theorem 1.1, nonzero frequencies.** On `ℛ` there is no nontrivial admissible solution at
    a nonzero spectral parameter in the closed right half-plane. -/
theorem thm_nonzero {g n : ℝ} (hR : InR g n) (P : LimitingProfile g n)
    {lam : ℂ} (hlam : lam ≠ 0) (hre : 0 ≤ lam.re)
    (S : EigenSol (P.toSZ hR.1 (by linarith [hR.2.2.1])) lam) (hS : Admissible S) :
    Trivial S := by
  obtain ⟨hg, hg2, hn23, hn5, hE⟩ := hR
  have hn : 0 < n := by linarith
  have hL := P.zlim_pos
  have hzL := P.z_top'
  have hs0 := P.s_top hg
  have hs1 := P.s_bot hg
  rcases lt_or_ge n 1 with h1 | h1
  · exact nonzero_below hg hn _ hL hzL hs0 hs1 hg2 hn23 h1 hlam hre S hS
  · rcases le_or_gt n (g + 1) with h2 | h2
    · exact nonzero_lower hg hn _ hL hzL hs0 hg2 h1 h2 hlam hre S hS
    · exact nonzero_above hg hn _ hL hzL hs0 hs1 hg2 h2 hn5 hE hlam hre S hS

/-- Zero frequency for any limiting profile (Proposition 8.1). -/
theorem zero_core {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (P : LimitingProfile g n)
    (hvar : VariationalUnique (P.toSZ hg hn)) (S : EigenSol (P.toSZ hg hn) 0)
    (hS : ZeroAdmissible S) : Trivial S := by
  have hzb : ∃ B, ∀ x, |(P.toSZ hg hn).z x| ≤ B := by
    refine ⟨max (1 / (g + 1)) (1 / n), fun x => ?_⟩
    have := P.slope hg hn x
    rw [abs_of_pos (P.z_pos hg hn x)]; exact this.2
  exact zero_frequency hg hn (P.toSZ hg hn) (P.s_bot hg) (P.s_top hg) hzb hvar S hS

/-- A zero of `D(·, (Γ,ν), 0)` in the closed right half-plane produces a nontrivial admissible
    solution along a limiting profile. -/
def EvansZeroSolution (D : ℂ → ℝ × ℝ → ℝ → ℂ) : Prop :=
  ∀ (lam : ℂ) (g n : ℝ) (hg : 0 < g) (hn : 0 < n), 0 ≤ lam.re → D lam (g, n) 0 = 0 →
    ∃ P : LimitingProfile g n,
      (lam ≠ 0 ∧ ∃ S : EigenSol (P.toSZ hg hn) lam, Admissible S ∧ ¬ Trivial S) ∨
      (lam = 0 ∧ ∃ S : EigenSol (P.toSZ hg hn) 0, ZeroAdmissible S ∧ ¬ Trivial S)

/-- Every limiting profile has the saddle property used at zero frequency. -/
def AllVariationalUnique : Prop :=
  ∀ (g n : ℝ) (hg : 0 < g) (hn : 0 < n) (P : LimitingProfile g n), VariationalUnique (P.toSZ hg hn)

/-- **Theorem 1.1.** `D_*(λ; Γ, ν) ≠ 0` on the closed right half-plane for `(Γ, ν) ∈ ℛ`. -/
theorem evans_R (D : ℂ → ℝ × ℝ → ℝ → ℂ) (hW : EvansZeroSolution D)
    (hV : AllVariationalUnique) {g n : ℝ} (hR : InR g n) {lam : ℂ} (hre : 0 ≤ lam.re) :
    D lam (g, n) 0 ≠ 0 := by
  intro h0
  have hg := hR.1
  have hn : 0 < n := by linarith [hR.2.2.1]
  obtain ⟨P, hP⟩ := hW lam g n hg hn hre h0
  rcases hP with ⟨hlam, S, hS, hnt⟩ | ⟨rfl, S, hS, hnt⟩
  · exact hnt (thm_nonzero hR P hlam hre S hS)
  · exact hnt (zero_core hg hn P (hV g n hg hn P) S hS)

/-- **Corollary 1.2.** For a compact set `K ⊆ ℛ` there is one `δ > 0` such that the Evans
    function does not vanish in the closed right half-plane for all shocks with parameters in
    `K` and strength parameter `0 ≤ ς < δ`. -/
theorem cor_finite {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKR : ∀ p ∈ K, InR p.1 p.2)
    (D : ℂ → ℝ × ℝ → ℝ → ℂ) (hW : EvansZeroSolution D) (hV : AllVariationalUnique)
    {Λ ς0 : ℝ} (hς0 : 0 < ς0)
    (hcont : ContinuousOn (fun q : ℂ × (ℝ × ℝ) × ℝ => D q.1 q.2.1 q.2.2)
      (halfDisk Λ ×ˢ K ×ˢ Icc 0 ς0))
    (hhigh : ∀ lam p ς, 0 ≤ lam.re → Λ < ‖lam‖ → p ∈ K → ς ∈ Icc 0 ς0 → D lam p ς ≠ 0) :
    ∃ δ > 0, ∀ lam p ς, 0 ≤ lam.re → p ∈ K → 0 ≤ ς → ς < δ → D lam p ς ≠ 0 := by
  obtain ⟨δ, hδ, h⟩ := finite_shock hK hK subset_rfl D hς0 hcont hhigh
    (fun lam p hre _ hp => evans_R D hW hV (hKR p hp) hre)
  exact ⟨δ, hδ, fun lam p ς hre hp hς hςδ => h lam p p ς hre hp hp (by simpa using hδ) hς hςδ⟩

/-! ### Examples (Appendix C) -/

/-- Air, `γ = 1.4`, `ν ≈ 1.47`, lies in the strip. -/
example : InR (2 / 5) (147 / 100) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  unfold GammaE
  split_ifs with h
  · norm_num
  · exact absurd (by norm_num : (147 / 100 : ℝ) ≤ 9 / 5) h

/-- Monatomic gases, `Γ = 2/3`, `ν = 15/8`: the hand check of Appendix C,
    `Π_{15/8}(2/3) = 505535/256 > 0`. -/
theorem monatomic_in_R : InR (2 / 3) (15 / 8) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  obtain ⟨h1, h2, h3⟩ := rhoE_spec (n := 15 / 8) (by norm_num) (by norm_num)
  have hPi : PiP (15 / 8) (2 / 3) = 505535 / 256 := by unfold PiP; norm_num
  have hle : rhoE (15 / 8) < 2 / 3 := by
    by_contra hc; push Not at hc
    have := PiP_mono (n := 15 / 8) (x := 2 / 3) (y := rhoE (15 / 8)) (by norm_num) (by norm_num)
      (by norm_num) hc (by linarith)
    rw [hPi, h3] at this; norm_num at this
  unfold GammaE
  split_ifs with h
  · exact absurd h (by norm_num)
  have := Gmap_strictMono (n := 15 / 8) (by norm_num) h1.le hle (by norm_num)
  have hG : Gmap (15 / 8) (2 / 3) ≤ 2 / 3 := by unfold Gmap; norm_num
  linarith

end

end StrongShock
