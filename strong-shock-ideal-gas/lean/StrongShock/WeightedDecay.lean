/-
  Lemma 7.1: the energy flux vanishes at both ends, for a weight with an exponential
  lower bound upstream.
-/
import StrongShock.WeightedExclusion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Filter Topology Set

namespace StrongShock

noncomputable section

/-- Admissibility at a nonzero frequency, as provided by [HLZ]: for every rate
    `ω < min{1, 1/ν}` the solution and its first derivatives are `O(e^{ωx})` upstream, and
    they tend to zero downstream. -/
structure Admissible {g n : ℝ} {T : SZTraj g n} {lam : ℂ} (S : EigenSol T lam) : Prop where
  up_decay : ∀ ω < min 1 (1 / n), ∃ C, ∀ x ≤ 0, ‖S.v x‖ ≤ C * Real.exp (ω * x) ∧
    ‖S.u x‖ ≤ C * Real.exp (ω * x) ∧ ‖S.up x‖ ≤ C * Real.exp (ω * x) ∧
    ‖S.ε x‖ ≤ C * Real.exp (ω * x) ∧ ‖S.εp x‖ ≤ C * Real.exp (ω * x)
  v_top : Tendsto S.v atTop (𝓝 0)
  u_top : Tendsto S.u atTop (𝓝 0)
  up_top : Tendsto S.up atTop (𝓝 0)
  ε_top : Tendsto S.ε atTop (𝓝 0)
  εp_top : Tendsto S.εp atTop (𝓝 0)

lemma tendsto_zero_of_abs_le {l : Filter ℝ} {f b : ℝ → ℝ} (h : ∀ᶠ x in l, |f x| ≤ b x)
    (hb : Tendsto b l (𝓝 0)) : Tendsto f l (𝓝 0) :=
  squeeze_zero_norm' (by simpa [Real.norm_eq_abs] using h) hb

lemma bdd_mul_tendsto {l : Filter ℝ} {c f : ℝ → ℝ} {B : ℝ} (hc : ∀ x, |c x| ≤ B)
    (hf : Tendsto f l (𝓝 0)) : Tendsto (fun x => c x * f x) l (𝓝 0) := by
  have hB : 0 ≤ B := le_trans (abs_nonneg _) (hc 0)
  apply tendsto_zero_of_abs_le (b := fun x => B * |f x|) (Eventually.of_forall fun x => ?_)
  · simpa using (hf.abs).const_mul B
  · rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hc x) (abs_nonneg _)

/-- Upstream: `f/w → 0` when `|f| ≤ C e^{ωx}` and `w² ≥ a₀ e^{Mx}` for `x ≤ X`, and `M < 2ω`. -/
lemma up_ratio' {f w : ℝ → ℝ} {C ω M a0 X : ℝ} (ha0 : 0 < a0) (hw : ∀ x, 0 < w x)
    (hf : ∀ x ≤ X, |f x| ≤ C * Real.exp (ω * x))
    (hlow : ∀ x ≤ X, a0 * Real.exp (M * x) ≤ w x ^ 2) (hωM : M < 2 * ω) :
    Tendsto (fun x => f x / w x) atBot (𝓝 0) := by
  have e : Tendsto (fun x => Real.sqrt (C ^ 2 / a0 * Real.exp ((2 * ω - M) * x))) atBot (𝓝 0) := by
    have : Tendsto (fun x => (2 * ω - M) * x) atBot atBot :=
      tendsto_id.const_mul_atBot (by linarith)
    have h1 := (Real.tendsto_exp_atBot.comp this).const_mul (C ^ 2 / a0)
    simp only [mul_zero] at h1
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at this
    exact this
  apply tendsto_zero_of_abs_le _ e
  rw [eventually_atBot]
  refine ⟨X, fun x hx => ?_⟩
  have hwx := hw x
  have h1 := hf x hx
  have h2 := hlow x hx
  have hC : 0 ≤ C * Real.exp (ω * x) := le_trans (abs_nonneg _) h1
  have hsq : f x ^ 2 ≤ (C * Real.exp (ω * x)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hexp : Real.exp (ω * x) ^ 2 = Real.exp ((2 * ω - M) * x) * Real.exp (M * x) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hE : (C * Real.exp (ω * x)) ^ 2
      = C ^ 2 / a0 * Real.exp ((2 * ω - M) * x) * (a0 * Real.exp (M * x)) := by
    rw [mul_pow, hexp]; field_simp
  have key : (f x / w x) ^ 2 ≤ C ^ 2 / a0 * Real.exp ((2 * ω - M) * x) := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    calc f x ^ 2 ≤ (C * Real.exp (ω * x)) ^ 2 := hsq
      _ = C ^ 2 / a0 * Real.exp ((2 * ω - M) * x) * (a0 * Real.exp (M * x)) := hE
      _ ≤ C ^ 2 / a0 * Real.exp ((2 * ω - M) * x) * w x ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt key

/-- The flux in terms of the normalized quantities `u/√a`, `(u'-du)/√a`, `h/√a`,
    `h/(√a W)`, `h'/(√a W)`. -/
lemma FluxW_eq {g n s z W w v u up h hp : ℝ} (hw : w ≠ 0) (hwa : w ^ 2 = As g s) (hW : W ≠ 0) :
    FluxW g n s z W v u up h hp
      = v ^ 2 / 2 - u * v - ((up - dS s z * u) / w) * (u / w) + g * u ^ 2 / 4
        + g * (u / w) * (h / w) + Vs g s * (h / (w * W)) ^ 2
        - 2 * n * (h / (w * W)) * (hp / (w * W))
        + 2 * (n - 1) * (cS g s z / W) * ((up - dS s z * u) / w) * (h / (w * W)) := by
  unfold FluxW
  rw [← hwa]
  field_simp
  ring

/-- Coefficient bounds along a trajectory whose slope stays in `[zl, zh]`. -/
lemma coeff_boundsW {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (T : SZTraj g n) {zl zh : ℝ}
    (hz : ∀ x, zl ≤ T.z x ∧ T.z x ≤ zh) :
    ∃ B, 0 ≤ B ∧ ∀ x, |cS g (T.s x) (T.z x)| ≤ B ∧ |c1S g n (T.s x) (T.z x)| ≤ B ∧
      |dS (T.s x) (T.z x)| ≤ B ∧ |Vs g (T.s x)| ≤ B := by
  set Kset := Icc (0:ℝ) 1 ×ˢ Icc zl zh
  have hKc : IsCompact Kset := isCompact_Icc.prod isCompact_Icc
  have hg2 : g + 2 ≠ 0 := by linarith
  let F : ℝ × ℝ → ℝ := fun p => |cS g p.1 p.2| + |c1S g n p.1 p.2| + |dS p.1 p.2| + |Vs g p.1|
  have hF : Continuous F := by
    simp only [F, cS, c1S, dS, Vs, As]
    fun_prop (disch := assumption)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  have hmem : (T.s x, T.z x) ∈ Kset := ⟨⟨(T.s_pos x).le, (T.s_lt x).le⟩, hz x⟩
  have h := hB _ hmem
  rw [Real.norm_eq_abs] at h
  have hFx : F (T.s x, T.z x) ≤ max B 0 := le_trans (le_abs_self _) (le_trans h (le_max_left _ _))
  simp only [F] at hFx
  have := abs_nonneg (cS g (T.s x) (T.z x)); have := abs_nonneg (c1S g n (T.s x) (T.z x))
  have := abs_nonneg (dS (T.s x) (T.z x)); have := abs_nonneg (Vs g (T.s x))
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Lower bound for `a` upstream of `X` when `d ≤ M` there. -/
lemma As_lower_on {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (T : SZTraj g n) {M X : ℝ}
    (hM : ∀ x ≤ X, dS (T.s x) (T.z x) ≤ M) (x : ℝ) (hx : x ≤ X) :
    As g (T.s X) * Real.exp (-(M * X)) * Real.exp (M * x) ≤ As g (T.s x) := by
  have hφ : ∀ y, HasDerivAt (fun t => As g (T.s t) * Real.exp (-(M * t)))
      (As g (T.s y) * (dS (T.s y) (T.z y) - M) * Real.exp (-(M * y))) y := by
    intro y
    have h := (T.hasDerivAt_A hg hn y).mul (((hasDerivAt_id y).const_mul M).neg.exp)
    refine hasDerivAt_of_eq h (fun t => by simp) ?_
    simp; ring
  have hanti : AntitoneOn (fun t => As g (T.s t) * Real.exp (-(M * t))) (Iic X) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic X)
    · exact fun y _ => (hφ y).continuousAt.continuousWithinAt
    · exact fun y _ => (hφ y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Iic] at hy
      rw [(hφ y).deriv]
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (T.As_pos hg hn y).le (by linarith [hM y (le_of_lt hy)]))
        (Real.exp_pos _).le
  have := hanti (show x ∈ Iic X from hx) (show X ∈ Iic X from le_refl X) hx
  simp only at this
  have he : Real.exp (-(M * x)) * Real.exp (M * x) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (M * x) := Real.exp_pos _
  calc As g (T.s X) * Real.exp (-(M * X)) * Real.exp (M * x)
      ≤ As g (T.s x) * Real.exp (-(M * x)) * Real.exp (M * x) :=
        mul_le_mul_of_nonneg_right this hpos.le
    _ = As g (T.s x) := by rw [mul_assoc, he, mul_one]

/-- Combination step: the normalized flux tends to zero with its building blocks. -/
lemma flux_comb {l : Filter ℝ} {g n B Bw : ℝ} {V0 U0 U P H R1 R2 cW Vc : ℝ → ℝ}
    (hV0 : Tendsto V0 l (𝓝 0)) (hU0 : Tendsto U0 l (𝓝 0)) (hU : Tendsto U l (𝓝 0))
    (hP : Tendsto P l (𝓝 0)) (hH : Tendsto H l (𝓝 0)) (hR1 : Tendsto R1 l (𝓝 0))
    (hR2 : Tendsto R2 l (𝓝 0)) (hVc : ∀ x, |Vc x| ≤ B) (hcW : ∀ x, |cW x| ≤ Bw) :
    Tendsto (fun x => V0 x ^ 2 / 2 - U0 x * V0 x - P x * U x + g * U0 x ^ 2 / 4
        + g * U x * H x + Vc x * R1 x ^ 2 - 2 * n * R1 x * R2 x
        + 2 * (n - 1) * cW x * P x * R1 x) l (𝓝 0) := by
  have t1 : Tendsto (fun x => V0 x ^ 2 / 2) l (𝓝 0) := by simpa using (hV0.pow 2).div_const 2
  have t2 : Tendsto (fun x => U0 x * V0 x) l (𝓝 0) := by simpa using hU0.mul hV0
  have t3 : Tendsto (fun x => P x * U x) l (𝓝 0) := by simpa using hP.mul hU
  have t4 : Tendsto (fun x => g * U0 x ^ 2 / 4) l (𝓝 0) := by
    simpa using ((hU0.pow 2).const_mul g).div_const 4
  have t5 : Tendsto (fun x => g * U x * H x) l (𝓝 0) := by simpa using (hU.const_mul g).mul hH
  have t6 : Tendsto (fun x => Vc x * R1 x ^ 2) l (𝓝 0) := by
    have := bdd_mul_tendsto hVc (by simpa using hR1.pow 2 : Tendsto (fun x => R1 x ^ 2) l (𝓝 0))
    exact this
  have t7 : Tendsto (fun x => 2 * n * R1 x * R2 x) l (𝓝 0) := by
    simpa using (hR1.const_mul (2 * n)).mul hR2
  have t8 : Tendsto (fun x => 2 * (n - 1) * cW x * P x * R1 x) l (𝓝 0) := by
    have h1 := bdd_mul_tendsto hcW (by simpa using hP.mul hR1 :
      Tendsto (fun x => P x * R1 x) l (𝓝 0))
    have := h1.const_mul (2 * (n - 1))
    simp only [mul_zero] at this
    refine this.congr (fun x => by ring)
  have := ((((((t1.sub t2).sub t3).add t4).add t5).add t6).sub t7).add t8
  simpa using this

/-- **Lemma 7.1.** For an admissible solution at a nonzero frequency the total energy flux
    tends to zero at both ends, provided the weight has an exponential lower bound upstream
    compatible with the decay rate. -/
theorem fluxW_tendsto {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (T : SZTraj g n) (R : Weight T)
    {zl zh : ℝ} (hz : ∀ x, zl ≤ T.z x ∧ T.z x ≤ zh) (hzl : 0 < zl)
    (hs_top : Tendsto T.s atTop (𝓝 0))
    {Bw : ℝ} (hcW : ∀ x, |cS g (T.s x) (T.z x) / R.W x| ≤ Bw)
    {k1 : ℝ} (hk1 : 0 < k1) (hWtop : ∀ x, 0 ≤ x → k1 ≤ R.W x)
    {X M μ kW : ℝ} (hkW : 0 < kW) (hμ : 0 ≤ μ) (hdM : ∀ x ≤ X, dS (T.s x) (T.z x) ≤ M)
    (hWup : ∀ x ≤ X, kW * Real.exp (μ * x) ≤ R.W x) (hrate : M / 2 + μ < min 1 (1 / n))
    {lam : ℂ} (S : EigenSol T lam) (hS : Admissible S) :
    let F := fun x => T.fluxW R (fun y => (S.v y).re) (fun y => (S.u y).re)
        (fun y => (S.up y).re) (fun y => (S.h y).re) (fun y => (S.hp y).re) x
      + T.fluxW R (fun y => (S.v y).im) (fun y => (S.u y).im)
        (fun y => (S.up y).im) (fun y => (S.h y).im) (fun y => (S.hp y).im) x
    Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 0) := by
  intro F
  obtain ⟨B, hB0, hB⟩ := coeff_boundsW hg hn T hz
  have hcB : ∀ x, |cS g (T.s x) (T.z x)| ≤ B := fun x => (hB x).1
  have hc1B : ∀ x, |c1S g n (T.s x) (T.z x)| ≤ B := fun x => (hB x).2.1
  have hdB : ∀ x, |dS (T.s x) (T.z x)| ≤ B := fun x => (hB x).2.2.1
  have hVB : ∀ x, |Vs g (T.s x)| ≤ B := fun x => (hB x).2.2.2
  have wpos := T.w_pos hg hn
  have Wpos := R.pos
  have wWpos : ∀ x, 0 < T.w x * R.W x := fun x => mul_pos (wpos x) (Wpos x)
  -- the flux of one component in normalized form
  have key : ∀ (l : Filter ℝ), (∀ (φ : ℂ → ℝ), (φ = Complex.re ∨ φ = Complex.im) →
      Tendsto (fun x => φ (S.v x)) l (𝓝 0) ∧ Tendsto (fun x => φ (S.u x)) l (𝓝 0) ∧
      Tendsto (fun x => φ (S.u x) / T.w x) l (𝓝 0) ∧
      Tendsto (fun x => (φ (S.up x) - dS (T.s x) (T.z x) * φ (S.u x)) / T.w x) l (𝓝 0) ∧
      Tendsto (fun x => φ (S.h x) / T.w x) l (𝓝 0) ∧
      Tendsto (fun x => φ (S.h x) / (T.w x * R.W x)) l (𝓝 0) ∧
      Tendsto (fun x => φ (S.hp x) / (T.w x * R.W x)) l (𝓝 0)) → Tendsto F l (𝓝 0) := by
    intro l hl
    have one : ∀ (φ : ℂ → ℝ), (φ = Complex.re ∨ φ = Complex.im) →
        Tendsto (fun x => T.fluxW R (fun y => φ (S.v y)) (fun y => φ (S.u y))
          (fun y => φ (S.up y)) (fun y => φ (S.h y)) (fun y => φ (S.hp y)) x) l (𝓝 0) := by
      intro φ hφ
      obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hl φ hφ
      have := flux_comb (g := g) (n := n) a1 a2 a3 a4 a5 a6 a7 hVB hcW
      refine this.congr (fun x => ?_)
      simp only [SZTraj.fluxW]
      rw [FluxW_eq (wpos x).ne' (T.w_sq hg hn x) (Wpos x).ne']
    have := (one Complex.re (Or.inl rfl)).add (one Complex.im (Or.inr rfl))
    simpa using this
  have hcomp : ∀ (φ : ℂ → ℝ), (φ = Complex.re ∨ φ = Complex.im) → ∀ x,
      φ (S.h x) = φ (S.ε x) + cS g (T.s x) (T.z x) * φ (S.u x) ∧
      φ (S.hp x) = φ (S.εp x) + cS g (T.s x) (T.z x) * φ (S.up x)
        + c1S g n (T.s x) (T.z x) * φ (S.u x) := by
    intro φ hφ x
    rcases hφ with rfl | rfl <;> simp [EigenSol.h, EigenSol.hp]
  have hφle : ∀ (φ : ℂ → ℝ), (φ = Complex.re ∨ φ = Complex.im) → ∀ z : ℂ, |φ z| ≤ ‖z‖ := by
    intro φ hφ z; rcases hφ with rfl | rfl
    · exact Complex.abs_re_le_norm z
    · exact Complex.abs_im_le_norm z
  constructor
  · -- upstream
    apply key
    intro φ hφ
    have hM0 : 0 < M := by
      have := hdM (min X 0) (min_le_left _ _)
      have : 0 < dS (T.s (min X 0)) (T.z (min X 0)) := by
        unfold dS; exact mul_pos (T.s_pos _) (lt_of_lt_of_le hzl (hz _).1)
      linarith
    obtain ⟨ω, hω1, hω2⟩ : ∃ ω, M / 2 + μ < ω ∧ ω < min 1 (1 / n) :=
      ⟨(M / 2 + μ + min 1 (1 / n)) / 2, by linarith, by linarith⟩
    have hωpos : 0 < ω := by linarith
    obtain ⟨C, hC⟩ := hS.up_decay ω hω2
    set X0 := min X 0
    have hX0X : X0 ≤ X := min_le_left _ _
    have hX00 : X0 ≤ 0 := min_le_right _ _
    set a0 := As g (T.s X) * Real.exp (-(M * X))
    have ha0 : 0 < a0 := mul_pos (T.As_pos hg hn X) (Real.exp_pos _)
    have hlow : ∀ x ≤ X0, a0 * Real.exp (M * x) ≤ T.w x ^ 2 := by
      intro x hx; rw [T.w_sq hg hn x]; exact As_lower_on hg hn T hdM x (hx.trans hX0X)
    have hlowW : ∀ x ≤ X0, (a0 * kW ^ 2) * Real.exp ((M + 2 * μ) * x) ≤ (T.w x * R.W x) ^ 2 := by
      intro x hx
      have h1 := hlow x hx
      have h2 := hWup x (hx.trans hX0X)
      have h3 : (kW * Real.exp (μ * x)) ^ 2 ≤ R.W x ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      have e : (a0 * kW ^ 2) * Real.exp ((M + 2 * μ) * x)
          = (a0 * Real.exp (M * x)) * (kW * Real.exp (μ * x)) ^ 2 := by
        rw [show (M + 2 * μ) * x = M * x + (μ * x + μ * x) by ring, Real.exp_add, Real.exp_add]
        ring
      rw [e, show (T.w x * R.W x) ^ 2 = T.w x ^ 2 * R.W x ^ 2 by ring]
      exact mul_le_mul h1 h3 (by positivity) (sq_nonneg _)
    have ha0W : 0 < a0 * kW ^ 2 := by positivity
    have bnd0 : ∀ {f : ℝ → ℝ} (K : ℝ), (∀ x ≤ X0, |f x| ≤ K * Real.exp (ω * x)) →
        Tendsto f atBot (𝓝 0) := by
      intro f K hf
      have e : Tendsto (fun x => K * Real.exp (ω * x)) atBot (𝓝 0) := by
        have : Tendsto (fun x => ω * x) atBot atBot := tendsto_id.const_mul_atBot hωpos
        simpa using (Real.tendsto_exp_atBot.comp this).const_mul K
      apply tendsto_zero_of_abs_le _ e
      rw [eventually_atBot]; exact ⟨X0, fun x hx => hf x hx⟩
    have bndw : ∀ {f : ℝ → ℝ} (K : ℝ), (∀ x ≤ X0, |f x| ≤ K * Real.exp (ω * x)) →
        Tendsto (fun x => f x / T.w x) atBot (𝓝 0) := fun K hf =>
      up_ratio' ha0 wpos hf hlow (by linarith)
    have bndwW : ∀ {f : ℝ → ℝ} (K : ℝ), (∀ x ≤ X0, |f x| ≤ K * Real.exp (ω * x)) →
        Tendsto (fun x => f x / (T.w x * R.W x)) atBot (𝓝 0) := fun K hf =>
      up_ratio' ha0W wWpos hf hlowW (by linarith)
    have E : ∀ (f : ℝ → ℂ), (∀ x ≤ 0, ‖f x‖ ≤ C * Real.exp (ω * x)) →
        ∀ x ≤ X0, |φ (f x)| ≤ C * Real.exp (ω * x) :=
      fun f hf x hx => (hφle φ hφ _).trans (hf x (hx.trans hX00))
    have Ev := E S.v (fun x hx => (hC x hx).1)
    have Eu := E S.u (fun x hx => (hC x hx).2.1)
    have Eup := E S.up (fun x hx => (hC x hx).2.2.1)
    have Eε := E S.ε (fun x hx => (hC x hx).2.2.2.1)
    have Eεp := E S.εp (fun x hx => (hC x hx).2.2.2.2)
    have hCnn : ∀ x ≤ X0, 0 ≤ C * Real.exp (ω * x) := fun x hx => le_trans (abs_nonneg _) (Eu x hx)
    have prodB : ∀ (c f : ℝ → ℝ), (∀ x, |c x| ≤ B) →
        (∀ x ≤ X0, |f x| ≤ C * Real.exp (ω * x)) →
        ∀ x ≤ X0, |c x * f x| ≤ B * (C * Real.exp (ω * x)) := by
      intro c f hc hf x hx
      rw [abs_mul]; exact mul_le_mul (hc x) (hf x hx) (abs_nonneg _) hB0
    have Eh : ∀ x ≤ X0, |φ (S.h x)| ≤ (1 + B) * C * Real.exp (ω * x) := by
      intro x hx
      rw [(hcomp φ hφ x).1]
      have h1 := prodB _ _ hcB Eu x hx
      have h2 := Eε x hx
      have := abs_add_le (φ (S.ε x)) (cS g (T.s x) (T.z x) * φ (S.u x))
      nlinarith
    have Ep : ∀ x ≤ X0, |φ (S.up x) - dS (T.s x) (T.z x) * φ (S.u x)|
        ≤ (1 + B) * C * Real.exp (ω * x) := by
      intro x hx
      have h1 := prodB _ _ hdB Eu x hx
      have h2 := Eup x hx
      have := abs_sub (φ (S.up x)) (dS (T.s x) (T.z x) * φ (S.u x))
      nlinarith
    have Ehp : ∀ x ≤ X0, |φ (S.hp x)| ≤ (1 + 2 * B) * C * Real.exp (ω * x) := by
      intro x hx
      rw [(hcomp φ hφ x).2]
      have h1 := prodB _ _ hcB Eup x hx
      have h2 := prodB _ _ hc1B Eu x hx
      have h3 := Eεp x hx
      have t1 := abs_add_le (φ (S.εp x) + cS g (T.s x) (T.z x) * φ (S.up x))
        (c1S g n (T.s x) (T.z x) * φ (S.u x))
      have t2 := abs_add_le (φ (S.εp x)) (cS g (T.s x) (T.z x) * φ (S.up x))
      nlinarith
    have Eh' : ∀ x ≤ X0, |φ (S.h x)| ≤ ((1 + B) * C) * Real.exp (ω * x) := by
      intro x hx; have := Eh x hx; linarith
    have Ep' : ∀ x ≤ X0, |φ (S.up x) - dS (T.s x) (T.z x) * φ (S.u x)|
        ≤ ((1 + B) * C) * Real.exp (ω * x) := by
      intro x hx; have := Ep x hx; linarith
    have Ehp' : ∀ x ≤ X0, |φ (S.hp x)| ≤ ((1 + 2 * B) * C) * Real.exp (ω * x) := by
      intro x hx; have := Ehp x hx; linarith
    exact ⟨bnd0 C Ev, bnd0 C Eu, bndw C Eu, bndw _ Ep', bndw _ Eh', bndwW _ Eh', bndwW _ Ehp'⟩
  · -- downstream
    apply key
    intro φ hφ
    have T0 : ∀ {f : ℝ → ℂ}, Tendsto f atTop (𝓝 0) → Tendsto (fun x => φ (f x)) atTop (𝓝 0) := by
      intro f hf
      rcases hφ with rfl | rfl
      · have := (Complex.continuous_re.tendsto 0).comp hf
        rw [Complex.zero_re] at this; exact this
      · have := (Complex.continuous_im.tendsto 0).comp hf
        rw [Complex.zero_im] at this; exact this
    -- `a` increases, so `w ≥ w(0)` downstream
    have hs_anti : Antitone T.s := by
      apply antitone_of_hasDerivAt_nonpos T.hs
      intro x; unfold fS
      have := T.s_pos x; have := T.s_lt x
      have := lt_of_lt_of_le hzl (hz x).1
      have : 0 < T.s x * (1 - T.s x) * T.z x := by
        have : 0 < 1 - T.s x := by linarith
        positivity
      show -T.s x * (1 - T.s x) * T.z x ≤ (0:ℝ)
      linarith
    have hw0 : ∀ x, 0 ≤ x → T.w 0 ≤ T.w x := by
      intro x hx
      unfold SZTraj.w
      apply Real.sqrt_le_sqrt
      unfold As
      have := hs_anti hx
      apply div_le_div_of_nonneg_right _ (by linarith)
      linarith
    have w0pos := wpos 0
    have divw : ∀ {f : ℝ → ℝ}, Tendsto f atTop (𝓝 0) →
        Tendsto (fun x => f x / T.w x) atTop (𝓝 0) := by
      intro f hf
      apply tendsto_zero_of_abs_le (b := fun x => |f x| / T.w 0) _
      · simpa using (hf.abs).div_const (T.w 0)
      rw [eventually_atTop]
      refine ⟨0, fun x hx => ?_⟩
      rw [abs_div, abs_of_pos (wpos x)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) w0pos (hw0 x hx)
    have divwW : ∀ {f : ℝ → ℝ}, Tendsto f atTop (𝓝 0) →
        Tendsto (fun x => f x / (T.w x * R.W x)) atTop (𝓝 0) := by
      intro f hf
      apply tendsto_zero_of_abs_le (b := fun x => |f x| / (T.w 0 * k1)) _
      · simpa using (hf.abs).div_const (T.w 0 * k1)
      rw [eventually_atTop]
      refine ⟨0, fun x hx => ?_⟩
      rw [abs_div, abs_of_pos (wWpos x)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
        (mul_le_mul (hw0 x hx) (hWtop x hx) hk1.le (wpos x).le)
    have Lu := T0 hS.u_top
    have Lup := T0 hS.up_top
    have Lε := T0 hS.ε_top
    have Lεp := T0 hS.εp_top
    have Lh : Tendsto (fun x => φ (S.h x)) atTop (𝓝 0) := by
      have := Lε.add (bdd_mul_tendsto hcB Lu); simp at this
      exact this.congr (fun x => ((hcomp φ hφ x).1).symm)
    have Lhp : Tendsto (fun x => φ (S.hp x)) atTop (𝓝 0) := by
      have := (Lεp.add (bdd_mul_tendsto hcB Lup)).add (bdd_mul_tendsto hc1B Lu); simp at this
      exact this.congr (fun x => ((hcomp φ hφ x).2).symm)
    have Lp : Tendsto (fun x => φ (S.up x) - dS (T.s x) (T.z x) * φ (S.u x)) atTop (𝓝 0) := by
      simpa using Lup.sub (bdd_mul_tendsto hdB Lu)
    exact ⟨T0 hS.v_top, Lu, divw Lu, divw Lp, divw Lh, divwW Lh, divwW Lhp⟩

end

end StrongShock
