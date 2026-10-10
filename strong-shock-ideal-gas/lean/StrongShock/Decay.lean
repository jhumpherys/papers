/-
  Lemma 8.1: vanishing of the energy flux at both ends, from the decay of admissible
  solutions supplied by the asymptotic theory of [HLZ, Lemmas 3.3, 3.6].
-/
import StrongShock.Exclusion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Filter Topology Set

namespace StrongShock

noncomputable section

/-- Admissibility at a nonzero frequency, in the form provided by [HLZ]: for every rate
    `ω < 1/ν` the solution and its first derivatives are `O(e^{ωx})` upstream, and they
    tend to zero downstream. -/
structure Admissible {g n : ℝ} {T : SZTraj g n} {lam : ℂ} (S : EigenSol T lam) : Prop where
  up_decay : ∀ ω < 1 / n, ∃ C, ∀ x ≤ 0, ‖S.v x‖ ≤ C * Real.exp (ω * x) ∧
    ‖S.u x‖ ≤ C * Real.exp (ω * x) ∧ ‖S.up x‖ ≤ C * Real.exp (ω * x) ∧
    ‖S.ε x‖ ≤ C * Real.exp (ω * x) ∧ ‖S.εp x‖ ≤ C * Real.exp (ω * x)
  v_top : Tendsto S.v atTop (𝓝 0)
  u_top : Tendsto S.u atTop (𝓝 0)
  up_top : Tendsto S.up atTop (𝓝 0)
  ε_top : Tendsto S.ε atTop (𝓝 0)
  εp_top : Tendsto S.εp atTop (𝓝 0)

/-- Squeeze helper: `|F| ≤ K·Σ xᵢ²` with each `xᵢ → 0` gives `F → 0`. -/
lemma tendsto_zero_of_sq_bound {l : Filter ℝ} {F : ℝ → ℝ} {xs : Fin 6 → ℝ → ℝ} {K : ℝ}
    (hK : ∀ᶠ t in l, |F t| ≤ K * ∑ i, xs i t ^ 2) (hx : ∀ i, Tendsto (xs i) l (𝓝 0)) :
    Tendsto F l (𝓝 0) := by
  have hsum : Tendsto (fun t => K * ∑ i, xs i t ^ 2) l (𝓝 (K * ∑ _i : Fin 6, (0:ℝ) ^ 2)) :=
    (tendsto_finset_sum _ (fun i _ => (hx i).pow 2)).const_mul K
  simp at hsum
  exact squeeze_zero_norm' (by simpa using hK) hsum

namespace SZTraj
variable {g n : ℝ} (T : SZTraj g n)

/-- A uniform bound on the flux by the squares of its arguments, given bounds on the
    coefficients. -/
lemma flux_bound (hg : 0 < g) (hn : 0 < n) {B : ℝ} (hB : 0 ≤ B)
    (hK : ∀ x, |Kc g n (T.s x) (T.z x)| ≤ B)
    (hc1 : ∀ x, |Vs g (T.s x) - g * cS g (T.s x) (T.z x) - dS (T.s x) (T.z x)| ≤ B)
    (hc2 : ∀ x, |Vs g (T.s x) + g * cS g (T.s x) (T.z x) - n * dS (T.s x) (T.z x)| ≤ B)
    (x v u y1 y1p y2 y2p : ℝ) :
    |Flux g n (T.s x) (T.z x) v u y1 y1p y2 y2p| ≤
      (2 + B + n / θ g + B / θ g + g) * (v ^ 2 + u ^ 2 + y1 ^ 2 + y1p ^ 2 + y2 ^ 2 + y2p ^ 2) := by
  have hθ := θ_pos g hg
  unfold Flux
  set K := Kc g n (T.s x) (T.z x)
  set c1 := Vs g (T.s x) - g * cS g (T.s x) (T.z x) - dS (T.s x) (T.z x)
  set c2 := Vs g (T.s x) + g * cS g (T.s x) (T.z x) - n * dS (T.s x) (T.z x)
  have hK' := hK x; have hc1' := hc1 x; have hc2' := hc2 x
  have ab : ∀ p q : ℝ, |p * q| ≤ (p ^ 2 + q ^ 2) / 2 := by
    intro p q; rw [abs_le]; constructor <;> nlinarith [sq_nonneg (p + q), sq_nonneg (p - q)]
  have t1 : |v ^ 2 / 2| ≤ v ^ 2 / 2 := by rw [abs_of_nonneg (by positivity)]
  have t2 := ab v u
  have t3 := ab y1p y1
  have t4 : |n / θ g * y2p * y2| ≤ n / θ g * ((y2p ^ 2 + y2 ^ 2) / 2) := by
    rw [mul_assoc, abs_mul, abs_of_pos (div_pos hn hθ)]
    exact mul_le_mul_of_nonneg_left (ab _ _) (div_pos hn hθ).le
  have t5 : |K * y1p * y2| ≤ B * ((y1p ^ 2 + y2 ^ 2) / 2) := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul hK' (ab _ _) (abs_nonneg _) hB
  have t6 : |c1 / 2 * y1 ^ 2| ≤ B * y1 ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg y1), abs_div, abs_two]
    have : |c1| / 2 ≤ B := by linarith [abs_nonneg c1]
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have t7 : |c2 / (2 * θ g) * y2 ^ 2| ≤ B / θ g * y2 ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg y2), abs_div, abs_of_pos (mul_pos two_pos hθ)]
    have : |c2| / (2 * θ g) ≤ B / θ g := by
      rw [div_le_div_iff₀ (mul_pos two_pos hθ) hθ]; nlinarith [abs_nonneg c2]
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have t8 : |g * y1 * y2| ≤ g * ((y1 ^ 2 + y2 ^ 2) / 2) := by
    rw [mul_assoc, abs_mul, abs_of_pos hg]
    exact mul_le_mul_of_nonneg_left (ab _ _) hg.le
  have b1 := abs_le.mp t1; have b2 := abs_le.mp t2; have b3 := abs_le.mp t3
  have b4 := abs_le.mp t4; have b5 := abs_le.mp t5; have b6 := abs_le.mp t6
  have b7 := abs_le.mp t7; have b8 := abs_le.mp t8
  have hn0 : 0 ≤ n / θ g := (div_pos hn hθ).le
  have hb0 : 0 ≤ B / θ g := div_nonneg hB hθ.le
  have s1 := sq_nonneg v; have s2 := sq_nonneg u; have s3 := sq_nonneg y1
  have s4 := sq_nonneg y1p; have s5 := sq_nonneg y2; have s6 := sq_nonneg y2p
  have m1 := mul_nonneg hn0 s6; have m2 := mul_nonneg hn0 s5; have m3 := mul_nonneg hb0 s5
  have m4 := mul_nonneg hB s4; have m5 := mul_nonneg hB s5; have m6 := mul_nonneg hB s3
  have m7 := mul_nonneg hg.le s3; have m8 := mul_nonneg hg.le s5
  have m9 := mul_nonneg hB s1; have m10 := mul_nonneg hB s2; have m11 := mul_nonneg hB s6
  have m12 := mul_nonneg hn0 s1; have m13 := mul_nonneg hn0 s2; have m14 := mul_nonneg hn0 s3
  have m15 := mul_nonneg hn0 s4; have m16 := mul_nonneg hb0 s1; have m17 := mul_nonneg hb0 s2
  have m18 := mul_nonneg hb0 s3; have m19 := mul_nonneg hb0 s4; have m20 := mul_nonneg hb0 s6
  have m21 := mul_nonneg hg.le s1; have m22 := mul_nonneg hg.le s2; have m23 := mul_nonneg hg.le s4
  have m24 := mul_nonneg hg.le s6
  rw [abs_le]; constructor <;> linarith

/-- Lower exponential bound for `a` upstream: `a(x) ≥ a(0) e^{Mx}` for `x ≤ 0` when
    `d = a'/a ≤ M`. -/
lemma As_lower (hg : 0 < g) (hn : 0 < n) {M : ℝ} (hM : ∀ x, dS (T.s x) (T.z x) ≤ M) (x : ℝ)
    (hx : x ≤ 0) : As g (T.s 0) * Real.exp (M * x) ≤ As g (T.s x) := by
  -- φ = a e^{-Mx} is antitone
  have hφ : ∀ y, HasDerivAt (fun t => As g (T.s t) * Real.exp (-(M * t)))
      (As g (T.s y) * (dS (T.s y) (T.z y) - M) * Real.exp (-(M * y))) y := by
    intro y
    have h := (T.hasDerivAt_A hg hn y).mul (((hasDerivAt_id y).const_mul M).neg.exp)
    refine hasDerivAt_of_eq h (fun t => by simp) ?_
    simp; ring
  have hanti : Antitone (fun t => As g (T.s t) * Real.exp (-(M * t))) := by
    apply antitone_of_hasDerivAt_nonpos hφ
    intro y
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (T.As_pos hg hn y).le (by linarith [hM y]))
      (Real.exp_pos _).le
  have := hanti hx
  simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at this
  have he : Real.exp (-(M * x)) * Real.exp (M * x) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (M * x) := Real.exp_pos _
  calc As g (T.s 0) * Real.exp (M * x) ≤ As g (T.s x) * Real.exp (-(M * x)) * Real.exp (M * x) :=
        mul_le_mul_of_nonneg_right this hpos.le
    _ = As g (T.s x) := by rw [mul_assoc, he, mul_one]

end SZTraj

/-- Coefficients are bounded when `(s,z)` stays in a compact set. -/
lemma coeff_bounds {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (T : SZTraj g n) {zl zh : ℝ}
    (hz : ∀ x, zl ≤ T.z x ∧ T.z x ≤ zh) :
    ∃ B, 0 ≤ B ∧ ∀ x, |Kc g n (T.s x) (T.z x)| ≤ B ∧ |cS g (T.s x) (T.z x)| ≤ B ∧
      |c1S g n (T.s x) (T.z x)| ≤ B ∧ |dS (T.s x) (T.z x)| ≤ B ∧
      |Vs g (T.s x) - g * cS g (T.s x) (T.z x) - dS (T.s x) (T.z x)| ≤ B ∧
      |Vs g (T.s x) + g * cS g (T.s x) (T.z x) - n * dS (T.s x) (T.z x)| ≤ B := by
  set Kset := Icc (0:ℝ) 1 ×ˢ Icc zl zh
  have hKc : IsCompact Kset := isCompact_Icc.prod isCompact_Icc
  have hg2 : g + 2 ≠ 0 := by linarith
  let F : ℝ × ℝ → ℝ := fun p => |Kc g n p.1 p.2| + |cS g p.1 p.2| + |c1S g n p.1 p.2|
    + |dS p.1 p.2| + |Vs g p.1 - g * cS g p.1 p.2 - dS p.1 p.2|
    + |Vs g p.1 + g * cS g p.1 p.2 - n * dS p.1 p.2|
  have hF : Continuous F := by
    simp only [F, Kc, cS, c1S, dS, Vs, As, θ]
    fun_prop (disch := assumption)
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  have hmem : (T.s x, T.z x) ∈ Kset := ⟨⟨(T.s_pos x).le, (T.s_lt x).le⟩, hz x⟩
  have h := hB _ hmem
  rw [Real.norm_eq_abs] at h
  have hFx : F (T.s x, T.z x) ≤ max B 0 := le_trans (le_abs_self _) (le_trans h (le_max_left _ _))
  simp only [F] at hFx
  have := abs_nonneg (Kc g n (T.s x) (T.z x)); have := abs_nonneg (cS g (T.s x) (T.z x))
  have := abs_nonneg (c1S g n (T.s x) (T.z x)); have := abs_nonneg (dS (T.s x) (T.z x))
  have := abs_nonneg (Vs g (T.s x) - g * cS g (T.s x) (T.z x) - dS (T.s x) (T.z x))
  have := abs_nonneg (Vs g (T.s x) + g * cS g (T.s x) (T.z x) - n * dS (T.s x) (T.z x))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma tendsto_zero_of_sq {l : Filter ℝ} {q : ℝ → ℝ} (h : Tendsto (fun x => q x ^ 2) l (𝓝 0)) :
    Tendsto q l (𝓝 0) := by
  have hs : Tendsto (fun x => Real.sqrt (q x ^ 2)) l (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h
    rw [Real.sqrt_zero] at this; exact this
  apply squeeze_zero_norm _ hs
  intro x; rw [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

/-- Upstream: `f/w → 0` when `|f| ≤ C e^{ωx}`, `w² ≥ a₀ e^{Mx}` and `2ω > M`. -/
lemma up_ratio {f w : ℝ → ℝ} {C ω M a0 : ℝ} (ha0 : 0 < a0) (hw : ∀ x, 0 < w x)
    (hf : ∀ x ≤ 0, |f x| ≤ C * Real.exp (ω * x))
    (hlow : ∀ x ≤ 0, a0 * Real.exp (M * x) ≤ w x ^ 2) (hωM : M < 2 * ω) :
    Tendsto (fun x => f x / w x) atBot (𝓝 0) := by
  apply tendsto_zero_of_sq
  have e : Tendsto (fun x => C ^ 2 / a0 * Real.exp ((2 * ω - M) * x)) atBot (𝓝 0) := by
    have : Tendsto (fun x => (2 * ω - M) * x) atBot atBot :=
      tendsto_id.const_mul_atBot (by linarith)
    simpa using (Real.tendsto_exp_atBot.comp this).const_mul (C ^ 2 / a0)
  apply squeeze_zero' (Eventually.of_forall fun x => sq_nonneg _) _ e
  rw [eventually_atBot]
  refine ⟨0, fun x hx => ?_⟩
  have hwx := hw x
  have h1 := hf x hx
  have h2 := hlow x hx
  have hC : 0 ≤ C * Real.exp (ω * x) := le_trans (abs_nonneg _) h1
  have hsq : f x ^ 2 ≤ (C * Real.exp (ω * x)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hexp : Real.exp (ω * x) ^ 2 = Real.exp ((2 * ω - M) * x) * Real.exp (M * x) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hE : (C * Real.exp (ω * x)) ^ 2 = C ^ 2 / a0 * Real.exp ((2 * ω - M) * x) * (a0 * Real.exp (M * x)) := by
    rw [mul_pow, hexp]; field_simp
  rw [div_pow, div_le_iff₀ (by positivity)]
  calc f x ^ 2 ≤ (C * Real.exp (ω * x)) ^ 2 := hsq
    _ = C ^ 2 / a0 * Real.exp ((2 * ω - M) * x) * (a0 * Real.exp (M * x)) := hE
    _ ≤ C ^ 2 / a0 * Real.exp ((2 * ω - M) * x) * w x ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Lemma 8.1.**  For an admissible solution at a nonzero frequency, the total energy
    flux tends to zero at both ends, provided the slope stays in `[zl, zh]` and the
    upstream window `zh/2 < 1/ν` is nonempty. -/
theorem flux_tendsto {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (T : SZTraj g n) {zl zh : ℝ}
    (hz : ∀ x, zl ≤ T.z x ∧ T.z x ≤ zh) (hzl : 0 ≤ zl) (hwin : zh / 2 < 1 / n)
    (hs_top : Tendsto T.s atTop (𝓝 0))
    {lam : ℂ} (S : EigenSol T lam) (hS : Admissible S) :
    let F := fun x => T.flux (fun y => (S.v y).re) (fun y => (S.u y).re)
        (fun y => (S.up y).re) (fun y => (S.h y).re) (fun y => (S.hp y).re) x
      + T.flux (fun y => (S.v y).im) (fun y => (S.u y).im)
        (fun y => (S.up y).im) (fun y => (S.h y).im) (fun y => (S.hp y).im) x
    Tendsto F atBot (𝓝 0) ∧ Tendsto F atTop (𝓝 0) := by
  intro F
  obtain ⟨B, hB0, hB⟩ := coeff_bounds hg hn T hz
  have hθ := θ_pos g hg
  have wpos := T.w_pos hg hn
  have key : ∀ l : Filter ℝ,
      (∀ (φ : ℂ → ℝ), (φ = Complex.re ∨ φ = Complex.im) →
        Tendsto (fun x => φ (S.v x)) l (𝓝 0) ∧ Tendsto (fun x => φ (S.u x)) l (𝓝 0) ∧
        Tendsto (fun x => φ (S.u x) / T.w x) l (𝓝 0) ∧
        Tendsto (fun x => (φ (S.up x) - dS (T.s x) (T.z x) * φ (S.u x) / 2) / T.w x) l (𝓝 0) ∧
        Tendsto (fun x => φ (S.h x) / T.w x) l (𝓝 0) ∧
        Tendsto (fun x => (φ (S.hp x) - dS (T.s x) (T.z x) * φ (S.h x) / 2) / T.w x) l (𝓝 0)) →
      Tendsto F l (𝓝 0) := by
    intro l hl
    have one : ∀ (φ : ℂ → ℝ), (φ = Complex.re ∨ φ = Complex.im) →
        Tendsto (fun x => T.flux (fun y => φ (S.v y)) (fun y => φ (S.u y))
          (fun y => φ (S.up y)) (fun y => φ (S.h y)) (fun y => φ (S.hp y)) x) l (𝓝 0) := by
      intro φ hφ
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hl φ hφ
      apply tendsto_zero_of_sq_bound (K := 2 + B + n / θ g + B / θ g + g)
        (xs := ![fun x => φ (S.v x), fun x => φ (S.u x), fun x => φ (S.u x) / T.w x,
          fun x => (φ (S.up x) - dS (T.s x) (T.z x) * φ (S.u x) / 2) / T.w x,
          fun x => φ (S.h x) / T.w x,
          fun x => (φ (S.hp x) - dS (T.s x) (T.z x) * φ (S.h x) / 2) / T.w x])
      · refine Eventually.of_forall (fun x => ?_)
        have := T.flux_bound hg hn hB0 (fun x => (hB x).1) (fun x => (hB x).2.2.2.2.1)
          (fun x => (hB x).2.2.2.2.2) x (φ (S.v x)) (φ (S.u x)) (φ (S.u x) / T.w x)
          ((φ (S.up x) - dS (T.s x) (T.z x) * φ (S.u x) / 2) / T.w x) (φ (S.h x) / T.w x)
          ((φ (S.hp x) - dS (T.s x) (T.z x) * φ (S.h x) / 2) / T.w x)
        simp only [Fin.sum_univ_six, Matrix.cons_val]
        unfold SZTraj.flux
        linarith
      · intro i; fin_cases i <;> assumption
    have := (one Complex.re (Or.inl rfl)).add (one Complex.im (Or.inr rfl))
    simpa using this
  have hcB : ∀ x, |cS g (T.s x) (T.z x)| ≤ B := fun x => (hB x).2.1
  have hc1B : ∀ x, |c1S g n (T.s x) (T.z x)| ≤ B := fun x => (hB x).2.2.1
  have hdB : ∀ x, |dS (T.s x) (T.z x)| ≤ B := fun x => (hB x).2.2.2.1
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
    obtain ⟨ω, hω1, hω2⟩ : ∃ ω, zh / 2 < ω ∧ ω < 1 / n :=
      ⟨(zh / 2 + 1 / n) / 2, by linarith, by linarith⟩
    obtain ⟨C, hC⟩ := hS.up_decay ω hω2
    have hdM : ∀ x, dS (T.s x) (T.z x) ≤ zh := by
      intro x; unfold dS; have := T.s_pos x; have := T.s_lt x; have := (hz x).1; have := (hz x).2
      nlinarith
    have a0 := T.As_pos hg hn 0
    have hlow : ∀ x ≤ 0, As g (T.s 0) * Real.exp (zh * x) ≤ T.w x ^ 2 := by
      intro x hx; rw [T.w_sq hg hn x]; exact T.As_lower hg hn hdM x hx
    have hωpos : 0 < ω := by linarith [hzl, (hz 0).1, (hz 0).2]
    have bnd : ∀ {f : ℝ → ℝ} (K : ℝ), (∀ x ≤ 0, |f x| ≤ K * Real.exp (ω * x)) →
        Tendsto (fun x => f x / T.w x) atBot (𝓝 0) := fun K hf =>
      up_ratio a0 wpos hf hlow (by linarith)
    have bnd0 : ∀ {f : ℝ → ℝ} (K : ℝ), (∀ x ≤ 0, |f x| ≤ K * Real.exp (ω * x)) →
        Tendsto f atBot (𝓝 0) := by
      intro f K hf
      have e : Tendsto (fun x => K * Real.exp (ω * x)) atBot (𝓝 0) := by
        have : Tendsto (fun x => ω * x) atBot atBot := tendsto_id.const_mul_atBot hωpos
        simpa using (Real.tendsto_exp_atBot.comp this).const_mul K
      apply squeeze_zero_norm' _ e
      rw [eventually_atBot]; exact ⟨0, fun x hx => by rw [Real.norm_eq_abs]; exact hf x hx⟩
    have Ev : ∀ x ≤ 0, |φ (S.v x)| ≤ C * Real.exp (ω * x) := fun x hx =>
      (hφle φ hφ _).trans (hC x hx).1
    have Eu : ∀ x ≤ 0, |φ (S.u x)| ≤ C * Real.exp (ω * x) := fun x hx =>
      (hφle φ hφ _).trans (hC x hx).2.1
    have Eup : ∀ x ≤ 0, |φ (S.up x)| ≤ C * Real.exp (ω * x) := fun x hx =>
      (hφle φ hφ _).trans (hC x hx).2.2.1
    have Eε : ∀ x ≤ 0, |φ (S.ε x)| ≤ C * Real.exp (ω * x) := fun x hx =>
      (hφle φ hφ _).trans (hC x hx).2.2.2.1
    have Eεp : ∀ x ≤ 0, |φ (S.εp x)| ≤ C * Real.exp (ω * x) := fun x hx =>
      (hφle φ hφ _).trans (hC x hx).2.2.2.2
    have prodB : ∀ (c : ℝ → ℝ) (f : ℝ → ℝ), (∀ x, |c x| ≤ B) →
        (∀ x ≤ 0, |f x| ≤ C * Real.exp (ω * x)) → ∀ x ≤ 0, |c x * f x| ≤ B * C * Real.exp (ω * x) := by
      intro c f hc hf x hx
      rw [abs_mul, mul_assoc]
      exact mul_le_mul (hc x) (hf x hx) (abs_nonneg _) hB0
    have Eh : ∀ x ≤ 0, |φ (S.h x)| ≤ (C + B * C) * Real.exp (ω * x) := by
      intro x hx
      rw [(hcomp φ hφ x).1]
      have := prodB _ _ hcB Eu x hx
      calc _ ≤ |φ (S.ε x)| + |cS g (T.s x) (T.z x) * φ (S.u x)| := abs_add_le _ _
        _ ≤ _ := by have := Eε x hx; nlinarith
    have Eup' : ∀ x ≤ 0, |φ (S.up x) - dS (T.s x) (T.z x) * φ (S.u x) / 2|
        ≤ (C + B * C) * Real.exp (ω * x) := by
      intro x hx
      have := prodB _ _ hdB Eu x hx
      calc _ ≤ |φ (S.up x)| + |dS (T.s x) (T.z x) * φ (S.u x) / 2| := abs_sub _ _
        _ ≤ _ := by
          rw [abs_div, abs_two]; have := Eup x hx
          have : 0 ≤ B * C * Real.exp (ω * x) := le_trans (abs_nonneg _) (prodB _ _ hdB Eu x hx)
          nlinarith
    have Ehp : ∀ x ≤ 0, |φ (S.hp x) - dS (T.s x) (T.z x) * φ (S.h x) / 2|
        ≤ (C + 2 * B * C + B * (C + B * C)) * Real.exp (ω * x) := by
      intro x hx
      rw [(hcomp φ hφ x).2]
      have h1 := prodB _ _ hcB Eup x hx
      have h2 := prodB _ _ hc1B Eu x hx
      have h3 : |dS (T.s x) (T.z x) * φ (S.h x)| ≤ B * ((C + B * C) * Real.exp (ω * x)) := by
        rw [abs_mul]; exact mul_le_mul (hdB x) (Eh x hx) (abs_nonneg _) hB0
      have h4 := Eεp x hx
      have e : φ (S.εp x) + cS g (T.s x) (T.z x) * φ (S.up x) + c1S g n (T.s x) (T.z x) * φ (S.u x)
          - dS (T.s x) (T.z x) * φ (S.h x) / 2 = φ (S.εp x) + cS g (T.s x) (T.z x) * φ (S.up x)
          + c1S g n (T.s x) (T.z x) * φ (S.u x) - (dS (T.s x) (T.z x) * φ (S.h x)) / 2 := by ring
      rw [e]
      have t := abs_sub (φ (S.εp x) + cS g (T.s x) (T.z x) * φ (S.up x)
          + c1S g n (T.s x) (T.z x) * φ (S.u x)) ((dS (T.s x) (T.z x) * φ (S.h x)) / 2)
      have t2 := abs_add_le (φ (S.εp x) + cS g (T.s x) (T.z x) * φ (S.up x))
          (c1S g n (T.s x) (T.z x) * φ (S.u x))
      have t3 := abs_add_le (φ (S.εp x)) (cS g (T.s x) (T.z x) * φ (S.up x))
      rw [abs_div, abs_two] at t
      have : 0 ≤ (B * ((C + B * C) * Real.exp (ω * x))) := le_trans (abs_nonneg _) h3
      nlinarith
    exact ⟨bnd0 C Ev, bnd0 C Eu, bnd C Eu, bnd _ Eup', bnd _ Eh, bnd _ Ehp⟩
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
    have bdd : ∀ {f c : ℝ → ℝ}, (∀ x, |c x| ≤ B) → Tendsto f atTop (𝓝 0) →
        Tendsto (fun x => c x * f x) atTop (𝓝 0) := by
      intro f c hc hf
      have : Tendsto (fun x => B * |f x|) atTop (𝓝 0) := by simpa using (hf.abs).const_mul B
      apply squeeze_zero_norm _ this
      intro x; rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hc x) (abs_nonneg _)
    have hwlim : Tendsto T.w atTop (𝓝 (Real.sqrt (As g 0))) := by
      have : Tendsto (fun x => As g (T.s x)) atTop (𝓝 (As g 0)) := by
        unfold As; exact ((tendsto_const_nhds.sub hs_top).const_mul 2).div_const _
      exact (Real.continuous_sqrt.tendsto _).comp this
    have hw0 : Real.sqrt (As g 0) ≠ 0 := by
      apply (Real.sqrt_pos.mpr _).ne'; unfold As; apply div_pos <;> linarith
    have divw : ∀ {f : ℝ → ℝ}, Tendsto f atTop (𝓝 0) → Tendsto (fun x => f x / T.w x) atTop (𝓝 0) := by
      intro f hf; have := hf.div hwlim hw0; rw [zero_div] at this; exact this
    have Lu := T0 hS.u_top
    have Lup := T0 hS.up_top
    have Lε := T0 hS.ε_top
    have Lεp := T0 hS.εp_top
    have Lh : Tendsto (fun x => φ (S.h x)) atTop (𝓝 0) := by
      have := Lε.add (bdd hcB Lu); simp at this
      exact this.congr (fun x => ((hcomp φ hφ x).1).symm)
    have Lhp : Tendsto (fun x => φ (S.hp x)) atTop (𝓝 0) := by
      have := (Lεp.add (bdd hcB Lup)).add (bdd hc1B Lu); simp at this
      exact this.congr (fun x => ((hcomp φ hφ x).2).symm)
    refine ⟨T0 hS.v_top, Lu, divw Lu, divw ?_, divw Lh, divw ?_⟩
    · have := Lup.sub ((bdd hdB Lu).div_const 2); simpa [mul_div_assoc] using this
    · have := Lhp.sub ((bdd hdB Lh).div_const 2); simpa [mul_div_assoc] using this

end

end StrongShock
