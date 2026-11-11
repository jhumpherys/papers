/-
  Proposition 7.2 (exclusion of nonzero frequencies) for an arbitrary thermal weight
  `ω = W²/2` that follows the profile.
-/
import StrongShock.Exclusion

open Filter Topology Set

namespace StrongShock

noncomputable section

/-- A thermal weight along a trajectory: `W > 0` with derivative `W1`. -/
structure Weight {g n : ℝ} (T : SZTraj g n) where
  W : ℝ → ℝ
  W1 : ℝ → ℝ
  hW : ∀ x, HasDerivAt W (W1 x) x
  pos : ∀ x, 0 < W x

namespace SZTraj
variable {g n : ℝ} (T : SZTraj g n)

/-- The energy flux of one real component along the trajectory. -/
def fluxW (R : Weight T) (v u up h hp : ℝ → ℝ) (x : ℝ) : ℝ :=
  FluxW g n (T.s x) (T.z x) (R.W x) (v x) (u x) (up x) (h x) (hp x)

section
variable (hg : 0 < g) (hn : 0 < n)
include hg hn

lemma hasDerivAt_fluxW (R : Weight T) {v vp u up upp h hp hpp : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (vp x) x) (hu : ∀ x, HasDerivAt u (up x) x)
    (hup : ∀ x, HasDerivAt up (upp x) x) (hh : ∀ x, HasDerivAt h (hp x) x)
    (hhp : ∀ x, HasDerivAt hp (hpp x) x) (x : ℝ) :
    HasDerivAt (T.fluxW R v u up h hp)
      (FluxWDeriv g n (T.s x) (T.z x) (R.W x) (R.W1 x) (v x) (vp x) (u x) (up x) (upp x)
        (h x) (hp x) (hpp x)) x := by
  have hA := T.hasDerivAt_A hg hn x
  have hV := T.hasDerivAt_V hg hn x
  have hc := T.hasDerivAt_c hg hn x
  have hd := T.hasDerivAt_d hg hn x
  have hW := R.hW x
  have hApos := T.As_pos hg hn x
  have hWpos := R.pos x
  have hvx := hv x; have hux := hu x; have hupx := hup x; have hhx := hh x; have hhpx := hhp x
  -- p = u' - d u
  have hp' := hupx.sub (hd.mul hux)
  have hAW : As g (T.s x) * R.W x ^ 2 ≠ 0 := by positivity
  have hden := hA.mul (hW.pow 2)
  have T1 := (hvx.pow 2).div_const 2
  have T2 := hux.mul hvx
  have T3 := (hp'.mul hux).div hA hApos.ne'
  have T4 := ((hux.pow 2).const_mul g).div_const 4
  have T5 := ((hux.const_mul g).mul hhx).div hA hApos.ne'
  have N := ((hV.mul (hhx.pow 2)).sub (((hhx.const_mul (2 * n)).mul hhpx))).add
    ((((hc.const_mul (2 * (n - 1))).mul hp').mul hhx))
  have T6 := N.div hden hAW
  have H := ((((T1.sub T2).sub T3).add T4).add T5).add T6
  refine hasDerivAt_of_eq H (fun y => by
    simp only [fluxW, FluxW, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply,
      Pi.pow_apply]; try ring) ?_
  simp only [FluxWDeriv, deltaW, V1S, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply,
    Pi.pow_apply, Nat.cast_ofNat]
  field_simp
  ring

/-- One real component: if the transformed residuals vanish, the flux derivative is minus
    the spectral term minus the normalized energy density. -/
lemma fluxW_deriv_eq (R : Weight T) {v vp u up upp h hp hpp Lv Lu Lh : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (vp x) x)
    (hu : ∀ x, HasDerivAt u (up x) x) (hup : ∀ x, HasDerivAt up (upp x) x)
    (hh : ∀ x, HasDerivAt h (hp x) x) (hhp : ∀ x, HasDerivAt hp (hpp x) x)
    (e1 : ∀ x, Lv x + vp x - up x = 0)
    (e2 : ∀ x, Res2 g n (T.s x) (T.z x) (Lu x) (u x) (up x) (upp x) (hp x) (vp x) = 0)
    (e3 : ∀ x, ResH g n (T.s x) (T.z x) (Lh x) (u x) (up x) (upp x) (hp x) (hpp x) = 0)
    (x : ℝ) :
    HasDerivAt (T.fluxW R v u up h hp)
      (-(Lv x * v x + Vs g (T.s x) / As g (T.s x) * Lu x * u x
          + 2 * Vs g (T.s x) / (As g (T.s x) * R.W x ^ 2) * Lh x * h x)
        - QW g n (T.s x) (T.z x) (R.W x) (R.W1 x) (u x / As g (T.s x))
            (T.w x * (up x - dS (T.s x) (T.z x) * u x) / As g (T.s x)) (h x / (T.w x * R.W x))
            ((hp x - (dS (T.s x) (T.z x) / 2 + R.W1 x / R.W x) * h x) / (T.w x * R.W x))) x := by
  have H := T.hasDerivAt_fluxW hg hn R hv hu hup hh hhp x
  have I := energy_identity_weighted g n (T.s x) (T.z x) (T.w x) (R.W x) (R.W1 x) hg hn
    (T.w_pos hg hn x).ne' (T.w_sq hg hn x) (T.Vs_pos hg hn x).ne' (R.pos x).ne'
    (u x) (up x) (upp x) (h x) (hp x) (hpp x) (v x) (vp x) (Lv x) (Lu x) (Lh x)
  rw [e1 x, e2 x, e3 x] at I
  convert H using 1
  linarith

end

end SZTraj

/-- **Proposition 7.2.** Let the pair form be coercive along the trajectory,
    `k(x) ξ² ≤ (1-κ)Φ² + 2mΦξ + Pξ²` with `k > 0`.  If `λ ≠ 0`, `Re λ ≥ 0`, and the total
    energy flux tends to zero at both ends, then the solution is trivial. -/
theorem exclusionW {g n : ℝ} (hg : 0 < g) (hg2 : g < 2) (hn : 0 < n) (T : SZTraj g n)
    (hz : ∀ x, 0 < T.z x) (R : Weight T) {k : ℝ → ℝ} (hk : ∀ x, 0 < k x)
    (hcoer : ∀ x X Y, k x * Y ^ 2 ≤ pairW g n (T.s x) (T.z x) (R.W x) (R.W1 x) X Y)
    {lam : ℂ} (hlam : lam ≠ 0) (hre : 0 ≤ lam.re) (S : EigenSol T lam)
    (hbot : Tendsto (fun x => T.fluxW R (fun y => (S.v y).re) (fun y => (S.u y).re)
        (fun y => (S.up y).re) (fun y => (S.h y).re) (fun y => (S.hp y).re) x
      + T.fluxW R (fun y => (S.v y).im) (fun y => (S.u y).im)
        (fun y => (S.up y).im) (fun y => (S.h y).im) (fun y => (S.hp y).im) x) atBot (𝓝 0))
    (htop : Tendsto (fun x => T.fluxW R (fun y => (S.v y).re) (fun y => (S.u y).re)
        (fun y => (S.up y).re) (fun y => (S.h y).re) (fun y => (S.hp y).re) x
      + T.fluxW R (fun y => (S.v y).im) (fun y => (S.u y).im)
        (fun y => (S.up y).im) (fun y => (S.h y).im) (fun y => (S.hp y).im) x) atTop (𝓝 0)) :
    ∀ x, S.v x = 0 ∧ S.u x = 0 ∧ S.ε x = 0 := by
  set F := fun x => T.fluxW R (fun y => (S.v y).re) (fun y => (S.u y).re)
        (fun y => (S.up y).re) (fun y => (S.h y).re) (fun y => (S.hp y).re) x
      + T.fluxW R (fun y => (S.v y).im) (fun y => (S.u y).im)
        (fun y => (S.up y).im) (fun y => (S.h y).im) (fun y => (S.hp y).im) x with hF
  have rv := fun x => hasDerivAt_re' (S.hv x)
  have ru := fun x => hasDerivAt_re' (S.hu x)
  have rup := fun x => hasDerivAt_re' (S.hup x)
  have rh := fun x => hasDerivAt_re' (S.hh hg hn x)
  have rhp := fun x => hasDerivAt_re' (S.hhp hg hn x)
  have iv := fun x => hasDerivAt_im' (S.hv x)
  have iu := fun x => hasDerivAt_im' (S.hu x)
  have iup := fun x => hasDerivAt_im' (S.hup x)
  have ih := fun x => hasDerivAt_im' (S.hh hg hn x)
  have ihp := fun x => hasDerivAt_im' (S.hhp hg hn x)
  have tr := fun x => S.transformed hg hn x
  have Vpos := T.Vs_pos hg hn
  have Re1 : ∀ x, (lam * S.v x).re + (S.vp x).re - (S.up x).re = 0 := by
    intro x; have := congrArg Complex.re (S.eq1 x); simp only [Complex.add_re] at this; linarith
  have Ie1 : ∀ x, (lam * S.v x).im + (S.vp x).im - (S.up x).im = 0 := by
    intro x; have := congrArg Complex.im (S.eq1 x); simp only [Complex.add_im] at this; linarith
  have Re2 : ∀ x, Res2 g n (T.s x) (T.z x) (lam * S.u x).re (S.u x).re (S.up x).re (S.upp x).re
      (S.hp x).re (S.vp x).re = 0 := by
    intro x; have := congrArg Complex.re (tr x).1
    simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.zero_re] at this
    rw [← this]; unfold Res2; have := Vpos x; field_simp
  have Ie2 : ∀ x, Res2 g n (T.s x) (T.z x) (lam * S.u x).im (S.u x).im (S.up x).im (S.upp x).im
      (S.hp x).im (S.vp x).im = 0 := by
    intro x; have := congrArg Complex.im (tr x).1
    simp only [Complex.add_im, Complex.sub_im, Complex.im_ofReal_mul, Complex.zero_im] at this
    rw [← this]; unfold Res2; have := Vpos x; field_simp
  have Re3 : ∀ x, ResH g n (T.s x) (T.z x) (lam * S.h x).re (S.u x).re (S.up x).re (S.upp x).re
      (S.hp x).re (S.hpp x).re = 0 := by
    intro x; have := congrArg Complex.re (tr x).2
    simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.zero_re] at this
    rw [← this]; unfold ResH; have := Vpos x; field_simp
  have Ie3 : ∀ x, ResH g n (T.s x) (T.z x) (lam * S.h x).im (S.u x).im (S.up x).im (S.upp x).im
      (S.hp x).im (S.hpp x).im = 0 := by
    intro x; have := congrArg Complex.im (tr x).2
    simp only [Complex.add_im, Complex.sub_im, Complex.im_ofReal_mul, Complex.zero_im] at this
    rw [← this]; unfold ResH; have := Vpos x; field_simp
  have DR := T.fluxW_deriv_eq hg hn R rv ru rup rh rhp Re1 Re2 Re3
  have DI := T.fluxW_deriv_eq hg hn R iv iu iup ih ihp Ie1 Ie2 Ie3
  -- shorthand for the normalized variables
  set φr := fun x => (S.u x).re / As g (T.s x)
  set φi := fun x => (S.u x).im / As g (T.s x)
  set ξr := fun x => (S.h x).re / (T.w x * R.W x)
  set ξi := fun x => (S.h x).im / (T.w x * R.W x)
  set D := fun x => (-((lam * S.v x).re * (S.v x).re
          + Vs g (T.s x) / As g (T.s x) * (lam * S.u x).re * (S.u x).re
          + 2 * Vs g (T.s x) / (As g (T.s x) * R.W x ^ 2) * (lam * S.h x).re * (S.h x).re)
        - QW g n (T.s x) (T.z x) (R.W x) (R.W1 x) (φr x)
            (T.w x * ((S.up x).re - dS (T.s x) (T.z x) * (S.u x).re) / As g (T.s x)) (ξr x)
            (((S.hp x).re - (dS (T.s x) (T.z x) / 2 + R.W1 x / R.W x) * (S.h x).re)
              / (T.w x * R.W x)))
      + (-((lam * S.v x).im * (S.v x).im
          + Vs g (T.s x) / As g (T.s x) * (lam * S.u x).im * (S.u x).im
          + 2 * Vs g (T.s x) / (As g (T.s x) * R.W x ^ 2) * (lam * S.h x).im * (S.h x).im)
        - QW g n (T.s x) (T.z x) (R.W x) (R.W1 x) (φi x)
            (T.w x * ((S.up x).im - dS (T.s x) (T.z x) * (S.u x).im) / As g (T.s x)) (ξi x)
            (((S.hp x).im - (dS (T.s x) (T.z x) / 2 + R.W1 x / R.W x) * (S.h x).im)
              / (T.w x * R.W x))) with hD
  have hFD : ∀ x, HasDerivAt F (D x) x := fun x => (DR x).add (DI x)
  have hspec : ∀ (z : ℂ) (r : ℝ), 0 ≤ r →
      0 ≤ r * (lam * z).re * z.re + r * (lam * z).im * z.im := by
    intro z r hr
    have : r * (lam * z).re * z.re + r * (lam * z).im * z.im = r * lam.re * (z.re ^ 2 + z.im ^ 2) := by
      simp only [Complex.mul_re, Complex.mul_im]; ring
    rw [this]; positivity
  -- lower bound for the energy density
  have hQ : ∀ x p X ξ ξp, (1 - g / 2) * As g (T.s x) * (As g (T.s x) * dS (T.s x) (T.z x)) * p ^ 2
      + k x * ξ ^ 2 ≤ QW g n (T.s x) (T.z x) (R.W x) (R.W1 x) p X ξ ξp := by
    intro x p X ξ ξp
    unfold QW
    have := hcoer x X ξ
    have := sq_nonneg (ξp + g * cS g (T.s x) (T.z x) * ξ / (2 * n)
      - (n - 1) * cS g (T.s x) (T.z x) * X / (2 * n * R.W x))
    nlinarith
  have hca : ∀ x, 0 < (1 - g / 2) * As g (T.s x) * (As g (T.s x) * dS (T.s x) (T.z x)) := by
    intro x
    have := T.As_pos hg hn x
    have : 0 < dS (T.s x) (T.z x) := by unfold dS; exact mul_pos (T.s_pos x) (hz x)
    have : 0 < 1 - g / 2 := by linarith
    positivity
  have hDle : ∀ x, D x ≤ -(((1 - g / 2) * As g (T.s x) * (As g (T.s x) * dS (T.s x) (T.z x)))
      * (φr x ^ 2 + φi x ^ 2) + k x * (ξr x ^ 2 + ξi x ^ 2)) := by
    intro x
    have a1 := hspec (S.v x) 1 zero_le_one
    have hA := T.As_pos hg hn x
    have hWp := R.pos x
    have a2 := hspec (S.u x) (Vs g (T.s x) / As g (T.s x)) (by have := Vpos x; positivity)
    have a3 := hspec (S.h x) (2 * Vs g (T.s x) / (As g (T.s x) * R.W x ^ 2))
      (by have := Vpos x; positivity)
    have q1 := hQ x (φr x) (T.w x * ((S.up x).re - dS (T.s x) (T.z x) * (S.u x).re) / As g (T.s x))
      (ξr x) (((S.hp x).re - (dS (T.s x) (T.z x) / 2 + R.W1 x / R.W x) * (S.h x).re)
              / (T.w x * R.W x))
    have q2 := hQ x (φi x) (T.w x * ((S.up x).im - dS (T.s x) (T.z x) * (S.u x).im) / As g (T.s x))
      (ξi x) (((S.hp x).im - (dS (T.s x) (T.z x) / 2 + R.W1 x / R.W x) * (S.h x).im)
              / (T.w x * R.W x))
    simp only [hD]
    nlinarith
  have hDnp : ∀ x, D x ≤ 0 := by
    intro x
    have := hDle x
    have := hca x
    have := hk x
    have : 0 ≤ ((1 - g / 2) * As g (T.s x) * (As g (T.s x) * dS (T.s x) (T.z x)))
      * (φr x ^ 2 + φi x ^ 2) + k x * (ξr x ^ 2 + ξi x ^ 2) := by positivity
    linarith
  have hanti : Antitone F := antitone_of_hasDerivAt_nonpos hFD hDnp
  have hF0 : ∀ x, F x = 0 := by
    intro x
    apply le_antisymm
    · exact ge_of_tendsto hbot (eventually_atBot.mpr ⟨x, fun y hy => hanti hy⟩)
    · exact le_of_tendsto htop (eventually_atTop.mpr ⟨x, fun y hy => hanti hy⟩)
  have hD0 : ∀ x, D x = 0 := by
    intro x
    have h1 : HasDerivAt F 0 x := by
      have : F = fun _ => 0 := funext hF0
      rw [this]; exact hasDerivAt_const x 0
    exact (hFD x).unique h1
  have huh : ∀ x, S.u x = 0 ∧ S.h x = 0 := by
    intro x
    have h0 := hDle x
    rw [hD0 x] at h0
    have hc := hca x
    have hkx := hk x
    have s1 := sq_nonneg (φr x); have s2 := sq_nonneg (φi x)
    have s3 := sq_nonneg (ξr x); have s4 := sq_nonneg (ξi x)
    have m1 := mul_nonneg hc.le (add_nonneg s1 s2)
    have m2 := mul_nonneg hkx.le (add_nonneg s3 s4)
    have z1 : φr x ^ 2 + φi x ^ 2 = 0 := by
      by_contra hne
      have : 0 < φr x ^ 2 + φi x ^ 2 := lt_of_le_of_ne (add_nonneg s1 s2) (Ne.symm hne)
      have := mul_pos hc this
      linarith
    have z2 : ξr x ^ 2 + ξi x ^ 2 = 0 := by
      by_contra hne
      have : 0 < ξr x ^ 2 + ξi x ^ 2 := lt_of_le_of_ne (add_nonneg s3 s4) (Ne.symm hne)
      have := mul_pos hkx this
      linarith
    have e1 : φr x = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
    have e2 : φi x = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
    have e3 : ξr x = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
    have e4 : ξi x = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
    have hA := (T.As_pos hg hn x).ne'
    have hwW : T.w x * R.W x ≠ 0 := (mul_pos (T.w_pos hg hn x) (R.pos x)).ne'
    simp only [φr, φi, ξr, ξi, div_eq_zero_iff, hA, hwW, or_false] at e1 e2 e3 e4
    exact ⟨Complex.ext e1 e2, Complex.ext e3 e4⟩
  have hu0 : ∀ x, S.up x = 0 ∧ S.upp x = 0 := by
    have hfun : S.u = fun _ => 0 := funext fun x => (huh x).1
    have hup0 : ∀ x, S.up x = 0 := fun x => by
      have h1 : HasDerivAt S.u 0 x := by rw [hfun]; exact hasDerivAt_const x 0
      exact (S.hu x).unique h1
    refine fun x => ⟨hup0 x, ?_⟩
    have hfun' : S.up = fun _ => 0 := funext hup0
    have h1 : HasDerivAt S.up 0 x := by rw [hfun']; exact hasDerivAt_const x 0
    exact (S.hup x).unique h1
  have hh0 : ∀ x, S.hp x = 0 := by
    have hfun : S.h = fun _ => 0 := funext fun x => (huh x).2
    intro x
    have h1 : HasDerivAt S.h 0 x := by rw [hfun]; exact hasDerivAt_const x 0
    exact (S.hh hg hn x).unique h1
  intro x
  have T2 := (tr x).1
  rw [(huh x).1, (hu0 x).1, (hu0 x).2, hh0 x] at T2
  have hA : (As g (T.s x) / Vs g (T.s x) : ℝ) ≠ 0 := by
    have := T.As_pos hg hn x; have := Vpos x; positivity
  have hvp : S.vp x = 0 := by
    simp only [mul_zero, add_zero, zero_sub, zero_add, neg_eq_zero, sub_zero] at T2
    rcases mul_eq_zero.mp T2 with h | h
    · exact absurd (by exact_mod_cast h) hA
    · exact h
  have E1 := S.eq1 x
  rw [hvp, (hu0 x).1, add_zero] at E1
  have hv0 : S.v x = 0 := by
    rcases mul_eq_zero.mp E1 with h | h
    · exact absurd h hlam
    · exact h
  refine ⟨hv0, (huh x).1, ?_⟩
  have : S.ε x = S.h x - (cS g (T.s x) (T.z x) : ℂ) * S.u x := by unfold EigenSol.h; ring
  rw [this, (huh x).1, (huh x).2]; ring

end

end StrongShock
