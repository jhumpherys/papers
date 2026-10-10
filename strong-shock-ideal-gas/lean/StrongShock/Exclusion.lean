/-
  Exclusion of nonzero frequencies (Section 8, Proposition 8.2).

  The argument is the energy method of Section 5 in pointwise form:  along a solution,
  the energy flux `𝓕` satisfies `𝓕' = -(Re λ)·E_dens - Q_dens ≤ 0`; since `𝓕 → 0` at both
  ends, `𝓕 ≡ 0`, which forces `Q_dens ≡ 0` and hence, by coercivity, a trivial solution.
-/
import StrongShock.Profile
import Mathlib.Analysis.Complex.RealDeriv

open Filter Topology Set

namespace StrongShock

noncomputable section

lemma hasDerivAt_re' {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).re) f'.re x := by
  have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  exact this

lemma hasDerivAt_im' {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun y => (f y).im) f'.im x := by
  have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x h
  exact this

namespace SZTraj
variable {g n : ℝ} (T : SZTraj g n)

/-- `w = √a` along the trajectory. -/
def w (x : ℝ) : ℝ := Real.sqrt (As g (T.s x))

lemma w_pos (hg : 0 < g) (hn : 0 < n) (x : ℝ) : 0 < T.w x :=
  Real.sqrt_pos.mpr (T.As_pos hg hn x)

lemma w_sq (hg : 0 < g) (hn : 0 < n) (x : ℝ) : T.w x ^ 2 = As g (T.s x) :=
  Real.sq_sqrt (T.As_pos hg hn x).le

/-- The real energy flux of one real component, written in terms of `v, u, u', h, h'`. -/
def flux (v u up h hp : ℝ → ℝ) (x : ℝ) : ℝ :=
  Flux g n (T.s x) (T.z x) (v x) (u x) (u x / T.w x)
    ((up x - dS (T.s x) (T.z x) * u x / 2) / T.w x) (h x / T.w x)
    ((hp x - dS (T.s x) (T.z x) * h x / 2) / T.w x)

section
variable (hg : 0 < g) (hn : 0 < n)
include hg hn

/-- Derivative of `y = u/w`. -/
lemma hasDerivAt_y {u up : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (up x) x) (x : ℝ) :
    HasDerivAt (fun y => u y / T.w y) ((up x - dS (T.s x) (T.z x) * u x / 2) / T.w x) x := by
  have hw := T.hasDerivAt_w hg hn x
  have hwp := T.w_pos hg hn x
  have h := (hu x).div hw hwp.ne'
  refine hasDerivAt_of_eq h (fun y => by simp only [w, Pi.div_apply]) ?_
  have hw0 : Real.sqrt (As g (T.s x)) ≠ 0 := hwp.ne'
  simp only [w, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply]
  field_simp

/-- Derivative of `y' = (u' - d u/2)/w`. -/
lemma hasDerivAt_yp {u up upp : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (up x) x)
    (hup : ∀ x, HasDerivAt up (upp x) x) (x : ℝ) :
    HasDerivAt (fun y => (up y - dS (T.s y) (T.z y) * u y / 2) / T.w y)
      ((upp x - dS (T.s x) (T.z x) * up x
        - (d1S g n (T.s x) (T.z x) / 2 - dS (T.s x) (T.z x) ^ 2 / 4) * u x) / T.w x) x := by
  have hw := T.hasDerivAt_w hg hn x
  have hwp := T.w_pos hg hn x
  have hd := T.hasDerivAt_d hg hn x
  have h := ((hup x).sub ((hd.mul (hu x)).div_const 2)).div hw hwp.ne'
  refine hasDerivAt_of_eq h (fun y => by simp only [w, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply]) ?_
  have hw0 : Real.sqrt (As g (T.s x)) ≠ 0 := hwp.ne'
  simp only [w, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply]
  field_simp
  ring

/-- Derivative of the energy flux of one component. -/
lemma hasDerivAt_flux {v vp u up upp h hp hpp : ℝ → ℝ} (hv : ∀ x, HasDerivAt v (vp x) x)
    (hu : ∀ x, HasDerivAt u (up x) x) (hup : ∀ x, HasDerivAt up (upp x) x)
    (hh : ∀ x, HasDerivAt h (hp x) x) (hhp : ∀ x, HasDerivAt hp (hpp x) x) (x : ℝ) :
    HasDerivAt (T.flux v u up h hp)
      (FluxDeriv g n (T.s x) (T.z x) (v x) (vp x) (u x) (up x)
        (u x / T.w x) ((up x - dS (T.s x) (T.z x) * u x / 2) / T.w x)
        ((upp x - dS (T.s x) (T.z x) * up x
          - (d1S g n (T.s x) (T.z x) / 2 - dS (T.s x) (T.z x) ^ 2 / 4) * u x) / T.w x)
        (h x / T.w x) ((hp x - dS (T.s x) (T.z x) * h x / 2) / T.w x)
        ((hpp x - dS (T.s x) (T.z x) * hp x
          - (d1S g n (T.s x) (T.z x) / 2 - dS (T.s x) (T.z x) ^ 2 / 4) * h x) / T.w x)) x := by
  have y1 := T.hasDerivAt_y hg hn hu x
  have y1p := T.hasDerivAt_yp hg hn hu hup x
  have y2 := T.hasDerivAt_y hg hn hh x
  have y2p := T.hasDerivAt_yp hg hn hh hhp x
  have hV := T.hasDerivAt_V hg hn x
  have hc := T.hasDerivAt_c hg hn x
  have hd := T.hasDerivAt_d hg hn x
  have hK := T.hasDerivAt_K hg hn x
  have hvx := hv x
  have hux := hu x
  have A1 := (hvx.pow 2).div_const 2
  have A2 := hvx.mul hux
  have A3 := y1p.mul y1
  have A4 := (y2p.mul y2).const_mul (n / θ g)
  have A5 := (hK.mul y1p).mul y2
  have A6 := (((hV.sub (hc.const_mul g)).sub hd).div_const 2).mul (y1.pow 2)
  have A7 := ((((hV.add (hc.const_mul g)).sub (hd.const_mul n)).div_const (2 * θ g))).mul (y2.pow 2)
  have A8 := (y1.const_mul g).mul y2
  have H := ((((((A1.sub A2).sub A3).sub A4).sub A5).add A6).add A7).add A8
  refine hasDerivAt_of_eq H (fun y => by simp only [flux, Flux, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply]; ring) ?_
  simp only [FluxDeriv, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply, Nat.cast_ofNat]
  ring

/-- One real component: if the (real parts of the) transformed residuals vanish, the flux
    derivative equals minus the spectral term minus the energy density. -/
lemma flux_deriv_eq {v vp u up upp h hp hpp Lv Lu Lh : ℝ → ℝ}
    (hv : ∀ x, HasDerivAt v (vp x) x)
    (hu : ∀ x, HasDerivAt u (up x) x) (hup : ∀ x, HasDerivAt up (upp x) x)
    (hh : ∀ x, HasDerivAt h (hp x) x) (hhp : ∀ x, HasDerivAt hp (hpp x) x)
    (e1 : ∀ x, Lv x + vp x - up x = 0)
    (e2 : ∀ x, Res2 g n (T.s x) (T.z x) (Lu x) (u x) (up x) (upp x) (hp x) (vp x) = 0)
    (e3 : ∀ x, ResH g n (T.s x) (T.z x) (Lh x) (u x) (up x) (upp x) (hp x) (hpp x) = 0)
    (x : ℝ) :
    HasDerivAt (T.flux v u up h hp)
      (-(Lv x * v x + Vs g (T.s x) / As g (T.s x) * Lu x * u x
          + Vs g (T.s x) / (As g (T.s x) * θ g) * Lh x * h x)
        - Qform g n (T.s x) (T.z x) ((up x - dS (T.s x) (T.z x) * u x / 2) / T.w x)
            ((hp x - dS (T.s x) (T.z x) * h x / 2) / T.w x) (u x / T.w x) (h x / T.w x)) x := by
  have H := T.hasDerivAt_flux hg hn hv hu hup hh hhp x
  have I := energy_identity_jet g n (T.s x) (T.z x) (T.w x) hg hn (T.w_pos hg hn x).ne'
    (T.w_sq hg hn x) (T.Vs_pos hg hn x).ne' (u x) (up x) (upp x) (h x) (hp x) (hpp x) (v x)
    (vp x) (Lv x) (Lu x) (Lh x)
  dsimp only at I
  rw [e1 x, e2 x, e3 x] at I
  convert H using 1
  linarith

end

end SZTraj

/-! ### The spectral problem and the exclusion theorem -/

/-- A solution of the integrated eigenvalue equations (3.1)–(3.3) along a limiting
    profile, with all the derivatives that appear. -/
structure EigenSol {g n : ℝ} (T : SZTraj g n) (lam : ℂ) where
  v : ℝ → ℂ
  u : ℝ → ℂ
  ε : ℝ → ℂ
  vp : ℝ → ℂ
  up : ℝ → ℂ
  upp : ℝ → ℂ
  εp : ℝ → ℂ
  εpp : ℝ → ℂ
  hv : ∀ x, HasDerivAt v (vp x) x
  hu : ∀ x, HasDerivAt u (up x) x
  hup : ∀ x, HasDerivAt up (upp x) x
  hε : ∀ x, HasDerivAt ε (εp x) x
  hεp : ∀ x, HasDerivAt εp (εpp x) x
  /-- (3.1) -/
  eq1 : ∀ x, lam * v x + vp x = up x
  /-- (3.2) -/
  eq2 : ∀ x, lam * u x + up x + (g / Vs g (T.s x) : ℝ) * εp x
      + (g * V1S g (T.s x) (T.z x) / Vs g (T.s x) : ℝ) * u x
      - (As g (T.s x) / Vs g (T.s x) : ℝ) * vp x = (1 / Vs g (T.s x) : ℝ) * upp x
  /-- (3.3) -/
  eq3 : ∀ x, lam * ε x + εp x
      + (V1S g (T.s x) (T.z x) - n * V2S g n (T.s x) (T.z x) / Vs g (T.s x) : ℝ) * u x
      + (As g (T.s x) - n * V1S g (T.s x) (T.z x) / Vs g (T.s x) : ℝ) * up x
      + (n * e1S g n (T.s x) (T.z x) / Vs g (T.s x) ^ 2 : ℝ) * vp x
      = (n / Vs g (T.s x) : ℝ) * εpp x

namespace EigenSol
variable {g n : ℝ} {T : SZTraj g n} {lam : ℂ} (S : EigenSol T lam)

/-- The thermal variable `h = ε + c u` and its derivatives. -/
def h (x : ℝ) : ℂ := S.ε x + (cS g (T.s x) (T.z x) : ℂ) * S.u x
def hp (x : ℝ) : ℂ := S.εp x + (cS g (T.s x) (T.z x) : ℂ) * S.up x
  + (c1S g n (T.s x) (T.z x) : ℂ) * S.u x
def hpp (x : ℝ) : ℂ := S.εpp x + (cS g (T.s x) (T.z x) : ℂ) * S.upp x
  + 2 * (c1S g n (T.s x) (T.z x) : ℂ) * S.up x + (c2S g n (T.s x) (T.z x) : ℂ) * S.u x

section
variable (hg : 0 < g) (hn : 0 < n)
include hg hn

lemma hasDerivAt_ofReal {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (fun y => (f y : ℂ)) (f' x : ℂ) x := (hf x).ofReal_comp

lemma hh (x : ℝ) : HasDerivAt S.h (S.hp x) x := by
  have hc := hasDerivAt_ofReal hg hn (T.hasDerivAt_c hg hn) x
  have := (S.hε x).add (hc.mul (S.hu x))
  refine hasDerivAt_of_eq this (fun y => by simp only [h, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]) ?_
  unfold hp; ring

lemma hhp (x : ℝ) : HasDerivAt S.hp (S.hpp x) x := by
  have hc := hasDerivAt_ofReal hg hn (T.hasDerivAt_c hg hn) x
  have hc1 := hasDerivAt_ofReal hg hn (T.hasDerivAt_c1 hg hn) x
  have := ((S.hεp x).add (hc.mul (S.hup x))).add (hc1.mul (S.hu x))
  refine hasDerivAt_of_eq this (fun y => by simp only [hp, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]) ?_
  unfold hpp; ring

/-- The transformed equations (4.5), (4.6) in complex form. -/
lemma transformed (x : ℝ) :
    lam * S.u x + (((Vs g (T.s x) - g * cS g (T.s x) (T.z x)) / Vs g (T.s x) : ℝ) : ℂ) * S.up x
        + ((g / Vs g (T.s x) : ℝ) : ℂ) * S.hp x
        + ((g * (V1S g (T.s x) (T.z x) - c1S g n (T.s x) (T.z x)) / Vs g (T.s x) : ℝ) : ℂ) * S.u x
        - ((As g (T.s x) / Vs g (T.s x) : ℝ) : ℂ) * S.vp x
        - ((1 / Vs g (T.s x) : ℝ) : ℂ) * S.upp x = 0 ∧
    lam * S.h x + (((Vs g (T.s x) + g * cS g (T.s x) (T.z x)) / Vs g (T.s x) : ℝ) : ℂ) * S.hp x
        + (((Vs g (T.s x) * As g (T.s x) - n * V1S g (T.s x) (T.z x)
            + 2 * n * c1S g n (T.s x) (T.z x) - g * cS g (T.s x) (T.z x) ^ 2) / Vs g (T.s x) : ℝ) : ℂ)
          * S.up x
        + (((Vs g (T.s x) * V1S g (T.s x) (T.z x) - n * V2S g n (T.s x) (T.z x)
            + g * cS g (T.s x) (T.z x) * V1S g (T.s x) (T.z x)
            - (Vs g (T.s x) + g * cS g (T.s x) (T.z x)) * c1S g n (T.s x) (T.z x)
            + n * c2S g n (T.s x) (T.z x)) / Vs g (T.s x) : ℝ) : ℂ) * S.u x
        - ((n / Vs g (T.s x) : ℝ) : ℂ) * S.hpp x
        - (((1 - n) * cS g (T.s x) (T.z x) / Vs g (T.s x) : ℝ) : ℂ) * S.upp x = 0 := by
  have hV : ((Vs g (T.s x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (T.Vs_pos hg hn x).ne'
  have he1 : (n : ℂ) * (e1S g n (T.s x) (T.z x) : ℂ)
      = (As g (T.s x) : ℂ) * (Vs g (T.s x) : ℂ) * (cS g (T.s x) (T.z x) : ℂ) := by
    have := e1S_eq g n (T.s x) (T.z x) hg.ne' hn.ne' (by linarith)
    exact_mod_cast this
  have TC := thermal_cancel (g : ℂ) n lam (Vs g (T.s x)) (V1S g (T.s x) (T.z x))
    (V2S g n (T.s x) (T.z x)) (As g (T.s x)) (cS g (T.s x) (T.z x)) (c1S g n (T.s x) (T.z x))
    (c2S g n (T.s x) (T.z x)) (e1S g n (T.s x) (T.z x))
    (S.u x) (S.up x) (S.upp x) (S.h x) (S.hp x) (S.hpp x) (S.vp x) hV he1
  simp only at TC
  obtain ⟨T2, T3⟩ := TC
  have E2 := S.eq2 x
  have E3 := S.eq3 x
  have hε : S.ε x = S.h x - (cS g (T.s x) (T.z x) : ℂ) * S.u x := by unfold h; ring
  have hεp : S.εp x = S.hp x - (cS g (T.s x) (T.z x) : ℂ) * S.up x
      - (c1S g n (T.s x) (T.z x) : ℂ) * S.u x := by unfold hp; ring
  have hεpp : S.εpp x = S.hpp x - (cS g (T.s x) (T.z x) : ℂ) * S.upp x
      - 2 * (c1S g n (T.s x) (T.z x) : ℂ) * S.up x - (c2S g n (T.s x) (T.z x) : ℂ) * S.u x := by
    unfold hpp; ring
  rw [hεp] at E2
  rw [hε, hεp, hεpp] at E3
  push_cast at E2 E3 ⊢
  have e2 : lam * S.u x + S.up x + ↑g / ↑(Vs g (T.s x)) * (S.hp x - ↑(cS g (T.s x) (T.z x)) * S.up x
      - ↑(c1S g n (T.s x) (T.z x)) * S.u x) + ↑g * ↑(V1S g (T.s x) (T.z x)) / ↑(Vs g (T.s x)) * S.u x
      - ↑(As g (T.s x)) / ↑(Vs g (T.s x)) * S.vp x - S.upp x / ↑(Vs g (T.s x)) = 0 := by
    linear_combination E2
  have e3 : lam * (S.h x - ↑(cS g (T.s x) (T.z x)) * S.u x)
      + (S.hp x - ↑(cS g (T.s x) (T.z x)) * S.up x - ↑(c1S g n (T.s x) (T.z x)) * S.u x)
      + (↑(V1S g (T.s x) (T.z x)) - ↑n * ↑(V2S g n (T.s x) (T.z x)) / ↑(Vs g (T.s x))) * S.u x
      + (↑(As g (T.s x)) - ↑n * ↑(V1S g (T.s x) (T.z x)) / ↑(Vs g (T.s x))) * S.up x
      + ↑n * ↑(e1S g n (T.s x) (T.z x)) / ↑(Vs g (T.s x)) ^ 2 * S.vp x
      - ↑n / ↑(Vs g (T.s x)) * (S.hpp x - ↑(cS g (T.s x) (T.z x)) * S.upp x
          - 2 * ↑(c1S g n (T.s x) (T.z x)) * S.up x - ↑(c2S g n (T.s x) (T.z x)) * S.u x) = 0 := by
    linear_combination E3
  constructor
  · linear_combination (-1 : ℂ) * T2 + e2
  · linear_combination (-1 : ℂ) * T3 + e3 + (cS g (T.s x) (T.z x) : ℂ) * e2

end

end EigenSol

/-- **Proposition 8.2 (abstract form).**  Let the energy form be coercive along the
    trajectory, `Q ≥ κ s |y|²` pointwise.  If `λ ≠ 0`, `Re λ ≥ 0`, and the total energy flux
    tends to zero at both ends, then the solution is trivial. -/
theorem exclusion {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (T : SZTraj g n) {κ : ℝ} (hκ : 0 < κ)
    (hcoer : ∀ x p1 p2 q1 q2, κ * T.s x * (q1 ^ 2 + q2 ^ 2) ≤ Qform g n (T.s x) (T.z x) p1 p2 q1 q2)
    {lam : ℂ} (hlam : lam ≠ 0) (hre : 0 ≤ lam.re) (S : EigenSol T lam)
    (hbot : Tendsto (fun x => T.flux (fun y => (S.v y).re) (fun y => (S.u y).re)
        (fun y => (S.up y).re) (fun y => (S.h y).re) (fun y => (S.hp y).re) x
      + T.flux (fun y => (S.v y).im) (fun y => (S.u y).im)
        (fun y => (S.up y).im) (fun y => (S.h y).im) (fun y => (S.hp y).im) x) atBot (𝓝 0))
    (htop : Tendsto (fun x => T.flux (fun y => (S.v y).re) (fun y => (S.u y).re)
        (fun y => (S.up y).re) (fun y => (S.h y).re) (fun y => (S.hp y).re) x
      + T.flux (fun y => (S.v y).im) (fun y => (S.u y).im)
        (fun y => (S.up y).im) (fun y => (S.h y).im) (fun y => (S.hp y).im) x) atTop (𝓝 0)) :
    ∀ x, S.v x = 0 ∧ S.u x = 0 ∧ S.ε x = 0 := by
  set F := fun x => T.flux (fun y => (S.v y).re) (fun y => (S.u y).re)
        (fun y => (S.up y).re) (fun y => (S.h y).re) (fun y => (S.hp y).re) x
      + T.flux (fun y => (S.v y).im) (fun y => (S.u y).im)
        (fun y => (S.up y).im) (fun y => (S.h y).im) (fun y => (S.hp y).im) x with hF
  -- real and imaginary component derivatives
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
  -- the transformed equations, componentwise
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
  have DR := T.flux_deriv_eq hg hn rv ru rup rh rhp Re1 Re2 Re3
  have DI := T.flux_deriv_eq hg hn iv iu iup ih ihp Ie1 Ie2 Ie3
  -- the derivative of the total flux
  set D := fun x => (-((lam * S.v x).re * (S.v x).re
          + Vs g (T.s x) / As g (T.s x) * (lam * S.u x).re * (S.u x).re
          + Vs g (T.s x) / (As g (T.s x) * θ g) * (lam * S.h x).re * (S.h x).re)
        - Qform g n (T.s x) (T.z x) (((S.up x).re - dS (T.s x) (T.z x) * (S.u x).re / 2) / T.w x)
            (((S.hp x).re - dS (T.s x) (T.z x) * (S.h x).re / 2) / T.w x) ((S.u x).re / T.w x)
            ((S.h x).re / T.w x))
      + (-((lam * S.v x).im * (S.v x).im
          + Vs g (T.s x) / As g (T.s x) * (lam * S.u x).im * (S.u x).im
          + Vs g (T.s x) / (As g (T.s x) * θ g) * (lam * S.h x).im * (S.h x).im)
        - Qform g n (T.s x) (T.z x) (((S.up x).im - dS (T.s x) (T.z x) * (S.u x).im / 2) / T.w x)
            (((S.hp x).im - dS (T.s x) (T.z x) * (S.h x).im / 2) / T.w x) ((S.u x).im / T.w x)
            ((S.h x).im / T.w x)) with hD
  have hFD : ∀ x, HasDerivAt F (D x) x := fun x => (DR x).add (DI x)
  -- the spectral term is nonnegative and the energy density is coercive
  have hspec : ∀ (z : ℂ) (r : ℝ), 0 ≤ r →
      0 ≤ r * (lam * z).re * z.re + r * (lam * z).im * z.im := by
    intro z r hr
    have : r * (lam * z).re * z.re + r * (lam * z).im * z.im = r * lam.re * (z.re ^ 2 + z.im ^ 2) := by
      simp only [Complex.mul_re, Complex.mul_im]; ring
    rw [this]; positivity
  have hDle : ∀ x, D x ≤ -(κ * T.s x * ((((S.u x).re / T.w x) ^ 2 + ((S.h x).re / T.w x) ^ 2)
      + (((S.u x).im / T.w x) ^ 2 + ((S.h x).im / T.w x) ^ 2))) := by
    intro x
    have a1 := hspec (S.v x) 1 zero_le_one
    have hA := T.As_pos hg hn x
    have hθ := θ_pos g hg
    have a2 := hspec (S.u x) (Vs g (T.s x) / As g (T.s x)) (by have := Vpos x; positivity)
    have a3 := hspec (S.h x) (Vs g (T.s x) / (As g (T.s x) * θ g)) (by have := Vpos x; positivity)
    have q1 := hcoer x (((S.up x).re - dS (T.s x) (T.z x) * (S.u x).re / 2) / T.w x)
      (((S.hp x).re - dS (T.s x) (T.z x) * (S.h x).re / 2) / T.w x) ((S.u x).re / T.w x)
      ((S.h x).re / T.w x)
    have q2 := hcoer x (((S.up x).im - dS (T.s x) (T.z x) * (S.u x).im / 2) / T.w x)
      (((S.hp x).im - dS (T.s x) (T.z x) * (S.h x).im / 2) / T.w x) ((S.u x).im / T.w x)
      ((S.h x).im / T.w x)
    simp only [hD]
    nlinarith
  have hDnp : ∀ x, D x ≤ 0 := by
    intro x
    have := hDle x
    have hs := T.s_pos x
    have : 0 ≤ κ * T.s x * ((((S.u x).re / T.w x) ^ 2 + ((S.h x).re / T.w x) ^ 2)
      + (((S.u x).im / T.w x) ^ 2 + ((S.h x).im / T.w x) ^ 2)) := by positivity
    linarith
  -- F is antitone with zero limits, hence identically zero
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
  -- hence u = h = 0
  have huh : ∀ x, S.u x = 0 ∧ S.h x = 0 := by
    intro x
    have := hDle x
    rw [hD0 x] at this
    have hs := T.s_pos x
    have hwp := T.w_pos hg hn x
    have hsum : ((S.u x).re / T.w x) ^ 2 + ((S.h x).re / T.w x) ^ 2
      + (((S.u x).im / T.w x) ^ 2 + ((S.h x).im / T.w x) ^ 2) = 0 := by
      have hk : 0 < κ * T.s x := mul_pos hκ hs
      have hnn : 0 ≤ ((S.u x).re / T.w x) ^ 2 + ((S.h x).re / T.w x) ^ 2
        + (((S.u x).im / T.w x) ^ 2 + ((S.h x).im / T.w x) ^ 2) := by positivity
      nlinarith
    have a1 := sq_nonneg ((S.u x).re / T.w x)
    have a2 := sq_nonneg ((S.h x).re / T.w x)
    have a3 := sq_nonneg ((S.u x).im / T.w x)
    have a4 := sq_nonneg ((S.h x).im / T.w x)
    have e1 : (S.u x).re / T.w x = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
    have e2 : (S.h x).re / T.w x = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
    have e3 : (S.u x).im / T.w x = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
    have e4 : (S.h x).im / T.w x = 0 := pow_eq_zero_iff two_ne_zero |>.mp (by linarith)
    rw [div_eq_zero_iff] at e1 e2 e3 e4
    constructor
    · apply Complex.ext
      · rcases e1 with h | h; · simpa using h
        · exact absurd h hwp.ne'
      · rcases e3 with h | h; · simpa using h
        · exact absurd h hwp.ne'
    · apply Complex.ext
      · rcases e2 with h | h; · simpa using h
        · exact absurd h hwp.ne'
      · rcases e4 with h | h; · simpa using h
        · exact absurd h hwp.ne'
  -- derivatives of u and h vanish
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
  -- momentum equation: v' = 0; mass equation: λ v = 0
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
