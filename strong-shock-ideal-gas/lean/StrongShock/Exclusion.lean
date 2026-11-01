/-
  Exclusion of nonzero frequencies (Section 7, Proposition 7.2).

  The argument is the energy method of Section 5 in pointwise form:  along a solution,
  the energy flux `𝓕` satisfies `𝓕' = -(Re λ)·E_dens - Q_dens ≤ 0`; since `𝓕 → 0` at both
  ends, `𝓕 ≡ 0`, which forces `Q_dens ≡ 0` and hence, by coercivity, a trivial solution.
-/
import StrongShock.SlopeSharp
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

end

end StrongShock
