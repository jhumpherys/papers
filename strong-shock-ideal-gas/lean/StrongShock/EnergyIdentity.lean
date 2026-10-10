/-
  Algebraic heart of the argument:
  * the thermal change of variables `h = ε + c u` (Section 4),
  * the pointwise energy identity (A.1) at the level of jets.
-/
import StrongShock.Basic

namespace StrongShock

noncomputable section

/-- Profile internal energy in `(s,z)` coordinates: `e = (a/Γ)(V - s z)`. -/
def eS (g s z : ℝ) : ℝ := As g s / g * (Vs g s - s * z)

/-- `e'` given by the profile equation (2.3). -/
def e1S (g n s z : ℝ) : ℝ := Vs g s / n * (eS g s z - (Vs g s - 1) ^ 2 / 2)

/-- Identity (4.1): `ν e' = a V c`. -/
lemma e1S_eq (g n s z : ℝ) (hg : g ≠ 0) (hn : n ≠ 0) (hg2 : g + 2 ≠ 0) :
    n * e1S g n s z = As g s * Vs g s * cS g s z := by
  unfold e1S eS As Vs cS
  field_simp
  ring

/-- Identity (4.2): `d + Γ c = s`. -/
lemma dS_add (g s z : ℝ) (hg : g ≠ 0) : dS s z + g * cS g s z = s := by
  unfold dS cS; field_simp; ring

/-- The thermal cancellation of Section 4, over an arbitrary field (in practice `ℂ`).
    `E2`, `E3` are the residuals of (3.2), (3.3) written with `ε = h - c u`;
    `R2`, `Rh` are the transformed residuals (4.5), (4.6).  In particular the mass
    derivative `v'` disappears from the thermal equation. -/
lemma thermal_cancel {K : Type*} [Field K] (g n lam V V1 V2 a c c1 c2 e1 u up upp h hp hpp vp : K)
    (hV : V ≠ 0) (he1 : n * e1 = a * V * c) :
    let epsp := hp - c * up - c1 * u
    let epspp := hpp - c * upp - 2 * c1 * up - c2 * u
    let E2 := lam * u + up + g / V * epsp + g * V1 / V * u - a / V * vp - upp / V
    let E3 := lam * (h - c * u) + epsp + (V1 - n * V2 / V) * u + (a - n * V1 / V) * up
      + n * e1 / V ^ 2 * vp - n / V * epspp
    let R2 := lam * u + (V - g * c) / V * up + g / V * hp + g * (V1 - c1) / V * u
      - a / V * vp - upp / V
    let Rh := lam * h + (V + g * c) / V * hp + (V * a - n * V1 + 2 * n * c1 - g * c ^ 2) / V * up
      + (V * V1 - n * V2 + g * c * V1 - (V + g * c) * c1 + n * c2) / V * u
      - n / V * hpp - (1 - n) * c / V * upp
    E2 = R2 ∧ E3 + c * E2 = Rh := by
  intro epsp epspp E2 E3 R2 Rh
  constructor
  · simp only [E2, R2, epsp]; field_simp; ring
  · have : n * e1 / V ^ 2 = a * c / V := by
      rw [he1]; field_simp
    simp only [E3, E2, Rh, epsp, epspp, this]
    field_simp
    ring

/-- Flux of the energy identity (Appendix A), one real component.
    Arguments: profile point `(s,z)`, perturbation `v, u`, and `y = (u,h)/√a`, `y'`. -/
def Flux (g n s z v u y1 y1p y2 y2p : ℝ) : ℝ :=
  v ^ 2 / 2 - v * u - y1p * y1 - n / θ g * y2p * y2 - Kc g n s z * y1p * y2
    + (Vs g s - g * cS g s z - dS s z) / 2 * y1 ^ 2
    + (Vs g s + g * cS g s z - n * dS s z) / (2 * θ g) * y2 ^ 2 + g * y1 * y2

/-- Its derivative along the profile, by the product rule. -/
def FluxDeriv (g n s z v vp u up y1 y1p y1pp y2 y2p y2pp : ℝ) : ℝ :=
  v * vp - (vp * u + v * up) - (y1p ^ 2 + y1pp * y1) - n / θ g * (y2p ^ 2 + y2pp * y2)
    - (K1c g n s z * y1p * y2 + Kc g n s z * y1pp * y2 + Kc g n s z * y1p * y2p)
    + (V1S g s z - g * c1S g n s z - d1S g n s z) / 2 * y1 ^ 2
    + (Vs g s - g * cS g s z - dS s z) * y1 * y1p
    + (V1S g s z + g * c1S g n s z - n * d1S g n s z) / (2 * θ g) * y2 ^ 2
    + (Vs g s + g * cS g s z - n * dS s z) / θ g * y2 * y2p
    + g * (y1p * y2 + y1 * y2p)

/-- Transformed momentum residual (4.5), one real component, with `Lu` standing for the
    corresponding component of `λ u`. -/
def Res2 (g n s z Lu u up upp hp vp : ℝ) : ℝ :=
  Lu + (Vs g s - g * cS g s z) / Vs g s * up + g / Vs g s * hp
    + g * (V1S g s z - c1S g n s z) / Vs g s * u - As g s / Vs g s * vp - upp / Vs g s

/-- Transformed thermal residual (4.6), one real component. -/
def ResH (g n s z Lh u up upp hp hpp : ℝ) : ℝ :=
  Lh + (Vs g s + g * cS g s z) / Vs g s * hp
    + (Vs g s * As g s - n * V1S g s z + 2 * n * c1S g n s z - g * cS g s z ^ 2) / Vs g s * up
    + (Vs g s * V1S g s z - n * V2S g n s z + g * cS g s z * V1S g s z
        - (Vs g s + g * cS g s z) * c1S g n s z + n * c2S g n s z) / Vs g s * u
    - n / Vs g s * hpp - (1 - n) * cS g s z / Vs g s * upp

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **Pointwise energy identity (A.1)** for one real component.  Here `w = √a`,
    `y₁ = u/w`, `y₂ = h/w`, the `y'`, `y''` are the corresponding derivatives (using
    `w' = w d/2`), and `Lv, Lu, Lh` are the spectral-parameter terms. -/
theorem energy_identity_jet (g n s z w : ℝ) (hg : 0 < g) (hn : 0 < n) (hw : w ≠ 0)
    (hwa : w ^ 2 = As g s) (hV : Vs g s ≠ 0)
    (u up upp h hp hpp v vp Lv Lu Lh : ℝ) :
    let d := dS s z
    let d1 := d1S g n s z
    let y1 := u / w
    let y1p := (up - d * u / 2) / w
    let y1pp := (upp - d * up - (d1 / 2 - d ^ 2 / 4) * u) / w
    let y2 := h / w
    let y2p := (hp - d * h / 2) / w
    let y2pp := (hpp - d * hp - (d1 / 2 - d ^ 2 / 4) * h) / w
    (Lv + vp - up) * v + Vs g s / As g s * Res2 g n s z Lu u up upp hp vp * u
      + Vs g s / (As g s * θ g) * ResH g n s z Lh u up upp hp hpp * h
    = Lv * v + Vs g s / As g s * Lu * u + Vs g s / (As g s * θ g) * Lh * h
      + Qform g n s z y1p y2p y1 y2
      + FluxDeriv g n s z v vp u up y1 y1p y1pp y2 y2p y2pp := by
  intro d d1 y1 y1p y1pp y2 y2p y2pp
  have hg2 : g + 2 ≠ 0 := by linarith
  have hs : s = 1 - (g + 2) * w ^ 2 / 2 := by
    unfold As at hwa; field_simp at hwa; linarith
  have hVs : Vs g s = 1 - w ^ 2 := by rw [hs]; unfold Vs; field_simp; ring
  have h1w : 1 - w ^ 2 ≠ 0 := by rw [← hVs]; exact hV
  simp only [d, d1, y1, y1p, y1pp, y2, y2p, y2pp, Res2, ResH, Qform, FluxDeriv, Rc, Cc, P1c, P2c,
    Kc, K1c, Bc, Lc, c2S, c1S_s, c1S_z, c1S, d1S, V1S, V2S, θ]
  rw [hVs, ← hwa]
  subst hs
  unfold cS dS fS fZ f0 f1
  have hn' : n ≠ 0 := hn.ne'
  have hg' : g ≠ 0 := hg.ne'
  field_simp
  ring

end

end StrongShock
