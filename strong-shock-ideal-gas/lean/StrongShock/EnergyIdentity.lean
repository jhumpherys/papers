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

/-! ### The weighted energy identity

The thermal weight is `ω = W²/2` with `W > 0` (Section 5).  The constant weight of
Section 6.1 is `W = a_*`, the variable weight (6.9) is `W = a + 4c/3`.  We use the rescaled
thermal variable `ξ̃ = h/(√a W) = ξ/√2`, which makes every coefficient rational. -/

/-- Logarithmic rate `δ = d + ω'/ω = d + 2W'/W` of (5.6). -/
def deltaW (s z W W1 : ℝ) : ℝ := dS s z + 2 * W1 / W
/-- `κ = (ν-1)²c²/(4νω)` of (5.6). -/
def kapW (g n s z W : ℝ) : ℝ := (n - 1) ^ 2 * cS g s z ^ 2 / (2 * n * W ^ 2)
/-- The thermal potential `P` of (5.7). -/
def PW (g n s z W W1 : ℝ) : ℝ :=
  As g s * dS s z / 2 + Vs g s * deltaW s z W W1 / 2
    - (n * deltaW s z W W1 - g * cS g s z) ^ 2 / (4 * n)
/-- `√2·m`, with `m` the coupling coefficient (5.10). -/
def mW (g n s z W W1 : ℝ) : ℝ :=
  (g * (Tcal g n s z - W ^ 2 / 2) + (n - 1) * cS g s z * W1 / W) / W

/-- The pair form `(1-κ)Φ² + 2mΦξ + Pξ²` of (5.11), written in `ξ̃ = ξ/√2`. -/
def pairW (g n s z W W1 X Y : ℝ) : ℝ :=
  (1 - kapW g n s z W) * X ^ 2 + 2 * mW g n s z W W1 * X * Y + 2 * PW g n s z W W1 * Y ^ 2

/-- The normalized energy density (5.11), one real component, in the variables
    `φ = u/a`, `Φ = √a φ'`, `ξ̃`, `ξ̃'`. -/
def QW (g n s z W W1 phi Phi xi xip : ℝ) : ℝ :=
  (1 - g / 2) * As g s * (As g s * dS s z) * phi ^ 2
    + 2 * n * (xip + g * cS g s z * xi / (2 * n) - (n - 1) * cS g s z * Phi / (2 * n * W)) ^ 2
    + pairW g n s z W W1 Phi xi

/-- The energy flux of one real component (Appendix A, after normalization). -/
def FluxW (g n s z W v u up h hp : ℝ) : ℝ :=
  v ^ 2 / 2 - u * v - (up - dS s z * u) * u / As g s + g * u ^ 2 / 4 + g * u * h / As g s
    + (Vs g s * h ^ 2 - 2 * n * h * hp
        + 2 * (n - 1) * cS g s z * (up - dS s z * u) * h) / (As g s * W ^ 2)

/-- Its derivative along the profile, by the product rule. -/
def FluxWDeriv (g n s z W W1 v vp u up upp h hp hpp : ℝ) : ℝ :=
  let a := As g s
  let d := dS s z
  let c := cS g s z
  let p := up - d * u
  let pp := upp - d1S g n s z * u - d * up
  let N := Vs g s * h ^ 2 - 2 * n * h * hp + 2 * (n - 1) * c * p * h
  let Np := -(a * d) * h ^ 2 + 2 * Vs g s * h * hp - 2 * n * (hp ^ 2 + h * hpp)
    + 2 * (n - 1) * (c1S g n s z * p * h + c * pp * h + c * p * hp)
  v * vp - (up * v + u * vp) - (pp * u + p * up) / a + p * u * d / a + g * u * up / 2
    + g * (up * h + u * hp) / a - g * u * h * d / a
    + Np / (a * W ^ 2) - deltaW s z W W1 * N / (a * W ^ 2)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- **Pointwise energy identity** (Appendix A together with Proposition 5.1) for one real
    component and an arbitrary weight `ω = W²/2`.  Here `w = √a`, and `W1` is the value of
    `W'`; no relation between `W` and the profile is assumed. -/
theorem energy_identity_weighted (g n s z w W W1 : ℝ) (hg : 0 < g) (hn : 0 < n) (hw : w ≠ 0)
    (hwa : w ^ 2 = As g s) (hV : Vs g s ≠ 0) (hW : W ≠ 0)
    (u up upp h hp hpp v vp Lv Lu Lh : ℝ) :
    (Lv + vp - up) * v + Vs g s / As g s * Res2 g n s z Lu u up upp hp vp * u
      + 2 * Vs g s / (As g s * W ^ 2) * ResH g n s z Lh u up upp hp hpp * h
    = Lv * v + Vs g s / As g s * Lu * u + 2 * Vs g s / (As g s * W ^ 2) * Lh * h
      + QW g n s z W W1 (u / As g s) (w * (up - dS s z * u) / As g s) (h / (w * W))
          ((hp - (dS s z / 2 + W1 / W) * h) / (w * W))
      + FluxWDeriv g n s z W W1 v vp u up upp h hp hpp := by
  have hg2 : g + 2 ≠ 0 := by linarith
  have hs : s = 1 - (g + 2) * w ^ 2 / 2 := by
    unfold As at hwa; field_simp at hwa; linarith
  have hVs : Vs g s = 1 - w ^ 2 := by rw [hs]; unfold Vs; field_simp; ring
  have h1w : 1 - w ^ 2 ≠ 0 := by rw [← hVs]; exact hV
  simp only [Res2, ResH, QW, pairW, kapW, PW, mW, deltaW, Tcal, FluxWDeriv, c2S, c1S_s, c1S_z,
    c1S, d1S, V1S, V2S]
  rw [hVs, ← hwa]
  subst hs
  unfold cS dS fS fZ f0 f1
  have hn' : n ≠ 0 := hn.ne'
  have hg' : g ≠ 0 := hg.ne'
  field_simp
  ring

end

end StrongShock
