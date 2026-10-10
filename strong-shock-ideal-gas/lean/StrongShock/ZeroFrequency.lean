/-
  Zero frequency (Section 9, Proposition 9.1).
-/
import StrongShock.Exclusion

open Filter Topology Set

namespace StrongShock

noncomputable section

lemma const_of_hasDerivAt_zero {f : ℝ → ℂ} (h : ∀ x, HasDerivAt f 0 x) (x y : ℝ) :
    f x = f y :=
  is_const_of_deriv_eq_zero (fun x => (h x).differentiableAt) (fun x => (h x).deriv) x y

/-- A function with zero derivative tending to `0` at `-∞` vanishes identically. -/
lemma zero_of_hasDerivAt_zero {f : ℝ → ℂ} (h : ∀ x, HasDerivAt f 0 x)
    (hbot : Tendsto f atBot (𝓝 0)) (x : ℝ) : f x = 0 := by
  have hc : f = fun _ => f x := funext fun y => const_of_hasDerivAt_zero h y x
  rw [hc] at hbot
  exact tendsto_nhds_unique tendsto_const_nhds hbot

/-! ### Downstream linear algebra -/

/-- Downstream sound speed `c₊ = √(2(Γ+1)/Γ)`. -/
def cplus (g : ℝ) : ℝ := Real.sqrt (2 * (g + 1) / g)

lemma cplus_sq {g : ℝ} (hg : 0 < g) : cplus g ^ 2 = 2 * (g + 1) / g :=
  Real.sq_sqrt (by positivity)

lemma one_lt_cplus {g : ℝ} (hg : 0 < g) : 1 < cplus g := by
  have h := cplus_sq hg
  have hc : 0 ≤ cplus g := Real.sqrt_nonneg _
  have : 1 < 2 * (g + 1) / g := by rw [lt_div_iff₀ hg]; linarith
  nlinarith

lemma astar_div_vstar {g : ℝ} (hg : 0 < g) : astar g / vstar g = 2 / g := by
  unfold astar vstar; have : g + 2 ≠ 0 := by linarith
  field_simp

lemma g_div_vstar {g : ℝ} (hg : 0 < g) : g / vstar g = g + 2 := by
  unfold vstar; have : g + 2 ≠ 0 := by linarith
  field_simp

/-- The downstream flux matrix `A₊` acting on `(v,u,ε)`; entries `a_*/v_* = 2/Γ` and
    `Γ/v_* = Γ + 2` (see `astar_div_vstar`, `g_div_vstar`). -/
def Aplus (g : ℝ) (w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![w 0 - w 1, -(2 / g) * w 0 + w 1 + (g + 2) * w 2, astar g * w 1 + w 2]

/-- Right eigenvectors of `A₊` for the positive characteristic speeds `1` and `1 + c₊`. -/
def r1 (g : ℝ) : Fin 3 → ℝ := ![g, 0, astar g]
def r2 (g : ℝ) : Fin 3 → ℝ := ![1, -cplus g, -astar g]
/-- The negative-speed left covector `ℓ₋ = (a_*/v_*, c₊, -Γ/v_*)`. -/
def ell (g : ℝ) : Fin 3 → ℝ := ![2 / g, cplus g, -(g + 2)]

lemma ell_eq_paper {g : ℝ} (hg : 0 < g) :
    ell g = ![astar g / vstar g, cplus g, -(g / vstar g)] := by
  rw [astar_div_vstar hg, g_div_vstar hg]; rfl

lemma cplus_sq' {g : ℝ} (hg : 0 < g) : cplus g ^ 2 = 2 / g + 2 := by
  rw [cplus_sq hg]; field_simp; ring

lemma Aplus_r1 {g : ℝ} (hg : 0 < g) : Aplus g (r1 g) = r1 g := by
  have e : (g + 2) * astar g = 2 := by
    unfold astar; have : g + 2 ≠ 0 := by linarith
    field_simp
  ext i; fin_cases i
  · show g - 0 = g; ring
  · show -(2 / g) * g + 0 + (g + 2) * astar g = 0
    have : g ≠ 0 := hg.ne'
    rw [e]; field_simp; norm_num
  · show astar g * 0 + astar g = astar g; ring

lemma Aplus_r2 {g : ℝ} (hg : 0 < g) : Aplus g (r2 g) = (1 + cplus g) • r2 g := by
  have h2 := cplus_sq' hg
  ext i; fin_cases i
  · simp [Aplus, r2]; (try ring)
  · show -(2 / g) * 1 + -cplus g + (g + 2) * -astar g = (1 + cplus g) * -cplus g
    have e : (g + 2) * astar g = 2 := by
      unfold astar; have : g + 2 ≠ 0 := by linarith
      field_simp
    linear_combination h2 - e
  · simp [Aplus, r2]; ring

/-- `ℓ₋ A₊ = (1 - c₊) ℓ₋`: `ℓ₋` is the left eigenvector of the negative speed `1 - c₊`. -/
lemma ell_Aplus {g : ℝ} (hg : 0 < g) (w : Fin 3 → ℝ) :
    (∑ i, ell g i * Aplus g w i) = (1 - cplus g) * ∑ i, ell g i * w i := by
  have h2 := cplus_sq' hg
  have : g + 2 ≠ 0 := by linarith
  have e : (g + 2) * astar g = 2 := by unfold astar; field_simp
  simp [Fin.sum_univ_three, ell, Aplus]
  linear_combination (w 1) * h2 - (w 1) * e

lemma ell_r1 {g : ℝ} (hg : 0 < g) : (∑ i, ell g i * r1 g i) = 0 := by
  have : g + 2 ≠ 0 := by linarith
  have : g ≠ 0 := hg.ne'
  simp [Fin.sum_univ_three, ell, r1, astar]; field_simp; ring

lemma ell_r2 {g : ℝ} (hg : 0 < g) : (∑ i, ell g i * r2 g i) = 0 := by
  have h2 := cplus_sq' hg
  have : g + 2 ≠ 0 := by linarith
  have e : (g + 2) * astar g = 2 := by unfold astar; field_simp
  simp [Fin.sum_univ_three, ell, r2]
  linear_combination (-1 : ℝ) * h2 + e

/-- `ℓ₋ · j_* < 0` for `j_* = (-a_*, -a_*, 0)`. -/
lemma ell_jstar {g : ℝ} (hg : 0 < g) :
    ell g 0 * (-astar g) + ell g 1 * (-astar g) + ell g 2 * 0 < 0 := by
  have hc : 0 < cplus g := lt_trans one_pos (one_lt_cplus hg)
  have ha : 0 < astar g := by unfold astar; positivity
  simp [ell]
  have : 0 < 2 / g * astar g + cplus g * astar g := by positivity
  linarith

/-! ### The zero-frequency argument -/

namespace SZTraj
variable {g n : ℝ} (T : SZTraj g n)

/-- `e'` along the profile, and the variational equation for the profile tangent. -/
lemma hasDerivAt_e (hg : 0 < g) (hn : 0 < n) (x : ℝ) :
    HasDerivAt (fun y => eS g (T.s y) (T.z y)) (e1S g n (T.s x) (T.z x)) x := by
  have hA := T.hasDerivAt_A hg hn x
  have hV := T.hasDerivAt_V hg hn x
  have h := (hA.div_const g).mul (hV.sub ((T.hs x).mul (T.hz x)))
  refine hasDerivAt_of_eq h (fun y => by simp only [eS, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply]) ?_
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply]
    have : g + 2 ≠ 0 := by linarith
    have : g ≠ 0 := hg.ne'
    have : n ≠ 0 := hn.ne'
    unfold e1S eS V1S Vs As dS fS fZ f0 f1; field_simp; ring

lemma hasDerivAt_e1 (hg : 0 < g) (hn : 0 < n) (x : ℝ) :
    HasDerivAt (fun y => e1S g n (T.s y) (T.z y))
      ((Vs g (T.s x) * As g (T.s x) / n + e1S g n (T.s x) (T.z x) / Vs g (T.s x))
          * V1S g (T.s x) (T.z x) + Vs g (T.s x) / n * e1S g n (T.s x) (T.z x)) x := by
  have hV := T.hasDerivAt_V hg hn x
  have he := T.hasDerivAt_e hg hn x
  have h := (hV.div_const n).mul (he.sub (((hV.sub_const 1).pow 2).div_const 2))
  refine hasDerivAt_of_eq h (fun y => by simp only [e1S, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply]) ?_
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply, Pi.pow_apply]
    have : g + 2 ≠ 0 := by linarith
    have : g ≠ 0 := hg.ne'
    have : n ≠ 0 := hn.ne'
    have hVp : Vs g (T.s x) ≠ 0 := (T.Vs_pos hg hn x).ne'
    have ha : As g (T.s x) = 1 - Vs g (T.s x) := by unfold As Vs; field_simp; ring
    simp only [Nat.cast_ofNat]
    rw [ha]
    unfold e1S
    field_simp
    ring

lemma V2S_eq (hg : 0 < g) (hn : 0 < n) (x : ℝ) :
    V2S g n (T.s x) (T.z x) = (2 * Vs g (T.s x) - 1) * V1S g (T.s x) (T.z x)
      + g * e1S g n (T.s x) (T.z x) := by
  have : g + 2 ≠ 0 := by linarith
  have : g ≠ 0 := hg.ne'
  have : n ≠ 0 := hn.ne'
  unfold V2S d1S c1S e1S eS V1S Vs As cS dS; field_simp; ring

end SZTraj

/-- Hypotheses describing an admissible solution at `λ = 0` (Section 3 and [HLZ, §3]):
    upstream decay; downstream, bounded limits lying in the positive-characteristic
    subspace and decaying derivatives. -/
structure ZeroAdmissible {g n : ℝ} {T : SZTraj g n} (S : EigenSol T 0) : Prop where
  v_bot : Tendsto S.v atBot (𝓝 0)
  u_bot : Tendsto S.u atBot (𝓝 0)
  ε_bot : Tendsto S.ε atBot (𝓝 0)
  up_top : Tendsto S.up atTop (𝓝 0)
  εp_top : Tendsto S.εp atTop (𝓝 0)
  lim : ∃ α β : ℂ, Tendsto S.v atTop (𝓝 (α * r1 (g) 0 + β * r2 g 0)) ∧
    Tendsto S.u atTop (𝓝 (α * r1 g 1 + β * r2 g 1)) ∧
    Tendsto S.ε atTop (𝓝 (α * r1 g 2 + β * r2 g 2))

/-- The downstream-decaying solutions of the variational equation (9.1) are multiples of
    the profile tangent (the downstream rest point is a saddle). -/
def VariationalUnique {g n : ℝ} (T : SZTraj g n) : Prop :=
  ∀ (Z1 Z2 Z1p Z2p : ℝ → ℂ), (∀ x, HasDerivAt Z1 (Z1p x) x) → (∀ x, HasDerivAt Z2 (Z2p x) x) →
    (∀ x, Z1p x = ((2 * Vs g (T.s x) - 1 : ℝ) : ℂ) * Z1 x + (g : ℂ) * Z2 x) →
    (∀ x, Z2p x = ((Vs g (T.s x) * As g (T.s x) / n + e1S g n (T.s x) (T.z x) / Vs g (T.s x) : ℝ) : ℂ) * Z1 x
        + ((Vs g (T.s x) / n : ℝ) : ℂ) * Z2 x) →
    Tendsto Z1 atTop (𝓝 0) → Tendsto Z2 atTop (𝓝 0) →
    ∃ A0 : ℂ, ∀ x, Z1 x = A0 * (V1S g (T.s x) (T.z x) : ℂ) ∧ Z2 x = A0 * (e1S g n (T.s x) (T.z x) : ℂ)

/-- **Proposition 9.1.** No nontrivial admissible solution at zero frequency. -/
theorem zero_frequency {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (T : SZTraj g n)
    (hs_bot : Tendsto T.s atBot (𝓝 1)) (hs_top : Tendsto T.s atTop (𝓝 0))
    (hzb : ∃ B, ∀ x, |T.z x| ≤ B)
    (hvar : VariationalUnique T) (S : EigenSol T 0) (hS : ZeroAdmissible S) :
    ∀ x, S.v x = 0 ∧ S.u x = 0 ∧ S.ε x = 0 := by
  obtain ⟨B, hB⟩ := hzb
  have Vpos := T.Vs_pos hg hn
  -- u = v
  have huv : ∀ x, S.v x = S.u x := by
    have hd : ∀ x, HasDerivAt (fun y => S.v y - S.u y) 0 x := by
      intro x
      have := (S.hv x).sub (S.hu x)
      refine hasDerivAt_of_eq this (fun y => rfl) ?_
      have := S.eq1 x; simp at this; rw [this]; ring
    intro x
    have := zero_of_hasDerivAt_zero hd (by simpa using hS.v_bot.sub hS.u_bot) x
    exact sub_eq_zero.mp this
  have hvp : ∀ x, S.vp x = S.up x := by
    intro x; have := S.eq1 x; simpa using this
  -- the variational pair
  obtain ⟨Z2, hZ2def⟩ : ∃ Z2 : ℝ → ℂ, ∀ x, Z2 x = S.εp x + (V1S g (T.s x) (T.z x) : ℂ) * S.u x :=
    ⟨_, fun _ => rfl⟩
  have hV1c := fun x => (T.hasDerivAt_V1 hg hn x).ofReal_comp
  have hZ1 : ∀ x, HasDerivAt S.up (S.upp x) x := S.hup
  have hZ2 : ∀ x, HasDerivAt Z2 (S.εpp x + (V2S g n (T.s x) (T.z x) : ℂ) * S.u x
      + (V1S g (T.s x) (T.z x) : ℂ) * S.up x) x := by
    intro x
    have := (S.hεp x).add ((hV1c x).mul (S.hu x))
    refine hasDerivAt_of_eq this (fun y => by rw [hZ2def y]; simp only [Pi.add_apply, Pi.mul_apply]) ?_
    ring
  have eqZ1 : ∀ x, S.upp x = ((2 * Vs g (T.s x) - 1 : ℝ) : ℂ) * S.up x + (g : ℂ) * Z2 x := by
    intro x
    have E := S.eq2 x
    rw [hvp x] at E
    have hV : (Vs g (T.s x) : ℂ) ≠ 0 := by exact_mod_cast (Vpos x).ne'
    have hW : (Vs g (T.s x) : ℂ) * (Vs g (T.s x) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hV
    have hA : (As g (T.s x) : ℂ) = 1 - Vs g (T.s x) := by
      have : As g (T.s x) = 1 - Vs g (T.s x) := by unfold As Vs; field_simp; ring
      exact_mod_cast this
    rw [hZ2def x]
    push_cast at E ⊢
    linear_combination (-(Vs g (T.s x) : ℂ)) * E
      + ((g : ℂ) * S.εp x + (g : ℂ) * (V1S g (T.s x) (T.z x) : ℂ) * S.u x
          - (As g (T.s x) : ℂ) * S.up x - S.upp x) * hW - S.up x * hA
  have eqZ2 : ∀ x, S.εpp x + (V2S g n (T.s x) (T.z x) : ℂ) * S.u x
      + (V1S g (T.s x) (T.z x) : ℂ) * S.up x =
      ((Vs g (T.s x) * As g (T.s x) / n + e1S g n (T.s x) (T.z x) / Vs g (T.s x) : ℝ) : ℂ) * S.up x
        + ((Vs g (T.s x) / n : ℝ) : ℂ) * Z2 x := by
    intro x
    have E := S.eq3 x
    rw [hvp x] at E
    have hV : (Vs g (T.s x) : ℂ) ≠ 0 := by exact_mod_cast (Vpos x).ne'
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hW : (Vs g (T.s x) : ℂ) * (Vs g (T.s x) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hV
    have hN : (n : ℂ) * (n : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hn'
    rw [hZ2def x]
    push_cast at E ⊢
    linear_combination (-((Vs g (T.s x) : ℂ) * (n : ℂ)⁻¹)) * E
      - ((S.εpp x + (V2S g n (T.s x) (T.z x) : ℂ) * S.u x + (V1S g (T.s x) (T.z x) : ℂ) * S.up x
          - (e1S g n (T.s x) (T.z x) : ℂ) * (Vs g (T.s x) : ℂ)⁻¹ * S.up x)
          * ((Vs g (T.s x) : ℂ) * (Vs g (T.s x) : ℂ)⁻¹)) * hN
      - (S.εpp x + (V2S g n (T.s x) (T.z x) : ℂ) * S.u x + (V1S g (T.s x) (T.z x) : ℂ) * S.up x
          - (e1S g n (T.s x) (T.z x) : ℂ) * (Vs g (T.s x) : ℂ)⁻¹ * S.up x) * hW
  -- decay of the variational pair downstream
  have hV1top : Tendsto (fun x => (V1S g (T.s x) (T.z x) : ℂ)) atTop (𝓝 0) := by
    have hs := hs_top
    have hb : Tendsto (fun x => V1S g (T.s x) (T.z x)) atTop (𝓝 0) := by
      -- |V1S| ≤ (2/(g+2)) * s * B
      have hbound : ∀ x, |V1S g (T.s x) (T.z x)| ≤ 2 / (g + 2) * B * T.s x := by
        intro x
        have hs0 := T.s_pos x; have hs1 := T.s_lt x
        unfold V1S As dS
        rw [abs_mul, abs_neg, abs_mul, abs_of_pos (by apply div_pos <;> linarith),
          abs_of_pos hs0]
        have := hB x
        have h1 : 2 * (1 - T.s x) / (g + 2) ≤ 2 / (g + 2) := by
          apply div_le_div_of_nonneg_right _ (by linarith); linarith
        have hz0 : 0 ≤ |T.z x| := abs_nonneg _
        calc 2 * (1 - T.s x) / (g + 2) * (T.s x * |T.z x|)
            ≤ 2 / (g + 2) * (T.s x * B) := by
              apply mul_le_mul h1 (mul_le_mul_of_nonneg_left this hs0.le) (by positivity)
                (by positivity)
          _ = 2 / (g + 2) * B * T.s x := by ring
      have h0 : Tendsto (fun x => 2 / (g + 2) * B * T.s x) atTop (𝓝 0) := by
        simpa using hs.const_mul (2 / (g + 2) * B)
      exact squeeze_zero_norm (fun x => by simpa using hbound x) h0
    have := (Complex.continuous_ofReal.tendsto 0).comp hb
    rw [Complex.ofReal_zero] at this; exact this
  obtain ⟨α, β, hvlim, hulim, hεlim⟩ := hS.lim
  have hZ2top : Tendsto Z2 atTop (𝓝 0) := by
    have := hS.εp_top.add (hV1top.mul hulim)
    simp only [zero_mul, add_zero] at this
    exact this.congr (fun x => (hZ2def x).symm)
  obtain ⟨A0, hA0⟩ := hvar S.up Z2 S.upp _ hZ1 hZ2 eqZ1 eqZ2 hS.up_top hZ2top
  -- integrate: u = A0 (V - 1), ε = A0 (e - (V-1)^2/2)
  have hVc := fun x => (T.hasDerivAt_V hg hn x).ofReal_comp
  have hec := fun x => (T.hasDerivAt_e hg hn x).ofReal_comp
  have hVbot : Tendsto (fun x => (Vs g (T.s x) : ℂ)) atBot (𝓝 1) := by
    have : Tendsto (fun x => Vs g (T.s x)) atBot (𝓝 (Vs g 1)) := by
      unfold Vs; exact ((tendsto_const_nhds.add (hs_bot.const_mul 2)).div_const _)
    have e : Vs g 1 = 1 := by unfold Vs; field_simp
    rw [e] at this
    have := (Complex.continuous_ofReal.tendsto 1).comp this
    rw [Complex.ofReal_one] at this; exact this
  have hebot : Tendsto (fun x => (eS g (T.s x) (T.z x) : ℂ)) atBot (𝓝 0) := by
    have hb : Tendsto (fun x => eS g (T.s x) (T.z x)) atBot (𝓝 0) := by
      have hbound : ∀ x, |eS g (T.s x) (T.z x)| ≤ (2 / (g + 2) / g * (1 + B)) * (1 - T.s x) := by
        intro x
        have hs0 := T.s_pos x; have hs1 := T.s_lt x
        unfold eS As Vs
        have hzb := hB x
        have hV1 : |(g + 2 * T.s x) / (g + 2) - T.s x * T.z x| ≤ 1 + B := by
          have : |(g + 2 * T.s x) / (g + 2)| ≤ 1 := by
            rw [abs_of_pos (by positivity), div_le_one (by linarith)]; linarith
          have h2 : |T.s x * T.z x| ≤ B := by
            rw [abs_mul, abs_of_pos hs0]; nlinarith [abs_nonneg (T.z x)]
          calc _ ≤ |(g + 2 * T.s x) / (g + 2)| + |T.s x * T.z x| := abs_sub _ _
            _ ≤ 1 + B := by linarith
        rw [abs_mul, abs_of_pos (by apply div_pos (by apply div_pos <;> linarith) hg)]
        calc 2 * (1 - T.s x) / (g + 2) / g * |(g + 2 * T.s x) / (g + 2) - T.s x * T.z x|
            ≤ 2 * (1 - T.s x) / (g + 2) / g * (1 + B) :=
              mul_le_mul_of_nonneg_left hV1 (by apply div_nonneg (by apply div_nonneg <;> linarith) hg.le)
          _ = (2 / (g + 2) / g * (1 + B)) * (1 - T.s x) := by ring
      have h0 : Tendsto (fun x => (2 / (g + 2) / g * (1 + B)) * (1 - T.s x)) atBot (𝓝 0) := by
        have := ((tendsto_const_nhds (x := (1:ℝ))).sub hs_bot).const_mul (2 / (g + 2) / g * (1 + B))
        simpa using this
      exact squeeze_zero_norm (fun x => by simpa using hbound x) h0
    have := (Complex.continuous_ofReal.tendsto 0).comp hb
    rw [Complex.ofReal_zero] at this; exact this
  have hu_eq : ∀ x, S.u x = A0 * ((Vs g (T.s x) : ℂ) - 1) := by
    have hd : ∀ x, HasDerivAt (fun y => S.u y - A0 * ((Vs g (T.s y) : ℂ) - 1)) 0 x := by
      intro x
      have := (S.hu x).sub (((hVc x).sub_const 1).const_mul A0)
      refine hasDerivAt_of_eq this (fun y => rfl) ?_
      rw [(hA0 x).1]; ring
    intro x
    have := zero_of_hasDerivAt_zero hd (by
      have := hS.u_bot.sub ((hVbot.sub_const 1).const_mul A0)
      simpa using this) x
    exact sub_eq_zero.mp this
  have hε_eq : ∀ x, S.ε x = A0 * ((eS g (T.s x) (T.z x) : ℂ) - ((Vs g (T.s x) : ℂ) - 1) ^ 2 / 2) := by
    have hd : ∀ x, HasDerivAt
        (fun y => S.ε y - A0 * ((eS g (T.s y) (T.z y) : ℂ) - ((Vs g (T.s y) : ℂ) - 1) ^ 2 / 2)) 0 x := by
      intro x
      have := (S.hε x).sub (((hec x).sub ((((hVc x).sub_const 1).pow 2).div_const 2)).const_mul A0)
      refine hasDerivAt_of_eq this (fun y => rfl) ?_
      have h2 := (hA0 x).2
      rw [hZ2def x] at h2
      have : S.εp x = A0 * (e1S g n (T.s x) (T.z x) : ℂ) - (V1S g (T.s x) (T.z x) : ℂ) * S.u x := by
        rw [← h2]; ring
      rw [this, hu_eq x]; simp only [Nat.cast_ofNat]; ring
    intro x
    have := zero_of_hasDerivAt_zero hd (by
      have := hS.ε_bot.sub ((hebot.sub (((hVbot.sub_const 1).pow 2).div_const 2)).const_mul A0)
      simpa using this) x
    exact sub_eq_zero.mp this
  -- downstream limits
  have hVtop : Tendsto (fun x => (Vs g (T.s x) : ℂ)) atTop (𝓝 (vstar g : ℂ)) := by
    have : Tendsto (fun x => Vs g (T.s x)) atTop (𝓝 (Vs g 0)) := by
      unfold Vs; exact ((tendsto_const_nhds.add (hs_top.const_mul 2)).div_const _)
    have e : Vs g 0 = vstar g := by unfold Vs vstar; ring_nf
    rw [e] at this
    exact (Complex.continuous_ofReal.tendsto _).comp this
  have hetop : Tendsto (fun x => (eS g (T.s x) (T.z x) : ℂ)) atTop (𝓝 ((astar g) ^ 2 / 2 : ℝ)) := by
    have hb : Tendsto (fun x => eS g (T.s x) (T.z x)) atTop (𝓝 (astar g ^ 2 / 2)) := by
      -- eS = As/g * (Vs - s z), with s → 0 and z bounded
      have hsz : Tendsto (fun x => T.s x * T.z x) atTop (𝓝 0) := by
        have hbound : ∀ x, |T.s x * T.z x| ≤ B * T.s x := by
          intro x; rw [abs_mul, abs_of_pos (T.s_pos x)]; nlinarith [hB x, T.s_pos x]
        exact squeeze_zero_norm (fun x => by simpa using hbound x) (by simpa using hs_top.const_mul B)
      have hA : Tendsto (fun x => As g (T.s x)) atTop (𝓝 (As g 0)) := by
        unfold As; exact ((tendsto_const_nhds.sub hs_top).const_mul 2).div_const _
      have hV : Tendsto (fun x => Vs g (T.s x)) atTop (𝓝 (Vs g 0)) := by
        unfold Vs; exact ((tendsto_const_nhds.add (hs_top.const_mul 2)).div_const _)
      have := (hA.div_const g).mul (hV.sub hsz)
      have e : As g 0 / g * (Vs g 0 - 0) = astar g ^ 2 / 2 := by
        unfold As Vs astar; field_simp; ring
      rw [e] at this
      convert this using 1
      funext y; rfl
    exact (Complex.continuous_ofReal.tendsto _).comp hb
  have hu_lim : Tendsto S.u atTop (𝓝 (A0 * ((vstar g : ℂ) - 1))) := by
    have := (hVtop.sub_const 1).const_mul A0
    exact this.congr (fun x => (hu_eq x).symm)
  have hε_lim : Tendsto S.ε atTop (𝓝 (A0 * (((astar g ^ 2 / 2 : ℝ) : ℂ) - ((vstar g : ℂ) - 1) ^ 2 / 2))) := by
    have := (hetop.sub (((hVtop.sub_const 1).pow 2).div_const 2)).const_mul A0
    exact this.congr (fun x => (hε_eq x).symm)
  have hv_lim : Tendsto S.v atTop (𝓝 (A0 * ((vstar g : ℂ) - 1))) :=
    hu_lim.congr (fun x => (huv x).symm)
  -- compare with the permitted limits
  have L1 := tendsto_nhds_unique hvlim hv_lim
  have L2 := tendsto_nhds_unique hulim hu_lim
  have L3 := tendsto_nhds_unique hεlim hε_lim
  have hvs : (vstar g : ℂ) - 1 = -(astar g : ℂ) := by
    have : vstar g - 1 = -astar g := by unfold vstar astar; field_simp; ring
    exact_mod_cast this
  have hes : ((astar g ^ 2 / 2 : ℝ) : ℂ) - ((vstar g : ℂ) - 1) ^ 2 / 2 = 0 := by
    rw [hvs]; push_cast; ring
  rw [hvs] at L1 L2; rw [hes] at L3
  -- apply ℓ₋
  have hl1 := ell_r1 hg
  have hl2 := ell_r2 hg
  have hj := ell_jstar hg
  simp only [Fin.sum_univ_three] at hl1 hl2
  have key : (A0 : ℂ) * ((ell g 0 * (-astar g) + ell g 1 * (-astar g) + ell g 2 * 0 : ℝ) : ℂ) = 0 := by
    push_cast
    have e0 : (α * (r1 g 0 : ℂ) + β * (r2 g 0 : ℂ)) = A0 * -(astar g : ℂ) := L1
    have e1' : (α * (r1 g 1 : ℂ) + β * (r2 g 1 : ℂ)) = A0 * -(astar g : ℂ) := L2
    have e2 : (α * (r1 g 2 : ℂ) + β * (r2 g 2 : ℂ)) = A0 * 0 := L3
    have c1 : ((ell g 0 * r1 g 0 + ell g 1 * r1 g 1 + ell g 2 * r1 g 2 : ℝ) : ℂ) = 0 := by
      exact_mod_cast hl1
    have c2 : ((ell g 0 * r2 g 0 + ell g 1 * r2 g 1 + ell g 2 * r2 g 2 : ℝ) : ℂ) = 0 := by
      exact_mod_cast hl2
    push_cast at c1 c2
    linear_combination (ell g 0 : ℂ) * e0.symm + (ell g 1 : ℂ) * e1'.symm
      + (ell g 2 : ℂ) * e2.symm + α * c1 + β * c2
  have hne : ((ell g 0 * (-astar g) + ell g 1 * (-astar g) + ell g 2 * 0 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hj.ne
  have hA00 : A0 = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact h
    · exact absurd h hne
  intro x
  have hu0 : S.u x = 0 := by rw [hu_eq x, hA00]; ring
  refine ⟨by rw [huv x, hu0], hu0, by rw [hε_eq x, hA00]; ring⟩

end

end StrongShock
