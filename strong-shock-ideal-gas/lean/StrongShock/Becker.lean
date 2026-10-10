/-
  Lemma 2.1: the strong-shock limit of the Becker profile is a limiting profile on the
  reference line `ν = Γ + 1`.  This also shows that the hypotheses packaged in
  `LimitingProfile` are satisfiable.
-/
import StrongShock.Profile
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Filter Topology Set

namespace StrongShock

noncomputable section

/-- `s(x) = 1/(1 + exp((x - x₀)/γ))`. -/
def beckerS (g x0 x : ℝ) : ℝ := 1 / (1 + Real.exp ((x - x0) / (g + 1)))

lemma beckerS_pos (g x0 x : ℝ) : 0 < beckerS g x0 x := by
  unfold beckerS; positivity

lemma beckerS_lt (g x0 x : ℝ) : beckerS g x0 x < 1 := by
  unfold beckerS
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos ((x - x0) / (g + 1))]

lemma beckerS_deriv {g : ℝ} (hg : 0 < g) (x0 x : ℝ) :
    HasDerivAt (beckerS g x0) (-(beckerS g x0 x) * (1 - beckerS g x0 x) / (g + 1)) x := by
  have h1 : HasDerivAt (fun y => (y - x0) / (g + 1)) (1 / (g + 1)) x :=
    ((hasDerivAt_id x).sub_const x0).div_const (g + 1)
  have h2 := h1.exp.const_add 1
  have hne : (1 + Real.exp ((x - x0) / (g + 1))) ≠ 0 := by positivity
  have h3 := h2.inv hne
  refine hasDerivAt_of_eq h3 (fun y => by simp [beckerS]) ?_
  unfold beckerS
  have : g + 1 ≠ 0 := by linarith
  field_simp
  ring

/-- The explicit limiting profile (2.4). -/
def becker (g x0 : ℝ) (hg : 0 < g) : LimitingProfile g (g + 1) where
  V := fun x => (g + 2 * beckerS g x0 x) / (g + 2)
  e := fun x => (1 - ((g + 2 * beckerS g x0 x) / (g + 2)) ^ 2) / (2 * (g + 1))
  hV := fun x => by
    have hs := beckerS_deriv hg x0 x
    have h := ((hs.const_mul 2).const_add g).div_const (g + 2)
    refine hasDerivAt_of_eq h (fun y => rfl) ?_
    have : g + 2 ≠ 0 := by linarith
    have : g + 1 ≠ 0 := by linarith
    field_simp
    ring
  he := fun x => by
    have hs := beckerS_deriv hg x0 x
    have hV := ((hs.const_mul 2).const_add g).div_const (g + 2)
    have h := ((hasDerivAt_const x (1:ℝ)).sub (hV.pow 2)).div_const (2 * (g + 1))
    refine hasDerivAt_of_eq h (fun y => rfl) ?_
    have : g + 2 ≠ 0 := by linarith
    have : g + 1 ≠ 0 := by linarith
    simp only [Pi.sub_apply, Pi.pow_apply, Nat.cast_ofNat]
    generalize beckerS g x0 x = S
    simp only [show (2:ℕ) - 1 = 1 from rfl, pow_one]
    field_simp
    ring
  V_gt := fun x => by
    have := beckerS_pos g x0 x
    unfold vstar
    apply div_lt_div_of_pos_right _ (by linarith); linarith
  V_lt := fun x => by
    have := beckerS_lt g x0 x
    rw [div_lt_one (by linarith)]; linarith
  V_bot := by
    have hs : Tendsto (beckerS g x0) atBot (𝓝 1) := by
      have h1 : Tendsto (fun x => (x - x0) / (g + 1)) atBot atBot :=
        (tendsto_atBot_add_const_right _ (-x0) tendsto_id).atBot_div_const (by linarith)
      have h2 := (Real.tendsto_exp_atBot.comp h1).const_add 1
      have h3 := h2.inv₀ (by norm_num)
      simp only [add_zero, inv_one] at h3
      refine h3.congr (fun x => ?_)
      simp [beckerS, Function.comp]
    have := ((hs.const_mul 2).const_add g).div_const (g + 2)
    have e : (g + 2 * 1) / (g + 2) = 1 := by
      have : g + 2 ≠ 0 := by linarith
      field_simp
    rw [e] at this
    exact this
  e_bot := by
    have hs : Tendsto (beckerS g x0) atBot (𝓝 1) := by
      have h1 : Tendsto (fun x => (x - x0) / (g + 1)) atBot atBot :=
        (tendsto_atBot_add_const_right _ (-x0) tendsto_id).atBot_div_const (by linarith)
      have h2 := (Real.tendsto_exp_atBot.comp h1).const_add 1
      have h3 := h2.inv₀ (by norm_num)
      simp only [add_zero, inv_one] at h3
      refine h3.congr (fun x => ?_)
      simp [beckerS, Function.comp]
    have := (((((hs.const_mul 2).const_add g).div_const (g + 2)).pow 2).const_sub 1).div_const
      (2 * (g + 1))
    have e : (1 - ((g + 2 * 1) / (g + 2)) ^ 2) / (2 * (g + 1)) = 0 := by
      have : g + 2 ≠ 0 := by linarith
      field_simp; ring
    rw [e] at this
    exact this
  V_top := by
    have hs : Tendsto (beckerS g x0) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x => (x - x0) / (g + 1)) atTop atTop :=
        (tendsto_atTop_add_const_right _ (-x0) tendsto_id).atTop_div_const (by linarith)
      have h2 := tendsto_atTop_add_const_left _ 1 (Real.tendsto_exp_atTop.comp h1)
      have h3 := h2.inv_tendsto_atTop
      refine h3.congr (fun x => ?_)
      simp [beckerS, Function.comp]
    have := ((hs.const_mul 2).const_add g).div_const (g + 2)
    have e : (g + 2 * 0) / (g + 2) = vstar g := by unfold vstar; ring_nf
    rw [e] at this
    exact this
  e_top := by
    have hs : Tendsto (beckerS g x0) atTop (𝓝 0) := by
      have h1 : Tendsto (fun x => (x - x0) / (g + 1)) atTop atTop :=
        (tendsto_atTop_add_const_right _ (-x0) tendsto_id).atTop_div_const (by linarith)
      have h2 := tendsto_atTop_add_const_left _ 1 (Real.tendsto_exp_atTop.comp h1)
      have h3 := h2.inv_tendsto_atTop
      refine h3.congr (fun x => ?_)
      simp [beckerS, Function.comp]
    have := (((((hs.const_mul 2).const_add g).div_const (g + 2)).pow 2).const_sub 1).div_const
      (2 * (g + 1))
    have e : (1 - ((g + 2 * 0) / (g + 2)) ^ 2) / (2 * (g + 1)) = astar g ^ 2 / 2 := by
      unfold astar
      have : g + 2 ≠ 0 := by linarith
      have : g + 1 ≠ 0 := by linarith
      field_simp; ring
    rw [e] at this
    exact this
  zlim := 1 / (g + 1)
  zlim_pos := by positivity
  z_top := by
    apply tendsto_const_nhds.congr
    intro x
    beta_reduce
    have hs := beckerS_pos g x0 x
    have hs1 := beckerS_lt g x0 x
    generalize beckerS g x0 x = S at hs hs1 ⊢
    have hg2 : g + 2 ≠ 0 := by linarith
    have hg1 : g + 1 ≠ 0 := by linarith
    have hV1 : 1 - (g + 2 * S) / (g + 2) = 2 * (1 - S) / (g + 2) := by field_simp; ring
    have hsP : ((g + 2) * ((g + 2 * S) / (g + 2)) - g) / 2 = S := by field_simp; ring
    rw [hV1, hsP]
    have hS1 : 1 - S ≠ 0 := by linarith
    have hS0 : S ≠ 0 := hs.ne'
    field_simp
    ring

end

end StrongShock
