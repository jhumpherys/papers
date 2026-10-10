/-
  Scalar coefficient bounds (Lemmas 5.1 and 6.1) and pointwise coercivity
  of the energy form (Propositions 5.2 and 6.2).
-/
import StrongShock.BernsteinBounds

namespace StrongShock

noncomputable section

lemma nonneg_of_mul_eq {x den r : ℝ} (h : x * den = r) (hden : 0 < den) (hr : 0 ≤ r) :
    0 ≤ x := by
  by_contra hx
  push Not at hx
  have : x * den < 0 := mul_neg_of_neg_of_pos hx hden
  linarith

/-- Parametrization of the algebraic region (7.1): `n = 1 + g k`, `z = 1/(1 + g t)` with
    `t = 1 + (k-1) τ` between `1` and `k`. -/
lemma strip_param {g n z : ℝ} (hT : InT g n) (hz : InSlope g n z) :
    ∃ k τ : ℝ, 1 / 2 ≤ k ∧ k ≤ 3 / 2 ∧ 0 ≤ τ ∧ τ ≤ 1 ∧ n = 1 + g * k ∧
      z = 1 / (1 + g * (1 + (k - 1) * τ)) := by
  obtain ⟨hg, hg2, hn1, hn2⟩ := hT
  obtain ⟨hzl, hzu⟩ := hz
  have hnpos : 0 < n := by linarith
  have hzpos : 0 < z := lt_of_lt_of_le (lt_min (by positivity) (by positivity)) hzl
  refine ⟨(n - 1) / g, ?_⟩
  have hk : n = 1 + g * ((n - 1) / g) := by field_simp; ring
  have hk1 : 1 / 2 ≤ (n - 1) / g := by rw [le_div_iff₀ hg]; linarith
  have hk2 : (n - 1) / g ≤ 3 / 2 := by rw [div_le_iff₀ hg]; linarith
  -- `u = 1/z` lies between `g+1` and `n`.
  set u := 1 / z with hu
  have hzu' : z = 1 / u := by rw [hu]; field_simp
  rcases lt_trichotomy n (1 + g) with hlt | heq | hgt
  · -- n < 1+g : z ∈ [1/(g+1), 1/n], u ∈ [n, g+1]
    have h1 : 1 / (g + 1) ≤ 1 / n := one_div_le_one_div_of_le hnpos (by linarith)
    rw [min_eq_left h1] at hzl; rw [max_eq_right h1] at hzu
    have hu1 : u ≤ g + 1 := by
      rw [hu, div_le_iff₀ hzpos]; rw [div_le_iff₀ (by linarith)] at hzl; linarith
    have hu2 : n ≤ u := by
      rw [hu, le_div_iff₀ hzpos]; rw [le_div_iff₀ hnpos] at hzu; linarith
    refine ⟨(u - 1 - g) / (n - 1 - g), hk1, hk2, ?_, ?_, hk, ?_⟩
    · exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · rw [div_le_one_of_neg (by linarith)]; linarith
    · have hne : n - 1 - g ≠ 0 := by linarith
      rw [hzu']; congr 1; field_simp; ring
  · -- n = 1+g : the interval collapses
    have hz1 : z = 1 / (g + 1) := by
      subst heq
      have : 1 / (g + 1) = 1 / (1 + g) := by ring_nf
      rw [this, min_self] at hzl; rw [this, max_self] at hzu
      rw [this]; linarith
    refine ⟨0, hk1, hk2, le_refl _, zero_le_one, hk, ?_⟩
    rw [hz1]; congr 1; ring
  · -- n > 1+g : z ∈ [1/n, 1/(g+1)], u ∈ [g+1, n]
    have h1 : 1 / n ≤ 1 / (g + 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
    rw [min_eq_right h1] at hzl; rw [max_eq_left h1] at hzu
    have hu1 : g + 1 ≤ u := by
      rw [hu, le_div_iff₀ hzpos]; rw [le_div_iff₀ (by linarith)] at hzu; linarith
    have hu2 : u ≤ n := by
      rw [hu, div_le_iff₀ hzpos]; rw [div_le_iff₀ hnpos] at hzl; linarith
    refine ⟨(u - 1 - g) / (n - 1 - g), hk1, hk2, ?_, ?_, hk, ?_⟩
    · exact div_nonneg (by linarith) (by linarith)
    · rw [div_le_one (by linarith)]; linarith
    · have hne : n - 1 - g ≠ 0 := by linarith
      rw [hzu']; congr 1; field_simp; ring

/-- Positivity facts for the box parameters. -/
lemma box_pos {g k τ : ℝ} (hg : 0 < g) (hk1 : 1 / 2 ≤ k) (hk2 : k ≤ 3 / 2) (hτ0 : 0 ≤ τ)
    (hτ1 : τ ≤ 1) : 0 < 1 + g * k ∧ 0 < 1 + g * (1 + (k - 1) * τ) := by
  constructor
  · nlinarith
  · have : 0 ≤ 1 + (k - 1) * τ := by nlinarith
    nlinarith

/-! ### Lemma 7.1: scalar bounds on the explicit transport region -/

section strip
variable {g n s z : ℝ}

set_option hygiene false in
macro "strip_bound" nm:ident bern:ident : tactic => `(tactic| (
  obtain ⟨k, τ, hk1, hk2, hτ0, hτ1, rfl, rfl⟩ := strip_param hT hz
  obtain ⟨hn, ht⟩ := box_pos hT.1 hk1 hk2 hτ0 hτ1
  have hb := $nm g k τ s hT.1 hn ht
  dsimp only at hb
  refine nonneg_of_mul_eq hb (by positivity) ?_
  first
    | exact mul_nonneg hs0 ($bern g k τ s (by linarith [hT.1]) (by linarith [hT.2.1]) hk1 hk2 hτ0 hτ1 hs0 hs1)
    | exact ($bern g k τ s (by linarith [hT.1]) (by linarith [hT.2.1]) hk1 hk2 hτ0 hτ1 hs0 hs1)
    | exact ($bern g k τ s (by linarith [hT.1]) (by linarith [hT.2.1]) hk1 hk2 hτ0 hτ1)
    | exact mul_nonneg hs0 ($bern g k τ s (by linarith [hT.1]) (by linarith) hk1 hk2 hτ0 hτ1 hs0 hs1)))

lemma strip_T1 (hT : InT g n) (hz : InSlope g n z) :
    0 ≤ n * θ g - (n - 1) ^ 2 * (1 - z) ^ 2 / g ^ 2 := by
  have hs0 : (0:ℝ) ≤ 0 := le_refl _
  have hs1 : (0:ℝ) ≤ 1 := zero_le_one
  obtain ⟨k, τ, hk1, hk2, hτ0, hτ1, rfl, rfl⟩ := strip_param hT hz
  obtain ⟨hn, ht⟩ := box_pos hT.1 hk1 hk2 hτ0 hτ1
  have hb := bridge_T1 g k τ 0 hT.1 hn ht
  dsimp only at hb
  exact nonneg_of_mul_eq hb (by have := hT.1; positivity)
    (bern_T1 g k τ 0 (by linarith [hT.1]) (by linarith [hT.2.1]) hk1 hk2 hτ0 hτ1)

lemma strip_Rup (hT : InT g n) (hz : InSlope g n z) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ s - Rc g n s z := by strip_bound bridge_Rup bern_Rup
lemma strip_Rlo (hT : InT g n) (hz : InSlope g n z) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ s + Rc g n s z := by strip_bound bridge_Rlo bern_Rlo
/-- (7.4): `C/s = 2 s (1-s) 𝔄 + s² 𝔅`. -/
lemma C_decomp (g n s z : ℝ) (hg : 0 < g) (hn : 0 < n) :
    Cc g n s z = s * (2 * s * (1 - s) * calA g n z + s ^ 2 * calB g n z) := by
  have : g + 2 ≠ 0 := by linarith
  simp only [calA, calB, Cc, Kc, Bc, Lc, c2S, c1S_s, c1S_z, c1S, d1S, V1S, V2S, cS, dS, Vs, As,
    fS, fZ, f0, f1, θ]
  field_simp
  ring

set_option hygiene false in
macro "strip_bound0" nm:ident bern:ident : tactic => `(tactic| (
  obtain ⟨k, τ, hk1, hk2, hτ0, hτ1, rfl, rfl⟩ := strip_param hT hz
  obtain ⟨hn, ht⟩ := box_pos hT.1 hk1 hk2 hτ0 hτ1
  have hb := $nm g k τ 0 hT.1 hn ht
  dsimp only at hb
  exact nonneg_of_mul_eq hb (by have := hT.1; positivity)
    ($bern g k τ 0 (by linarith [hT.1]) (by linarith [hT.2.1]) hk1 hk2 hτ0 hτ1)))

lemma strip_Alo (hT : InT g n) (hz : InSlope g n z) : 0 ≤ calA g n z := by
  strip_bound0 bridge_Alo bern_Alo
lemma strip_Aup (hT : InT g n) (hz : InSlope g n z) : 0 ≤ 1 / 3 - calA g n z := by
  strip_bound0 bridge_Aup bern_Aup
lemma strip_Blo (hT : InT g n) (hz : InSlope g n z) : 0 ≤ calB g n z + 1 / 6 := by
  strip_bound0 bridge_Blo bern_Blo
lemma strip_Bup (hT : InT g n) (hz : InSlope g n z) : 0 ≤ 1 / 5 - calB g n z := by
  strip_bound0 bridge_Bup bern_Bup

/-- The bound `|C| ≤ (5/21) s` of Lemma 7.1, via (7.4) and the bounds on `𝔄, 𝔅`. -/
lemma strip_C (hT : InT g n) (hz : InSlope g n z) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |Cc g n s z| ≤ 5 / 21 * s := by
  have hn : 0 < n := by linarith [hT.1, hT.2.2.1]
  rw [C_decomp g n s z hT.1 hn]
  have a1 := strip_Alo hT hz; have a2 := strip_Aup hT hz
  have b1 := strip_Blo hT hz; have b2 := strip_Bup hT hz
  have hss : 0 ≤ s * (1 - s) := mul_nonneg hs0 (by linarith)
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  set A := calA g n z; set B := calB g n z
  have up : 2 * s * (1 - s) * A + s ^ 2 * B ≤ 5 / 21 := by
    have e1 : 2 * s * (1 - s) * A ≤ 2 * (s * (1 - s)) * (1 / 3) := by nlinarith
    have e2 : s ^ 2 * B ≤ s ^ 2 * (1 / 5) := by nlinarith
    nlinarith [sq_nonneg (s - 5 / 7)]
  have lo : -(5 / 21) ≤ 2 * s * (1 - s) * A + s ^ 2 * B := by
    have e1 : 0 ≤ 2 * s * (1 - s) * A := by nlinarith
    have e2 : s ^ 2 * (-(1 / 6)) ≤ s ^ 2 * B := by nlinarith
    have : s ^ 2 ≤ 1 := by nlinarith
    nlinarith
  rw [abs_mul, abs_of_nonneg hs0]
  have := abs_le.mpr ⟨lo, up⟩
  nlinarith [abs_nonneg (2 * s * (1 - s) * A + s ^ 2 * B)]

lemma strip_P1lo (hT : InT g n) (hg : g ≤ 2 / 5) (hz : InSlope g n z) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : 0 ≤ P1c g n s z - 3 / 32 * s := by
  obtain ⟨k, τ, hk1, hk2, hτ0, hτ1, rfl, rfl⟩ := strip_param hT hz
  obtain ⟨hn, ht⟩ := box_pos hT.1 hk1 hk2 hτ0 hτ1
  have hb := bridge_P1lo g k τ s hT.1 hn ht
  dsimp only at hb
  exact nonneg_of_mul_eq hb (by have := hT.1; positivity)
    (mul_nonneg hs0 (bern_P1lo g k τ s (by linarith [hT.1]) hg hk1 hk2 hτ0 hτ1 hs0 hs1))
lemma strip_P1hi (hT : InT g n) (hg : 2 / 5 ≤ g) (hz : InSlope g n z) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : 0 ≤ P1c g n s z - 3 / 50 * s := by
  obtain ⟨k, τ, hk1, hk2, hτ0, hτ1, rfl, rfl⟩ := strip_param hT hz
  obtain ⟨hn, ht⟩ := box_pos hT.1 hk1 hk2 hτ0 hτ1
  have hb := bridge_P1hi g k τ s hT.1 hn ht
  dsimp only at hb
  exact nonneg_of_mul_eq hb (by have := hT.1; positivity)
    (mul_nonneg hs0 (bern_P1hi g k τ s hg hT.2.1 hk1 hk2 hτ0 hτ1 hs0 hs1))
lemma strip_P2lo (hT : InT g n) (hg : g ≤ 2 / 5) (hz : InSlope g n z) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : 0 ≤ P2c g n s z - 1 / 2 * s := by
  obtain ⟨k, τ, hk1, hk2, hτ0, hτ1, rfl, rfl⟩ := strip_param hT hz
  obtain ⟨hn, ht⟩ := box_pos hT.1 hk1 hk2 hτ0 hτ1
  have hb := bridge_P2lo g k τ s hT.1 hn ht
  dsimp only at hb
  exact nonneg_of_mul_eq hb (by have := hT.1; positivity)
    (mul_nonneg hs0 (bern_P2lo g k τ s (by linarith [hT.1]) hg hk1 hk2 hτ0 hτ1 hs0 hs1))
lemma strip_P2hi (hT : InT g n) (hg : 2 / 5 ≤ g) (hz : InSlope g n z) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : 0 ≤ P2c g n s z - 3 / 4 * s := by
  obtain ⟨k, τ, hk1, hk2, hτ0, hτ1, rfl, rfl⟩ := strip_param hT hz
  obtain ⟨hn, ht⟩ := box_pos hT.1 hk1 hk2 hτ0 hτ1
  have hb := bridge_P2hi g k τ s hT.1 hn ht
  dsimp only at hb
  exact nonneg_of_mul_eq hb (by have := hT.1; positivity)
    (mul_nonneg hs0 (bern_P2hi g k τ s hg hT.2.1 hk1 hk2 hτ0 hτ1 hs0 hs1))

end strip

/-! ### Square completion (5.10) -/

lemma Qform_complete (g n s z p1 p2 q1 q2 : ℝ) (hθ : 0 < θ g)
    (hD : 0 < 4 * (n / θ g) - Kc g n s z ^ 2) :
    Qform g n s z p1 p2 q1 q2 =
      (p1 + (Kc g n s z * p2 + Rc g n s z * q2) / 2) ^ 2
      + (4 * (n / θ g) - Kc g n s z ^ 2) / 4 *
          (p2 - Kc g n s z * Rc g n s z * q2 / (4 * (n / θ g) - Kc g n s z ^ 2)) ^ 2
      + P1c g n s z * q1 ^ 2
      + (P2c g n s z - n / θ g * Rc g n s z ^ 2 / (4 * (n / θ g) - Kc g n s z ^ 2)) * q2 ^ 2
      + Cc g n s z * q1 * q2 := by
  unfold Qform
  generalize Kc g n s z = K at *
  generalize Rc g n s z = R
  generalize n / θ g = m at *
  generalize hDdef : 4 * m - K ^ 2 = D at *
  have hm : m = (D + K ^ 2) / 4 := by linarith
  subst hm
  have hD0 : D ≠ 0 := hD.ne'
  field_simp
  ring

/-- An elementary two-by-two estimate. -/
lemma two_by_two {a b c ρ q1 q2 : ℝ} (hρ : 0 < ρ) (hc : 0 ≤ c) (ha : c * ρ ≤ a)
    (hb : c ≤ b * ρ) (C : ℝ) (hC : |C| ≤ 2 * c) :
    0 ≤ a * q1 ^ 2 + b * q2 ^ 2 + C * q1 * q2 := by
  have h1 : |C * q1 * q2| ≤ 2 * c * (|q1| * |q2|) := by
    rw [abs_mul, abs_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right hC (by positivity)
  have h2 : 2 * (|q1| * |q2|) * ρ ≤ ρ ^ 2 * q1 ^ 2 + q2 ^ 2 := by
    have := sq_nonneg (ρ * |q1| - |q2|)
    have e1 : |q1| ^ 2 = q1 ^ 2 := sq_abs q1
    have e2 : |q2| ^ 2 = q2 ^ 2 := sq_abs q2
    nlinarith
  have h3 : 2 * c * (|q1| * |q2|) * ρ ≤ c * ρ ^ 2 * q1 ^ 2 + c * q2 ^ 2 := by nlinarith
  have h4 : c * ρ ^ 2 * q1 ^ 2 + c * q2 ^ 2 ≤ ρ * (a * q1 ^ 2 + b * q2 ^ 2) := by
    have e1 := mul_le_mul_of_nonneg_right ha (mul_nonneg hρ.le (sq_nonneg q1))
    have e2 := mul_le_mul_of_nonneg_right hb (sq_nonneg q2)
    nlinarith
  have h5 : -(C * q1 * q2) ≤ |C * q1 * q2| := neg_le_abs _
  nlinarith

/-- Coercivity given the scalar bounds (generic form). -/
lemma coercive_of_bounds {g n s z : ℝ} (hg : 0 < g) (hn : 0 < n) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (χ α β κ ρ γc : ℝ) (hχ : χ < 1) (hχ0 : 0 ≤ χ)
    (hK : Kc g n s z ^ 2 ≤ 4 * χ * (n / θ g))
    (hR : Rc g n s z ^ 2 ≤ s ^ 2)
    (hP1 : α * s ≤ P1c g n s z) (hP2 : β * s ≤ P2c g n s z)
    (hC : |Cc g n s z| ≤ γc * s) (hρ : 0 < ρ) (hγ : 0 ≤ γc)
    (h1 : γc / 2 * ρ ≤ α - κ) (h2 : γc / 2 ≤ (β - 1 / (4 * (1 - χ)) - κ) * ρ)
    (p1 p2 q1 q2 : ℝ) :
    κ * s * (q1 ^ 2 + q2 ^ 2) ≤ Qform g n s z p1 p2 q1 q2 := by
  have hθ := θ_pos g hg
  set m := n / θ g with hm
  have hmpos : 0 < m := by positivity
  set K := Kc g n s z
  set R := Rc g n s z
  have hD : 0 < 4 * m - K ^ 2 := by nlinarith
  rw [Qform_complete g n s z p1 p2 q1 q2 hθ hD]
  -- the Schur term
  have hS : m * R ^ 2 / (4 * m - K ^ 2) ≤ s * (1 / (4 * (1 - χ))) := by
    rw [div_le_iff₀ hD]
    have h4 : 4 * m * (1 - χ) ≤ 4 * m - K ^ 2 := by nlinarith
    have : m * R ^ 2 ≤ m * s ^ 2 := mul_le_mul_of_nonneg_left hR hmpos.le
    have hs2 : s ^ 2 ≤ s := by nlinarith
    have hfrac : s * (1 / (4 * (1 - χ))) * (4 * m - K ^ 2) ≥ s * (1 / (4 * (1 - χ))) * (4 * m * (1 - χ)) :=
      mul_le_mul_of_nonneg_left h4 (by have : 0 < 1 - χ := by linarith
                                       positivity)
    have heq : s * (1 / (4 * (1 - χ))) * (4 * m * (1 - χ)) = s * m := by
      have : 1 - χ ≠ 0 := by linarith
      field_simp
    nlinarith
  have hsq1 := sq_nonneg (p1 + (K * p2 + R * q2) / 2)
  have hsq2 : 0 ≤ (4 * m - K ^ 2) / 4 * (p2 - K * R * q2 / (4 * m - K ^ 2)) ^ 2 := by positivity
  -- remaining 2x2 form
  have key : 0 ≤ (P1c g n s z - κ * s) * q1 ^ 2
      + (P2c g n s z - m * R ^ 2 / (4 * m - K ^ 2) - κ * s) * q2 ^ 2
      + Cc g n s z * q1 * q2 := by
    apply two_by_two (c := γc / 2 * s) (ρ := ρ) hρ (by positivity)
    · nlinarith
    · nlinarith
    · linarith
  nlinarith

/-! ### Proposition 7.2 (pointwise form): coercivity on the explicit region -/

theorem strip_coercive {g n s z : ℝ} (hT : InT g n) (hz : InSlope g n z) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (p1 p2 q1 q2 : ℝ) :
    s / 200 * (q1 ^ 2 + q2 ^ 2) ≤ Qform g n s z p1 p2 q1 q2 := by
  have hg := hT.1
  have hn : 0 < n := by linarith [hT.2.2.1]
  have hθ := θ_pos g hg
  -- χ ≤ s^2/4 ≤ 1/4
  have hT1 := strip_T1 hT hz
  have hK : Kc g n s z ^ 2 ≤ 4 * (1 / 4) * (n / θ g) := by
    have e : Kc g n s z ^ 2 = s ^ 2 * ((n - 1) ^ 2 * (1 - z) ^ 2 / g ^ 2) / θ g ^ 2 := by
      unfold Kc cS; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have : (n - 1) ^ 2 * (1 - z) ^ 2 / g ^ 2 ≤ n * θ g := by linarith
    have hs2 : s ^ 2 ≤ 1 := by nlinarith
    have : s ^ 2 * ((n - 1) ^ 2 * (1 - z) ^ 2 / g ^ 2) ≤ 1 * (n * θ g) := by
      apply mul_le_mul hs2 this (by positivity) (by norm_num)
    have e2 : 4 * (1 / 4) * (n / θ g) * θ g ^ 2 = n * θ g := by field_simp
    nlinarith
  have hR : Rc g n s z ^ 2 ≤ s ^ 2 := by
    have a := strip_Rup hT hz hs0.le hs1
    have b := strip_Rlo hT hz hs0.le hs1
    nlinarith
  have hC : |Cc g n s z| ≤ 5 / 21 * s := strip_C hT hz hs0.le hs1
  rcases le_total g (2 / 5) with hgl | hgh
  · have hP1 := strip_P1lo hT hgl hz hs0.le hs1
    have hP2 := strip_P2lo hT hgl hz hs0.le hs1
    have := coercive_of_bounds hg hn hs0 hs1 (1 / 4) (3 / 32) (1 / 2) (1 / 200) (37 / 50) (5 / 21)
      (by norm_num) (by norm_num) hK hR (by linarith) (by linarith) hC (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) p1 p2 q1 q2
    linarith
  · have hP1 := strip_P1hi hT hgh hz hs0.le hs1
    have hP2 := strip_P2hi hT hgh hz hs0.le hs1
    have := coercive_of_bounds hg hn hs0 hs1 (1 / 4) (3 / 50) (3 / 4) (1 / 200) (2 / 5) (5 / 21)
      (by norm_num) (by norm_num) hK hR (by linarith) (by linarith) hC (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) p1 p2 q1 q2
    linarith

/-! ### Lemma 6.1 and Proposition 6.2: the reference line `ν = Γ + 1` -/

section line
variable {g s : ℝ}

set_option hygiene false in
macro "line_bound" nm:ident bern:ident : tactic => `(tactic| (
  have hb := $nm g s hg
  dsimp only at hb
  refine nonneg_of_mul_eq hb (by positivity) ?_
  exact mul_nonneg hs0 ($bern g 1 0 s hg.le hg1 hs0 hs1)))

lemma line_T1 (hg : 0 < g) (hg1 : g ≤ 1) :
    0 ≤ 4 * (1 + g) * θ g - 6 * ((1 + g) - 1) ^ 2 * (1 - 1 / (1 + g)) ^ 2 / g ^ 2 := by
  have hb := bridge_LT1 g 0 hg
  dsimp only at hb
  exact nonneg_of_mul_eq hb (by positivity) (bern_LT1 g 1 0 0 hg.le hg1)
lemma line_P1 (hg : 0 < g) (hg1 : g ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ P1c g (1 + g) s (1 / (1 + g)) - 1 / 24 * s := by line_bound bridge_LP1 bern_LP1
lemma line_P2 (hg : 0 < g) (hg1 : g ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ P2c g (1 + g) s (1 / (1 + g)) - 1 / 2 * s := by line_bound bridge_LP2 bern_LP2
lemma line_Rup (hg : 0 < g) (hg1 : g ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ s - Rc g (1 + g) s (1 / (1 + g)) := by line_bound bridge_LRup bern_LRup
lemma line_Rlo (hg : 0 < g) (hg1 : g ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ s + Rc g (1 + g) s (1 / (1 + g)) := by line_bound bridge_LRlo bern_LRlo
lemma line_Cnn (hg : 0 < g) (hg1 : g ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ Cc g (1 + g) s (1 / (1 + g)) := by line_bound bridge_LCnn bern_LCnn
lemma line_Cup (hg : 0 < g) (hg1 : g ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ 1 / 6 * s - Cc g (1 + g) s (1 / (1 + g)) := by line_bound bridge_LCup bern_LCup

end line

/-- Proposition 6.2 (pointwise): on the reference line the energy form is coercive. -/
theorem line_coercive {g s : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (p1 p2 q1 q2 : ℝ) :
    s / 180 * (q1 ^ 2 + q2 ^ 2) ≤ Qform g (1 + g) s (1 / (1 + g)) p1 p2 q1 q2 := by
  have hn : 0 < 1 + g := by linarith
  have hθ := θ_pos g hg
  have hT1 := line_T1 hg hg1
  have hK : Kc g (1 + g) s (1 / (1 + g)) ^ 2 ≤ 4 * (1 / 6) * ((1 + g) / θ g) := by
    have e : Kc g (1 + g) s (1 / (1 + g)) ^ 2 =
        s ^ 2 * (((1 + g) - 1) ^ 2 * (1 - 1 / (1 + g)) ^ 2 / g ^ 2) / θ g ^ 2 := by
      unfold Kc cS; field_simp; ring
    rw [e, div_le_iff₀ (by positivity)]
    have h6 : 6 * (((1 + g) - 1) ^ 2 * (1 - 1 / (1 + g)) ^ 2 / g ^ 2) ≤ 4 * (1 + g) * θ g := by
      have : 6 * (((1 + g) - 1) ^ 2 * (1 - 1 / (1 + g)) ^ 2 / g ^ 2)
          = 6 * ((1 + g) - 1) ^ 2 * (1 - 1 / (1 + g)) ^ 2 / g ^ 2 := by ring
      linarith
    have hs2 : s ^ 2 ≤ 1 := by nlinarith
    have hX : 0 ≤ ((1 + g) - 1) ^ 2 * (1 - 1 / (1 + g)) ^ 2 / g ^ 2 := by positivity
    have e2 : 4 * (1 / 6) * ((1 + g) / θ g) * θ g ^ 2 = (2 / 3) * ((1 + g) * θ g) := by
      field_simp; ring
    nlinarith
  have hR : Rc g (1 + g) s (1 / (1 + g)) ^ 2 ≤ s ^ 2 := by
    have a := line_Rup hg hg1 hs0.le hs1
    have b := line_Rlo hg hg1 hs0.le hs1
    nlinarith
  have hC : |Cc g (1 + g) s (1 / (1 + g))| ≤ 1 / 6 * s := by
    have a := line_Cup hg hg1 hs0.le hs1
    have b := line_Cnn hg hg1 hs0.le hs1
    rw [abs_le]; constructor <;> linarith
  have hP1 := line_P1 hg hg1 hs0.le hs1
  have hP2 := line_P2 hg hg1 hs0.le hs1
  have := coercive_of_bounds hg hn hs0 hs1 (1 / 6) (1 / 24) (1 / 2) (1 / 180) (43 / 100) (1 / 6)
    (by norm_num) (by norm_num) hK hR (by linarith) (by linarith) hC (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) p1 p2 q1 q2
  linarith

end

end StrongShock
