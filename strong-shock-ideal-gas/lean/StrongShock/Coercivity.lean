/-
  Section 6: pointwise coercivity of the pair form for both weights.
  Everything here is algebra in the profile coordinates `(s,z)`.
-/
import StrongShock.EnergyIdentity
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace StrongShock

noncomputable section

/-- A two-by-two form with nonnegative diagonal and nonnegative determinant is nonnegative. -/
lemma form_nonneg {α β γ X Z : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hdet : β ^ 2 ≤ α * γ) :
    0 ≤ α * X ^ 2 + 2 * β * X * Z + γ * Z ^ 2 := by
  rcases hα.lt_or_eq with hα' | hα'
  · have h : α * (α * X ^ 2 + 2 * β * X * Z + γ * Z ^ 2)
        = (α * X + β * Z) ^ 2 + (α * γ - β ^ 2) * Z ^ 2 := by ring
    have : 0 ≤ α * (α * X ^ 2 + 2 * β * X * Z + γ * Z ^ 2) := by
      rw [h]; have := sq_nonneg (α * X + β * Z); have := sq_nonneg Z; nlinarith
    exact (mul_nonneg_iff_of_pos_left hα').mp this
  · subst hα'
    have hβ : β = 0 := by nlinarith [sq_nonneg β]
    subst hβ; simp; positivity

/-! ### The constant weight below the reference line (Section 6.1) -/

lemma upper_id (g n a c : ℝ) (hg : g ≠ 0) (hn : n ≠ 0) (hg2 : g + 2 ≠ 0) :
    let d := 1 - a * (g + 2) / 2 - g * c
    2 / (g + 2) ^ 2 * (2 - (1 - d) ^ 2) - (a ^ 2 / 2 + (3 * n + 1) / (2 * n) * a * c
      + (n + 1) / (2 * n) * c ^ 2 + (n - 1) * (n - 2) / (2 * n * g) * c * d)
    = (n - 1) / (2 * n) * a * d
      + ((3 * n - 1) / (2 * n) - 2 * (2 / (g + 2) ^ 2) - (n - 1) * (n - 2) / (2 * n * g)) * c * d
      + (d - c) * (((3 * n + 1) / (2 * n) - 2 * g / (g + 2)) * a
        + ((n + 1) / (2 * n) - 2 / (g + 2) ^ 2 * g ^ 2) * c + 2 * (2 / (g + 2) ^ 2) * d) := by
  intro d
  simp only [d]
  field_simp
  ring

lemma eta_lt_half (g : ℝ) (hg : 0 < g) : 2 * (2 / (g + 2) ^ 2) < 1 := by
  have h4 : 4 < (g + 2) ^ 2 := by
    have e : (g + 2) ^ 2 = 4 + g * (g + 4) := by ring
    have : 0 < g * (g + 4) := by positivity
    rw [e]; linarith
  rw [show 2 * (2 / (g + 2) ^ 2) = 4 / (g + 2) ^ 2 by ring, div_lt_one (by positivity)]
  exact h4

lemma eta_g_sq (g : ℝ) (hg : 0 < g) (hg2 : g < 2) : 2 / (g + 2) ^ 2 * g ^ 2 < 1 / 2 := by
  rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
  have : g ^ 2 < (g + 2) ^ 2 / 4 := by nlinarith
  nlinarith

lemma alpha1_pos (g n : ℝ) (hg : 0 < g) (hg2 : g < 2) (hn1 : 1 ≤ n) : 0 < (3 * n + 1) / (2 * n) - 2 * g / (g + 2) := by
  have h1 : 1 ≤ (3 * n + 1) / (2 * n) := by rw [le_div_iff₀ (by positivity)]; linarith
  have h2 : 2 * g / (g + 2) < 1 := by rw [div_lt_one (by linarith)]; linarith
  linarith

lemma alpha2_nonneg (g n : ℝ) (hg : 0 < g) (hg2 : g < 2) (hn1 : 1 ≤ n) :
    0 ≤ (n + 1) / (2 * n) - 2 / (g + 2) ^ 2 * g ^ 2 := by
  have h1 : 1 / 2 ≤ (n + 1) / (2 * n) := by rw [le_div_iff₀ (by positivity)]; linarith
  linarith [eta_g_sq g hg hg2]

lemma alpha2_shift (g n : ℝ) (hg : 0 < g) (hg2 : g < 2) (hn1 : 1 ≤ n) :
    0 ≤ (n + 1) / (2 * n) - 2 / (g + 2) ^ 2 * g ^ 2 - (2 - n) / (2 * n) := by
  have e : (n + 1) / (2 * n) - (2 - n) / (2 * n) = 1 - 1 / (2 * n) := by
    have : n ≠ 0 := by linarith
    field_simp; ring
  have h1 : 1 / (2 * n) ≤ 1 / 2 := by rw [div_le_div_iff₀ (by positivity) two_pos]; linarith
  linarith [eta_g_sq g hg hg2]

lemma alpha4_nonneg (g n : ℝ) (hg : 0 < g) (hn1 : 1 ≤ n) (hng : n ≤ g + 1) :
    0 ≤ (3 * n - 1) / (2 * n) - 2 * (2 / (g + 2) ^ 2) - (n - 1) * (n - 2) / (2 * n * g) := by
  have hn0 : 0 < n := by linarith
  have hη := eta_lt_half g hg
  rcases le_total n 2 with h2 | h2
  · have h3 : (n - 1) * (n - 2) / (2 * n * g) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith))
        (by positivity)
    have h4 : 1 ≤ (3 * n - 1) / (2 * n) := by rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  · have h3 : (n - 1) * (n - 2) / (2 * n * g) ≤ (n - 2) / (2 * n) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ (n - 2) * (2 * n) * (g + 1 - n) :=
        mul_nonneg (mul_nonneg (by linarith) (by positivity)) (by linarith)
      nlinarith
    have e : (3 * n - 1) / (2 * n) - (n - 2) / (2 * n) = 1 + 1 / (2 * n) := by
      field_simp; ring
    have : 0 < 1 / (2 * n) := by positivity
    linarith

/-- **Lemma 6.1.** Bounds on `𝒯` in the cone below the reference line. -/
lemma Tcal_bounds {g n s z : ℝ} (hg : 0 < g) (hg2 : g < 2) (hn1 : 1 ≤ n) (hng : n ≤ g + 1)
    (hs0 : 0 < s) (hs1 : s < 1) (hz0 : 1 / (g + 1) ≤ z) (hz1 : z ≤ 1 / n) :
    2 / (g + 2) ^ 2 * (1 - dS s z) ^ 2 ≤ Tcal g n s z ∧
      Tcal g n s z ≤ 2 / (g + 2) ^ 2 * (2 - (1 - dS s z) ^ 2) := by
  have hg1 : 0 < g + 1 := by linarith
  have hn0 : 0 < n := by linarith
  have hzpos : 0 < z := lt_of_lt_of_le (by positivity) hz0
  have hnz : n * z ≤ 1 := by rw [le_div_iff₀ hn0] at hz1; linarith
  have hgz : 1 ≤ (g + 1) * z := by rw [div_le_iff₀ hg1] at hz0; linarith
  -- profile quantities as functions of s, z
  have hc : cS g s z = s * (1 - z) / g := rfl
  have hd : dS s z = s * z := rfl
  have ha : As g s = 2 * (1 - s) / (g + 2) := rfl
  have hcone1 : (n - 1) * dS s z ≤ g * cS g s z := by
    rw [hc, hd, mul_div_cancel₀ _ hg.ne']; nlinarith
  have hcone2 : cS g s z ≤ dS s z := by
    rw [hc, hd, div_le_iff₀ hg]; nlinarith
  have hc0 : 0 ≤ cS g s z := by
    rw [hc]; apply div_nonneg _ hg.le
    have : z ≤ 1 := by nlinarith
    nlinarith
  have hd0 : 0 < dS s z := by rw [hd]; positivity
  have ha0 : 0 < As g s := by rw [ha]; apply div_pos <;> linarith
  have hdrel : dS s z = 1 - As g s * (g + 2) / 2 - g * cS g s z := by
    rw [hc, hd, ha]; field_simp; ring
  have hT : Tcal g n s z = As g s ^ 2 / 2 + (3 * n + 1) / (2 * n) * As g s * cS g s z
      + (n + 1) / (2 * n) * cS g s z ^ 2
      + (n - 1) * (n - 2) / (2 * n * g) * cS g s z * dS s z := rfl
  generalize As g s = a at *
  generalize cS g s z = c at *
  generalize dS s z = d at *
  subst hdrel
  set d := 1 - a * (g + 2) / 2 - g * c with hd'
  constructor
  · have hlow : Tcal g n s z - 2 / (g + 2) ^ 2 * (1 - d) ^ 2
        = ((3 * n + 1) / (2 * n) - 2 * g / (g + 2)) * a * c
          + ((n + 1) / (2 * n) - 2 / (g + 2) ^ 2 * g ^ 2) * c ^ 2
          + (n - 1) * (n - 2) / (2 * n * g) * c * d := by
      rw [hT, hd']; field_simp; ring
    have h1 := mul_nonneg (mul_nonneg (alpha1_pos g n hg hg2 hn1).le ha0.le) hc0
    rcases le_total 2 n with h2 | h2
    · have h3 : 0 ≤ (n - 1) * (n - 2) / (2 * n * g) :=
        div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      have h4 := mul_nonneg (alpha2_nonneg g n hg hg2 hn1) (sq_nonneg c)
      have h5 := mul_nonneg (mul_nonneg h3 hc0) hd0.le
      linarith
    · have e : (n + 1) / (2 * n) - 2 / (g + 2) ^ 2 * g ^ 2
          = ((n + 1) / (2 * n) - 2 / (g + 2) ^ 2 * g ^ 2 - (2 - n) / (2 * n))
            + (2 - n) / (2 * n) := by ring
      have e2 : (n - 1) * (n - 2) / (2 * n * g) * c * d + (2 - n) / (2 * n) * c ^ 2
          = (2 - n) / (2 * n * g) * c * (g * c - (n - 1) * d) := by
        field_simp; ring
      have h4 := mul_nonneg (alpha2_shift g n hg hg2 hn1) (sq_nonneg c)
      have h5 : 0 ≤ (2 - n) / (2 * n * g) * c * (g * c - (n - 1) * d) :=
        mul_nonneg (mul_nonneg (div_nonneg (by linarith) (by positivity)) hc0) (by linarith)
      nlinarith
  · have hup := upper_id g n a c hg.ne' hn0.ne' (by linarith)
    simp only at hup
    rw [← hd'] at hup
    have hupT : 2 / (g + 2) ^ 2 * (2 - (1 - d) ^ 2) - Tcal g n s z
        = (n - 1) / (2 * n) * a * d
          + ((3 * n - 1) / (2 * n) - 2 * (2 / (g + 2) ^ 2) - (n - 1) * (n - 2) / (2 * n * g)) * c * d
          + (d - c) * (((3 * n + 1) / (2 * n) - 2 * g / (g + 2)) * a
            + ((n + 1) / (2 * n) - 2 / (g + 2) ^ 2 * g ^ 2) * c + 2 * (2 / (g + 2) ^ 2) * d) := by
      rw [hT]; exact hup
    have e1 : 0 ≤ (n - 1) / (2 * n) * a * d :=
      mul_nonneg (mul_nonneg (div_nonneg (by linarith) (by positivity)) ha0.le) hd0.le
    have e2 := mul_nonneg (mul_nonneg (alpha4_nonneg g n hg hn1 hng) hc0) hd0.le
    have e3 : 0 ≤ (d - c) * (((3 * n + 1) / (2 * n) - 2 * g / (g + 2)) * a
            + ((n + 1) / (2 * n) - 2 / (g + 2) ^ 2 * g ^ 2) * c + 2 * (2 / (g + 2) ^ 2) * d) := by
      apply mul_nonneg (by linarith)
      have := mul_nonneg (alpha1_pos g n hg hg2 hn1).le ha0.le
      have := mul_nonneg (alpha2_nonneg g n hg hg2 hn1) hc0
      have : 0 ≤ 2 * (2 / (g + 2) ^ 2) * d := by positivity
      linarith
    linarith

/-- A form with `0 < α ≤ 1` and `αγ - β² ≥ k ≥ 0` dominates `k Y²`. -/
lemma form_lower {α β γ k X Y : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hk : 0 ≤ k)
    (hdet : k ≤ α * γ - β ^ 2) : k * Y ^ 2 ≤ α * X ^ 2 + 2 * β * X * Y + γ * Y ^ 2 := by
  have h : α * (α * X ^ 2 + 2 * β * X * Y + γ * Y ^ 2)
      = (α * X + β * Y) ^ 2 + (α * γ - β ^ 2) * Y ^ 2 := by ring
  have h1 : α * (k * Y ^ 2) ≤ α * (α * X ^ 2 + 2 * β * X * Y + γ * Y ^ 2) := by
    rw [h]
    have := sq_nonneg (α * X + β * Y)
    have := mul_le_mul_of_nonneg_right hdet (sq_nonneg Y)
    have : α * (k * Y ^ 2) ≤ k * Y ^ 2 := by
      have := mul_nonneg hk (sq_nonneg Y)
      nlinarith
    linarith
  exact le_of_mul_le_mul_left h1 hα

lemma sq_le_of_abs {x y : ℝ} (h1 : x ≤ y) (h2 : -y ≤ x) : x ^ 2 ≤ y ^ 2 := by
  have hy : 0 ≤ y := by linarith
  have := abs_le.mpr ⟨h2, h1⟩
  calc x ^ 2 = |x| ^ 2 := (sq_abs _).symm
    _ ≤ y ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2

lemma P_lower {g n c d : ℝ} (hg2 : g < 2) (hn1 : 1 ≤ n) (hd0 : 0 < d)
    (h1 : (n - 1) * d ≤ g * c) (h2 : g * c ≤ g * d) :
    d * (2 - d) / 4 ≤ d / 2 - (n * d - g * c) ^ 2 / (4 * n) := by
  have hn0 : 0 < n := by linarith
  have e1 : n * d - g * c ≤ d := by linarith
  have e2 : -d ≤ n * d - g * c := by
    have : (1 - g) * d ≤ (n - g) * d := mul_le_mul_of_nonneg_right (by linarith) hd0.le
    have : -d < (1 - g) * d := by nlinarith
    linarith
  have hsq := sq_le_of_abs e1 e2
  have : (n * d - g * c) ^ 2 / (4 * n) ≤ d ^ 2 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 4)
    have h3 : d ^ 2 * 4 ≤ d ^ 2 * (4 * n) := mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg d)
    nlinarith
  have e : d * (2 - d) / 4 = d / 2 - d ^ 2 / 4 := by ring
  linarith

lemma m_bound {g η T d P : ℝ} (hη : 0 < η) (hd0 : 0 < d) (hd1 : d < 1)
    (hTl : η * (1 - d) ^ 2 ≤ T) (hTu : T ≤ η * (2 - (1 - d) ^ 2)) (hP : d * (2 - d) / 4 ≤ P) :
    g ^ 2 * (T - η) ^ 2 / (2 * η) ≤ g ^ 2 * η * (2 * P) := by
  have hq0 : 0 ≤ d * (2 - d) := mul_nonneg hd0.le (by linarith)
  have hq1 : d * (2 - d) ≤ 1 := by nlinarith [sq_nonneg (d - 1)]
  have e1 : T - η ≤ η * (d * (2 - d)) := by nlinarith
  have e2 : -(η * (d * (2 - d))) ≤ T - η := by nlinarith
  have hsq := sq_le_of_abs e1 e2
  have hq : (η * (d * (2 - d))) ^ 2 ≤ η ^ 2 * (d * (2 - d)) := by
    have : (d * (2 - d)) ^ 2 ≤ d * (2 - d) := by nlinarith
    calc (η * (d * (2 - d))) ^ 2 = η ^ 2 * (d * (2 - d)) ^ 2 := by ring
      _ ≤ η ^ 2 * (d * (2 - d)) := mul_le_mul_of_nonneg_left this (sq_nonneg η)
  have h4 : (T - η) ^ 2 ≤ η ^ 2 * (4 * P) := by
    have : η ^ 2 * (d * (2 - d)) ≤ η ^ 2 * (4 * P) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg η)
    linarith
  rw [div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left h4 (sq_nonneg g)
  have e : g ^ 2 * η * (2 * P) * (2 * η) = g ^ 2 * (η ^ 2 * (4 * P)) := by ring
  linarith

lemma kappa_bound {g n c : ℝ} (hg : 0 < g) (hg2 : g < 2) (hn1 : 1 ≤ n) (hng : n ≤ g + 1) (hc0 : 0 ≤ c)
    (hcs : (g + 1) * c < 1) : (n - 1) ^ 2 * c ^ 2 * (g + 2) ^ 2 / (8 * n) < 3 / 8 := by
  have hg1 : 0 < g + 1 := by linarith
  have hn0 : 0 < n := by linarith
  have hc1 : c < 1 / (g + 1) := by rw [lt_div_iff₀ hg1]; linarith
  have ht : (n - 1) ^ 2 / n ≤ g ^ 2 / (g + 1) := by
    rw [div_le_div_iff₀ hn0 hg1]
    have h0 : 0 ≤ n - 1 := by linarith
    have h3 : 0 ≤ (n - 1) * (g + 1 - n) := mul_nonneg h0 (by linarith)
    have h4 : 0 ≤ (g + 1 - n) * (g + n - 1 + g * n) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  have hc2 : c ^ 2 ≤ (1 / (g + 1)) ^ 2 := pow_le_pow_left₀ hc0 hc1.le 2
  have e : (n - 1) ^ 2 * c ^ 2 * (g + 2) ^ 2 / (8 * n)
      = (n - 1) ^ 2 / n * c ^ 2 * ((g + 2) ^ 2 / 8) := by field_simp
  rw [e]
  have h1 : (n - 1) ^ 2 / n * c ^ 2 ≤ g ^ 2 / (g + 1) * (1 / (g + 1)) ^ 2 :=
    mul_le_mul ht hc2 (sq_nonneg c) (by positivity)
  have h1' := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ (g + 2) ^ 2 / 8)
  have h2 : g ^ 2 / (g + 1) * (1 / (g + 1)) ^ 2 * ((g + 2) ^ 2 / 8) < 3 / 8 := by
    have e2 : g ^ 2 / (g + 1) * (1 / (g + 1)) ^ 2 * ((g + 2) ^ 2 / 8)
        = (g * (g + 2)) ^ 2 / (8 * (g + 1) ^ 3) := by field_simp
    rw [e2, div_lt_div_iff₀ (by positivity) (by norm_num)]
    have e3 : g * (g + 2) = (g + 1) ^ 2 - 1 := by ring
    have h5 : 0 < (g + 1) ^ 2 - 1 := by nlinarith
    have h6 : ((g + 1) ^ 2 - 1) ^ 2 < ((g + 1) ^ 2) ^ 2 := by nlinarith
    have h7 : ((g + 1) ^ 2) ^ 2 * 8 < 3 * (8 * (g + 1) ^ 3) := by
      have : ((g + 1) ^ 2) ^ 2 = (g + 1) * (g + 1) ^ 3 := by ring
      rw [this]
      have h9 : 0 < (g + 1) ^ 3 := by positivity
      have h8 : (g + 1) * (g + 1) ^ 3 < 3 * (g + 1) ^ 3 := mul_lt_mul_of_pos_right (by linarith) h9
      linarith
    rw [e3]; linarith
  linarith

/-- **Proposition 6.2.** Coercivity of the pair form with the constant weight
    `W = a_* = 2/(Γ+2)`, below the reference line. -/
theorem lower_coercive {g n s z : ℝ} (hg : 0 < g) (hg2 : g < 2) (hn1 : 1 ≤ n) (hng : n ≤ g + 1)
    (hs0 : 0 < s) (hs1 : s < 1) (hz0 : 1 / (g + 1) ≤ z) (hz1 : z ≤ 1 / n) (X Y : ℝ) :
    dS s z * (2 - dS s z) / 16 * Y ^ 2 ≤ pairW g n s z (2 / (g + 2)) 0 X Y := by
  have hg1 : 0 < g + 1 := by linarith
  have hn0 : 0 < n := by linarith
  have hzpos : 0 < z := lt_of_lt_of_le (by positivity) hz0
  have hnz : n * z ≤ 1 := by rw [le_div_iff₀ hn0] at hz1; linarith
  have hgz : 1 ≤ (g + 1) * z := by rw [div_le_iff₀ hg1] at hz0; linarith
  have hz1' : z ≤ 1 := by nlinarith
  obtain ⟨hTl, hTu⟩ := Tcal_bounds hg hg2 hn1 hng hs0 hs1 hz0 hz1
  have hc : cS g s z = s * (1 - z) / g := rfl
  have hd : dS s z = s * z := rfl
  have hcone1 : (n - 1) * dS s z ≤ g * cS g s z := by
    rw [hc, hd, mul_div_cancel₀ _ hg.ne']; nlinarith
  have hcone2 : g * cS g s z ≤ g * dS s z := by
    rw [hc, hd, mul_div_cancel₀ _ hg.ne']; nlinarith
  have hc0 : 0 ≤ cS g s z := by rw [hc]; apply div_nonneg _ hg.le; nlinarith
  have hd0 : 0 < dS s z := by rw [hd]; positivity
  have hd1 : dS s z < 1 := by rw [hd]; nlinarith
  have hcs : (g + 1) * cS g s z < 1 := by
    have : dS s z + g * cS g s z = s := by rw [hc, hd]; field_simp; ring
    have : cS g s z ≤ dS s z := by nlinarith
    linarith
  have haV : As g s + Vs g s = 1 := by unfold As Vs; field_simp; ring
  have hP : PW g n s z (2 / (g + 2)) 0
      = dS s z / 2 - (n * dS s z - g * cS g s z) ^ 2 / (4 * n) := by
    unfold PW deltaW
    rw [show dS s z + 2 * 0 / (2 / (g + 2)) = dS s z by simp]
    have : As g s * dS s z / 2 + Vs g s * dS s z / 2 = dS s z / 2 := by
      rw [← add_div, ← add_mul, haV, one_mul]
    linarith
  have hm : mW g n s z (2 / (g + 2)) 0 ^ 2
      = g ^ 2 * (Tcal g n s z - 2 / (g + 2) ^ 2) ^ 2 / (2 * (2 / (g + 2) ^ 2)) := by
    unfold mW; field_simp; ring
  have hk : kapW g n s z (2 / (g + 2)) = (n - 1) ^ 2 * cS g s z ^ 2 * (g + 2) ^ 2 / (8 * n) := by
    unfold kapW; field_simp; ring
  have hPlow := P_lower hg2 hn1 hd0 hcone1 hcone2
  rw [← hP] at hPlow
  have hm2 := m_bound (g := g) (by positivity) hd0 hd1 hTl hTu hPlow
  rw [← hm] at hm2
  have hκ := kappa_bound hg hg2 hn1 hng hc0 hcs
  rw [← hk] at hκ
  have hκ0 : 0 ≤ kapW g n s z (2 / (g + 2)) := by unfold kapW; positivity
  have hgη := eta_g_sq g hg hg2
  unfold pairW
  generalize PW g n s z (2 / (g + 2)) 0 = P at *
  generalize mW g n s z (2 / (g + 2)) 0 = m at *
  generalize kapW g n s z (2 / (g + 2)) = κ at *
  generalize dS s z = d at *
  have hPpos : 0 < d * (2 - d) / 4 := by
    have : 0 < 2 - d := by linarith
    positivity
  apply form_lower (by linarith) (by linarith) (by linarith)
  have h1 : (1 - κ - 2 / (g + 2) ^ 2 * g ^ 2) * (2 * P) ≥ (1 / 8) * (2 * P) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have h2 : g ^ 2 * (2 / (g + 2) ^ 2) * (2 * P) = 2 / (g + 2) ^ 2 * g ^ 2 * (2 * P) := by ring
  nlinarith

/-! ### The variable weight (Section 6.2) -/

/-- The variable weight `W = ϖ = a + 4c/3` of (6.9) and its derivative along the profile. -/
def Wv (g s z : ℝ) : ℝ := As g s + 4 / 3 * cS g s z
def W1v (g n s z : ℝ) : ℝ := As g s * dS s z + 4 / 3 * c1S g n s z

/-- The endpoint polynomial `Π_ν` of (1.8). -/
def PiP (n ρ : ℝ) : ℝ :=
  9 * (32 * n - 9 * (n - 1) ^ 2) * (3 * ρ ^ 2 + 4 * ρ - n * (n - 2))
    - ((11 * n - 9) * ρ - 9 * n * (n - 1)) ^ 2

def PiA (n : ℝ) : ℝ := -364 * n ^ 2 + 1548 * n - 324
def PiB (n : ℝ) : ℝ := 198 * (n - 1) ^ 3 - 90 * (n - 1) ^ 2 + 1188 * (n - 1) + 1152
def PiC (n : ℝ) : ℝ := -18 * n * (5 * n - 9) * (5 * n - 1)

lemma PiP_eq (n ρ : ℝ) : PiP n ρ = PiA n * ρ ^ 2 + PiB n * ρ + PiC n := by
  unfold PiP PiA PiB PiC; ring

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- **Proposition 6.3** (interpolation of the energy matrix), in the rescaled variable. -/
theorem var_decomp (g n s z X Y : ℝ) (hg : 0 < g) (hg2' : g < 2) (hn : 0 < n) (hs : 0 < s) (hs1 : s < 1)
    (hz : 0 < z) (hW : Wv g s z ≠ 0) :
    let a := As g s
    let d := dS s z
    let t := n - 1
    let ρ := g * cS g s z / dS s z
    let θ := a / Wv g s z
    let u0 := (2 + 2 * ρ - n) / n
    let u1 := (n + 4 * ρ) / (3 * n)
    let k0 := 9 * t ^ 2 / (32 * n)
    let m0 := ((11 * n - 9) * ρ - 9 * n * t) / (24 * n)
    let p0 := (3 * ρ ^ 2 + 4 * ρ - n * (n - 2)) / (2 * n)
    let m1 := (n + 3) * ρ / (6 * n)
    let p1 := (23 * ρ ^ 2 + (4 * n + 24) * ρ + 6 * n - n ^ 2) / (18 * n)
    pairW g n s z (Wv g s z) (W1v g n s z) X Y
      = (1 - θ) * ((1 - k0) * X ^ 2 + 2 * m0 * X * (d * Y) + p0 * (d * Y) ^ 2)
        + θ * (X ^ 2 + 2 * m1 * X * (d * Y) + p1 * (d * Y) ^ 2)
        + θ * (1 - θ) * (3 * t * X + 4 * n * (u1 - u0) * (d * Y)) ^ 2 / (32 * n)
        + a * d * (2 + g * ((1 - θ) * u0 + θ * u1)) / 2 * Y ^ 2 := by
  intro a d t ρ θ u0 u1 k0 m0 p0 m1 p1
  have hdne : dS s z ≠ 0 := by unfold dS; positivity
  have h3 := hn.ne'
  have h4 := hg.ne'
  have hdrel : dS s z = 1 - (g + 2) * As g s / 2 - g * cS g s z := by
    unfold dS As cS; field_simp; ring
  have hV : Vs g s = 1 - As g s := by unfold Vs As; field_simp; ring
  simp only [a, d, t, ρ, θ, u0, u1, k0, m0, p0, m1, p1]
  unfold pairW kapW mW PW deltaW Tcal W1v c1S
  unfold Wv at hW ⊢
  rw [hV, hdrel]
  rw [hdrel] at hdne
  generalize As g s = A at *
  generalize cS g s z = c at *
  set W := A + 4 / 3 * c with hWdef
  set D := 1 - (g + 2) * A / 2 - g * c with hDdef
  clear_value W D
  have hg4 : g - 4 ≠ 0 := by intro h; linarith
  have hc : c = 3 * (W - A) / 4 := by rw [hWdef]; ring
  subst hc
  have hA : A = (4 * D - 4 + 3 * g * W) / (g - 4) := by
    rw [eq_div_iff hg4, hDdef]; ring
  subst hA
  field_simp
  ring

set_option maxHeartbeats 4000000 in
/-- **Proposition 6.5.** Coercivity of the pair form with the variable weight, given the
    endpoint condition `Π_ν(ρ) ≥ 0` at the local slope ratio `ρ = Γc/d`. -/
theorem var_coercive {g n s z : ℝ} (hg : 0 < g) (hg2 : g < 2) (hn : 2 / 3 < n) (hn5 : n < 5)
    (hs : 0 < s) (hs1 : s < 1) (hz : 0 < z) (hz1 : z ≤ 1)
    (hPi : 0 ≤ PiP n (g * cS g s z / dS s z)) (X Y : ℝ) :
    As g s * dS s z * Y ^ 2 ≤ pairW g n s z (Wv g s z) (W1v g n s z) X Y := by
  have hn0 : 0 < n := by linarith
  have ha : 0 < As g s := by unfold As; apply div_pos <;> linarith
  have hc : 0 ≤ cS g s z := by unfold cS; apply div_nonneg _ hg.le; nlinarith
  have hd : 0 < dS s z := by unfold dS; positivity
  have hWpos : 0 < Wv g s z := by unfold Wv; positivity
  have hD := var_decomp g n s z X Y hg hg2 hn0 hs hs1 hz hWpos.ne'
  simp only at hD
  rw [hD]
  set ρ := g * cS g s z / dS s z with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  set θ := As g s / Wv g s z with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hWpos]; unfold Wv; linarith
  generalize As g s = a at *
  generalize dS s z = d at *
  generalize hρ' : ρ = r at *
  -- the two endpoint matrices
  have hk0 : 0 < 1 - 9 * (n - 1) ^ 2 / (32 * n) := by
    rw [sub_pos, div_lt_one (by positivity)]; nlinarith
  have hdet0 : (((11 * n - 9) * r - 9 * n * (n - 1)) / (24 * n)) ^ 2
      ≤ (1 - 9 * (n - 1) ^ 2 / (32 * n)) * ((3 * r ^ 2 + 4 * r - n * (n - 2)) / (2 * n)) := by
    have e : (1 - 9 * (n - 1) ^ 2 / (32 * n)) * ((3 * r ^ 2 + 4 * r - n * (n - 2)) / (2 * n))
        - (((11 * n - 9) * r - 9 * n * (n - 1)) / (24 * n)) ^ 2 = PiP n r / (576 * n ^ 2) := by
      unfold PiP; field_simp; ring
    have : 0 ≤ PiP n r / (576 * n ^ 2) := by positivity
    linarith
  have hp0 : 0 ≤ (3 * r ^ 2 + 4 * r - n * (n - 2)) / (2 * n) := by
    by_contra hneg; push Not at hneg
    have := mul_neg_of_pos_of_neg hk0 hneg
    nlinarith [sq_nonneg (((11 * n - 9) * r - 9 * n * (n - 1)) / (24 * n))]
  have hdet1 : ((n + 3) * r / (6 * n)) ^ 2
      ≤ 1 * ((23 * r ^ 2 + (4 * n + 24) * r + 6 * n - n ^ 2) / (18 * n)) := by
    have e : 1 * ((23 * r ^ 2 + (4 * n + 24) * r + 6 * n - n ^ 2) / (18 * n))
        - ((n + 3) * r / (6 * n)) ^ 2
        = (2 * n ^ 2 * (6 - n) + 8 * n * (n + 6) * r + (40 * n - n ^ 2 - 9) * r ^ 2) / (36 * n ^ 2) := by
      field_simp; ring
    have h1 : 0 ≤ 2 * n ^ 2 * (6 - n) := by
      have : 0 ≤ 6 - n := by linarith
      positivity
    have h2 : 0 ≤ 8 * n * (n + 6) * r := by positivity
    have h3 : 0 ≤ (40 * n - n ^ 2 - 9) * r ^ 2 := by
      apply mul_nonneg _ (sq_nonneg r); nlinarith
    have : 0 ≤ (2 * n ^ 2 * (6 - n) + 8 * n * (n + 6) * r + (40 * n - n ^ 2 - 9) * r ^ 2)
        / (36 * n ^ 2) := by positivity
    linarith
  have hp1 : 0 ≤ (23 * r ^ 2 + (4 * n + 24) * r + 6 * n - n ^ 2) / (18 * n) := by
    have := sq_nonneg ((n + 3) * r / (6 * n))
    linarith
  have E0 := form_nonneg (X := X) (Z := d * Y) hk0.le hp0 hdet0
  have E1 := form_nonneg (X := X) (Z := d * Y) zero_le_one hp1 hdet1
  -- positivity of the interpolated rate
  have hu0 : 0 ≤ (2 + 2 * r - n) / n := by
    have e : (3 * r ^ 2 + 4 * r - n * (n - 2)) / (2 * n)
        = (1 + r) * ((2 + 2 * r - n) / n) - (n * ((2 + 2 * r - n) / n) - r) ^ 2 / (2 * n) := by
      field_simp; ring
    by_contra hneg; push Not at hneg
    have h1 : (1 + r) * ((2 + 2 * r - n) / n) < 0 := mul_neg_of_pos_of_neg (by linarith) hneg
    have h2 : 0 ≤ (n * ((2 + 2 * r - n) / n) - r) ^ 2 / (2 * n) := by positivity
    linarith
  have hu1 : 0 ≤ (n + 4 * r) / (3 * n) := by positivity
  have hups : 0 ≤ (1 - θ) * ((2 + 2 * r - n) / n) + θ * ((n + 4 * r) / (3 * n)) := by
    have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - θ) hu0
    have := mul_nonneg hθ0 hu1
    linarith
  have T1 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - θ) E0
  have T2 := mul_nonneg hθ0 E1
  have T3 : 0 ≤ θ * (1 - θ) * (3 * (n - 1) * X + 4 * n * ((n + 4 * r) / (3 * n)
      - (2 + 2 * r - n) / n) * (d * Y)) ^ 2 / (32 * n) := by
    apply div_nonneg _ (by positivity)
    exact mul_nonneg (mul_nonneg hθ0 (by linarith)) (sq_nonneg _)
  have T4 : a * d * Y ^ 2 ≤ a * d * (2 + g * ((1 - θ) * ((2 + 2 * r - n) / n)
      + θ * ((n + 4 * r) / (3 * n)))) / 2 * Y ^ 2 := by
    have : 0 ≤ g * ((1 - θ) * ((2 + 2 * r - n) / n) + θ * ((n + 4 * r) / (3 * n))) :=
      mul_nonneg hg.le hups
    have had : 0 ≤ a * d * Y ^ 2 := by positivity
    nlinarith
  linarith

end

end StrongShock
