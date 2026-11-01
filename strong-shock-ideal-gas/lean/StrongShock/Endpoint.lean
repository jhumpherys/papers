/-
  Lemma 6.4 and the endpoint condition: monotonicity of `Π_ν`, the strip `ν ≤ 9/5`, and the
  equivalence of `Γ ≥ Γ_E(ν)` with `Π_ν(ρ_r) ≥ 0`.
-/
import StrongShock.Coercivity

namespace StrongShock

noncomputable section

lemma PiB_pos {n : ℝ} (hn : 2 / 3 < n) (hn5 : n < 5) : 0 < PiB n := by
  unfold PiB
  set t := n - 1 with ht
  rcases le_total 0 t with h | h
  · have : 0 ≤ t * (1188 - 90 * t) := mul_nonneg h (by linarith)
    have : 0 ≤ 198 * t ^ 3 := by positivity
    nlinarith
  · have h1 : -1 / 3 < t := by linarith
    have : t ^ 2 ≤ 1 / 9 := by nlinarith
    have : -(1 / 27) ≤ t ^ 3 := by nlinarith
    nlinarith

lemma PiP_t (n : ℝ) : PiP n (n - 1) = 2 * n * (144 + 140 * (n - 1)
    + (n - 1) * (4 - (n - 1)) * (109 + 83 * (n - 1))) := by
  unfold PiP; ring

lemma PiP_t_pos {n : ℝ} (hn : 1 < n) (hn5 : n < 5) : 0 < PiP n (n - 1) := by
  rw [PiP_t]
  have h1 : 0 < n - 1 := by linarith
  have h2 : 0 < 4 - (n - 1) := by linarith
  have : 0 ≤ (n - 1) * (4 - (n - 1)) * (109 + 83 * (n - 1)) := by positivity
  have : 0 < n := by linarith
  positivity

/-- On the strip `2/3 < ν ≤ 9/5`, `Π_ν(ρ) ≥ 0` for every `ρ ≥ 0` (Lemma 6.4). -/
lemma PiP_strip {n ρ : ℝ} (hn : 2 / 3 < n) (hn9 : n ≤ 9 / 5) (hρ : 0 ≤ ρ) : 0 ≤ PiP n ρ := by
  rw [PiP_eq]
  have hA : 0 < PiA n := by
    unfold PiA
    have := mul_pos (by linarith : (0:ℝ) < n - 2 / 3) (by linarith : (0:ℝ) < 9 / 5 - n + 1)
    nlinarith
  have hB := PiB_pos hn (by linarith)
  have hC : 0 ≤ PiC n := by
    unfold PiC
    have : 0 ≤ n * (9 - 5 * n) * (5 * n - 1) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith
  have := mul_nonneg hA.le (sq_nonneg ρ)
  have := mul_nonneg hB.le hρ
  linarith

/-- Monotonicity of `Π_ν` on `[0, ν - 1]` (Lemma 6.4). -/
lemma PiP_mono {n x y : ℝ} (hn : 1 < n) (hn5 : n < 5) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy : y ≤ n - 1) : PiP n x ≤ PiP n y := by
  rw [PiP_eq, PiP_eq]
  have e : PiA n * y ^ 2 + PiB n * y + PiC n - (PiA n * x ^ 2 + PiB n * x + PiC n)
      = (y - x) * (PiA n * (x + y) + PiB n) := by ring
  have hB := PiB_pos (by linarith) hn5
  have hslope : 0 ≤ PiA n * (x + y) + PiB n := by
    rcases le_total 0 (PiA n) with hA | hA
    · have := mul_nonneg hA (by linarith : (0:ℝ) ≤ x + y)
      linarith
    · -- the derivative at ρ = ν - 1 is positive
      have hd : 0 < 2 * PiA n * (n - 1) + PiB n := by
        have e2 : 2 * PiA n * (n - 1) + PiB n = 1152 + (n - 1) * (2908 + 1550 * (n - 1)
            - 530 * (n - 1) ^ 2) := by unfold PiA PiB; ring
        rw [e2]
        have h1 : 0 < n - 1 := by linarith
        have h2 : 0 ≤ (n - 1) * (4 - (n - 1)) := mul_nonneg h1.le (by linarith)
        have : 0 < 2908 + 1550 * (n - 1) - 530 * (n - 1) ^ 2 := by nlinarith
        positivity
      have : PiA n * (2 * (n - 1)) ≤ PiA n * (x + y) :=
        mul_le_mul_of_nonpos_left (by linarith) hA
      linarith
  have := mul_nonneg (by linarith : (0:ℝ) ≤ y - x) hslope
  linarith

/-! ### The boundary `Γ_E` -/

/-- The zero `ρ_E` of `Π_ν` in `(0, ν - 1)`, for `9/5 < ν < 5`. -/
def rhoE (n : ℝ) : ℝ :=
  -2 * PiC n / (PiB n + Real.sqrt (PiB n ^ 2 - 4 * PiA n * PiC n))

/-- The map `ρ ↦ Γ` inverting the downstream slope relation (6.7). -/
def Gmap (n ρ : ℝ) : ℝ := 2 * n * ρ / (2 * n + (n - 1) * ρ - ρ ^ 2)

/-- The function `Γ_E` of (1.9). -/
def GammaE (n : ℝ) : ℝ := if n ≤ 9 / 5 then 0 else Gmap n (rhoE n)

/-- The region `ℛ` of (1.10). -/
def InR (g n : ℝ) : Prop := 0 < g ∧ g < 2 ∧ 2 / 3 < n ∧ n < 5 ∧ GammaE n ≤ g

lemma Gmap_den_pos {n ρ : ℝ} (hn : 0 < n) (hρ : 0 ≤ ρ) (hρt : ρ ≤ n - 1) :
    0 < 2 * n + (n - 1) * ρ - ρ ^ 2 := by
  have : 0 ≤ ρ * (n - 1 - ρ) := mul_nonneg hρ (by linarith)
  nlinarith

lemma Gmap_strictMono {n x y : ℝ} (hn : 0 < n) (hx : 0 ≤ x) (hxy : x < y) (hy : y ≤ n - 1) :
    Gmap n x < Gmap n y := by
  unfold Gmap
  have hdx := Gmap_den_pos hn hx (by linarith)
  have hdy := Gmap_den_pos hn (by linarith) hy
  rw [div_lt_div_iff₀ hdx hdy]
  have e : 2 * n * y * (2 * n + (n - 1) * x - x ^ 2) - 2 * n * x * (2 * n + (n - 1) * y - y ^ 2)
      = 2 * n * (y - x) * (2 * n + x * y) := by ring
  have : 0 < 2 * n * (y - x) * (2 * n + x * y) := by
    have : 0 ≤ x * y := mul_nonneg hx (by linarith)
    have : 0 < y - x := by linarith
    positivity
  linarith

/-- Properties of `ρ_E` (Lemma 6.4): it is a zero of `Π_ν` in `(0, ν - 1)`. -/
lemma rhoE_spec {n : ℝ} (hn : 9 / 5 < n) (hn5 : n < 5) :
    0 < rhoE n ∧ rhoE n < n - 1 ∧ PiP n (rhoE n) = 0 := by
  have hB := PiB_pos (by linarith) hn5
  have hC : PiC n < 0 := by
    unfold PiC
    have : 0 < n * (5 * n - 9) * (5 * n - 1) :=
      mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    linarith
  have hPt := PiP_t_pos (by linarith) hn5
  rw [PiP_eq] at hPt
  set A := PiA n
  set B := PiB n
  set C := PiC n
  set t := n - 1 with ht
  have ht0 : 0 < t := by linarith
  set D := B ^ 2 - 4 * A * C with hD
  have hDpos : 0 < D := by
    rcases le_or_gt 0 A with hA | hA
    · have : 0 ≤ -4 * A * C := by nlinarith
      nlinarith [sq_pos_of_pos hB]
    · have e : D = (2 * A * t + B) ^ 2 - 4 * A * (A * t ^ 2 + B * t + C) := by rw [hD]; ring
      rw [e]
      have : 0 < -4 * A * (A * t ^ 2 + B * t + C) := by
        have := mul_pos (by linarith : (0:ℝ) < -A) hPt
        linarith
      nlinarith [sq_nonneg (2 * A * t + B)]
  set q := Real.sqrt D with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = D := Real.sq_sqrt hDpos.le
  have hBq : 0 < B + q := by linarith
  have hr : rhoE n = -2 * C / (B + q) := rfl
  set r := rhoE n
  have hr0 : 0 < r := by rw [hr]; apply div_pos (by linarith) hBq
  have hrel : r * (B + q) = -2 * C := by rw [hr]; field_simp
  have hroot : A * r ^ 2 + B * r + C = 0 := by
    have : (A * r ^ 2 + B * r + C) * (B + q) ^ 2 = C * (4 * A * C - B ^ 2 + q ^ 2) := by
      have e1 : (A * r ^ 2 + B * r + C) * (B + q) ^ 2
          = A * (r * (B + q)) ^ 2 + B * (r * (B + q)) * (B + q) + C * (B + q) ^ 2 := by ring
      rw [e1, hrel]; ring
    rw [hq2, hD] at this
    have h0 : C * (4 * A * C - B ^ 2 + (B ^ 2 - 4 * A * C)) = 0 := by ring
    rw [h0] at this
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exfalso; have := pow_pos hBq 2; linarith
  refine ⟨hr0, ?_, by rw [PiP_eq]; exact hroot⟩
  -- ρ_E < ν - 1
  by_contra hcon; push Not at hcon
  have hfac : A * t ^ 2 + B * t + C = (t - r) * (A * (t + r) + B) := by
    have : C = -(A * r ^ 2 + B * r) := by linarith
    rw [this]; ring
  rcases le_or_gt 0 A with hA | hA
  · have hAr : 0 < A * r + B := by
      have : r * (A * r + B) = -C := by linarith
      by_contra h; push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos hr0.le h
      linarith
    have : 0 < A * (t + r) + B := by nlinarith
    have : (t - r) * (A * (t + r) + B) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) this.le
    linarith
  · have hlin : 2 * A * r + B = q := by
      have h1 : (2 * A * r + B) * (B + q) = q * (B + q) := by
        have : (2 * A * r + B) * (B + q) = 2 * A * (r * (B + q)) + B * (B + q) := by ring
        rw [this, hrel]
        have : q * (B + q) = B * q + q ^ 2 := by ring
        rw [this, hq2, hD]; ring
      exact mul_right_cancel₀ hBq.ne' h1
    have e : (t - r) * (A * (t + r) + B) = (t - r) * (A * (t - r) + q) := by
      rw [← hlin]; ring
    rw [hfac, e] at hPt
    have h1 : 0 ≤ r - t := by linarith
    have : (t - r) * (A * (t - r) + q) = -((r - t) * (-A * (r - t) + q)) := by ring
    rw [this] at hPt
    have : 0 ≤ (r - t) * (-A * (r - t) + q) := by
      apply mul_nonneg h1
      have := mul_nonneg (by linarith : (0:ℝ) ≤ -A) h1
      linarith
    linarith

/-- **The endpoint condition** (6.16): above the reference line, `Γ ≥ Γ_E(ν)` gives
    `Π_ν(ρ_r) ≥ 0`, where `ρ_r` is the downstream slope ratio. -/
theorem endpoint {g n ρr : ℝ} (hg : 0 < g) (hn : 9 / 5 < n) (hn5 : n < 5) (hρ0 : 0 ≤ ρr)
    (hρt : ρr ≤ n - 1) (hroot : ρr ^ 2 + (2 * n / g - (n - 1)) * ρr - 2 * n = 0)
    (hE : GammaE n ≤ g) : 0 ≤ PiP n ρr := by
  have hn0 : 0 < n := by linarith
  obtain ⟨h1, h2, h3⟩ := rhoE_spec hn hn5
  have hGE : GammaE n = Gmap n (rhoE n) := by
    unfold GammaE
    split_ifs with h
    · exact absurd h (by linarith)
    · rfl
  have hg_eq : g = Gmap n ρr := by
    unfold Gmap
    have hden := Gmap_den_pos hn0 hρ0 hρt
    rw [eq_div_iff hden.ne']
    have : g * (ρr ^ 2 + (2 * n / g - (n - 1)) * ρr - 2 * n) = 0 := by rw [hroot]; ring
    have e : g * (ρr ^ 2 + (2 * n / g - (n - 1)) * ρr - 2 * n)
        = -(g * (2 * n + (n - 1) * ρr - ρr ^ 2) - 2 * n * ρr) := by field_simp; ring
    linarith
  have hle : rhoE n ≤ ρr := by
    by_contra hc; push Not at hc
    have := Gmap_strictMono hn0 hρ0 hc h2.le
    rw [← hg_eq, ← hGE] at this
    linarith
  have := PiP_mono (by linarith) hn5 h1.le hle hρt
  linarith

end

end StrongShock
