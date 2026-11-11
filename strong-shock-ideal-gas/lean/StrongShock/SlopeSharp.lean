/-
  Lemma 2.2, refined: the sharp slope bounds above the reference line and below `ν = 1`,
  the downstream slope relation, and the upstream limit of the slope.
-/
import StrongShock.Profile
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Filter Topology Set

namespace StrongShock

noncomputable section

namespace SZTraj
variable {g n : ℝ}

/-- The downstream slope is the positive root of `f₀`. -/
lemma zlim_root (hg : 0 < g) (hn : 0 < n) (T : SZTraj g n) {L : ℝ}
    (hzL : Tendsto T.z atTop (𝓝 L)) (hs0 : Tendsto T.s atTop (𝓝 0)) : f0 g n L = 0 := by
  have hcont : Tendsto (fun y => fZ g n (T.s y) (T.z y)) atTop (𝓝 (fZ g n 0 L)) := by
    have hc : Continuous (fun p : ℝ × ℝ => fZ g n p.1 p.2) := by
      unfold fZ f0 f1; fun_prop
    exact (hc.tendsto (0, L)).comp (hs0.prodMk_nhds hzL)
  have := deriv_limit_zero T.hz hzL hcont
  simpa [fZ] using this

/-- The downstream slope relation (6.7): `ρ_r = (1-r)/r` solves
    `ρ² + (2ν/Γ - (ν-1))ρ - 2ν = 0`. -/
lemma rho_root (hg : 0 < g) (hn : 0 < n) {L : ℝ} (hL : 0 < L) (h0 : f0 g n L = 0) :
    ((1 - L) / L) ^ 2 + (2 * n / g - (n - 1)) * ((1 - L) / L) - 2 * n = 0 := by
  have hg2 : g + 2 ≠ 0 := by linarith
  have e : ((1 - L) / L) ^ 2 + (2 * n / g - (n - 1)) * ((1 - L) / L) - 2 * n
      = -(n * (g + 2) / g) * f0 g n L / L ^ 2 := by
    unfold f0; field_simp; ring
  rw [e, h0]; simp

/-- Barrier used for the sharp bounds: if `L < b` and `fZ(s,b) > 0`, then `z ≤ b`. -/
lemma le_of_barrier (T : SZTraj g n) {L : ℝ} (hzL : Tendsto T.z atTop (𝓝 L)) {b : ℝ}
    (hb : L < b) (hf : ∀ y, 0 < fZ g n (T.s y) b) (x : ℝ) : T.z x ≤ b := by
  by_contra hx; push Not at hx
  have := stays_above T.hz (b := b) (x0 := x) hx.le (fun y hy => by rw [hy]; exact hf y)
  have hge : b ≤ L := ge_of_tendsto hzL (eventually_atTop.mpr ⟨x, this⟩)
  linarith

lemma ge_of_barrier (T : SZTraj g n) {L : ℝ} (hzL : Tendsto T.z atTop (𝓝 L)) {b : ℝ}
    (hb : b < L) (hf : ∀ y, fZ g n (T.s y) b < 0) (x : ℝ) : b ≤ T.z x := by
  by_contra hx; push Not at hx
  have := stays_below T.hz (b := b) (x0 := x) hx.le (fun y hy => by rw [hy]; exact hf y)
  have hle : L ≤ b := le_of_tendsto hzL (eventually_atTop.mpr ⟨x, this⟩)
  linarith

/-- **Lemma 2.2, above the reference line**: `1/ν < r < 1/(Γ+1)` and `1/ν ≤ z ≤ r`. -/
theorem sharp_above (hg : 0 < g) (hn : 0 < n) (hgn : g + 1 < n) (T : SZTraj g n) {L : ℝ}
    (hL : 0 < L) (hzL : Tendsto T.z atTop (𝓝 L)) (hs0 : Tendsto T.s atTop (𝓝 0)) :
    1 / n < L ∧ L < 1 / (g + 1) ∧ ∀ x, 1 / n ≤ T.z x ∧ T.z x ≤ L := by
  have hroot := zlim_root hg hn T hzL hs0
  have z0pos : 0 < 1 / (g + 1) := by positivity
  have z1pos : 0 < 1 / n := by positivity
  have hz0 : 0 < f0 g n (1 / (g + 1)) := by
    rw [f0_at_z0 g n hg hn]; apply div_pos _ (by positivity)
    have : 0 < n - g - 1 := by linarith
    positivity
  have hz1 : f0 g n (1 / n) < 0 := by
    rw [f0_at_z1 g n hg hn]; apply div_neg_of_neg_of_pos (by linarith) (by positivity)
  have hL0 : L < 1 / (g + 1) := (f0_sign hg hn hL hroot z0pos).1.1 hz0
  have hL1 : 1 / n < L := (f0_sign hg hn hL hroot z1pos).2.1 hz1
  refine ⟨hL1, hL0, fun x => ⟨?_, ?_⟩⟩
  · have := slope_interval hg hn T hL hzL hs0 x
    have h1 : 1 / n ≤ 1 / (g + 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
    have := this.1; rwa [min_eq_right h1] at this
  · by_contra hx; push Not at hx
    have hup := (slope_interval hg hn T hL hzL hs0 x).2
    have h1 : 1 / n ≤ 1 / (g + 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
    rw [max_eq_left h1] at hup
    set b := (L + T.z x) / 2
    have hb1 : L < b := by simp only [b]; linarith
    have hb2 : b < T.z x := by simp only [b]; linarith
    have hb3 : b < 1 := by
      have : 1 / (g + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
      linarith
    have := le_of_barrier T hzL hb1 (fun y => by
      have hf0 : 0 < f0 g n b := (f0_sign hg hn hL hroot (by linarith)).1.2 hb1
      have hf1 : 0 < f1 n b := by unfold f1; nlinarith
      unfold fZ
      have := T.s_pos y; have := T.s_lt y
      nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - T.s y) hf0, mul_pos (T.s_pos y) hf1]) x
    linarith

lemma f0_one (g n : ℝ) (hg : 0 < g) : f0 g n 1 = 2 * g / (g + 2) := by
  unfold f0
  have : g + 2 ≠ 0 := by linarith
  field_simp; ring

/-- **Lemma 2.2, below `ν = 1`**: `r < 1` and `r ≤ z ≤ 1`. -/
theorem sharp_below (hg : 0 < g) (hn : 0 < n) (hn1 : n < 1) (T : SZTraj g n) {L : ℝ}
    (hL : 0 < L) (hzL : Tendsto T.z atTop (𝓝 L)) (hs0 : Tendsto T.s atTop (𝓝 0)) :
    L < 1 ∧ ∀ x, L ≤ T.z x ∧ T.z x ≤ 1 := by
  have hroot := zlim_root hg hn T hzL hs0
  have hf01 : 0 < f0 g n 1 := by rw [f0_one g n hg]; positivity
  have hL1 : L < 1 := (f0_sign hg hn hL hroot one_pos).1.1 hf01
  have hn' : 1 < 1 / n := by rw [lt_div_iff₀ hn]; linarith
  refine ⟨hL1, fun x => ⟨?_, ?_⟩⟩
  · by_contra hx; push Not at hx
    have hzpos : 0 < T.z x := by
      have := (slope_interval hg hn T hL hzL hs0 x).1
      exact lt_of_lt_of_le (lt_min (by positivity) (by positivity)) this
    set b := (T.z x + L) / 2
    have hb1 : b < L := by simp only [b]; linarith
    have hb2 : T.z x < b := by simp only [b]; linarith
    have := ge_of_barrier T hzL hb1 (fun y => by
      have hf0 : f0 g n b < 0 := (f0_sign hg hn hL hroot (by linarith)).2.2 hb1
      have hf1 : f1 n b < 0 := by unfold f1; nlinarith
      unfold fZ
      have := T.s_pos y; have := T.s_lt y
      nlinarith [mul_neg_of_pos_of_neg (by linarith : (0:ℝ) < 1 - T.s y) hf0,
        mul_neg_of_pos_of_neg (T.s_pos y) hf1]) x
    linarith
  · exact le_of_barrier T hzL hL1 (fun y => by
      unfold fZ
      have hf1 : f1 n 1 = 0 := by unfold f1; ring
      rw [hf1]
      have := T.s_lt y
      nlinarith [mul_pos (by linarith : (0:ℝ) < 1 - T.s y) hf01]) x

/-- Strictly below `ν = 1`, the slope stays strictly below one. -/
lemma z_lt_one (hg : 0 < g) (hn : 0 < n) (T : SZTraj g n) (hle : ∀ x, T.z x ≤ 1) (x : ℝ) :
    T.z x < 1 := by
  rcases (hle x).lt_or_eq with h | h
  · exact h
  · exfalso
    have hmax : IsLocalMax T.z x := Filter.Eventually.of_forall (fun y => by rw [h]; exact hle y)
    have h0 := hmax.hasDerivAt_eq_zero (T.hz x)
    rw [h] at h0
    unfold fZ at h0
    have hf1 : f1 n 1 = 0 := by unfold f1; ring
    rw [hf1, f0_one g n hg] at h0
    have := T.s_lt x
    have : 0 < (1 - T.s x) * (2 * g / (g + 2)) := mul_pos (by linarith) (by positivity)
    linarith

/-! ### The upstream limit of the slope -/

/-- A function bounded above by `m` whose derivative is uniformly negative whenever it sits
    `ε` below `m`, far upstream, tends to `m` as `x → -∞`. -/
lemma tendsto_bot_of_push {z z' : ℝ → ℝ} (hz : ∀ x, HasDerivAt z (z' x) x) {m : ℝ}
    (hle : ∀ x, z x ≤ m)
    (hpush : ∀ ε > 0, ∃ X δ, 0 < δ ∧ ∀ x ≤ X, z x ≤ m - ε → z' x ≤ -δ) :
    Tendsto z atBot (𝓝 m) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => Eventually.of_forall (fun x => lt_of_le_of_lt (hle x) hb)⟩
  set ε := m - a with hεdef
  have hε : 0 < ε := by linarith
  obtain ⟨X, δ, hδ, hX⟩ := hpush (ε / 2) (by linarith)
  -- some point upstream of X lies above m - ε/2
  have hex : ∃ x1 ≤ X, m - ε / 2 < z x1 := by
    by_contra hno; push Not at hno
    set x := X - (|m - z X| + 1) / δ with hxdef
    have hxX : x < X := by
      have : 0 < (|m - z X| + 1) / δ := by positivity
      linarith
    obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope z z' hxX
      (fun y _ => (hz y).continuousAt.continuousWithinAt) (fun y _ => hz y)
    have hzc : z' c ≤ -δ := hX c (by linarith [hc.2]) (hno c (by linarith [hc.2]))
    rw [hc'] at hzc
    have hpos : 0 < X - x := by linarith
    rw [div_le_iff₀ hpos] at hzc
    have : X - x = (|m - z X| + 1) / δ := by rw [hxdef]; ring
    rw [this] at hzc
    have e : -δ * ((|m - z X| + 1) / δ) = -(|m - z X| + 1) := by field_simp
    rw [e] at hzc
    have := hle x
    have := le_abs_self (m - z X)
    linarith
  obtain ⟨x1, hx1X, hx1⟩ := hex
  rw [eventually_atBot]
  refine ⟨x1, fun x hx => ?_⟩
  have hzx : m - ε / 2 < z x := by
    rcases hx.lt_or_eq with hlt | heq
    · by_contra hc; push Not at hc
      have hbar := image_le_of_deriv_right_lt_deriv_boundary (f := z) (f' := z') (a := x) (b := x1)
        (fun y _ => (hz y).continuousAt.continuousWithinAt) (fun y _ => (hz y).hasDerivWithinAt)
        (B := fun _ => m - ε / 2) (B' := fun _ => 0) hc (fun y => hasDerivAt_const y _)
        (fun y hy hyB => by
          have := hX y (by linarith [hy.2]) (by rw [hyB])
          linarith)
      have := hbar ⟨hlt.le, le_refl x1⟩
      linarith
    · rw [heq]; exact hx1
  linarith

/-- Below `ν = 1` the slope tends to `1` upstream. -/
theorem z_bot_below (hg : 0 < g) (hn : 0 < n) (hn1 : n < 1) (T : SZTraj g n) {L : ℝ}
    (hL : 0 < L) (hzL : Tendsto T.z atTop (𝓝 L)) (hs0 : Tendsto T.s atTop (𝓝 0))
    (hs1 : Tendsto T.s atBot (𝓝 1)) : Tendsto T.z atBot (𝓝 1) := by
  obtain ⟨hL1, hz⟩ := sharp_below hg hn hn1 T hL hzL hs0
  have hroot := zlim_root hg hn T hzL hs0
  apply tendsto_bot_of_push T.hz (fun x => (hz x).2)
  intro ε hε
  set β := (g - 2) / (g + 2) + g / (n * (g + 2))
  set K := 1 + |β| with hK
  have hKpos : 0 < K := by positivity
  have hf0le : ∀ y, 0 ≤ y → y ≤ 1 → f0 g n y ≤ K := by
    intro y hy0 hy1
    unfold f0
    have h1 : 0 ≤ g / (n * (g + 2)) := by positivity
    have h2 : β * y ≤ |β| := by
      calc β * y ≤ |β * y| := le_abs_self _
        _ = |β| * |y| := abs_mul _ _
        _ ≤ |β| * 1 := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); rw [abs_le]; constructor <;> linarith
        _ = |β| := mul_one _
    have : y ^ 2 ≤ 1 := by nlinarith
    simp only [β] at h2
    linarith
  set η := min (1 / 2) (ε ^ 2 / (4 * K)) with hη
  have hηpos : 0 < η := lt_min (by norm_num) (by positivity)
  have ev : ∀ᶠ x in atBot, 1 - η < T.s x := hs1.eventually (lt_mem_nhds (by linarith))
  obtain ⟨X, hX⟩ := eventually_atBot.mp ev
  refine ⟨X, ε ^ 2 / 4, by positivity, fun x hx hzx => ?_⟩
  have hsx := hX x hx
  have hs1' := T.s_lt x
  have hzx0 : L ≤ T.z x := (hz x).1
  have hf0 := hf0le (T.z x) (by linarith) (hz x).2
  have hf1 : f1 n (T.z x) ≤ -ε ^ 2 := by
    unfold f1
    have h1 : ε ≤ 1 - T.z x := by linarith
    have hn' : 1 < 1 / n := by rw [lt_div_iff₀ hn]; linarith
    have h2 : ε ≤ 1 / n - T.z x := by linarith
    have : ε * ε ≤ (1 - T.z x) * (1 / n - T.z x) := mul_le_mul h1 h2 hε.le (by linarith)
    nlinarith
  have hη1 : η ≤ 1 / 2 := min_le_left _ _
  have hη2 : η ≤ ε ^ 2 / (4 * K) := min_le_right _ _
  have h1s : (1 - T.s x) * f0 g n (T.z x) ≤ ε ^ 2 / 4 := by
    have h3 : (1 - T.s x) * f0 g n (T.z x) ≤ η * K := by
      rcases le_total 0 (f0 g n (T.z x)) with h | h
      · exact mul_le_mul (by linarith) hf0 h hηpos.le
      · have := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ 1 - T.s x) h
        have := mul_pos hηpos hKpos
        linarith
    have h4 : η * K ≤ ε ^ 2 / 4 := by
      calc η * K ≤ ε ^ 2 / (4 * K) * K := mul_le_mul_of_nonneg_right hη2 hKpos.le
        _ = ε ^ 2 / 4 := by field_simp
    linarith
  have h2s : T.s x * f1 n (T.z x) ≤ -(ε ^ 2 / 2) := by
    have : 1 / 2 ≤ T.s x := by linarith
    have := mul_le_mul_of_nonneg_left hf1 (T.s_pos x).le
    nlinarith [sq_nonneg ε]
  show fZ g n (T.s x) (T.z x) ≤ -(ε ^ 2 / 4)
  unfold fZ
  linarith

/-- Above the reference line the slope tends to `1/ν` upstream. -/
theorem z_bot_above (hg : 0 < g) (hn : 0 < n) (hgn : g + 1 < n) (T : SZTraj g n) {L : ℝ}
    (hL : 0 < L) (hzL : Tendsto T.z atTop (𝓝 L)) (hs0 : Tendsto T.s atTop (𝓝 0))
    (hs1 : Tendsto T.s atBot (𝓝 1)) : Tendsto T.z atBot (𝓝 (1 / n)) := by
  obtain ⟨hL1, hL0, hz⟩ := sharp_above hg hn hgn T hL hzL hs0
  have hg1 : 1 / (g + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  -- apply the push lemma to -z
  have hneg : Tendsto (fun x => -T.z x) atBot (𝓝 (-(1 / n))) := by
    apply tendsto_bot_of_push (z' := fun x => -fZ g n (T.s x) (T.z x)) (fun x => (T.hz x).neg)
      (fun x => by show -T.z x ≤ -(1 / n); linarith [(hz x).1])
    intro ε hε
    set β := (g - 2) / (g + 2) + g / (n * (g + 2))
    set K := |β| + g / (n * (g + 2)) + 1 with hK
    have hKpos : 0 < K := by positivity
    have hf0ge : ∀ y, 0 ≤ y → y ≤ 1 → -K ≤ f0 g n y := by
      intro y hy0 hy1
      unfold f0
      have h2 : -|β| ≤ β * y := by
        have : |β * y| ≤ |β| := by
          rw [abs_mul]
          have : |y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
          calc |β| * |y| ≤ |β| * 1 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
            _ = |β| := mul_one _
        linarith [neg_abs_le (β * y)]
      simp only [β] at h2
      nlinarith [sq_nonneg y]
    set κ := g / (g + 1) * ε with hκ
    have hκpos : 0 < κ := by positivity
    set η := min (1 / 2) (κ / (4 * K)) with hη
    have hηpos : 0 < η := lt_min (by norm_num) (by positivity)
    have ev : ∀ᶠ x in atBot, 1 - η < T.s x := hs1.eventually (lt_mem_nhds (by linarith))
    obtain ⟨X, hX⟩ := eventually_atBot.mp ev
    refine ⟨X, κ / 4, by positivity, fun x hx hzx => ?_⟩
    have hsx := hX x hx
    have hs1' := T.s_lt x
    have hzx1 : T.z x ≤ 1 / (g + 1) := le_trans (hz x).2 hL0.le
    have hzx0 : 1 / n ≤ T.z x := (hz x).1
    have hzx' : -T.z x ≤ -(1 / n) - ε := hzx
    have hzge : 1 / n + ε ≤ T.z x := by linarith
    have hf0 := hf0ge (T.z x) (by have : 0 < 1 / n := by positivity
                                  linarith) (by linarith)
    have hf1 : κ ≤ f1 n (T.z x) := by
      unfold f1
      have h1 : g / (g + 1) ≤ 1 - T.z x := by
        have : 1 - 1 / (g + 1) = g / (g + 1) := by field_simp; ring
        linarith
      have h2 : ε ≤ T.z x - 1 / n := by linarith
      have : g / (g + 1) * ε ≤ (1 - T.z x) * (T.z x - 1 / n) :=
        mul_le_mul h1 h2 hε.le (by linarith)
      simp only [hκ]; nlinarith
    have hη1 : η ≤ 1 / 2 := min_le_left _ _
    have hη2 : η ≤ κ / (4 * K) := min_le_right _ _
    have h1s : -(κ / 4) ≤ (1 - T.s x) * f0 g n (T.z x) := by
      have h3 : -(η * K) ≤ (1 - T.s x) * f0 g n (T.z x) := by
        rcases le_total 0 (f0 g n (T.z x)) with h | h
        · have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - T.s x) h
          have := mul_pos hηpos hKpos
          linarith
        · have : (1 - T.s x) * (-f0 g n (T.z x)) ≤ η * K :=
            mul_le_mul (by linarith) (by linarith) (by linarith) hηpos.le
          linarith
      have h4 : η * K ≤ κ / 4 := by
        calc η * K ≤ κ / (4 * K) * K := mul_le_mul_of_nonneg_right hη2 hKpos.le
          _ = κ / 4 := by field_simp
      linarith
    have h2s : κ / 2 ≤ T.s x * f1 n (T.z x) := by
      have : 1 / 2 ≤ T.s x := by linarith
      have := mul_le_mul_of_nonneg_left hf1 (T.s_pos x).le
      nlinarith
    show -fZ g n (T.s x) (T.z x) ≤ -(κ / 4)
    unfold fZ
    linarith
  have := hneg.neg
  simpa using this

/-- `s` decreases along the profile. -/
lemma s_antitone (T : SZTraj g n) (hz : ∀ x, 0 < T.z x) : Antitone T.s := by
  apply antitone_of_hasDerivAt_nonpos T.hs
  intro x
  have := T.s_pos x; have := T.s_lt x; have := hz x
  have : 0 < T.s x * (1 - T.s x) * T.z x := by
    have : 0 < 1 - T.s x := by linarith
    positivity
  show -T.s x * (1 - T.s x) * T.z x ≤ (0:ℝ)
  linarith

/-- Below `ν = 1`, the gap `1 - z` decays upstream no faster than `e^{κx}` for any
    `κ > 1/ν - 1` (proof of Lemma 7.1). -/
theorem one_sub_z_lower (hg : 0 < g) (hn : 0 < n) (hn1 : n < 1) (T : SZTraj g n) {L : ℝ}
    (hL : 0 < L) (hzL : Tendsto T.z atTop (𝓝 L)) (hs0 : Tendsto T.s atTop (𝓝 0))
    (hs1 : Tendsto T.s atBot (𝓝 1)) {κ : ℝ} (hκ : 1 / n - 1 < κ) :
    ∃ X C, 0 < C ∧ ∀ x ≤ X, C * Real.exp (κ * x) ≤ 1 - T.z x := by
  obtain ⟨hL1, hz⟩ := sharp_below hg hn hn1 T hL hzL hs0
  have hroot := zlim_root hg hn T hzL hs0
  have hlt := z_lt_one hg hn T (fun x => (hz x).2)
  have hbot := z_bot_below hg hn hn1 T hL hzL hs0 hs1
  set ε := κ - (1 / n - 1) with hεdef
  have hε : 0 < ε := by linarith
  have ev : ∀ᶠ x in atBot, 1 - ε < T.z x := hbot.eventually (lt_mem_nhds (by linarith))
  obtain ⟨X, hX⟩ := eventually_atBot.mp ev
  -- φ = (1 - z) e^{-κx} is antitone on (-∞, X]
  have hφ : ∀ y, HasDerivAt (fun t => (1 - T.z t) * Real.exp (-(κ * t)))
      ((-fZ g n (T.s y) (T.z y) - κ * (1 - T.z y)) * Real.exp (-(κ * y))) y := by
    intro y
    have h := ((hasDerivAt_const y (1:ℝ)).sub (T.hz y)).mul
      (((hasDerivAt_id y).const_mul κ).neg.exp)
    refine hasDerivAt_of_eq h (fun t => by simp) ?_
    simp; ring
  have hanti : AntitoneOn (fun t => (1 - T.z t) * Real.exp (-(κ * t))) (Iic X) := by
    apply antitoneOn_of_deriv_nonpos (convex_Iic X)
    · exact fun y _ => (hφ y).continuousAt.continuousWithinAt
    · exact fun y _ => (hφ y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Iic] at hy
      rw [(hφ y).deriv]
      apply mul_nonpos_of_nonpos_of_nonneg _ (Real.exp_pos _).le
      have hzy := hX y hy.le
      have hf0 : 0 ≤ f0 g n (T.z y) := by
        rcases ((hz y).1).lt_or_eq with h | h
        · exact ((f0_sign hg hn hL hroot (by linarith [(hz y).1])).1.2 h).le
        · rw [← h, hroot]
      have hsy := T.s_pos y; have hsy1 := T.s_lt y
      have hw : 0 ≤ 1 - T.z y := by linarith [(hz y).2]
      have hn' : 1 < 1 / n := by rw [lt_div_iff₀ hn]; linarith
      have hprod : 0 ≤ (1 - T.z y) * (1 / n - T.z y) := mul_nonneg hw (by linarith [(hz y).2])
      have hf1 : -f1 n (T.z y) = (1 - T.z y) * (1 / n - T.z y) := by unfold f1; ring
      have h1 : -(T.s y * f1 n (T.z y)) ≤ (1 - T.z y) * (1 / n - T.z y) := by
        have : -(T.s y * f1 n (T.z y)) = T.s y * ((1 - T.z y) * (1 / n - T.z y)) := by
          rw [← hf1]; ring
        rw [this]
        nlinarith
      have h2 : (1 - T.z y) * (1 / n - T.z y) ≤ κ * (1 - T.z y) := by
        have : 1 / n - T.z y ≤ κ := by linarith
        nlinarith
      have h3 : 0 ≤ (1 - T.s y) * f0 g n (T.z y) := mul_nonneg (by linarith) hf0
      unfold fZ
      linarith
  have hwX : 0 < 1 - T.z X := by linarith [hlt X]
  refine ⟨X, (1 - T.z X) * Real.exp (-(κ * X)), by positivity, fun x hx => ?_⟩
  have := hanti (show x ∈ Iic X from hx) (show X ∈ Iic X from le_refl X) hx
  simp only at this
  have he : Real.exp (-(κ * x)) * Real.exp (κ * x) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (κ * x) := Real.exp_pos _
  calc (1 - T.z X) * Real.exp (-(κ * X)) * Real.exp (κ * x)
      ≤ (1 - T.z x) * Real.exp (-(κ * x)) * Real.exp (κ * x) :=
        mul_le_mul_of_nonneg_right this hpos.le
    _ = 1 - T.z x := by rw [mul_assoc, he, mul_one]

end SZTraj

end

end StrongShock
