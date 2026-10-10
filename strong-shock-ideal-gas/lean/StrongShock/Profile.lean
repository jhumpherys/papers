/-
  The limiting profile (Section 2): the `(s,z)` system, its relation to the profile
  equations (2.3), derivatives of the energy coefficients along the profile, and the
  invariant slope interval (Lemma 2.2).
-/
import StrongShock.EnergyIdentity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Topology Set

namespace StrongShock

noncomputable section

/-- Transport a derivative statement along a pointwise equality of functions and an
    equality of derivative values. -/
lemma hasDerivAt_of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {f' g' : E} {x : ℝ} (h : HasDerivAt g g' x) (hf : ∀ y, f y = g y)
    (hd : f' = g') : HasDerivAt f f' x := by
  rw [show f = g from funext hf, hd]; exact h

/-- A limiting profile in the sense of Section 2: a solution of (2.3) with `e_- = 0`,
    taking values strictly between the endstates, with the endstate limits, and whose
    normalized slope `z = -V'/(a s)` has a positive limit downstream (this is the
    exponential convergence along the downstream stable direction, [HLZ, §2.5]). -/
structure LimitingProfile (g n : ℝ) where
  V : ℝ → ℝ
  e : ℝ → ℝ
  hV : ∀ x, HasDerivAt V (V x * (V x - 1) + g * e x) x
  he : ∀ x, HasDerivAt e (V x / n * (e x - (V x - 1) ^ 2 / 2)) x
  V_gt : ∀ x, vstar g < V x
  V_lt : ∀ x, V x < 1
  V_bot : Tendsto V atBot (𝓝 1)
  e_bot : Tendsto e atBot (𝓝 0)
  V_top : Tendsto V atTop (𝓝 (vstar g))
  e_top : Tendsto e atTop (𝓝 (astar g ^ 2 / 2))
  zlim : ℝ
  zlim_pos : 0 < zlim
  z_top : Tendsto (fun x => (V x * (1 - V x) - g * e x) / ((1 - V x) * (((g + 2) * V x - g) / 2)))
    atTop (𝓝 zlim)

/-- A trajectory of the `(s,z)` system with `0 < s < 1`. -/
structure SZTraj (g n : ℝ) where
  s : ℝ → ℝ
  z : ℝ → ℝ
  hs : ∀ x, HasDerivAt s (fS (s x) (z x)) x
  hz : ∀ x, HasDerivAt z (fZ g n (s x) (z x)) x
  s_pos : ∀ x, 0 < s x
  s_lt : ∀ x, s x < 1

namespace LimitingProfile
variable {g n : ℝ} (P : LimitingProfile g n)

def s (x : ℝ) : ℝ := ((g + 2) * P.V x - g) / 2
def z (x : ℝ) : ℝ := (P.V x * (1 - P.V x) - g * P.e x) / ((1 - P.V x) * P.s x)

lemma s_pos (hg : 0 < g) (x : ℝ) : 0 < P.s x := by
  have := P.V_gt x; unfold vstar at this; unfold s
  rw [div_lt_iff₀ (by linarith)] at this; linarith
lemma s_lt (hg : 0 < g) (x : ℝ) : P.s x < 1 := by
  have := P.V_lt x; unfold s
  have : (g + 2) * (P.V x - 1) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
  linarith

/-- `V` and `e` are recovered from `(s,z)` (the reconstruction in Lemma 2.2). -/
lemma V_eq (hg : 0 < g) (x : ℝ) : P.V x = Vs g (P.s x) := by
  unfold Vs s; (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]); field_simp; (try ring)
lemma e_eq (hg : 0 < g) (x : ℝ) : P.e x = eS g (P.s x) (P.z x) := by
  have h1 : 1 - P.V x ≠ 0 := by linarith [P.V_lt x]
  have h2 : P.s x ≠ 0 := (P.s_pos hg x).ne'
  have hVs : Vs g (P.s x) = P.V x := (P.V_eq hg x).symm
  have hAs : As g (P.s x) = 1 - P.V x := by unfold As s; (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]); field_simp; (try ring)
  have hsz : P.s x * P.z x = (P.V x * (1 - P.V x) - g * P.e x) / (1 - P.V x) := by
    unfold z; field_simp
  unfold eS
  rw [hVs, hAs, hsz]
  field_simp
  ring

/-- Eliminating `e` (proof of Lemma 2.2): the profile gives a trajectory of the
    `(s,z)` system. -/
def toSZ (hg : 0 < g) (hn : 0 < n) : SZTraj g n where
  s := P.s
  z := P.z
  hs := fun x => by
    have h := ((P.hV x).const_mul (g + 2)).sub_const g |>.div_const 2
    refine hasDerivAt_of_eq h (fun y => by simp [s]) ?_
    · have h1 : 1 - P.V x ≠ 0 := by linarith [P.V_lt x]
      have h2 : (g + 2) * P.V x - g ≠ 0 := by
        have := P.s_pos hg x; unfold s at this; linarith
      unfold fS z s
      field_simp
      ring
  hz := fun x => by
    have hVx := P.hV x
    have hex := P.he x
    have h1 : 1 - P.V x ≠ 0 := by linarith [P.V_lt x]
    have h2 : (g + 2) * P.V x - g ≠ 0 := by
      have := P.s_pos hg x; unfold s at this; linarith
    have hden : (1 - P.V x) * (((g + 2) * P.V x - g) / 2) ≠ 0 := by
      apply mul_ne_zero h1; exact div_ne_zero h2 two_ne_zero
    have hnum := (hVx.mul ((hasDerivAt_const x (1:ℝ)).sub hVx)).sub (hex.const_mul g)
    have hD := ((hasDerivAt_const x (1:ℝ)).sub hVx).mul
      (((hVx.const_mul (g + 2)).sub_const g).div_const 2)
    have hq := HasDerivAt.div hnum hD hden
    refine hasDerivAt_of_eq hq (fun y => by simp only [z, s, Pi.sub_apply, Pi.mul_apply, Pi.div_apply]) ?_
    have hn' : n ≠ 0 := hn.ne'
    have hg2 : g + 2 ≠ 0 := by linarith
    (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply])
    unfold fZ f0 f1 z s
    field_simp
    ring
  s_pos := P.s_pos hg
  s_lt := P.s_lt hg

lemma s_top (hg : 0 < g) : Tendsto P.s atTop (𝓝 0) := by
  have := ((P.V_top.const_mul (g + 2)).sub_const g).div_const 2
  have e : ((g + 2) * vstar g - g) / 2 = 0 := by unfold vstar; (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]); field_simp; (try ring)
  rw [e] at this
  exact this

end LimitingProfile

/-! ### Derivatives of the coefficients along a trajectory -/

namespace SZTraj
variable {g n : ℝ} (T : SZTraj g n)

section
variable (hg : 0 < g) (hn : 0 < n)
include hg hn

lemma hasDerivAt_V (x : ℝ) :
    HasDerivAt (fun y => Vs g (T.s y)) (V1S g (T.s x) (T.z x)) x := by
  have h := ((T.hs x).const_mul 2).const_add g |>.div_const (g + 2)
  refine hasDerivAt_of_eq h (fun y => by simp [Vs]) ?_
  · have : g + 2 ≠ 0 := by linarith
    unfold V1S As dS fS; (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]); field_simp; (try ring)

lemma hasDerivAt_A (x : ℝ) :
    HasDerivAt (fun y => As g (T.s y)) (As g (T.s x) * dS (T.s x) (T.z x)) x := by
  have h := (((hasDerivAt_const x (1:ℝ)).sub (T.hs x)).const_mul 2).div_const (g + 2)
  refine hasDerivAt_of_eq h (fun y => by simp [As]) ?_
  · have : g + 2 ≠ 0 := by linarith
    unfold As dS fS; (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]); field_simp; (try ring)

lemma hasDerivAt_c (x : ℝ) :
    HasDerivAt (fun y => cS g (T.s y) (T.z y)) (c1S g n (T.s x) (T.z x)) x := by
  have h := ((T.hs x).mul ((hasDerivAt_const x (1:ℝ)).sub (T.hz x))).div_const g
  refine hasDerivAt_of_eq h (fun y => by simp [cS]) ?_
  · have : g + 2 ≠ 0 := by linarith
    have : g ≠ 0 := hg.ne'
    have : n ≠ 0 := hn.ne'
    unfold c1S Vs cS dS As fS fZ f0 f1; (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]); field_simp; (try ring)

lemma hasDerivAt_d (x : ℝ) :
    HasDerivAt (fun y => dS (T.s y) (T.z y)) (d1S g n (T.s x) (T.z x)) x := by
  have h := (T.hs x).mul (T.hz x)
  refine hasDerivAt_of_eq h (fun y => by simp [dS]) ?_
  · have : g + 2 ≠ 0 := by linarith
    have : g ≠ 0 := hg.ne'
    have : n ≠ 0 := hn.ne'
    unfold d1S c1S Vs cS dS As fS fZ f0 f1; (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]); field_simp; (try ring)

lemma hasDerivAt_c1 (x : ℝ) :
    HasDerivAt (fun y => c1S g n (T.s y) (T.z y)) (c2S g n (T.s x) (T.z x)) x := by
  have hV := T.hasDerivAt_V hg hn x
  have hA := T.hasDerivAt_A hg hn x
  have hc := T.hasDerivAt_c hg hn x
  have hd := T.hasDerivAt_d hg hn x
  have h := ((hV.mul hc).div_const n).sub (hd.mul (hA.add hc))
  refine hasDerivAt_of_eq h (fun y => by simp [c1S]) ?_
  · have : g + 2 ≠ 0 := by linarith
    have : g ≠ 0 := hg.ne'
    have : n ≠ 0 := hn.ne'
    unfold c2S c1S_s c1S_z d1S c1S V1S Vs cS dS As fS fZ f0 f1; (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]); field_simp; (try ring)

lemma hasDerivAt_V1 (x : ℝ) :
    HasDerivAt (fun y => V1S g (T.s y) (T.z y)) (V2S g n (T.s x) (T.z x)) x := by
  have hA := T.hasDerivAt_A hg hn x
  have hd := T.hasDerivAt_d hg hn x
  have h := (hA.mul hd).neg
  refine hasDerivAt_of_eq h (fun y => by simp [V1S]) ?_
  · unfold V2S; ring

lemma hasDerivAt_K (x : ℝ) :
    HasDerivAt (fun y => Kc g n (T.s y) (T.z y)) (K1c g n (T.s x) (T.z x)) x := by
  have h := ((T.hasDerivAt_c hg hn x).const_mul (1 - n)).div_const (θ g)
  refine hasDerivAt_of_eq h (fun y => by simp [Kc, mul_div_assoc]) ?_
  · simp [K1c, mul_div_assoc]

lemma As_pos (x : ℝ) : 0 < As g (T.s x) := by
  unfold As; have := T.s_lt x; apply div_pos <;> linarith

lemma Vs_pos (x : ℝ) : 0 < Vs g (T.s x) := by
  unfold Vs; have := T.s_pos x; apply div_pos <;> linarith

/-- `w = √a` satisfies `w' = w d/2`. -/
lemma hasDerivAt_w (x : ℝ) :
    HasDerivAt (fun y => Real.sqrt (As g (T.s y)))
      (Real.sqrt (As g (T.s x)) * dS (T.s x) (T.z x) / 2) x := by
  have hA := T.hasDerivAt_A hg hn x
  have hpos := T.As_pos hg hn x
  have h := hA.sqrt hpos.ne'
  convert h using 1
  have hw : Real.sqrt (As g (T.s x)) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hsq := Real.sq_sqrt hpos.le
  field_simp
  rw [hsq]
  ring

end

/-! ### The invariant slope interval (Lemma 2.2) -/

/-- Barrier: if `z(x₀) ≥ b` and `z' > 0` whenever `z = b`, then `z ≥ b` on `[x₀, ∞)`. -/
lemma stays_above {z z' : ℝ → ℝ} (hz : ∀ x, HasDerivAt z (z' x) x) {b x0 : ℝ}
    (h0 : b ≤ z x0) (hb : ∀ x, z x = b → 0 < z' x) : ∀ x, x0 ≤ x → b ≤ z x := by
  intro x hx
  have := image_le_of_deriv_right_lt_deriv_boundary (f := fun _ => b) (f' := fun _ => 0)
    (a := x0) (b := x) continuousOn_const (fun y _ => hasDerivWithinAt_const y _ b) h0 hz
    (fun y _ hy => hb y hy.symm)
  exact this ⟨hx, le_refl _⟩

lemma stays_below {z z' : ℝ → ℝ} (hz : ∀ x, HasDerivAt z (z' x) x) {b x0 : ℝ}
    (h0 : z x0 ≤ b) (hb : ∀ x, z x = b → z' x < 0) : ∀ x, x0 ≤ x → z x ≤ b := by
  have := stays_above (z := fun x => -z x) (z' := fun x => -z' x) (fun x => (hz x).neg)
    (b := -b) (x0 := x0) (by linarith) (fun x hx => by
      have := hb x (by linarith); linarith)
  intro x hx; have := this x hx; linarith

/-- If `z → L` and `z' = F → m`, then `m = 0`. -/
lemma deriv_limit_zero {z z' : ℝ → ℝ} (hz : ∀ x, HasDerivAt z (z' x) x) {L m : ℝ}
    (hL : Tendsto z atTop (𝓝 L)) (hm : Tendsto z' atTop (𝓝 m)) : m = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · -- eventually z' < m/2 < 0, so z(x+1) - z(x) ≤ m/2
    have ev : ∀ᶠ x in atTop, z' x < m / 2 := hm.eventually (gt_mem_nhds (by linarith))
    obtain ⟨X, hX⟩ := eventually_atTop.mp ev
    have hdiff : Tendsto (fun x => z (x + 1) - z x) atTop (𝓝 (L - L)) :=
      (hL.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)).sub hL
    rw [sub_self] at hdiff
    have ev2 : ∀ᶠ x in atTop, z (x + 1) - z x ≤ m / 2 := by
      filter_upwards [eventually_ge_atTop X] with x hx
      obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope z z' (by linarith : x < x + 1)
        (fun y _ => (hz y).continuousAt.continuousWithinAt) (fun y _ => hz y)
      have : z' c < m / 2 := hX c (by linarith [hc.1])
      rw [hc'] at this; simp at this; linarith
    have := le_of_tendsto hdiff ev2
    linarith
  · have ev : ∀ᶠ x in atTop, m / 2 < z' x := hm.eventually (lt_mem_nhds (by linarith))
    obtain ⟨X, hX⟩ := eventually_atTop.mp ev
    have hdiff : Tendsto (fun x => z (x + 1) - z x) atTop (𝓝 (L - L)) :=
      (hL.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)).sub hL
    rw [sub_self] at hdiff
    have ev2 : ∀ᶠ x in atTop, m / 2 ≤ z (x + 1) - z x := by
      filter_upwards [eventually_ge_atTop X] with x hx
      obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope z z' (by linarith : x < x + 1)
        (fun y _ => (hz y).continuousAt.continuousWithinAt) (fun y _ => hz y)
      have : m / 2 < z' c := hX c (by linarith [hc.1])
      rw [hc'] at this; simp at this; linarith
    have := ge_of_tendsto hdiff ev2
    linarith

/-- Sign structure of `f₀` on the positive axis: `f₀(z) = (z - L)(z + L + β)`. -/
lemma f0_sign {g n L z : ℝ} (hg : 0 < g) (hn : 0 < n) (hL : 0 < L) (hL0 : f0 g n L = 0)
    (hz : 0 < z) : (0 < f0 g n z ↔ L < z) ∧ (f0 g n z < 0 ↔ z < L) := by
  set β := (g - 2) / (g + 2) + g / (n * (g + 2))
  have hc : 0 < g / (n * (g + 2)) := by positivity
  have hfac : f0 g n z = (z - L) * (z + L + β) := by
    have : f0 g n z - f0 g n L = (z - L) * (z + L + β) := by unfold f0; ring
    linarith
  have hLβ : 0 < L + β := by
    have : L * (L + β) = g / (n * (g + 2)) := by
      have := hL0; unfold f0 at this; linarith [this]
    by_contra h; push Not at h; nlinarith
  have hpos : 0 < z + L + β := by linarith
  rw [hfac]
  constructor
  · constructor
    · intro h; by_contra h'; push Not at h'; nlinarith
    · intro h; nlinarith
  · constructor
    · intro h; by_contra h'; push Not at h'; nlinarith
    · intro h; nlinarith

lemma f0_at_z0 (g n : ℝ) (hg : 0 < g) (hn : 0 < n) :
    f0 g n (1 / (g + 1)) = g ^ 2 * (n - g - 1) / (n * (g + 1) ^ 2 * (g + 2)) := by
  unfold f0; (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]); field_simp; (try ring)
lemma f0_at_z1 (g n : ℝ) (hg : 0 < g) (hn : 0 < n) :
    f0 g n (1 / n) = 2 * (g + 1 - n) / (n ^ 2 * (g + 2)) := by
  unfold f0; (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]); field_simp; (try ring)

/-- **Lemma 2.2.** Along a trajectory whose slope tends to a positive limit and whose
    `s` tends to `0` downstream, `z` stays in the slope interval. -/
theorem slope_interval {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (T : SZTraj g n) {L : ℝ}
    (hL : 0 < L) (hzL : Tendsto T.z atTop (𝓝 L)) (hs0 : Tendsto T.s atTop (𝓝 0)) (x : ℝ) :
    InSlope g n (T.z x) := by
  -- the limit is the positive root of f₀
  have hcont : Tendsto (fun y => fZ g n (T.s y) (T.z y)) atTop (𝓝 (fZ g n 0 L)) := by
    have hc : Continuous (fun p : ℝ × ℝ => fZ g n p.1 p.2) := by
      unfold fZ f0 f1; fun_prop
    exact (hc.tendsto (0, L)).comp (hs0.prodMk_nhds hzL)
  have hroot : f0 g n L = 0 := by
    have := deriv_limit_zero T.hz hzL hcont
    simpa [fZ] using this
  have z0pos : 0 < 1 / (g + 1) := by positivity
  have z1pos : 0 < 1 / n := by positivity
  have hfz : ∀ y, fZ g n (T.s y) (T.z y) = fZ g n (T.s y) (T.z y) := fun _ => rfl
  -- generic upper / lower barrier statements
  have upper : ∀ b, L < b → (∀ y, 0 < fZ g n (T.s y) b) → T.z x ≤ b := by
    intro b hb hf
    by_contra hx; push Not at hx
    have := stays_above T.hz (b := b) (x0 := x) hx.le (fun y hy => by rw [hy]; exact hf y)
    have hge : b ≤ L := ge_of_tendsto hzL (eventually_atTop.mpr ⟨x, this⟩)
    linarith
  have lower : ∀ b, b < L → (∀ y, fZ g n (T.s y) b < 0) → b ≤ T.z x := by
    intro b hb hf
    by_contra hx; push Not at hx
    have := stays_below T.hz (b := b) (x0 := x) hx.le (fun y hy => by rw [hy]; exact hf y)
    have hle : L ≤ b := le_of_tendsto hzL (eventually_atTop.mpr ⟨x, this⟩)
    linarith
  have sp := T.s_pos; have sl := T.s_lt
  rcases lt_trichotomy n (g + 1) with hlt | heq | hgt
  · -- interval [1/(g+1), 1/n]
    have hz0 : f0 g n (1 / (g + 1)) < 0 := by
      rw [f0_at_z0 g n hg hn]; apply div_neg_of_neg_of_pos
      · have : n - g - 1 < 0 := by linarith
        nlinarith [sq_pos_of_pos hg]
      · positivity
    have hz1 : 0 < f0 g n (1 / n) := by
      rw [f0_at_z1 g n hg hn]; apply div_pos (by linarith) (by positivity)
    have hL0 : 1 / (g + 1) < L := ((f0_sign hg hn hL hroot z0pos).2.1 hz0)
    have hL1 : L < 1 / n := ((f0_sign hg hn hL hroot z1pos).1.1 hz1)
    have h1 : 1 / (g + 1) ≤ 1 / n := one_div_le_one_div_of_le hn (by linarith)
    constructor
    · rw [min_eq_left h1]
      apply lower _ hL0
      intro y
      have hf1 : f1 n (1 / (g + 1)) < 0 := by
        unfold f1
        have : 1 / (g + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
        have : 1 / (g + 1) < 1 / n := one_div_lt_one_div_of_lt hn (by linarith)
        nlinarith
      unfold fZ
      have := sp y; have := sl y
      nlinarith
    · rw [max_eq_right h1]
      apply upper _ hL1
      intro y
      have hf1 : f1 n (1 / n) = 0 := by unfold f1; ring
      unfold fZ; rw [hf1]
      have := sl y
      nlinarith
  · -- the reference line: the interval collapses to {1/(g+1)}
    subst heq
    have hz0 : f0 g (g + 1) (1 / (g + 1)) = 0 := by rw [f0_at_z0 g _ hg hn]; ring
    have hLz : L = 1 / (g + 1) := by
      rcases lt_trichotomy L (1 / (g + 1)) with h | h | h
      · have := (f0_sign hg hn hL hroot z0pos).1.2 h; linarith
      · exact h
      · have := (f0_sign hg hn hL hroot z0pos).2.2 h; linarith
    have hfac : ∀ y b, fZ g (g + 1) (T.s y) b =
        (b - 1 / (g + 1)) * ((1 - T.s y) * (b + g / (g + 2)) + T.s y * (1 - b)) := by
      intro y b
      have hg1 : g + 1 ≠ 0 := by linarith
      have hg2 : g + 2 ≠ 0 := by linarith
      unfold fZ f0 f1; (try simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.div_apply, Pi.neg_apply]); field_simp; (try ring)
    have hz0lt : 1 / (g + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have hgg : 0 < g / (g + 2) := by positivity
    have h1 : min (1 / (g + 1)) (1 / (g + 1)) = 1 / (g + 1) := min_self _
    have h2 : max (1 / (g + 1)) (1 / (g + 1)) = 1 / (g + 1) := max_self _
    have hup : T.z x ≤ 1 / (g + 1) := by
      by_contra hc; push Not at hc
      obtain ⟨b, hbdef⟩ : ∃ b, b = (1 / (g + 1) + min (T.z x) 1) / 2 := ⟨_, rfl⟩
      have hm1 : 1 / (g + 1) < min (T.z x) 1 := lt_min hc hz0lt
      have hb1 : 1 / (g + 1) < b := by linarith
      have hb2 : b < min (T.z x) 1 := by linarith
      have hb3 : b < 1 := lt_of_lt_of_le hb2 (min_le_right _ _)
      have hb4 : b < T.z x := lt_of_lt_of_le hb2 (min_le_left _ _)
      have := upper b (by rw [hLz]; exact hb1) (fun y => by
        rw [hfac]
        have := sp y; have := sl y
        apply mul_pos (by linarith)
        nlinarith)
      linarith
    have hlo : 1 / (g + 1) ≤ T.z x := by
      by_contra hc; push Not at hc
      obtain ⟨b, hbdef⟩ : ∃ b, b = (1 / (g + 1) + max (T.z x) 0) / 2 := ⟨_, rfl⟩
      have hm1 : max (T.z x) 0 < 1 / (g + 1) := max_lt hc z0pos
      have hb1 : b < 1 / (g + 1) := by linarith
      have hb2 : max (T.z x) 0 < b := by linarith
      have hb3 : 0 < b := lt_of_le_of_lt (le_max_right _ _) hb2
      have hb4 : T.z x < b := lt_of_le_of_lt (le_max_left _ _) hb2
      have := lower b (by rw [hLz]; exact hb1) (fun y => by
        rw [hfac]
        have := sp y; have := sl y
        apply mul_neg_of_neg_of_pos (by linarith)
        nlinarith)
      linarith
    constructor
    · rw [h1]; exact hlo
    · rw [h2]; exact hup
  · -- interval [1/n, 1/(g+1)]
    have hz0 : 0 < f0 g n (1 / (g + 1)) := by
      rw [f0_at_z0 g n hg hn]; apply div_pos _ (by positivity)
      have : 0 < n - g - 1 := by linarith
      positivity
    have hz1 : f0 g n (1 / n) < 0 := by
      rw [f0_at_z1 g n hg hn]; apply div_neg_of_neg_of_pos (by linarith) (by positivity)
    have hL0 : L < 1 / (g + 1) := ((f0_sign hg hn hL hroot z0pos).1.1 hz0)
    have hL1 : 1 / n < L := ((f0_sign hg hn hL hroot z1pos).2.1 hz1)
    have h1 : 1 / n ≤ 1 / (g + 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
    constructor
    · rw [min_eq_right h1]
      apply lower _ hL1
      intro y
      have hf1 : f1 n (1 / n) = 0 := by unfold f1; ring
      unfold fZ; rw [hf1]
      have := sl y
      nlinarith
    · rw [max_eq_left h1]
      apply upper _ hL0
      intro y
      have hf1 : 0 < f1 n (1 / (g + 1)) := by
        unfold f1
        have : 1 / (g + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
        have : 1 / n < 1 / (g + 1) := one_div_lt_one_div_of_lt (by linarith) (by linarith)
        nlinarith
      unfold fZ
      have := sp y; have := sl y
      nlinarith

end SZTraj

end

end StrongShock
