/-
  Main results: limiting spectral stability on the reference line `ν = Γ + 1` and on the
  explicit transport region 𝒯, and the passage to sufficiently strong finite shocks.
  External inputs from [HLZ] appear as explicit hypotheses (see README).
-/
import StrongShock.Decay
import StrongShock.Bounds
import StrongShock.ZeroFrequency
import StrongShock.Finite

open Filter Topology Set

namespace StrongShock

noncomputable section

namespace LimitingProfile
variable {g n : ℝ} (P : LimitingProfile g n)

lemma s_bot (hg : 0 < g) : Tendsto P.s atBot (𝓝 1) := by
  have := ((P.V_bot.const_mul (g + 2)).sub_const g).div_const 2
  have e : ((g + 2) * 1 - g) / 2 = 1 := by ring
  rw [e] at this; exact this

lemma z_top' : Tendsto P.z atTop (𝓝 P.zlim) := by
  have := P.z_top; unfold z s; exact this

lemma slope (hg : 0 < g) (hn : 0 < n) (x : ℝ) : InSlope g n ((P.toSZ hg hn).z x) :=
  SZTraj.slope_interval hg hn (P.toSZ hg hn) P.zlim_pos P.z_top' (P.s_top hg) x

end LimitingProfile

/-- The trivial-solution conclusion. -/
def Trivial {g n : ℝ} {T : SZTraj g n} {lam : ℂ} (S : EigenSol T lam) : Prop :=
  ∀ x, S.v x = 0 ∧ S.u x = 0 ∧ S.ε x = 0

/-- Nonzero frequencies: coercivity + the slope interval ⇒ no admissible solution. -/
theorem nonzero_core {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (P : LimitingProfile g n)
    {κ : ℝ} (hκ : 0 < κ) (hwin : n < 2 * (g + 1))
    (hcoer : ∀ x p1 p2 q1 q2, κ * (P.toSZ hg hn).s x * (q1 ^ 2 + q2 ^ 2) ≤
      Qform g n ((P.toSZ hg hn).s x) ((P.toSZ hg hn).z x) p1 p2 q1 q2)
    {lam : ℂ} (hlam : lam ≠ 0) (hre : 0 ≤ lam.re) (S : EigenSol (P.toSZ hg hn) lam)
    (hS : Admissible S) : Trivial S := by
  have hz : ∀ x, min (1 / (g + 1)) (1 / n) ≤ (P.toSZ hg hn).z x ∧ (P.toSZ hg hn).z x ≤ max (1 / (g + 1)) (1 / n) :=
    fun x => P.slope hg hn x
  have hzl : 0 ≤ min (1 / (g + 1)) (1 / n) := le_min (by positivity) (by positivity)
  have hw : max (1 / (g + 1)) (1 / n) / 2 < 1 / n := by
    rcases le_total (1 / (g + 1)) (1 / n) with h | h
    · rw [max_eq_right h]; have : 0 < 1 / n := by positivity
      linarith
    · rw [max_eq_left h, div_div, div_lt_div_iff₀ (by positivity) hn]; linarith
  obtain ⟨hbot, htop⟩ := flux_tendsto hg hn (P.toSZ hg hn) hz hzl hw (P.s_top hg) S hS
  exact exclusion hg hn (P.toSZ hg hn) hκ hcoer hlam hre S hbot htop

/-- Zero frequency for any limiting profile (Proposition 9.1). -/
theorem zero_core {g n : ℝ} (hg : 0 < g) (hn : 0 < n) (P : LimitingProfile g n)
    (hvar : VariationalUnique (P.toSZ hg hn)) (S : EigenSol (P.toSZ hg hn) 0)
    (hS : ZeroAdmissible S) : Trivial S := by
  have hzb : ∃ B, ∀ x, |(P.toSZ hg hn).z x| ≤ B := by
    refine ⟨max (1 / (g + 1)) (1 / n), fun x => ?_⟩
    have := P.slope hg hn x
    have hpos : 0 < min (1 / (g + 1)) (1 / n) := lt_min (by positivity) (by positivity)
    rw [abs_of_pos (lt_of_lt_of_le hpos this.1)]; exact this.2
  exact zero_frequency hg hn (P.toSZ hg hn) (P.s_bot hg) (P.s_top hg) hzb hvar S hS

/-! ### Theorem 1.1: the reference line `ν = Γ + 1`, `0 < Γ ≤ 1` -/

theorem thm_line_nonzero {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) (P : LimitingProfile g (g + 1))
    {lam : ℂ} (hlam : lam ≠ 0) (hre : 0 ≤ lam.re)
    (S : EigenSol (P.toSZ hg (by linarith)) lam) (hS : Admissible S) : Trivial S := by
  have hn : 0 < g + 1 := by linarith
  apply nonzero_core hg hn P (κ := 1 / 180) (by norm_num) (by linarith) _ hlam hre S hS
  intro x p1 p2 q1 q2
  have hsl := P.slope hg hn x
  have hz : (P.toSZ hg hn).z x = 1 / (g + 1) := by
    have h1 : min (1 / (g + 1)) (1 / (g + 1)) = 1 / (g + 1) := min_self _
    have h2 : max (1 / (g + 1)) (1 / (g + 1)) = 1 / (g + 1) := max_self _
    have := hsl; unfold InSlope at this; rw [h1, h2] at this
    linarith [this.1, this.2]
  rw [hz]
  have key := line_coercive hg hg1 ((P.toSZ hg hn).s_pos x) ((P.toSZ hg hn).s_lt x).le p1 p2 q1 q2
  have e1 : (1 : ℝ) + g = g + 1 := by ring
  rw [e1] at key
  linarith

theorem thm_line_zero {g : ℝ} (hg : 0 < g) (P : LimitingProfile g (g + 1))
    (hvar : VariationalUnique (P.toSZ hg (by linarith)))
    (S : EigenSol (P.toSZ hg (by linarith)) 0) (hS : ZeroAdmissible S) : Trivial S :=
  zero_core hg _ P hvar S hS

/-! ### Theorem 1.2: the explicit transport region 𝒯 -/

theorem thm_transport_nonzero {g n : ℝ} (hT : InT g n) (P : LimitingProfile g n)
    {lam : ℂ} (hlam : lam ≠ 0) (hre : 0 ≤ lam.re)
    (S : EigenSol (P.toSZ hT.1 (by linarith [hT.2.2.1, hT.1])) lam) (hS : Admissible S) :
    Trivial S := by
  have hg := hT.1
  have hn : 0 < n := by linarith [hT.2.2.1]
  apply nonzero_core hg hn P (κ := 1 / 200) (by norm_num) (by linarith [hT.2.2.2]) _ hlam hre S hS
  intro x p1 p2 q1 q2
  have := strip_coercive hT (P.slope hg hn x) ((P.toSZ hg hn).s_pos x)
    ((P.toSZ hg hn).s_lt x).le p1 p2 q1 q2
  linarith

theorem thm_transport_zero {g n : ℝ} (hT : InT g n) (P : LimitingProfile g n)
    (hvar : VariationalUnique (P.toSZ hT.1 (by linarith [hT.2.2.1, hT.1])))
    (S : EigenSol (P.toSZ hT.1 (by linarith [hT.2.2.1, hT.1])) 0) (hS : ZeroAdmissible S) :
    Trivial S :=
  zero_core hT.1 _ P hvar S hS

/-! ### Finite shocks (Corollary 1.3 and Theorem 1.4)

`D lam (Γ, ν) ς` stands for the integrated Evans function at shock-strength parameter
`ς = v₊ - v_*(Γ)`.  Its existence, joint continuity through `ς = 0` [HLZ, Prop. 3.8], the
uniform high-frequency bound [HLZ, Prop. 4.1], and the characterization of its limiting zeros
by admissible solutions are the inputs from [HLZ]; the limiting nonvanishing is what the
theorems above prove. -/

/-- The parameter band of Corollary 1.3. -/
def bandT (I : Set ℝ) : Set (ℝ × ℝ) := {p | p.1 ∈ I ∧ 1 + p.1 / 2 ≤ p.2 ∧ p.2 ≤ 1 + 3 * p.1 / 2}

lemma isCompact_bandT {I : Set ℝ} (hI : IsCompact I) : IsCompact (bandT I) := by
  have hc : IsCompact (I ×ˢ Icc (sInf ((fun g => 1 + g / 2) '' I))
      (sSup ((fun g => 1 + 3 * g / 2) '' I))) :=
    hI.prod isCompact_Icc
  apply hc.of_isClosed_subset
  · apply IsClosed.inter (hI.isClosed.preimage continuous_fst)
    apply IsClosed.inter
    · exact isClosed_le (f := fun p : ℝ × ℝ => 1 + p.1 / 2) (g := fun p : ℝ × ℝ => p.2)
        (by fun_prop) (by fun_prop)
    · exact isClosed_le (f := fun p : ℝ × ℝ => p.2) (g := fun p : ℝ × ℝ => 1 + 3 * p.1 / 2)
        (by fun_prop) (by fun_prop)
  · rintro ⟨g, n⟩ ⟨hg, h1, h2⟩
    refine ⟨hg, ?_, ?_⟩
    · exact le_trans (csInf_le (hI.image (f := fun g : ℝ => 1 + g / 2) (by fun_prop)).bddBelow
        ⟨g, hg, rfl⟩) h1
    · exact le_trans h2 (le_csSup (hI.image (f := fun g : ℝ => 1 + 3 * g / 2) (by fun_prop)).bddAbove
        ⟨g, hg, rfl⟩)

/-- **Corollary 1.3.**  For a compact `I ⊆ (0, 2/3]` there is a single `δ > 0` such that the
    Evans function does not vanish on the closed right half-plane for every shock in the closed
    band `1 + Γ/2 ≤ ν ≤ 1 + 3Γ/2`, `Γ ∈ I`, with `0 ≤ v₊ - v_* < δ`. -/
theorem cor_transport_finite {I : Set ℝ} (hI : IsCompact I) (D : ℂ → ℝ × ℝ → ℝ → ℂ)
    {Λ ς0 : ℝ} (hς0 : 0 < ς0)
    (hcont : ContinuousOn (fun q : ℂ × (ℝ × ℝ) × ℝ => D q.1 q.2.1 q.2.2)
      (halfDisk Λ ×ˢ bandT I ×ˢ Icc 0 ς0))
    (hhigh : ∀ lam p ς, 0 ≤ lam.re → Λ < ‖lam‖ → p ∈ bandT I → ς ∈ Icc 0 ς0 → D lam p ς ≠ 0)
    (hlim : ∀ lam p, 0 ≤ lam.re → p ∈ bandT I → D lam p 0 ≠ 0) :
    ∃ δ > 0, ∀ lam p ς, 0 ≤ lam.re → p ∈ bandT I → 0 ≤ ς → ς < δ → D lam p ς ≠ 0 := by
  obtain ⟨δ, hδ, h⟩ := finite_shock (isCompact_bandT hI) (isCompact_bandT hI) subset_rfl D hς0
    hcont hhigh (fun lam p hre _ hp => hlim lam p hre hp)
  exact ⟨δ, hδ, fun lam p ς hre hp hς hςδ => h lam p p ς hre hp hp (by simpa using hδ) hς hςδ⟩

/-- **Theorem 1.4.**  Nearby transport parameters and finite shocks: for compact `I ⊆ (0,1]`
    there is `δ > 0` with `D ≠ 0` on the closed right half-plane whenever `Γ ∈ I`,
    `|ν - (Γ+1)| < δ` and `0 ≤ v₊ - v_* < δ`. -/
theorem thm_near_line_finite {I : Set ℝ} (hI : IsCompact I) (r : ℝ) (hr : 0 < r)
    (D : ℂ → ℝ × ℝ → ℝ → ℂ) {Λ ς0 : ℝ} (hς0 : 0 < ς0)
    (hcont : ContinuousOn (fun q : ℂ × (ℝ × ℝ) × ℝ => D q.1 q.2.1 q.2.2)
      (halfDisk Λ ×ˢ {p : ℝ × ℝ | p.1 ∈ I ∧ |p.2 - (p.1 + 1)| ≤ r} ×ˢ Icc 0 ς0))
    (hhigh : ∀ lam p ς, 0 ≤ lam.re → Λ < ‖lam‖ → p ∈ {p : ℝ × ℝ | p.1 ∈ I ∧ |p.2 - (p.1 + 1)| ≤ r} →
      ς ∈ Icc 0 ς0 → D lam p ς ≠ 0)
    (hlim : ∀ lam g, 0 ≤ lam.re → g ∈ I → D lam (g, g + 1) 0 ≠ 0) :
    ∃ δ > 0, ∀ lam g n ς, 0 ≤ lam.re → g ∈ I → |n - (g + 1)| < δ → 0 ≤ ς → ς < δ →
      D lam (g, n) ς ≠ 0 := by
  set K := {p : ℝ × ℝ | p.1 ∈ I ∧ |p.2 - (p.1 + 1)| ≤ r}
  set K0 := (fun g => (g, g + 1)) '' I
  have hK0 : IsCompact K0 := hI.image (by fun_prop)
  have hK : IsCompact K := by
    have hc : IsCompact (I ×ˢ ((fun p : ℝ × ℝ => p.1 + p.2) '' (I ×ˢ Icc (1 - r) (1 + r)))) :=
      hI.prod ((hI.prod isCompact_Icc).image (by fun_prop))
    apply hc.of_isClosed_subset
    · apply IsClosed.inter (hI.isClosed.preimage continuous_fst)
      exact isClosed_le (f := fun p : ℝ × ℝ => |p.2 - (p.1 + 1)|) (g := fun _ => r)
        (by fun_prop) (by fun_prop)
    · rintro ⟨g, n⟩ ⟨hg, hn⟩
      refine ⟨hg, (g, n - g), ⟨hg, ?_, ?_⟩, by simp⟩ <;>
        · have := abs_le.mp hn; simp only at this ⊢; linarith [this.1, this.2]
  have hsub : K0 ⊆ K := by
    rintro _ ⟨g, hg, rfl⟩; exact ⟨hg, by simp; linarith⟩
  obtain ⟨δ, hδ, h⟩ := finite_shock hK hK0 hsub D hς0 hcont hhigh (by
    rintro lam _ hre _ ⟨g, hg, rfl⟩; exact hlim lam g hre hg)
  refine ⟨min δ r, lt_min hδ hr, fun lam g n ς hre hg hn hς hςδ => ?_⟩
  apply h lam (g, n) (g, g + 1) ς hre ⟨hg, (hn.trans_le (min_le_right _ _)).le⟩ ⟨g, hg, rfl⟩
  · rw [Prod.dist_eq]; simp only [dist_self, Real.dist_eq]
    exact max_lt hδ (hn.trans_le (min_le_left _ _))
  · exact hς
  · exact hςδ.trans_le (min_le_left _ _)

/-! ### Linking the limiting theorems to the Evans function

The integrated Evans function vanishes at a limiting parameter exactly when the continued
incoming and outgoing spaces intersect, i.e. when there is a nontrivial admissible solution
[HLZ, Section 3].  We record the direction that is needed as the hypothesis `EvansZeroSolution`,
and deduce the limiting nonvanishing used above from Theorems 1.1 and 1.2. -/

/-- A zero of `D(·, (Γ,ν), 0)` in the closed right half-plane produces a nontrivial admissible
    solution along a limiting profile. -/
def EvansZeroSolution (D : ℂ → ℝ × ℝ → ℝ → ℂ) : Prop :=
  ∀ (lam : ℂ) (g n : ℝ) (hg : 0 < g) (hn : 0 < n), 0 ≤ lam.re → D lam (g, n) 0 = 0 →
    ∃ P : LimitingProfile g n,
      (lam ≠ 0 ∧ ∃ S : EigenSol (P.toSZ hg hn) lam, Admissible S ∧ ¬ Trivial S) ∨
      (lam = 0 ∧ ∃ S : EigenSol (P.toSZ hg hn) 0, ZeroAdmissible S ∧ ¬ Trivial S)

/-- Every limiting profile has the saddle property used at zero frequency. -/
def AllVariationalUnique : Prop :=
  ∀ (g n : ℝ) (hg : 0 < g) (hn : 0 < n) (P : LimitingProfile g n), VariationalUnique (P.toSZ hg hn)

/-- Theorem 1.2 in Evans form: `D_*(λ; Γ, ν) ≠ 0` on the closed right half-plane for `(Γ,ν) ∈ 𝒯`. -/
theorem evans_transport (D : ℂ → ℝ × ℝ → ℝ → ℂ) (hW : EvansZeroSolution D)
    (hV : AllVariationalUnique) {g n : ℝ} (hT : InT g n) {lam : ℂ} (hre : 0 ≤ lam.re) :
    D lam (g, n) 0 ≠ 0 := by
  intro h0
  have hg := hT.1
  have hn : 0 < n := by linarith [hT.2.2.1]
  obtain ⟨P, hP⟩ := hW lam g n hg hn hre h0
  rcases hP with ⟨hlam, S, hS, hnt⟩ | ⟨rfl, S, hS, hnt⟩
  · exact hnt (thm_transport_nonzero hT P hlam hre S hS)
  · exact hnt (thm_transport_zero hT P (hV g n hg hn P) S hS)

/-- Theorem 1.1 in Evans form: `D_*(λ; Γ, Γ+1) ≠ 0` on the closed right half-plane, `0 < Γ ≤ 1`. -/
theorem evans_line (D : ℂ → ℝ × ℝ → ℝ → ℂ) (hW : EvansZeroSolution D)
    (hV : AllVariationalUnique) {g : ℝ} (hg : 0 < g) (hg1 : g ≤ 1) {lam : ℂ} (hre : 0 ≤ lam.re) :
    D lam (g, g + 1) 0 ≠ 0 := by
  intro h0
  have hn : 0 < g + 1 := by linarith
  obtain ⟨P, hP⟩ := hW lam g (g + 1) hg hn hre h0
  rcases hP with ⟨hlam, S, hS, hnt⟩ | ⟨rfl, S, hS, hnt⟩
  · exact hnt (thm_line_nonzero hg hg1 P hlam hre S hS)
  · exact hnt (thm_line_zero hg P (hV g (g + 1) hg hn P) S hS)

/-- **Corollary 1.3, complete form.**  Combining `cor_transport_finite` with Theorem 1.2. -/
theorem cor_transport_finite' {I : Set ℝ} (hI : IsCompact I) (hIsub : I ⊆ Set.Ioc 0 (2 / 3))
    (D : ℂ → ℝ × ℝ → ℝ → ℂ) (hW : EvansZeroSolution D) (hV : AllVariationalUnique)
    {Λ ς0 : ℝ} (hς0 : 0 < ς0)
    (hcont : ContinuousOn (fun q : ℂ × (ℝ × ℝ) × ℝ => D q.1 q.2.1 q.2.2)
      (halfDisk Λ ×ˢ bandT I ×ˢ Icc 0 ς0))
    (hhigh : ∀ lam p ς, 0 ≤ lam.re → Λ < ‖lam‖ → p ∈ bandT I → ς ∈ Icc 0 ς0 → D lam p ς ≠ 0) :
    ∃ δ > 0, ∀ lam p ς, 0 ≤ lam.re → p ∈ bandT I → 0 ≤ ς → ς < δ → D lam p ς ≠ 0 := by
  apply cor_transport_finite hI D hς0 hcont hhigh
  rintro lam ⟨g, n⟩ hre ⟨hg, h1, h2⟩
  have hgI := hIsub hg
  exact evans_transport D hW hV ⟨hgI.1, hgI.2, h1, h2⟩ hre

/-- **Theorem 1.4, complete form.**  Combining `thm_near_line_finite` with Theorem 1.1. -/
theorem thm_near_line_finite' {I : Set ℝ} (hI : IsCompact I) (hIsub : I ⊆ Set.Ioc 0 1)
    (r : ℝ) (hr : 0 < r) (D : ℂ → ℝ × ℝ → ℝ → ℂ) (hW : EvansZeroSolution D)
    (hV : AllVariationalUnique) {Λ ς0 : ℝ} (hς0 : 0 < ς0)
    (hcont : ContinuousOn (fun q : ℂ × (ℝ × ℝ) × ℝ => D q.1 q.2.1 q.2.2)
      (halfDisk Λ ×ˢ {p : ℝ × ℝ | p.1 ∈ I ∧ |p.2 - (p.1 + 1)| ≤ r} ×ˢ Icc 0 ς0))
    (hhigh : ∀ lam p ς, 0 ≤ lam.re → Λ < ‖lam‖ → p ∈ {p : ℝ × ℝ | p.1 ∈ I ∧ |p.2 - (p.1 + 1)| ≤ r} →
      ς ∈ Icc 0 ς0 → D lam p ς ≠ 0) :
    ∃ δ > 0, ∀ lam g n ς, 0 ≤ lam.re → g ∈ I → |n - (g + 1)| < δ → 0 ≤ ς → ς < δ →
      D lam (g, n) ς ≠ 0 :=
  thm_near_line_finite hI r hr D hς0 hcont hhigh
    (fun lam g hre hg => evans_line D hW hV (hIsub hg).1 (hIsub hg).2 hre)

/-! ### Physical interpretation (1.10) and examples -/

/-- Under Stokes' hypothesis `ν = 3(Γ+1)/(4 Pr)`; the explicit region in Prandtl form. -/
theorem prandtl_region {g Pr : ℝ} (hg : 0 < g) (hP : 0 < Pr) :
    (1 + g / 2 ≤ 3 * (g + 1) / (4 * Pr) ∧ 3 * (g + 1) / (4 * Pr) ≤ 1 + 3 * g / 2) ↔
    (3 * (1 + g) / (4 * (1 + 3 * g / 2)) ≤ Pr ∧ Pr ≤ 3 * (1 + g) / (4 * (1 + g / 2))) := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · rw [div_le_iff₀ (by positivity)]; rw [div_le_iff₀ (by positivity)] at h2; linarith
    · rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ (by positivity)] at h1; linarith
  · rintro ⟨h1, h2⟩
    constructor
    · rw [le_div_iff₀ (by positivity)]; rw [le_div_iff₀ (by positivity)] at h2; linarith
    · rw [div_le_iff₀ (by positivity)]; rw [div_le_iff₀ (by positivity)] at h1; linarith

example : InT (2 / 5) (147 / 100) := by unfold InT; norm_num        -- air, ν ≈ 1.47
example : InT (2 / 3) (15 / 8) := by unfold InT; norm_num           -- monatomic, Pr = 2/3
example : (3 * (2 / 3 + 1) / (4 * (2 / 3)) : ℝ) = 15 / 8 := by norm_num

end

end StrongShock
