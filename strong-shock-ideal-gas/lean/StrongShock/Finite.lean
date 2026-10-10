/-
  Passage to sufficiently strong finite shocks (Section 10): compactness and continuity.
-/
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Complex.Basic

open Filter Topology Set

namespace StrongShock

/-- If `D` is continuous on a compact set and nonvanishing on a compact subset `Base`,
    then it is nonvanishing on a uniform neighborhood of `Base`. -/
theorem nonvanishing_near {X : Type*} [PseudoMetricSpace X] {Dom Base : Set X}
    (hDom : IsCompact Dom) (hBase : IsCompact Base) (D : X → ℂ) (hD : ContinuousOn D Dom)
    (hsub : Base ⊆ Dom) (hne : ∀ b ∈ Base, D b ≠ 0) :
    ∃ δ > 0, ∀ x ∈ Dom, ∀ b ∈ Base, dist x b < δ → D x ≠ 0 := by
  rcases Base.eq_empty_or_nonempty with hE | hNE
  · exact ⟨1, one_pos, fun x _ b hb => by simp [hE] at hb⟩
  -- positive minimum of ‖D‖ on Base
  obtain ⟨b0, hb0, hmin⟩ := hBase.exists_isMinOn hNE
    ((continuous_norm.comp_continuousOn (hD.mono hsub)))
  set m := ‖D b0‖
  have hm : 0 < m := norm_pos_iff.mpr (hne b0 hb0)
  -- uniform continuity
  have hU := hDom.uniformContinuousOn_of_continuous hD
  rw [Metric.uniformContinuousOn_iff] at hU
  obtain ⟨δ, hδ, hδU⟩ := hU m hm
  refine ⟨δ, hδ, fun x hx b hb hxb hDx => ?_⟩
  have h1 := hδU x hx b (hsub hb) hxb
  rw [hDx, dist_comm, dist_zero_right] at h1
  have h2 : m ≤ ‖D b‖ := hmin hb
  linarith

/-- The closed right half-disk `{Re λ ≥ 0, |λ| ≤ Λ}`. -/
def halfDisk (Λ : ℝ) : Set ℂ := {lam | 0 ≤ lam.re ∧ ‖lam‖ ≤ Λ}

lemma isCompact_halfDisk (Λ : ℝ) : IsCompact (halfDisk Λ) := by
  apply (isCompact_closedBall (0 : ℂ) Λ).of_isClosed_subset
  · exact (isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le continuous_norm continuous_const)
  · intro z hz; simpa [halfDisk] using hz.2

/-- **Abstract finite-shock theorem.**  Let `D(λ, p, ς)` be jointly continuous on
    `halfDisk Λ × K × [0, ς₀]`, nonvanishing for `Re λ ≥ 0, |λ| > Λ` (uniform high-frequency
    bound), and nonvanishing at `ς = 0` for parameters in a compact base set `K₀ ⊆ K`.
    Then there is `δ > 0` such that `D(λ,p,ς) ≠ 0` for all `Re λ ≥ 0`, all `p ∈ K` with
    `dist(p, K₀) < δ`, and all `0 ≤ ς < δ`. -/
theorem finite_shock {P : Type*} [PseudoMetricSpace P] {K K0 : Set P} (hK : IsCompact K)
    (hK0 : IsCompact K0) (hsub : K0 ⊆ K) (D : ℂ → P → ℝ → ℂ) {Λ ς0 : ℝ} (hς0 : 0 < ς0)
    (hcont : ContinuousOn (fun q : ℂ × P × ℝ => D q.1 q.2.1 q.2.2) (halfDisk Λ ×ˢ K ×ˢ Icc 0 ς0))
    (hhigh : ∀ lam p ς, 0 ≤ lam.re → Λ < ‖lam‖ → p ∈ K → ς ∈ Icc 0 ς0 → D lam p ς ≠ 0)
    (hlim : ∀ lam p, 0 ≤ lam.re → ‖lam‖ ≤ Λ → p ∈ K0 → D lam p 0 ≠ 0) :
    ∃ δ > 0, ∀ lam p p0 ς, 0 ≤ lam.re → p ∈ K → p0 ∈ K0 → dist p p0 < δ → 0 ≤ ς → ς < δ →
      D lam p ς ≠ 0 := by
  have hDom : IsCompact (halfDisk Λ ×ˢ K ×ˢ Icc 0 ς0) :=
    (isCompact_halfDisk Λ).prod (hK.prod isCompact_Icc)
  have hBase : IsCompact (halfDisk Λ ×ˢ K0 ×ˢ ({0} : Set ℝ)) :=
    (isCompact_halfDisk Λ).prod (hK0.prod isCompact_singleton)
  have hsub' : halfDisk Λ ×ˢ K0 ×ˢ ({0} : Set ℝ) ⊆ halfDisk Λ ×ˢ K ×ˢ Icc 0 ς0 := by
    rintro ⟨l, p, t⟩ ⟨hl, hp, ht⟩
    simp only [mem_singleton_iff] at ht
    exact ⟨hl, hsub hp, by rw [ht]; exact ⟨le_refl _, hς0.le⟩⟩
  obtain ⟨δ, hδ, hnear⟩ := nonvanishing_near hDom hBase _ hcont hsub' (by
    rintro ⟨l, p, t⟩ ⟨hl, hp, ht⟩
    simp only [mem_singleton_iff] at ht
    rw [ht]; exact hlim l p hl.1 hl.2 hp)
  refine ⟨min δ ς0, lt_min hδ hς0, fun lam p p0 ς hre hp hp0 hdist hς hςδ => ?_⟩
  by_cases hΛ : ‖lam‖ ≤ Λ
  · have := hnear (lam, p, ς) ⟨⟨hre, hΛ⟩, hp, ⟨hς, (hςδ.trans_le (min_le_right _ _)).le⟩⟩
      (lam, p0, 0) ⟨⟨hre, hΛ⟩, hp0, rfl⟩ (by
        rw [Prod.dist_eq, Prod.dist_eq]
        simp only [dist_self, Real.dist_eq, sub_zero, abs_of_nonneg hς]
        apply max_lt (lt_of_le_of_lt (le_refl 0) hδ)
        apply max_lt (hdist.trans_le (min_le_left _ _)) (hςδ.trans_le (min_le_left _ _)))
    exact this
  · push Not at hΛ
    exact hhigh lam p ς hre hΛ hp ⟨hς, (hςδ.trans_le (min_le_right _ _)).le⟩

end StrongShock
