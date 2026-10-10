import Mathlib

/-!
# Riccati Stability Without Auxiliary Matrices

A Lean 4 formalization, depending only on Mathlib, of every result in

  Jeffrey Humpherys, *Riccati Stability Without Auxiliary Matrices*.

The file contains no `sorry`, and the main results depend only on the
standard axioms `propext`, `Classical.choice` and `Quot.sound`
(see `AxiomCheck.lean`).

## Design choices

* `Σ` is reserved syntax in Lean, so the matrix family is called `S`.
* Instead of building `H^{1/2}` with the functional calculus inside every
  statement, the metric gain is defined through the quadratic form
  `z ↦ zᴴ H z`.  The lemma `metricGain_eq_norm2` connects it to the paper's
  `‖H^{1/2} X H^{-1/2}‖₂`, so the paper's statements are recovered exactly.
* The spectral norm is the operator norm of `Matrix.toEuclideanCLM`, which
  avoids depending on scoped norm instances.
* `Matrix.inv` returns `0` on singular matrices, so `resolvent A B ω` is
  only meaningful when `iω` is not an eigenvalue of `A`; all results using
  it carry an `IsHurwitz A` hypothesis, matching the paper.
* Attainment of the supremum in the definition of the covariance radius
  (`covRadius_sq_feasible`) needs `n ≥ 1`, stated as `[Nonempty n]`.  For
  `n = 0` no nonzero vector exists, so no `t` is feasible.

## Paper label → Lean name

* Lemma brl              → `riccatiStable_iff_boundedReal`
* (eq:lmi) ⇔ (eq:ric)    → `riccatiStable_iff_lmiFeasible`
* Definition cov         → `CovFeasible`, `covRadius`
* attainment remark      → `covFeasible_le_sup_norm`, `covRadius_sq_feasible`
* Theorem covdual        → `covRadius_eq_optNorm`
* Remark single          → `covRadius_pair`
* Lemma word             → `specRad_prod_rpow_le_covRadius`
* compactness of Σ_{A,B} → `isCompact_resolventFamily`
* Theorem main           → `riccatiStable_iff`
* Corollary finitecert   → `not_riccatiStable_iff`
* Proposition bounds     → `specRad_resolvent_le_rhoR`, `rhoR_le_sup_norm2`,
                           `specRad_resolvent_prod_rpow_le_rhoR`
* Remark (Verriest)      → `specRad_inv_mul_le_rhoR`, `rhoR_scale`, `rhoR_similar`
* Example ex:2d          → section `Example`
* Discussion (bisection) → `rhoR_lt_iff`
-/

open Matrix
open scoped Matrix ComplexOrder

noncomputable section

namespace RiccatiStability

/-! ## Basic objects -/

section Basic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complexification of a real matrix. -/
abbrev cplx (M : Matrix n n ℝ) : Matrix n n ℂ := M.map (algebraMap ℝ ℂ)

/-- Spectral radius of a complex matrix: the largest eigenvalue modulus. -/
def specRad (M : Matrix n n ℂ) : ℝ :=
  sSup ((fun μ : ℂ => ‖μ‖) '' spectrum ℂ M)

/-- Spectral norm `‖M‖₂`, the operator norm on `EuclideanSpace ℂ n`. -/
def norm2 (M : Matrix n n ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) M‖

/-- `A` is Hurwitz: every complex eigenvalue has negative real part. -/
def IsHurwitz (A : Matrix n n ℝ) : Prop :=
  ∀ μ ∈ spectrum ℂ (cplx A), μ.re < 0

/-- Verriest's Riccati stability, inequality (eq:ric). -/
def RiccatiStable (A B : Matrix n n ℝ) : Prop :=
  ∃ P Q : Matrix n n ℝ, P.PosDef ∧ Q.PosDef ∧
    (-(Aᵀ * P + P * A + Q + P * B * Q⁻¹ * Bᵀ * P)).PosDef

/-- The block LMI (eq:lmi). -/
def LMIFeasible (A B : Matrix n n ℝ) : Prop :=
  ∃ P Q : Matrix n n ℝ, P.PosDef ∧ Q.PosDef ∧
    (-(Matrix.fromBlocks (Aᵀ * P + P * A + Q) (P * B) (Bᵀ * P) (-Q))).PosDef

/-- The resolvent family `G_{A,B}(ω) = (iωI - A)⁻¹ B`, (eq:G). -/
def resolvent (A B : Matrix n n ℝ) (ω : ℝ) : Matrix n n ℂ :=
  (((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - cplx A)⁻¹ * cplx B

/-- The real quadratic form `zᴴ H z` (real part; exact when `H` is Hermitian). -/
def qf (H : Matrix n n ℂ) (z : n → ℂ) : ℝ :=
  (star z ⬝ᵥ (H *ᵥ z)).re

/-- Induced norm of `X` for the metric `‖z‖_H = (zᴴ H z)^{1/2}`.
For `H = R * R` with `R` positive definite this is `‖R X R⁻¹‖₂`,
see `metricGain_eq_norm2`. -/
def metricGain (H X : Matrix n n ℂ) : ℝ :=
  ⨆ z : {z : n → ℂ // z ≠ 0}, Real.sqrt (qf (Xᴴ * H * X) z.1 / qf H z.1)

/-- `γ_H = sup_{X ∈ S} ‖H^{1/2} X H^{-1/2}‖₂`. -/
def familyGain (H : Matrix n n ℂ) (S : Set (Matrix n n ℂ)) : ℝ :=
  ⨆ X : S, metricGain H X.1

/-- Optimal common ellipsoidal norm, the right side of (eq:covdual). -/
def optNorm (S : Set (Matrix n n ℂ)) : ℝ :=
  ⨅ H : {H : Matrix n n ℂ // H.PosDef}, familyGain H.1 S

/-- Rank-one covariance `z zᴴ`. -/
def rankOne (z : n → ℂ) : Matrix n n ℂ := vecMulVec z (star z)

/-- Feasibility of `t` in Definition def:cov (eq:covdef):
at most `n²+1` pairs `(X_j, z_j)`, `X_j ∈ S`, not all `z_j = 0`, with
`∑ X_j z_j z_jᴴ X_jᴴ ⪰ t ∑ z_j z_jᴴ`.  Note `X z zᴴ Xᴴ = rankOne (X z)`. -/
def CovFeasible (S : Set (Matrix n n ℂ)) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∃ (m : ℕ) (X : Fin m → Matrix n n ℂ) (z : Fin m → n → ℂ),
    m ≤ Fintype.card n ^ 2 + 1 ∧ (∀ j, X j ∈ S) ∧ (∃ j, z j ≠ 0) ∧
    (∑ j, rankOne (X j *ᵥ z j) - (t : ℂ) • ∑ j, rankOne (z j)).PosSemidef

/-- The covariance radius `ρ_cov(S)`. -/
def covRadius (S : Set (Matrix n n ℂ)) : ℝ :=
  Real.sqrt (sSup {t : ℝ | CovFeasible S t})

end Basic




/-! ## Section 2: the covariance radius -/

section Covariance

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Proved helpers -/

theorem specRad_nonneg (M : Matrix n n ℂ) : 0 ≤ specRad M :=
  Real.sSup_nonneg (by rintro _ ⟨μ, -, rfl⟩; exact norm_nonneg μ)

/-- Every eigenvalue modulus is at most the spectral radius. -/
theorem norm_le_specRad {M : Matrix n n ℂ} {μ : ℂ} (h : μ ∈ spectrum ℂ M) :
    ‖μ‖ ≤ specRad M :=
  le_csSup ((finite_spectrum M).image _).bddAbove ⟨μ, h, rfl⟩

/-- The spectral radius is attained (nontrivial index type). -/
theorem exists_mem_spectrum_norm_eq_specRad [Nonempty n] (M : Matrix n n ℂ) :
    ∃ μ ∈ spectrum ℂ M, ‖μ‖ = specRad M := by
  have hfin : (spectrum ℂ M).Finite := finite_spectrum M
  have hne : (spectrum ℂ M).Nonempty :=
    spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ M
  obtain ⟨μ, hμ, h⟩ := (hne.image (fun μ : ℂ => ‖μ‖)).csSup_mem (hfin.image _)
  exact ⟨μ, hμ, h⟩

omit [DecidableEq n] in
theorem metricGain_nonneg (H X : Matrix n n ℂ) : 0 ≤ metricGain H X :=
  Real.iSup_nonneg fun _ => Real.sqrt_nonneg _

omit [DecidableEq n] in
theorem familyGain_nonneg (H : Matrix n n ℂ) (S : Set (Matrix n n ℂ)) :
    0 ≤ familyGain H S :=
  Real.iSup_nonneg fun _ => metricGain_nonneg _ _

omit [DecidableEq n] in
theorem optNorm_le_familyGain (S : Set (Matrix n n ℂ)) {H : Matrix n n ℂ}
    (hH : H.PosDef) : optNorm S ≤ familyGain H S :=
  ciInf_le ⟨0, by rintro _ ⟨H', rfl⟩; exact familyGain_nonneg _ _⟩
    (⟨H, hH⟩ : {H : Matrix n n ℂ // H.PosDef})

theorem le_optNorm_of_forall {S : Set (Matrix n n ℂ)} {c : ℝ}
    (h : ∀ H : Matrix n n ℂ, H.PosDef → c ≤ familyGain H S) :
    c ≤ optNorm S := by
  have : Nonempty {H : Matrix n n ℂ // H.PosDef} := ⟨⟨1, Matrix.PosDef.one⟩⟩
  exact le_ciInf fun H => h H.1 H.2

/-- Every spectrum element of a matrix has an eigenvector. -/
theorem exists_eigvec_of_mem_spectrum {M : Matrix n n ℂ} {μ : ℂ}
    (h : μ ∈ spectrum ℂ M) : ∃ v : n → ℂ, v ≠ 0 ∧ M *ᵥ v = μ • v := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    not_not] at h
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
  refine ⟨v, hv, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec] at hMv
  have hsm : (μ • (1 : Matrix n n ℂ)) *ᵥ v = μ • v := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hsm, sub_eq_zero] at hMv
  exact hMv.symm

theorem specRad_neg (M : Matrix n n ℂ) : specRad (-M) = specRad M := by
  unfold specRad
  have hs : spectrum ℂ (-M) = -spectrum ℂ M := by
    exact (spectrum.neg_eq M).symm
  rw [hs]
  congr 1
  ext x
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨-μ, hμ, norm_neg μ⟩
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨-μ, by simpa [Set.mem_neg] using hμ, norm_neg μ⟩

omit [DecidableEq n] in
theorem qf_pos {H : Matrix n n ℂ} (hH : H.PosDef) {z : n → ℂ} (hz : z ≠ 0) :
    0 < qf H z := by
  have h : 0 < star z ⬝ᵥ (H *ᵥ z) := by
    exact hH.dotProduct_mulVec_pos hz
  unfold qf
  exact (Complex.pos_iff.mp h).1

omit [DecidableEq n] in
theorem qf_nonneg {H : Matrix n n ℂ} (hH : H.PosDef) (z : n → ℂ) :
    0 ≤ qf H z := by
  by_cases hz : z = 0
  · subst hz
    simp [qf]
  · exact (qf_pos hH hz).le

/-- Every positive semidefinite matrix factors as `Bᴴ B`. -/
theorem exists_eq_conjTranspose_mul_self {H : Matrix n n ℂ}
    (hH : H.PosSemidef) : ∃ B : Matrix n n ℂ, H = Bᴴ * B := by
  have hA : H.IsHermitian := hH.isHermitian
  set U : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hU
  set s : n → ℂ := fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ) with hsdef
  refine ⟨diagonal s * star U, ?_⟩
  have hspec : H = U * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hss : diagonal s * diagonal s = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [hsdef, Function.comp]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hH.eigenvalues_nonneg i)]
    rfl
  have hsH : (diagonal s)ᴴ = diagonal s := by
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    simp [hsdef]
  have hUU : (star U)ᴴ = U := by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose]
  rw [conjTranspose_mul, hUU, hsH]
  conv_lhs => rw [hspec]
  rw [← hss]
  simp only [Matrix.mul_assoc]

/-- `tr(H M) ≥ 0` (real part) for `H, M ⪰ 0`, via `H = Bᴴ B`. -/
theorem trace_mul_re_nonneg {H M : Matrix n n ℂ} (hH : H.PosSemidef)
    (hM : M.PosSemidef) : 0 ≤ ((H * M).trace).re := by
  obtain ⟨B, rfl⟩ := exists_eq_conjTranspose_mul_self hH
  have h1 : (B * M * Bᴴ).PosSemidef := hM.mul_mul_conjTranspose_same B
  have h2 : 0 ≤ (B * M * Bᴴ).trace := h1.trace_nonneg
  have h3 : (Bᴴ * B * M).trace = (B * M * Bᴴ).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [h3]
  exact (Complex.nonneg_iff.mp h2).1

omit [DecidableEq n] in
/-- `tr(H z zᴴ) = zᴴ H z`. -/
theorem trace_mul_rankOne (H : Matrix n n ℂ) (w : n → ℂ) :
    (H * rankOne w).trace = star w ⬝ᵥ (H *ᵥ w) := by
  simp only [rankOne, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.vecMulVec_apply, dotProduct, Matrix.mulVec, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

omit [DecidableEq n] in
/-- `zᴴ (Xᴴ H X) z = (X z)ᴴ H (X z)`. -/
theorem qf_conj (H X : Matrix n n ℂ) (z : n → ℂ) :
    qf (Xᴴ * H * X) z = qf H (X *ᵥ z) := by
  unfold qf
  congr 1
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.star_mulVec]

omit [DecidableEq n] in
theorem continuous_qf (H : Matrix n n ℂ) : Continuous (qf H) := by
  unfold qf
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  fun_prop

omit [DecidableEq n] in
theorem qf_smul (H : Matrix n n ℂ) (r : ℝ) (z : n → ℂ) :
    qf H (r • z) = r ^ 2 * qf H z := by
  unfold qf
  simp only [Matrix.mulVec_smul, star_smul, star_trivial, smul_dotProduct,
    dotProduct_smul, Complex.smul_re]
  ring

omit [DecidableEq n] in
/-- Uniform comparison of quadratic forms over a compact family:
`(X z)ᴴ H (X z) ≤ C · zᴴ H z` for all `X ∈ S` and all `z`.  Route: minimum of
`qf H` on the unit sphere is positive; maximum of `(X, w) ↦ qf H (X w)` on
`S × sphere` is finite; rescale `z` onto the sphere. -/
theorem exists_qf_ratio_bound {S : Set (Matrix n n ℂ)} (hS : IsCompact S)
    {H : Matrix n n ℂ} (hH : H.PosDef) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X ∈ S, ∀ z : n → ℂ, qf (Xᴴ * H * X) z ≤ C * qf H z := by
  have hK : IsCompact (Metric.sphere (0 : n → ℂ) 1) := isCompact_sphere 0 1
  by_cases hKne : (Metric.sphere (0 : n → ℂ) 1).Nonempty
  swap
  · refine ⟨0, le_rfl, fun X _ z => ?_⟩
    have hz : z = 0 := by
      by_contra hz
      apply hKne
      refine ⟨‖z‖⁻¹ • z, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
    subst hz
    simp [qf]
  obtain ⟨w0, hw0K, hmin⟩ := hK.exists_isMinOn hKne (continuous_qf H).continuousOn
  have hw0 : w0 ≠ 0 := by
    intro h
    have h1 := mem_sphere_zero_iff_norm.mp hw0K
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hm : 0 < qf H w0 := qf_pos hH hw0
  obtain ⟨M, hM⟩ : ∃ M, ∀ X ∈ S, ∀ w ∈ Metric.sphere (0 : n → ℂ) 1,
      qf H (X *ᵥ w) ≤ M := by
    have hc : Continuous fun p : Matrix n n ℂ × (n → ℂ) => qf H (p.1 *ᵥ p.2) :=
      (continuous_qf H).comp (continuous_fst.matrix_mulVec continuous_snd)
    obtain ⟨M, hM⟩ := (hS.prod hK).bddAbove_image hc.continuousOn
    exact ⟨M, fun X hX w hw => hM ⟨(X, w), ⟨hX, hw⟩, rfl⟩⟩
  have hC : 0 ≤ max M 0 / qf H w0 := div_nonneg (le_max_right _ _) hm.le
  refine ⟨max M 0 / qf H w0, hC, fun X hX z => ?_⟩
  rw [qf_conj]
  by_cases hz : z = 0
  · subst hz
    simp [qf]
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have key : ∀ (r : ℝ) (w : n → ℂ), w ∈ Metric.sphere (0 : n → ℂ) 1 →
      qf H (X *ᵥ (r • w)) ≤ max M 0 / qf H w0 * qf H (r • w) := by
    intro r w hwK
    rw [Matrix.mulVec_smul, qf_smul, qf_smul]
    have h1 : qf H (X *ᵥ w) ≤ max M 0 := (hM X hX w hwK).trans (le_max_left _ _)
    have h2 : qf H w0 ≤ qf H w := hmin hwK
    have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
    have hm0 : qf H w0 ≠ 0 := hm.ne'
    calc r ^ 2 * qf H (X *ᵥ w) ≤ r ^ 2 * max M 0 := mul_le_mul_of_nonneg_left h1 hr2
      _ = max M 0 / qf H w0 * (r ^ 2 * qf H w0) := by
          rw [div_mul_eq_mul_div, eq_div_iff hm0]
          ring
      _ ≤ max M 0 / qf H w0 * (r ^ 2 * qf H w) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hr2) hC
  have hwK : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ hnz.ne']
  have h := key ‖z‖ (‖z‖⁻¹ • z) hwK
  rwa [smul_smul, mul_inv_cancel₀ hnz.ne', one_smul] at h

omit [Fintype n] [DecidableEq n] in
/-- `(c w)(c w)ᴴ = |c|² w wᴴ`. -/
theorem rankOne_smul (c : ℂ) (w : n → ℂ) :
    rankOne (c • w) = (c * star c) • rankOne w := by
  ext i j
  simp only [rankOne, Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul,
    star_mul', Matrix.smul_apply]
  ring

omit [DecidableEq n] in
/-- The definition of `metricGain` as a supremum gives the pointwise bound. -/
theorem qf_le_metricGain_sq {H : Matrix n n ℂ} (hH : H.PosDef)
    (X : Matrix n n ℂ) (z : n → ℂ) :
    qf (Xᴴ * H * X) z ≤ metricGain H X ^ 2 * qf H z := by
  obtain ⟨C, -, hC⟩ := exists_qf_ratio_bound (isCompact_singleton (x := X)) hH
  by_cases hz : z = 0
  · subst hz
    simp [qf]
  have hq : 0 < qf H z := qf_pos hH hz
  have hnum : 0 ≤ qf (Xᴴ * H * X) z := by
    rw [qf_conj]
    exact qf_nonneg hH _
  have hbdd : BddAbove (Set.range fun y : {y : n → ℂ // y ≠ 0} =>
      Real.sqrt (qf (Xᴴ * H * X) y.1 / qf H y.1)) := by
    refine ⟨Real.sqrt C, ?_⟩
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (qf_pos hH hy)]
    exact hC X (Set.mem_singleton X) y
  have h1 : Real.sqrt (qf (Xᴴ * H * X) z / qf H z) ≤ metricGain H X :=
    le_ciSup hbdd ⟨z, hz⟩
  have h2 : qf (Xᴴ * H * X) z / qf H z ≤ metricGain H X ^ 2 := by
    calc qf (Xᴴ * H * X) z / qf H z
        = Real.sqrt (qf (Xᴴ * H * X) z / qf H z) ^ 2 :=
          (Real.sq_sqrt (div_nonneg hnum hq.le)).symm
      _ ≤ metricGain H X ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
  rwa [div_le_iff₀ hq] at h2

omit [DecidableEq n] in
/-- One member's gain is at most the family gain (compact family). -/
theorem metricGain_le_familyGain {S : Set (Matrix n n ℂ)} (hS : IsCompact S)
    {H : Matrix n n ℂ} (hH : H.PosDef) {X : Matrix n n ℂ} (hX : X ∈ S) :
    metricGain H X ≤ familyGain H S := by
  obtain ⟨C, -, hC⟩ := exists_qf_ratio_bound hS hH
  have hbound : ∀ Y ∈ S, metricGain H Y ≤ Real.sqrt C := by
    intro Y hY
    unfold metricGain
    refine Real.iSup_le (fun y => ?_) (Real.sqrt_nonneg _)
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (qf_pos hH y.2)]
    exact hC Y hY y.1
  unfold familyGain
  exact le_ciSup (f := fun Y : S => metricGain H Y.1)
    ⟨Real.sqrt C, by rintro _ ⟨Y, rfl⟩; exact hbound Y.1 Y.2⟩ ⟨X, hX⟩

/-! ### Results -/

/-- `zᴴ z = ‖z‖²` in `EuclideanSpace ℂ n`. -/
theorem qf_one_eq (z : n → ℂ) :
    qf 1 z = ‖(WithLp.toLp 2 z : EuclideanSpace ℂ n)‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  unfold qf
  rw [Matrix.one_mulVec]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.star_def, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- The metric gain for `H = I` is the spectral norm. -/
theorem metricGain_one (X : Matrix n n ℂ) : metricGain 1 X = norm2 X := by
  have hq : ∀ z, qf (Xᴴ * 1 * X) z
      = ‖(WithLp.toLp 2 (X *ᵥ z) : EuclideanSpace ℂ n)‖ ^ 2 := by
    intro z
    rw [qf_conj, qf_one_eq]
  apply le_antisymm
  · refine Real.iSup_le (fun z => ?_) (by unfold norm2; exact norm_nonneg _)
    have hz : 0 < ‖(WithLp.toLp 2 z.1 : EuclideanSpace ℂ n)‖ := by
      rw [norm_pos_iff]
      intro h
      exact z.2 (by simpa using congrArg WithLp.ofLp h)
    rw [hq, qf_one_eq, ← div_pow, Real.sqrt_sq (div_nonneg (norm_nonneg _) hz.le),
      div_le_iff₀ hz]
    have h := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := n) X).le_opNorm (WithLp.toLp 2 z.1)
    rw [Matrix.toEuclideanCLM_toLp] at h
    exact h
  · unfold norm2
    refine ContinuousLinearMap.opNorm_le_bound _ (metricGain_nonneg _ _) fun v => ?_
    have hv : v = WithLp.toLp 2 v.ofLp := rfl
    rw [hv, Matrix.toEuclideanCLM_toLp]
    have h := qf_le_metricGain_sq Matrix.PosDef.one X v.ofLp
    rw [hq, qf_one_eq] at h
    have h2 : ‖(WithLp.toLp 2 (X *ᵥ v.ofLp) : EuclideanSpace ℂ n)‖ ^ 2
        ≤ (metricGain 1 X * ‖(WithLp.toLp 2 v.ofLp : EuclideanSpace ℂ n)‖) ^ 2 := by
      rw [mul_pow]
      exact h
    have h3 := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (mul_nonneg (metricGain_nonneg _ _) (norm_nonneg _))] at h3

/-- Positive definite square roots exist (the paper's `H^{1/2}`).
Route: `Matrix.IsHermitian.spectral_theorem` or `CFC.sqrt`. -/
theorem exists_posDef_sqrt {H : Matrix n n ℂ} (hH : H.PosDef) :
    ∃ R : Matrix n n ℂ, R.PosDef ∧ R * R = H := by
  have hA : H.IsHermitian := hH.isHermitian
  set V : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hVdef
  set s : n → ℂ := fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ) with hsdef
  have hsV : Vᴴ * V = 1 := by
    first
      | exact Matrix.mem_unitaryGroup_iff'.mp hA.eigenvectorUnitary.2
      | exact Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have hspec : H = V * diagonal (RCLike.ofReal ∘ hA.eigenvalues) * Vᴴ := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hss : diagonal s * diagonal s = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [hsdef, Function.comp]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hH.posSemidef.eigenvalues_nonneg i)]
    rfl
  have hs0 : ∀ i, 0 ≤ s i := fun i => by
    simp only [hsdef]
    exact Complex.zero_le_real.mpr (Real.sqrt_nonneg _)
  have hD : (diagonal s).PosSemidef := Matrix.posSemidef_diagonal_iff.mpr hs0
  have hRpsd : (V * diagonal s * Vᴴ).PosSemidef := hD.mul_mul_conjTranspose_same V
  have hRR : V * diagonal s * Vᴴ * (V * diagonal s * Vᴴ) = H := by
    have h1 : V * diagonal s * Vᴴ * (V * diagonal s * Vᴴ)
        = V * (diagonal s * diagonal s) * Vᴴ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Vᴴ V, hsV, Matrix.one_mul]
    rw [h1, hss, ← hspec]
  refine ⟨V * diagonal s * Vᴴ, ?_, hRR⟩
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hRpsd.isHermitian fun x hx => ?_
  refine lt_of_le_of_ne (hRpsd.dotProduct_mulVec_nonneg x) fun h0 => ?_
  have hRx : (V * diagonal s * Vᴴ) *ᵥ x = 0 := by
    first
      | exact (hRpsd.dotProduct_mulVec_zero_iff (x := x)).mp h0.symm
      | exact hRpsd.dotProduct_mulVec_zero_iff.mp h0.symm
  have hHx : H *ᵥ x = 0 := by
    rw [← hRR, ← Matrix.mulVec_mulVec, hRx, Matrix.mulVec_zero]
  have hpos := hH.dotProduct_mulVec_pos hx
  rw [hHx] at hpos
  simp at hpos

/-- Weak duality, first half of Theorem thm:covdual: any balance (with any
number of terms) is bounded by any metric gain.  Route: take the trace of the
balance against `H` and use `metricGain_le_iff`. -/
theorem balance_le_familyGain_sq {S : Set (Matrix n n ℂ)} (hS : IsCompact S)
    {m : ℕ} (X : Fin m → Matrix n n ℂ) (z : Fin m → n → ℂ)
    (hX : ∀ j, X j ∈ S) (hz : ∃ j, z j ≠ 0) {t : ℝ}
    (hbal : (∑ j, rankOne (X j *ᵥ z j) - (t : ℂ) • ∑ j, rankOne (z j)).PosSemidef)
    {H : Matrix n n ℂ} (hH : H.PosDef) :
    t ≤ familyGain H S ^ 2 := by
  set γ := familyGain H S with hγdef
  have h1 := trace_mul_re_nonneg hH.posSemidef hbal
  have hexp : ((H * (∑ j, rankOne (X j *ᵥ z j)
      - (t : ℂ) • ∑ j, rankOne (z j))).trace).re
      = ∑ j, qf H (X j *ᵥ z j) - t * ∑ j, qf H (z j) := by
    simp only [Matrix.mul_sub, Finset.mul_sum, Matrix.mul_smul, Matrix.trace_sub,
      Matrix.trace_sum, Matrix.trace_smul, trace_mul_rankOne, Complex.sub_re,
      Complex.re_sum, smul_eq_mul, Complex.re_ofReal_mul, qf]
  rw [hexp] at h1
  have h2 : ∑ j, qf H (X j *ᵥ z j) ≤ γ ^ 2 * ∑ j, qf H (z j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← qf_conj]
    calc qf ((X j)ᴴ * H * X j) (z j)
        ≤ metricGain H (X j) ^ 2 * qf H (z j) := qf_le_metricGain_sq hH (X j) (z j)
      _ ≤ γ ^ 2 * qf H (z j) := by
          apply mul_le_mul_of_nonneg_right _ (qf_nonneg hH _)
          exact pow_le_pow_left₀ (metricGain_nonneg _ _)
            (metricGain_le_familyGain hS hH (hX j)) 2
  have hpos : 0 < ∑ j, qf H (z j) := by
    obtain ⟨j, hj⟩ := hz
    exact Finset.sum_pos' (fun i _ => qf_nonneg hH _)
      ⟨j, Finset.mem_univ _, qf_pos hH hj⟩
  have h3 : t * ∑ j, qf H (z j) ≤ γ ^ 2 * ∑ j, qf H (z j) := by linarith
  exact le_of_mul_le_mul_right h3 hpos

/-- Feasible values are bounded by `max_{X∈S} ‖X‖₂²` (trace argument), so
the supremum in def:cov is finite. -/
theorem covFeasible_le_sup_norm {S : Set (Matrix n n ℂ)} (hS : IsCompact S)
    {t : ℝ} (ht : CovFeasible S t) :
    t ≤ ⨆ X : S, norm2 X.1 ^ 2 := by
  obtain ⟨-, m, X, z, -, hX, hz, hbal⟩ := ht
  have h1 := balance_le_familyGain_sq hS X z hX hz hbal Matrix.PosDef.one
  obtain ⟨C, hC0, hC⟩ := exists_qf_ratio_bound hS (Matrix.PosDef.one : (1 : Matrix n n ℂ).PosDef)
  have hb : ∀ Y ∈ S, metricGain 1 Y ≤ Real.sqrt C := by
    intro Y hY
    unfold metricGain
    refine Real.iSup_le (fun y => ?_) (Real.sqrt_nonneg _)
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (qf_pos Matrix.PosDef.one y.2)]
    exact hC Y hY y.1
  have hn : ∀ Y : Matrix n n ℂ, 0 ≤ norm2 Y := fun Y => norm_nonneg _
  have hbdd : BddAbove (Set.range fun Y : S => norm2 Y.1 ^ 2) := ⟨C, by
    rintro _ ⟨Y, rfl⟩
    show norm2 Y.1 ^ 2 ≤ C
    have h0 := metricGain_nonneg 1 Y.1
    have hY := hb Y.1 Y.2
    have hs := Real.sq_sqrt hC0
    have hs0 := Real.sqrt_nonneg C
    rw [← metricGain_one]
    nlinarith⟩
  obtain ⟨j, -⟩ := hz
  haveI : Nonempty S := ⟨⟨X j, hX j⟩⟩
  have h2 : familyGain 1 S ≤ Real.sqrt (⨆ Y : S, norm2 Y.1 ^ 2) := by
    unfold familyGain
    refine ciSup_le fun Y => ?_
    rw [metricGain_one, ← Real.sqrt_sq (hn Y.1)]
    exact Real.sqrt_le_sqrt (le_ciSup hbdd Y)
  have hfg := familyGain_nonneg (1 : Matrix n n ℂ) S
  have hsup0 : 0 ≤ ⨆ Y : S, norm2 Y.1 ^ 2 :=
    le_ciSup_of_le hbdd ⟨X j, hX j⟩ (sq_nonneg _)
  have hs0 := Real.sqrt_nonneg (⨆ Y : S, norm2 Y.1 ^ 2)
  have hss := Real.sq_sqrt hsup0
  nlinarith

theorem optNorm_nonneg (S : Set (Matrix n n ℂ)) : 0 ≤ optNorm S :=
  le_optNorm_of_forall fun H _ => familyGain_nonneg H S

/-- Every feasible value is at most `(inf_H γ_H)²` (weak duality). -/
theorem covFeasible_le_optNorm_sq {S : Set (Matrix n n ℂ)} (hS : IsCompact S)
    {t : ℝ} (ht : CovFeasible S t) : t ≤ optNorm S ^ 2 := by
  obtain ⟨ht0, m, X, z, -, hX, hz, hbal⟩ := ht
  have h : Real.sqrt t ≤ optNorm S := le_optNorm_of_forall fun H hH => by
    calc Real.sqrt t ≤ Real.sqrt (familyGain H S ^ 2) :=
          Real.sqrt_le_sqrt (balance_le_familyGain_sq hS X z hX hz hbal hH)
      _ = familyGain H S := Real.sqrt_sq (familyGain_nonneg H S)
  calc t = Real.sqrt t ^ 2 := (Real.sq_sqrt ht0).symm
    _ ≤ optNorm S ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2

theorem bddAbove_covFeasible {S : Set (Matrix n n ℂ)} (hS : IsCompact S) :
    BddAbove {t : ℝ | CovFeasible S t} :=
  ⟨optNorm S ^ 2, fun _ ht => covFeasible_le_optNorm_sq hS ht⟩

/-- Theorem thm:covdual, inequality `ρ_cov ≤ inf_H γ_H`. -/
theorem covRadius_le_optNorm {S : Set (Matrix n n ℂ)} (hS : IsCompact S) :
    covRadius S ≤ optNorm S := by
  unfold covRadius
  rcases Set.eq_empty_or_nonempty {t : ℝ | CovFeasible S t} with he | hne
  · rw [he, Real.sSup_empty, Real.sqrt_zero]
    exact optNorm_nonneg S
  · calc Real.sqrt (sSup {t : ℝ | CovFeasible S t}) ≤ Real.sqrt (optNorm S ^ 2) :=
          Real.sqrt_le_sqrt (csSup_le hne fun _ ht => covFeasible_le_optNorm_sq hS ht)
      _ = optNorm S := Real.sqrt_sq (optNorm_nonneg S)

/-! ### Carathéodory step and the Hermitian dimension count -/

/-- Hermitian matrices as a real subspace. -/
def hermSub : Submodule ℝ (Matrix n n ℂ) where
  carrier := {A | Aᴴ = A}
  add_mem' := by
    intro A B hA hB
    show (A + B)ᴴ = A + B
    have hA' : Aᴴ = A := hA
    have hB' : Bᴴ = B := hB
    rw [conjTranspose_add, hA', hB']
  zero_mem' := by simp
  smul_mem' := by
    intro c A hA
    show (c • A)ᴴ = c • A
    have hA' : Aᴴ = A := hA
    rw [conjTranspose_smul, hA', star_trivial]

/-- `A ↦ ((i, j) ↦ Re A_ij + Im A_ij)`, real-linear. -/
def reImMap : Matrix n n ℂ →ₗ[ℝ] (n × n → ℝ) where
  toFun A p := (A p.1 p.2).re + (A p.1 p.2).im
  map_add' A B := by
    ext p
    simp only [Matrix.add_apply, Complex.add_re, Complex.add_im, Pi.add_apply]
    ring
  map_smul' c A := by
    ext p
    simp only [Matrix.smul_apply, Complex.smul_re, Complex.smul_im, RingHom.id_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

omit [Fintype n] [DecidableEq n] in
/-- `reImMap` is injective on Hermitian matrices. -/
theorem eq_zero_of_mem_hermSub_of_reImMap_eq_zero {A : Matrix n n ℂ}
    (hA : A ∈ hermSub) (h0 : reImMap A = 0) : A = 0 := by
  have hA' : Aᴴ = A := hA
  ext i j
  have h1 := congrFun h0 (i, j)
  have h2 := congrFun h0 (j, i)
  have hji : A j i = star (A i j) := by
    have h := congrFun (congrFun hA' i) j
    rw [conjTranspose_apply] at h
    rw [← h, star_star]
  simp only [reImMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h1 h2
  rw [hji, Complex.star_def, Complex.conj_re, Complex.conj_im] at h2
  apply Complex.ext <;> simp <;> linarith

omit [DecidableEq n] in
/-- Any real subspace of Hermitian matrices has dimension at most `n²`. -/
theorem finrank_le_of_le_hermSub {W : Submodule ℝ (Matrix n n ℂ)} (hW : W ≤ hermSub) :
    Module.finrank ℝ W ≤ Fintype.card n ^ 2 := by
  have hinj : Function.Injective (reImMap.comp W.subtype) := by
    intro a b hab
    have h : reImMap ((a : Matrix n n ℂ) - (b : Matrix n n ℂ)) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr hab
    have hmem : (a : Matrix n n ℂ) - (b : Matrix n n ℂ) ∈ hermSub :=
      hermSub.sub_mem (hW a.2) (hW b.2)
    exact Subtype.ext (sub_eq_zero.mp (eq_zero_of_mem_hermSub_of_reImMap_eq_zero hmem h))
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, ← sq] at h

omit [Fintype n] [DecidableEq n] in
theorem conjTranspose_rankOne (z : n → ℂ) : (rankOne z)ᴴ = rankOne z := by
  ext i j
  simp [rankOne, Matrix.vecMulVec_apply, Matrix.conjTranspose_apply, mul_comm]

/-- The set `C_t = {t zzᴴ - (Xz)(Xz)ᴴ : X ∈ S, ‖z‖ = 1}` from the proof of
Theorem thm:covdual. -/
def balanceSet (S : Set (Matrix n n ℂ)) (t : ℝ) : Set (Matrix n n ℂ) :=
  {A | ∃ X ∈ S, ∃ z : n → ℂ, ‖z‖ = 1 ∧ A = (t : ℂ) • rankOne z - rankOne (X *ᵥ z)}

omit [DecidableEq n] in
theorem mem_hermSub_of_mem_balanceSet {S : Set (Matrix n n ℂ)} {t : ℝ}
    {A : Matrix n n ℂ} (hA : A ∈ balanceSet S t) : A ∈ hermSub := by
  obtain ⟨X, -, z, -, rfl⟩ := hA
  show _ᴴ = _
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_rankOne, conjTranspose_rankOne,
    Complex.star_def, Complex.conj_ofReal]

omit [DecidableEq n] in
/-- Carathéodory half of the separation step: `0 ∈ conv C_t` gives a balance
at level `t` with at most `n² + 1` terms. -/
theorem covFeasible_of_zero_mem_convexHull {S : Set (Matrix n n ℂ)} {t : ℝ}
    (ht0 : 0 ≤ t) (h : (0 : Matrix n n ℂ) ∈ convexHull ℝ (balanceSet S t)) :
    CovFeasible S t := by
  obtain ⟨ι, _, p, w, hrange, hai, hwpos, hw1, hsum⟩ :=
    eq_pos_convex_span_of_mem_convexHull h
  have hp : ∀ i, p i ∈ balanceSet S t := fun i => hrange ⟨i, rfl⟩
  have hcard : Fintype.card ι ≤ Fintype.card n ^ 2 + 1 := by
    have h1 := hai.card_le_finrank_succ
    have h2 : vectorSpan ℝ (Set.range p) ≤ hermSub := by
      rw [vectorSpan_def, Submodule.span_le]
      rintro _ ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
      exact hermSub.sub_mem (mem_hermSub_of_mem_balanceSet (hp i))
        (mem_hermSub_of_mem_balanceSet (hp j))
    have h3 := finrank_le_of_le_hermSub h2
    omega
  choose X hX z hz hpz using hp
  have hι : Nonempty ι := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    simp at hw1
  obtain ⟨i0⟩ := hι
  let c : ι → ℂ := fun i => ((Real.sqrt (w i) : ℝ) : ℂ)
  have hc : ∀ i, c i * star (c i) = (w i : ℂ) := by
    intro i
    show ((Real.sqrt (w i) : ℝ) : ℂ) * star ((Real.sqrt (w i) : ℝ) : ℂ) = (w i : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hwpos i).le]
  let f : ι → Matrix n n ℂ := fun i =>
    rankOne (X i *ᵥ (c i • z i)) - (t : ℂ) • rankOne (c i • z i)
  have hterm : ∀ i, f i = -((w i : ℂ) • p i) := by
    intro i
    show rankOne (X i *ᵥ (c i • z i)) - (t : ℂ) • rankOne (c i • z i) = -((w i : ℂ) • p i)
    rw [hpz i, Matrix.mulVec_smul, rankOne_smul, rankOne_smul, hc, smul_sub, smul_smul,
      smul_smul, mul_comm (t : ℂ)]
    abel
  let e := Fintype.equivFin ι
  refine ⟨ht0, Fintype.card ι, fun k => X (e.symm k), fun k => c (e.symm k) • z (e.symm k),
    hcard, fun k => hX _, ⟨e i0, ?_⟩, ?_⟩
  · simp only [Equiv.symm_apply_apply]
    refine smul_ne_zero ?_ ?_
    · show ((Real.sqrt (w i0) : ℝ) : ℂ) ≠ 0
      exact_mod_cast (Real.sqrt_pos.mpr (hwpos i0)).ne'
    · intro hz0
      have h1 := hz i0
      rw [hz0, norm_zero] at h1
      exact zero_ne_one h1
  · have key : ∑ k, rankOne (X (e.symm k) *ᵥ (c (e.symm k) • z (e.symm k)))
        - (t : ℂ) • ∑ k, rankOne (c (e.symm k) • z (e.symm k)) = 0 := by
      calc ∑ k, rankOne (X (e.symm k) *ᵥ (c (e.symm k) • z (e.symm k)))
            - (t : ℂ) • ∑ k, rankOne (c (e.symm k) • z (e.symm k))
          = ∑ k, f (e.symm k) := by
            rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        _ = ∑ i, f i := Equiv.sum_comp e.symm f
        _ = ∑ i, -((w i : ℂ) • p i) := Finset.sum_congr rfl fun i _ => hterm i
        _ = 0 := by
            rw [Finset.sum_neg_distrib]
            simp only [Complex.coe_smul]
            rw [hsum, neg_zero]
    convert Matrix.PosSemidef.zero using 1

/-- Convex hulls of compact sets are compact in finite dimension (via
Carathéodory: a finite union of images of simplex × sᵐ). -/
theorem isCompact_convexHull_of_isCompact {E : Type*} [TopologicalSpace E] [AddCommGroup E]
    [Module ℝ E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  let N := Module.finrank ℝ E + 1
  let φ : (m : ℕ) → (Fin m → ℝ) × (Fin m → E) → E := fun m q => ∑ i, q.1 i • q.2 i
  let K : (m : ℕ) → Set ((Fin m → ℝ) × (Fin m → E)) := fun m =>
    stdSimplex ℝ (Fin m) ×ˢ Set.univ.pi (fun _ => s)
  have hK : ∀ m, IsCompact (K m) := fun m =>
    (isCompact_stdSimplex ℝ (Fin m)).prod (isCompact_univ_pi fun _ => hs)
  have hφ : ∀ m, Continuous (φ m) := fun m => by
    fun_prop
  have heq : convexHull ℝ s = ⋃ m ∈ Finset.range (N + 1), φ m '' K m := by
    ext x
    constructor
    · intro hx
      obtain ⟨ι, _, z, w, hrange, hai, hwpos, hw1, hsum⟩ :=
        eq_pos_convex_span_of_mem_convexHull hx
      have hcard : Fintype.card ι ≤ N := by
        have h1 := hai.card_le_finrank_succ
        have h2 := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
        show Fintype.card ι ≤ Module.finrank ℝ E + 1
        omega
      let e := Fintype.equivFin ι
      refine Set.mem_iUnion₂.mpr ⟨Fintype.card ι, Finset.mem_range.mpr (by omega),
        ⟨(fun k => w (e.symm k), fun k => z (e.symm k)),
          ⟨⟨fun k => (hwpos _).le, ?_⟩, fun k _ => hrange ⟨_, rfl⟩⟩, ?_⟩⟩
      · show ∑ k, w (e.symm k) = 1
        rw [Equiv.sum_comp e.symm w, hw1]
      · show ∑ k, w (e.symm k) • z (e.symm k) = x
        rw [Equiv.sum_comp e.symm (fun i => w i • z i), hsum]
    · intro hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨m, -, ⟨w, p⟩, ⟨⟨hw0, hw1⟩, hp⟩, rfl⟩ := hx
      exact (convex_convexHull ℝ s).sum_mem (fun i _ => hw0 i) hw1
        (fun i _ => subset_convexHull ℝ s (hp i (Set.mem_univ _)))
  rw [heq]
  exact (Finset.range (N + 1)).isCompact_biUnion fun m _ => (hK m).image (hφ m)

/-- Every real-linear functional agrees on Hermitian matrices with
`A ↦ Re tr(H A)` for a Hermitian `H`. -/
theorem exists_hermitian_trace_rep (f : Matrix n n ℂ →ₗ[ℝ] ℝ) :
    ∃ H : Matrix n n ℂ, H.IsHermitian ∧ ∀ A ∈ hermSub, f A = (H * A).trace.re := by
  let K : Matrix n n ℂ := Matrix.of fun j i =>
    ((f (single i j (1 : ℂ)) : ℝ) : ℂ) - Complex.I * ((f (single i j Complex.I) : ℝ) : ℂ)
  have hK : ∀ A : Matrix n n ℂ, f A = (K * A).trace.re := by
    intro A
    have hsingle : ∀ i j, f (single i j (A i j))
        = f (single i j (1 : ℂ)) * (A i j).re + f (single i j Complex.I) * (A i j).im := by
      intro i j
      have hdec : single i j (A i j)
          = (A i j).re • single i j (1 : ℂ) + (A i j).im • single i j Complex.I := by
        ext a b
        by_cases ha : i = a <;> by_cases hb : j = b <;>
          simp [ha, hb]
      rw [hdec, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      ring
    conv_lhs => rw [matrix_eq_sum_single A]
    simp only [map_sum, hsingle]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, K, Matrix.of_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re]
  refine ⟨(1 / 2 : ℝ) • (K + Kᴴ), ?_, fun A hA => ?_⟩
  · show ((1 / 2 : ℝ) • (K + Kᴴ))ᴴ = (1 / 2 : ℝ) • (K + Kᴴ)
    rw [conjTranspose_smul, star_trivial, conjTranspose_add, conjTranspose_conjTranspose,
      add_comm]
  · have hA' : Aᴴ = A := hA
    have h2 : (Kᴴ * A).trace.re = (K * A).trace.re := by
      have e1 : (A * K)ᴴ = Kᴴ * A := by rw [conjTranspose_mul, hA']
      rw [← e1, trace_conjTranspose, trace_mul_comm A K, Complex.star_def, Complex.conj_re]
    rw [hK, Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add,
      Complex.smul_re, Complex.add_re, h2]
    ring

omit [DecidableEq n] in
/-- `xᴴ H x` is real for Hermitian `H`. -/
theorem im_star_dotProduct_mulVec_self {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (x : n → ℂ) : (star x ⬝ᵥ (H *ᵥ x)).im = 0 := by
  have hs : star (star x ⬝ᵥ (H *ᵥ x)) = star x ⬝ᵥ (H *ᵥ x) := by
    first
      | (rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hH.eq]
         exact (Matrix.dotProduct_mulVec _ _ _).symm)
      | (rw [Matrix.star_dotProduct, star_star, Matrix.star_mulVec, hH.eq, dotProduct_comm]
         exact (Matrix.dotProduct_mulVec _ _ _).symm)
      | (simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star,
          Finset.mul_sum, hH.apply]
         rw [Finset.sum_comm]
         refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
         ring)
  exact Complex.conj_eq_iff_im.mp hs

omit [DecidableEq n] in
/-- A Hermitian matrix with positive quadratic form is positive definite. -/
theorem posDef_of_qf_pos {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (h : ∀ x : n → ℂ, x ≠ 0 → 0 < qf H x) : H.PosDef := by
  have h' : ∀ x : n → ℂ, x ≠ 0 → 0 < star x ⬝ᵥ (H *ᵥ x) := fun x hx =>
    Complex.pos_iff.mpr ⟨h x hx, (im_star_dotProduct_mulVec_self hH x).symm⟩
  exact Matrix.PosDef.of_dotProduct_mulVec_pos hH h'

/-- The separation half of Theorem thm:covdual.
Route.  Work in `V = Matrix n n ℂ` as a real vector space and let
`C_t = {t zzᴴ - (Xz)(Xz)ᴴ : X ∈ S, ‖z‖ = 1}` (compact, Hermitian-valued).
(a) If `0 ∈ convexHull ℝ C_t`: `eq_pos_convex_span_of_mem_convexHull` gives
affinely independent points with positive weights `w_i`; rescale
`z_i ↦ √w_i z_i` to get a balance that is an equality.  Count: the
`vectorSpan` lies in the Hermitian matrices, on which the real-linear map
`A ↦ (i, j) ↦ Re A_ij + Im A_ij` into `n × n → ℝ` is injective, so
`AffineIndependent.card_le_finrank_succ` gives at most `n² + 1` terms.
(b) Otherwise `geometric_hahn_banach_compact_closed` separates `{0}` from
`convexHull ℝ C_t` (compact in finite dimension) by a real functional `f`
with `f > 0` on `C_t`.  Write `f(A) = Re tr(K A)` and symmetrize to a
Hermitian `H` with `f(A) = Re tr(H A)` for Hermitian `A`, so
`f(t zzᴴ - XzzᴴXᴴ) = t·qf H z - qf H (X z) > 0`.  Taking `X = 0` gives
`H ≻ 0`; then `metricGain H X ≤ √t` for all `X ∈ S`, so
`optNorm S ≤ √t < optNorm S`, a contradiction. -/
theorem covFeasible_of_lt_optNorm_sq {S : Set (Matrix n n ℂ)} (hS : IsCompact S)
    (h0 : (0 : Matrix n n ℂ) ∈ S) {t : ℝ} (ht0 : 0 < t) (ht : t < optNorm S ^ 2) :
    CovFeasible S t := by
  by_cases hmem : (0 : Matrix n n ℂ) ∈ convexHull ℝ (balanceSet S t)
  · exact covFeasible_of_zero_mem_convexHull ht0.le hmem
  exfalso
  let g : Matrix n n ℂ × (n → ℂ) → Matrix n n ℂ := fun q =>
    (t : ℂ) • rankOne q.2 - rankOne (q.1 *ᵥ q.2)
  have hg : Continuous g := by
    simp only [g, rankOne]
    fun_prop
  have hCeq : balanceSet S t = g '' (S ×ˢ Metric.sphere (0 : n → ℂ) 1) := by
    ext A
    constructor
    · rintro ⟨X, hX, z, hz, rfl⟩
      exact ⟨(X, z), ⟨hX, mem_sphere_zero_iff_norm.mpr hz⟩, rfl⟩
    · rintro ⟨⟨X, z⟩, ⟨hX, hz⟩, rfl⟩
      exact ⟨X, hX, z, mem_sphere_zero_iff_norm.mp hz, rfl⟩
  have hC : IsCompact (balanceSet S t) := by
    rw [hCeq]
    exact (hS.prod (isCompact_sphere 0 1)).image hg
  have hT : IsCompact (convexHull ℝ (balanceSet S t)) := isCompact_convexHull_of_isCompact hC
  -- transport to the plain function space, which carries the needed instances
  let Φ : Matrix n n ℂ →ₗ[ℝ] (n → n → ℂ) :=
    { toFun := fun A i j => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΦc : Continuous Φ :=
    continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j
  have hT' : IsCompact (Φ '' convexHull ℝ (balanceSet S t)) := hT.image hΦc
  have hconv' : Convex ℝ (Φ '' convexHull ℝ (balanceSet S t)) :=
    (convex_convexHull ℝ _).linear_image Φ
  have hdisj : Disjoint (Φ '' convexHull ℝ (balanceSet S t)) {0} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨c, hc, hc0⟩
    apply hmem
    have hc' : c = 0 := by
      ext i j
      exact congrFun (congrFun hc0 i) j
    rwa [hc'] at hc
  obtain ⟨f, u, v, hfu, huv, hfv⟩ := geometric_hahn_banach_compact_closed hconv' hT'
    (convex_singleton (0 : n → n → ℂ)) isClosed_singleton hdisj
  have hv : v < 0 := by
    have h := hfv 0 (Set.mem_singleton _)
    rwa [map_zero] at h
  let L : Matrix n n ℂ →ₗ[ℝ] ℝ := -((f : (n → n → ℂ) →ₗ[ℝ] ℝ) ∘ₗ Φ)
  obtain ⟨H, hHerm, hrep⟩ := exists_hermitian_trace_rep L
  have key : ∀ X ∈ S, ∀ z : n → ℂ, ‖z‖ = 1 → qf H (X *ᵥ z) < t * qf H z := by
    intro X hX z hz
    have hc : (t : ℂ) • rankOne z - rankOne (X *ᵥ z) ∈ balanceSet S t := ⟨X, hX, z, hz, rfl⟩
    have h1 : f (Φ ((t : ℂ) • rankOne z - rankOne (X *ᵥ z))) < 0 :=
      ((hfu _ ⟨_, subset_convexHull ℝ _ hc, rfl⟩).trans huv).trans hv
    have h2 := hrep _ (mem_hermSub_of_mem_balanceSet hc)
    have hcomp : (H * ((t : ℂ) • rankOne z - rankOne (X *ᵥ z))).trace.re
        = t * qf H z - qf H (X *ᵥ z) := by
      rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
        trace_mul_rankOne, trace_mul_rankOne, Complex.sub_re, smul_eq_mul,
        Complex.re_ofReal_mul]
      rfl
    have h3 : L ((t : ℂ) • rankOne z - rankOne (X *ᵥ z))
        = -f (Φ ((t : ℂ) • rankOne z - rankOne (X *ᵥ z))) := rfl
    linarith
  have hposunit : ∀ z : n → ℂ, ‖z‖ = 1 → 0 < qf H z := by
    intro z hz
    have h := key 0 h0 z hz
    rw [Matrix.zero_mulVec] at h
    have hq0 : qf H 0 = 0 := by simp [qf]
    rw [hq0] at h
    nlinarith
  have hpos : ∀ x : n → ℂ, x ≠ 0 → 0 < qf H x := by
    intro x hx
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hw : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
    have h := hposunit _ hw
    rw [qf_smul] at h
    have ha : 0 < ‖x‖⁻¹ := inv_pos.mpr hnx
    nlinarith [sq_nonneg (‖x‖⁻¹)]
  have hHpd : H.PosDef := posDef_of_qf_pos hHerm hpos
  have hle : ∀ X ∈ S, ∀ z : n → ℂ, qf H (X *ᵥ z) ≤ t * qf H z := by
    intro X hX z
    by_cases hz : z = 0
    · subst hz
      simp [qf]
    have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hw : ‖‖z‖⁻¹ • z‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnz.ne']
    have h := (key X hX _ hw).le
    rw [Matrix.mulVec_smul, qf_smul, qf_smul] at h
    have hr : 0 < (‖z‖⁻¹) ^ 2 := by positivity
    nlinarith
  have hgain : familyGain H S ≤ Real.sqrt t := by
    unfold familyGain
    refine Real.iSup_le (fun X => ?_) (Real.sqrt_nonneg _)
    unfold metricGain
    refine Real.iSup_le (fun y => ?_) (Real.sqrt_nonneg _)
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (qf_pos hHpd y.2), qf_conj]
    exact hle X.1 X.2 y.1
  have hopt := (optNorm_le_familyGain S hHpd).trans hgain
  have hsq : optNorm S ^ 2 ≤ t := by
    calc optNorm S ^ 2 ≤ Real.sqrt t ^ 2 := pow_le_pow_left₀ (optNorm_nonneg S) hopt 2
      _ = t := Real.sq_sqrt ht0.le
  linarith

/-- Theorem thm:covdual, inequality `inf_H γ_H ≤ ρ_cov`, from the separation step. -/
theorem optNorm_le_covRadius {S : Set (Matrix n n ℂ)} (hS : IsCompact S)
    (h0 : (0 : Matrix n n ℂ) ∈ S) : optNorm S ≤ covRadius S := by
  have hc0 : 0 ≤ covRadius S := Real.sqrt_nonneg _
  by_contra hlt
  rw [not_le] at hlt
  have hα : 0 < optNorm S := lt_of_le_of_lt hc0 hlt
  have hmid0 : 0 < (covRadius S + optNorm S) / 2 := by linarith
  have hmidβ : covRadius S < (covRadius S + optNorm S) / 2 := by linarith
  have hmidα : (covRadius S + optNorm S) / 2 < optNorm S := by linarith
  have ht0 : 0 < ((covRadius S + optNorm S) / 2) ^ 2 := pow_pos hmid0 2
  have htα : ((covRadius S + optNorm S) / 2) ^ 2 < optNorm S ^ 2 :=
    pow_lt_pow_left₀ hmidα hmid0.le two_ne_zero
  have hfeas := covFeasible_of_lt_optNorm_sq hS h0 ht0 htα
  have h1 : ((covRadius S + optNorm S) / 2) ^ 2 ≤ sSup {t : ℝ | CovFeasible S t} :=
    le_csSup (bddAbove_covFeasible hS) hfeas
  have h2 : (covRadius S + optNorm S) / 2 ≤ covRadius S := by
    calc (covRadius S + optNorm S) / 2
        = Real.sqrt (((covRadius S + optNorm S) / 2) ^ 2) := (Real.sqrt_sq hmid0.le).symm
      _ ≤ Real.sqrt (sSup {t : ℝ | CovFeasible S t}) := Real.sqrt_le_sqrt h1
      _ = covRadius S := rfl
  linarith

/-- Theorem thm:covdual. -/
theorem covRadius_eq_optNorm {S : Set (Matrix n n ℂ)} (hS : IsCompact S)
    (h0 : (0 : Matrix n n ℂ) ∈ S) :
    covRadius S = optNorm S :=
  le_antisymm (covRadius_le_optNorm hS) (optNorm_le_covRadius hS h0)

/-- The separation argument at the endpoint `t = (inf_H γ_H)²`: the strict
margin of the separating functional, together with compactness of the unit
sphere, would push the optimal common norm strictly below itself. -/
theorem covFeasible_optNorm_sq {S : Set (Matrix n n ℂ)} (hS : IsCompact S)
    (h0 : (0 : Matrix n n ℂ) ∈ S) (hpos0 : 0 < optNorm S) :
    CovFeasible S (optNorm S ^ 2) := by
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = optNorm S ^ 2 := ⟨_, rfl⟩
  rw [← htdef]
  have ht0 : 0 < t := by rw [htdef]; positivity
  by_cases hmem : (0 : Matrix n n ℂ) ∈ convexHull ℝ (balanceSet S t)
  · exact covFeasible_of_zero_mem_convexHull ht0.le hmem
  exfalso
  let g : Matrix n n ℂ × (n → ℂ) → Matrix n n ℂ := fun q =>
    (t : ℂ) • rankOne q.2 - rankOne (q.1 *ᵥ q.2)
  have hg : Continuous g := by
    simp only [g, rankOne]
    fun_prop
  have hCeq : balanceSet S t = g '' (S ×ˢ Metric.sphere (0 : n → ℂ) 1) := by
    ext A
    constructor
    · rintro ⟨X, hX, z, hz, rfl⟩
      exact ⟨(X, z), ⟨hX, mem_sphere_zero_iff_norm.mpr hz⟩, rfl⟩
    · rintro ⟨⟨X, z⟩, ⟨hX, hz⟩, rfl⟩
      exact ⟨X, hX, z, mem_sphere_zero_iff_norm.mp hz, rfl⟩
  have hC : IsCompact (balanceSet S t) := by
    rw [hCeq]
    exact (hS.prod (isCompact_sphere 0 1)).image hg
  have hT : IsCompact (convexHull ℝ (balanceSet S t)) := isCompact_convexHull_of_isCompact hC
  -- transport to the plain function space, which carries the needed instances
  let Φ : Matrix n n ℂ →ₗ[ℝ] (n → n → ℂ) :=
    { toFun := fun A i j => A i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΦc : Continuous Φ :=
    continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i j
  have hT' : IsCompact (Φ '' convexHull ℝ (balanceSet S t)) := hT.image hΦc
  have hconv' : Convex ℝ (Φ '' convexHull ℝ (balanceSet S t)) :=
    (convex_convexHull ℝ _).linear_image Φ
  have hdisj : Disjoint (Φ '' convexHull ℝ (balanceSet S t)) {0} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨c, hc, hc0⟩
    apply hmem
    have hc' : c = 0 := by
      ext i j
      exact congrFun (congrFun hc0 i) j
    rwa [hc'] at hc
  obtain ⟨f, u, v, hfu, huv, hfv⟩ := geometric_hahn_banach_compact_closed hconv' hT'
    (convex_singleton (0 : n → n → ℂ)) isClosed_singleton hdisj
  have hv : v < 0 := by
    have h := hfv 0 (Set.mem_singleton _)
    rwa [map_zero] at h
  let L : Matrix n n ℂ →ₗ[ℝ] ℝ := -((f : (n → n → ℂ) →ₗ[ℝ] ℝ) ∘ₗ Φ)
  obtain ⟨H, hHerm, hrep⟩ := exists_hermitian_trace_rep L
  have hu : u < 0 := huv.trans hv
  have key : ∀ X ∈ S, ∀ z : n → ℂ, ‖z‖ = 1 → qf H (X *ᵥ z) - u ≤ t * qf H z := by
    intro X hX z hz
    have hc : (t : ℂ) • rankOne z - rankOne (X *ᵥ z) ∈ balanceSet S t := ⟨X, hX, z, hz, rfl⟩
    have h1 : f (Φ ((t : ℂ) • rankOne z - rankOne (X *ᵥ z))) < u :=
      hfu _ ⟨_, subset_convexHull ℝ _ hc, rfl⟩
    have h2 := hrep _ (mem_hermSub_of_mem_balanceSet hc)
    have hcomp : (H * ((t : ℂ) • rankOne z - rankOne (X *ᵥ z))).trace.re
        = t * qf H z - qf H (X *ᵥ z) := by
      rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
        trace_mul_rankOne, trace_mul_rankOne, Complex.sub_re, smul_eq_mul,
        Complex.re_ofReal_mul]
      rfl
    have h3 : L ((t : ℂ) • rankOne z - rankOne (X *ᵥ z))
        = -f (Φ ((t : ℂ) • rankOne z - rankOne (X *ᵥ z))) := rfl
    linarith
  have hq0 : qf H 0 = 0 := by simp [qf]
  have hposunit : ∀ z : n → ℂ, ‖z‖ = 1 → 0 < qf H z := by
    intro z hz
    have h := key 0 h0 z hz
    rw [Matrix.zero_mulVec, hq0] at h
    by_contra hneg
    push_neg at hneg
    have : t * qf H z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0.le hneg
    linarith
  have hpos : ∀ x : n → ℂ, x ≠ 0 → 0 < qf H x := by
    intro x hx
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hw : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnx.ne']
    have h := hposunit _ hw
    rw [qf_smul] at h
    have ha : 0 < ‖x‖⁻¹ := inv_pos.mpr hnx
    nlinarith [sq_nonneg (‖x‖⁻¹)]
  have hHpd : H.PosDef := posDef_of_qf_pos hHerm hpos
  obtain ⟨M0, hM0⟩ :=
    (isCompact_sphere (0 : n → ℂ) 1).bddAbove_image (continuous_qf H).continuousOn
  have hMpos : 0 < max M0 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM : ∀ z : n → ℂ, ‖z‖ = 1 → qf H z ≤ max M0 1 := fun z hz =>
    (hM0 ⟨z, mem_sphere_zero_iff_norm.mpr hz, rfl⟩).trans (le_max_left _ _)
  have hle : ∀ X ∈ S, ∀ z : n → ℂ, qf H (X *ᵥ z) ≤ (t + u / max M0 1) * qf H z := by
    intro X hX z
    by_cases hz : z = 0
    · subst hz
      simp [qf]
    have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hw : ‖‖z‖⁻¹ • z‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnz.ne']
    have h := key X hX _ hw
    have hMw := hM _ hw
    have hmarg : u ≤ u / max M0 1 * qf H (‖z‖⁻¹ • z) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hMpos]
      nlinarith
    have hunit : qf H (X *ᵥ (‖z‖⁻¹ • z))
        ≤ (t + u / max M0 1) * qf H (‖z‖⁻¹ • z) := by
      nlinarith
    rw [Matrix.mulVec_smul, qf_smul, qf_smul] at hunit
    have hr : 0 < (‖z‖⁻¹) ^ 2 := by positivity
    nlinarith
  have hgain : familyGain H S ≤ Real.sqrt (t + u / max M0 1) := by
    unfold familyGain
    refine Real.iSup_le (fun X => ?_) (Real.sqrt_nonneg _)
    unfold metricGain
    refine Real.iSup_le (fun y => ?_) (Real.sqrt_nonneg _)
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (qf_pos hHpd y.2), qf_conj]
    exact hle X.1 X.2 y.1
  have hopt := (optNorm_le_familyGain S hHpd).trans hgain
  have hneg : u / max M0 1 < 0 := div_neg_of_neg_of_pos hu hMpos
  by_cases ht' : 0 ≤ t + u / max M0 1
  · have hsq : optNorm S ^ 2 ≤ t + u / max M0 1 := by
      calc optNorm S ^ 2 ≤ Real.sqrt (t + u / max M0 1) ^ 2 :=
            pow_le_pow_left₀ (optNorm_nonneg S) hopt 2
        _ = t + u / max M0 1 := Real.sq_sqrt ht'
    linarith
  · have hz : Real.sqrt (t + u / max M0 1) = 0 :=
      Real.sqrt_eq_zero'.mpr (not_le.mp ht').le
    rw [hz] at hopt
    linarith

/-- The supremum in def:cov is attained.  (For `n` empty no `z ≠ 0` exists,
so feasibility needs `Nonempty n`.) -/
theorem covRadius_sq_feasible [Nonempty n] {S : Set (Matrix n n ℂ)} (hS : IsCompact S)
    (h0 : (0 : Matrix n n ℂ) ∈ S) :
    CovFeasible S (covRadius S ^ 2) := by
  rw [covRadius_eq_optNorm hS h0]
  rcases (optNorm_nonneg S).lt_or_eq with hpos | hzero
  · exact covFeasible_optNorm_sq hS h0 hpos
  · rw [← hzero, zero_pow two_ne_zero]
    obtain ⟨i⟩ := ‹Nonempty n›
    refine ⟨le_rfl, 1, fun _ => 0, fun _ => fun _ => 1, Nat.le_add_left 1 _,
      fun _ => h0, ⟨0, fun h => by simpa using congrFun h i⟩, ?_⟩
    first
      | simpa [rankOne] using (Matrix.PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
      | (simp [rankOne]; exact Matrix.PosSemidef.zero)

/-- The eigenvector chain in the proof of Lemma lem:word.
Route: pick `μ ∈ spectrum` with `‖μ‖ = specRad W` (the spectrum is finite
and nonempty when `W ≠ 0` in a nontrivial matrix ring), an eigenvector
`v` from `exists_eigvec_of_mem_spectrum`, set `v_k = v`,
`v_{j-1} = X_j v_j`, `t = |μ|^{2/k}`, `z_j = t^{(j-1)/2} v_j`; the balance is
then an equality (so `PosSemidef` of `0`).  Indexing note: `List.ofFn X`
multiplies `X 0 * X 1 * ⋯`, so the chain runs from the last index down. -/
theorem exists_word_balance {k : ℕ} (hk : 0 < k) (X : Fin k → Matrix n n ℂ)
    (hW : 0 < specRad (List.ofFn X).prod) :
    ∃ z : Fin k → n → ℂ, (∃ j, z j ≠ 0) ∧
      (∑ j, rankOne (X j *ᵥ z j)
        - ((specRad (List.ofFn X).prod ^ ((2 : ℝ) / k) : ℝ) : ℂ)
          • ∑ j, rankOne (z j)).PosSemidef := by
  set W := (List.ofFn X).prod with hWdef
  have hne : (spectrum ℂ W).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h0 : specRad W = 0 := by
      unfold specRad
      rw [h, Set.image_empty, Real.sSup_empty]
    linarith
  obtain ⟨μ, hμ, hμr⟩ : ∃ μ ∈ spectrum ℂ W, ‖μ‖ = specRad W := by
    obtain ⟨μ, hμ, h⟩ :=
      (hne.image (fun μ : ℂ => ‖μ‖)).csSup_mem ((finite_spectrum W).image _)
    exact ⟨μ, hμ, h⟩
  obtain ⟨v, hv0, hWv⟩ := exists_eigvec_of_mem_spectrum hμ
  set t : ℝ := specRad W ^ ((2 : ℝ) / k) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hW _
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  let u : ℕ → n → ℂ := fun j => ((List.ofFn X).drop j).prod *ᵥ v
  have hstep : ∀ j : Fin k, X j *ᵥ u (j.1 + 1) = u j.1 := by
    intro j
    have hj : j.1 < (List.ofFn X).length := by simp
    show X j *ᵥ (((List.ofFn X).drop (j.1 + 1)).prod *ᵥ v)
      = ((List.ofFn X).drop j.1).prod *ᵥ v
    rw [List.drop_eq_getElem_cons hj, List.prod_cons, List.getElem_ofFn,
      Matrix.mulVec_mulVec]
  have hu0 : u 0 = μ • v := by
    show ((List.ofFn X).drop 0).prod *ᵥ v = μ • v
    rw [List.drop_zero, ← hWdef, hWv]
  have huk : u k = v := by
    show ((List.ofFn X).drop k).prod *ᵥ v = v
    rw [List.drop_eq_nil_of_le (by simp), List.prod_nil, Matrix.one_mulVec]
  let c : ℕ → ℂ := fun j => ((Real.sqrt t ^ j : ℝ) : ℂ)
  have hc : ∀ j, c j * star (c j) = ((t ^ j : ℝ) : ℂ) := by
    intro j
    show ((Real.sqrt t ^ j : ℝ) : ℂ) * star ((Real.sqrt t ^ j : ℝ) : ℂ)
      = ((t ^ j : ℝ) : ℂ)
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← mul_pow,
      Real.mul_self_sqrt ht0.le]
  let a : ℕ → Matrix n n ℂ := fun j => ((t ^ j : ℝ) : ℂ) • rankOne (u j)
  let z : Fin k → n → ℂ := fun j => c j.1 • u (j.1 + 1)
  refine ⟨z, ?_, ?_⟩
  · refine ⟨⟨k - 1, Nat.sub_lt hk one_pos⟩, ?_⟩
    show c (k - 1) • u (k - 1 + 1) ≠ 0
    rw [Nat.sub_add_cancel hk, huk]
    refine smul_ne_zero ?_ hv0
    show ((Real.sqrt t ^ (k - 1) : ℝ) : ℂ) ≠ 0
    exact_mod_cast (pow_pos hs0 _).ne'
  · have hterm : ∀ j : Fin k,
        rankOne (X j *ᵥ z j) - (t : ℂ) • rankOne (z j) = a j.1 - a (j.1 + 1) := by
      intro j
      show rankOne (X j *ᵥ (c j.1 • u (j.1 + 1))) - (t : ℂ) • rankOne (c j.1 • u (j.1 + 1))
        = ((t ^ j.1 : ℝ) : ℂ) • rankOne (u j.1)
          - ((t ^ (j.1 + 1) : ℝ) : ℂ) • rankOne (u (j.1 + 1))
      rw [Matrix.mulVec_smul, hstep j, rankOne_smul, rankOne_smul, hc, smul_smul,
        ← Complex.ofReal_mul, pow_succ']
    have hsum : ∑ j, rankOne (X j *ᵥ z j) - (t : ℂ) • ∑ j, rankOne (z j) = a 0 - a k := by
      calc ∑ j, rankOne (X j *ᵥ z j) - (t : ℂ) • ∑ j, rankOne (z j)
          = ∑ j : Fin k, (a j.1 - a (j.1 + 1)) := by
            rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun j _ => hterm j
        _ = ∑ j ∈ Finset.range k, (a j - a (j + 1)) :=
            Fin.sum_univ_eq_sum_range (fun j => a j - a (j + 1)) k
        _ = a 0 - a k := Finset.sum_range_sub' a k
    have htk : t ^ k = specRad W ^ 2 := by
      rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (specRad_nonneg W),
        div_mul_cancel₀ (2 : ℝ) (by exact_mod_cast hk.ne' : (k : ℝ) ≠ 0)]
      exact Real.rpow_two _
    have hend : a 0 = a k := by
      show ((t ^ 0 : ℝ) : ℂ) • rankOne (u 0) = ((t ^ k : ℝ) : ℂ) • rankOne (u k)
      rw [hu0, huk, rankOne_smul, pow_zero, Complex.ofReal_one, one_smul, htk,
        Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hμr]
    rw [hsum, hend, sub_self]
    exact Matrix.PosSemidef.zero

/-- Lemma lem:word: `r(X₁⋯X_k)^{1/k} ≤ ρ_cov(S)`. Proved from
`exists_word_balance`, weak duality, and Theorem thm:covdual. -/
theorem specRad_prod_rpow_le_covRadius {S : Set (Matrix n n ℂ)}
    (hS : IsCompact S) (h0 : (0 : Matrix n n ℂ) ∈ S)
    {k : ℕ} (hk : 0 < k) (X : Fin k → Matrix n n ℂ) (hX : ∀ j, X j ∈ S) :
    specRad (List.ofFn X).prod ^ ((k : ℝ)⁻¹) ≤ covRadius S := by
  set W := (List.ofFn X).prod with hWdef
  rcases (specRad_nonneg W).lt_or_eq with hpos | hzero
  · obtain ⟨z, hz, hbal⟩ := exists_word_balance hk X hpos
    set t := specRad W ^ ((2 : ℝ) / k) with ht
    have key : ∀ H : Matrix n n ℂ, H.PosDef → Real.sqrt t ≤ familyGain H S := by
      intro H hH
      have h1 := balance_le_familyGain_sq hS X z hX hz hbal hH
      calc Real.sqrt t ≤ Real.sqrt (familyGain H S ^ 2) := Real.sqrt_le_sqrt h1
        _ = familyGain H S := Real.sqrt_sq (familyGain_nonneg H S)
    have h2 : Real.sqrt t ≤ covRadius S := by
      rw [covRadius_eq_optNorm hS h0]
      exact le_optNorm_of_forall key
    have h3 : Real.sqrt t = specRad W ^ ((k : ℝ)⁻¹) := by
      rw [ht, Real.sqrt_eq_rpow, ← Real.rpow_mul (specRad_nonneg W)]
      congr 1
      ring
    rw [← h3]
    exact h2
  · rw [← hzero, Real.zero_rpow (inv_ne_zero (Nat.cast_ne_zero.mpr hk.ne'))]
    exact Real.sqrt_nonneg _

end Covariance

/-! ## Section 3: main characterization and bounds -/

section Main

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `Σ_{A,B} = {G_{A,B}(ω) : ω ∈ ℝ} ∪ {0}`. -/
def resolventFamily (A B : Matrix n n ℝ) : Set (Matrix n n ℂ) :=
  Set.range (resolvent A B) ∪ {0}

/-- `ρ_R(A,B) = ρ_cov(Σ_{A,B})`, (eq:rhoR). -/
def rhoR (A B : Matrix n n ℝ) : ℝ := covRadius (resolventFamily A B)

omit [DecidableEq n] in
/-- Matrix inversion commutes with ring homomorphisms between fields. -/
theorem map_inv_eq [DecidableEq n] {K L : Type*} [Field K] [Field L] (f : K →+* L)
    (M : Matrix n n K) : (M⁻¹).map f = (M.map f)⁻¹ := by
  have hd : f M.det = (M.map f).det := RingHom.map_det f M
  have ha : M.adjugate.map f = (M.map f).adjugate := RingHom.map_adjugate f M
  rw [Matrix.inv_def, Matrix.inv_def, ← ha, ← hd]
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Ring.inverse_eq_inv',
    map_inv₀]

theorem inv_neg_eq (M : Matrix n n ℂ) : (-M)⁻¹ = -M⁻¹ := by
  by_cases h : IsUnit M.det
  · apply Matrix.inv_eq_left_inv
    rw [neg_mul_neg, Matrix.nonsing_inv_mul M h]
  · have h' : ¬ IsUnit (-M).det := by
      rw [Matrix.det_neg]
      intro hu
      apply h
      rw [isUnit_iff_ne_zero] at hu ⊢
      intro h0
      apply hu
      rw [h0, mul_zero]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h', Matrix.nonsing_inv_apply_not_isUnit _ h,
      neg_zero]

/-- An eigenvector puts its eigenvalue in the spectrum. -/
theorem mem_spectrum_of_eigvec {M : Matrix n n ℂ} {μ : ℂ} {v : n → ℂ} (hv : v ≠ 0)
    (h : M *ᵥ v = μ • v) : μ ∈ spectrum ℂ M := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨v, hv, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    h, sub_self]

/-- For Hurwitz `A`, `iωI - A` is nonsingular. -/
theorem det_resolvent_ne_zero {A : Matrix n n ℝ} (hA : IsHurwitz A) (ω : ℝ) :
    (((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - cplx A).det ≠ 0 := by
  have hns : ((ω : ℂ) * Complex.I) ∉ spectrum ℂ (cplx A) := by
    intro hmem
    have h := hA _ hmem
    simp at h
  rw [spectrum.mem_iff, not_not, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    Algebra.algebraMap_eq_smul_one] at hns
  exact hns

/-- For Hurwitz `A` and every real `s`, `iI - sA` is nonsingular. -/
theorem det_aux_ne_zero {A : Matrix n n ℝ} (hA : IsHurwitz A) (s : ℝ) :
    (Complex.I • (1 : Matrix n n ℂ) - (s : ℂ) • cplx A).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    sub_eq_zero] at hMv
  by_cases hs : s = 0
  · subst hs
    simp at hMv
    exact hv hMv
  · have hAv : cplx A *ᵥ v = (((s⁻¹ : ℝ) : ℂ) * Complex.I) • v := by
      rw [mul_smul, hMv, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hs,
        Complex.ofReal_one, one_smul]
    have h := hA _ (mem_spectrum_of_eigvec hv hAv)
    simp at h

/-- Continuity of `ω ↦ G(ω)` for Hurwitz `A`. -/
theorem continuous_resolvent {A : Matrix n n ℝ} (hA : IsHurwitz A) (B : Matrix n n ℝ) :
    Continuous (resolvent A B) := by
  have hM : Continuous fun ω : ℝ => ((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - cplx A := by
    fun_prop
  have hinv : Continuous fun ω : ℝ =>
      (((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - cplx A)⁻¹ := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv']
    exact (hM.matrix_det.inv₀ (det_resolvent_ne_zero hA)).smul hM.matrix_adjugate
  unfold resolvent
  exact hinv.matrix_mul continuous_const

/-- Compactness of `Σ_{A,B}` for Hurwitz `A`.  With
`F(s) = s (iI - sA)⁻¹ B` (continuous on `ℝ`, `F 0 = 0`) we have
`G(ω) = F(1/ω)` for `ω ≠ 0`, so `Σ_{A,B} = G([-1,1]) ∪ F([-1,1])`. -/
theorem isCompact_resolventFamily {A : Matrix n n ℝ} (hA : IsHurwitz A)
    (B : Matrix n n ℝ) : IsCompact (resolventFamily A B) := by
  let F : ℝ → Matrix n n ℂ := fun s =>
    (s : ℂ) • ((Complex.I • (1 : Matrix n n ℂ) - (s : ℂ) • cplx A)⁻¹ * cplx B)
  have hF : Continuous F := by
    have hN : Continuous fun s : ℝ => Complex.I • (1 : Matrix n n ℂ) - (s : ℂ) • cplx A := by
      fun_prop
    have hNinv : Continuous fun s : ℝ =>
        (Complex.I • (1 : Matrix n n ℂ) - (s : ℂ) • cplx A)⁻¹ := by
      simp only [Matrix.inv_def, Ring.inverse_eq_inv']
      exact (hN.matrix_det.inv₀ (det_aux_ne_zero hA)).smul hN.matrix_adjugate
    exact Complex.continuous_ofReal.smul (hNinv.matrix_mul continuous_const)
  have hF0 : F 0 = 0 := by simp [F]
  have key : ∀ ω : ℝ, ω ≠ 0 → resolvent A B ω = F ω⁻¹ := by
    intro ω hω
    set N := Complex.I • (1 : Matrix n n ℂ) - ((ω⁻¹ : ℝ) : ℂ) • cplx A with hNdef
    have hN : IsUnit N.det := isUnit_iff_ne_zero.mpr (det_aux_ne_zero hA ω⁻¹)
    have hMN : ((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - cplx A = (ω : ℂ) • N := by
      rw [hNdef, smul_sub, smul_smul, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hω,
        Complex.ofReal_one, one_smul]
    have hinv : (((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - cplx A)⁻¹
        = ((ω⁻¹ : ℝ) : ℂ) • N⁻¹ := by
      rw [hMN]
      apply Matrix.inv_eq_left_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul,
        inv_mul_cancel₀ hω, Complex.ofReal_one, one_smul, Matrix.nonsing_inv_mul N hN]
    show _ = ((ω⁻¹ : ℝ) : ℂ) • (N⁻¹ * cplx B)
    unfold resolvent
    rw [hinv, Matrix.smul_mul]
  have heq : resolventFamily A B
      = resolvent A B '' Set.Icc (-1) 1 ∪ F '' Set.Icc (-1) 1 := by
    ext X
    constructor
    · rintro (⟨ω, rfl⟩ | hX)
      · by_cases hω : |ω| ≤ 1
        · exact Or.inl ⟨ω, abs_le.mp hω, rfl⟩
        · rw [not_le] at hω
          have hω0 : ω ≠ 0 := by
            intro h
            rw [h, abs_zero] at hω
            linarith
          refine Or.inr ⟨ω⁻¹, ?_, (key ω hω0).symm⟩
          rw [Set.mem_Icc, ← abs_le, abs_inv]
          exact inv_le_one_of_one_le₀ hω.le
      · rw [Set.mem_singleton_iff] at hX
        subst hX
        exact Or.inr ⟨0, ⟨by norm_num, by norm_num⟩, hF0⟩
    · rintro (⟨ω, -, rfl⟩ | ⟨s, -, rfl⟩)
      · exact Or.inl ⟨ω, rfl⟩
      · by_cases hs : s = 0
        · subst hs
          exact Or.inr hF0
        · refine Or.inl ⟨s⁻¹, ?_⟩
          rw [key s⁻¹ (inv_ne_zero hs), inv_inv]
  rw [heq]
  exact (isCompact_Icc.image (continuous_resolvent hA B)).union (isCompact_Icc.image hF)

/-- Conjugation symmetry for real data: `G(-ω) = conj G(ω)`. -/
theorem resolvent_neg {A : Matrix n n ℝ} (hA : IsHurwitz A)
    (B : Matrix n n ℝ) (ω : ℝ) :
    resolvent A B (-ω) = (resolvent A B ω).map (starRingEnd ℂ) := by
  unfold resolvent
  rw [Matrix.map_mul, map_inv_eq]
  congr 1
  · congr 1
    ext i j
    by_cases h : i = j <;> simp [h, cplx]
  · ext i j
    simp [cplx]

/-! ### Real metrics, conjugation, and the averaging step -/

omit [DecidableEq n] in
theorem qf_add_left (M N : Matrix n n ℂ) (z : n → ℂ) : qf (M + N) z = qf M z + qf N z := by
  unfold qf
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]

omit [DecidableEq n] in
theorem qf_smul_left (c : ℝ) (M : Matrix n n ℂ) (z : n → ℂ) : qf (c • M) z = c * qf M z := by
  unfold qf
  rw [Matrix.smul_mulVec, dotProduct_smul, Complex.smul_re, smul_eq_mul]

omit [DecidableEq n] in
theorem map_conj_mulVec (M : Matrix n n ℂ) (z : n → ℂ) :
    M.map (starRingEnd ℂ) *ᵥ star z = star (M *ᵥ z) := by
  ext i
  simp [Matrix.mulVec, dotProduct]

omit [DecidableEq n] in
theorem qf_map_conj (H : Matrix n n ℂ) (w : n → ℂ) :
    qf (H.map (starRingEnd ℂ)) w = qf H (star w) := by
  unfold qf
  have h : star w ⬝ᵥ (H.map (starRingEnd ℂ) *ᵥ w)
      = starRingEnd ℂ (star (star w) ⬝ᵥ (H *ᵥ star w)) := by
    simp [dotProduct, Matrix.mulVec, map_sum, mul_comm]
  rw [h, Complex.conj_re]

omit [DecidableEq n] in
theorem qf_cplx_ofReal (Q : Matrix n n ℝ) (x : n → ℝ) :
    qf (cplx Q) (fun i => (x i : ℂ)) = x ⬝ᵥ (Q *ᵥ x) := by
  have h : star (fun i => (x i : ℂ)) ⬝ᵥ (cplx Q *ᵥ fun i => (x i : ℂ))
      = ((x ⬝ᵥ (Q *ᵥ x) : ℝ) : ℂ) := by
    simp [dotProduct, Matrix.mulVec, cplx, Complex.ofReal_sum, Complex.ofReal_mul]
  unfold qf
  rw [h, Complex.ofReal_re]

omit [DecidableEq n] in
theorem qf_cplx_eq (Q : Matrix n n ℝ) (z : n → ℂ) :
    qf (cplx Q) z = (fun i => (z i).re) ⬝ᵥ (Q *ᵥ fun i => (z i).re)
      + (fun i => (z i).im) ⬝ᵥ (Q *ᵥ fun i => (z i).im) := by
  simp [qf, cplx, dotProduct, Matrix.mulVec, Complex.re_sum, Complex.im_sum, Complex.mul_re]
  exact Finset.sum_add_distrib

omit [DecidableEq n] in
/-- A real positive definite matrix is positive definite over `ℂ`. -/
theorem posDef_cplx_of_posDef {Q : Matrix n n ℝ} (hQ : Q.PosDef) : (cplx Q).PosDef := by
  have hQh : (cplx Q).IsHermitian := by
    ext i j
    have h := hQ.isHermitian.apply i j
    simp only [star_trivial] at h
    simp [cplx, Matrix.conjTranspose_apply, h]
  refine posDef_of_qf_pos hQh fun z hz => ?_
  rw [qf_cplx_eq]
  have hre : 0 ≤ (fun i => (z i).re) ⬝ᵥ (Q *ᵥ fun i => (z i).re) := by
    have h := hQ.posSemidef.dotProduct_mulVec_nonneg (fun i => (z i).re)
    simpa using h
  have him : 0 ≤ (fun i => (z i).im) ⬝ᵥ (Q *ᵥ fun i => (z i).im) := by
    have h := hQ.posSemidef.dotProduct_mulVec_nonneg (fun i => (z i).im)
    simpa using h
  by_cases ha : (fun i => (z i).re) = 0
  · have hb : (fun i => (z i).im) ≠ 0 := by
      intro hb
      apply hz
      funext i
      apply Complex.ext
      · exact congrFun ha i
      · exact congrFun hb i
    have h := hQ.dotProduct_mulVec_pos hb
    simp only [star_trivial] at h
    linarith
  · have h := hQ.dotProduct_mulVec_pos ha
    simp only [star_trivial] at h
    linarith

omit [DecidableEq n] in
theorem metricGain_zero (H : Matrix n n ℂ) : metricGain H 0 = 0 :=
  le_antisymm (Real.iSup_le (fun z => by simp [qf]) le_rfl) (metricGain_nonneg _ _)

/-- The family gain over `Σ_{A,B}` is the supremum over frequencies. -/
theorem familyGain_resolventFamily_le {A : Matrix n n ℝ} (hA : IsHurwitz A)
    (B : Matrix n n ℝ) {H : Matrix n n ℂ} (hH : H.PosDef) :
    familyGain H (resolventFamily A B) ≤ ⨆ ω : ℝ, metricGain H (resolvent A B ω) := by
  have hbdd : BddAbove (Set.range fun ω => metricGain H (resolvent A B ω)) :=
    ⟨familyGain H (resolventFamily A B), by
      rintro _ ⟨ω, rfl⟩
      exact metricGain_le_familyGain (isCompact_resolventFamily hA B) hH
        (Set.mem_union_left _ (Set.mem_range_self ω))⟩
  have hnn : 0 ≤ ⨆ ω : ℝ, metricGain H (resolvent A B ω) :=
    Real.iSup_nonneg fun _ => metricGain_nonneg _ _
  unfold familyGain
  refine Real.iSup_le (fun X => ?_) hnn
  rcases X.2 with ⟨ω, hω⟩ | hX0
  · rw [← hω]
    exact le_ciSup hbdd ω
  · rw [Set.mem_singleton_iff.mp hX0, metricGain_zero]
    exact hnn

/-- The averaging step in the proof of thm:main.  Route:
`covRadius_eq_optNorm` turns `ρ_R < 1` into a Hermitian `H ≻ 0` with
`sup_ω metricGain H (G ω) < 1`; `resolvent_neg` shows `conj H` gives the same
bound (evaluate at `-ω` and conjugate); `metricGain_le_iff` makes the bound a
semidefinite inequality, which is preserved by averaging, so
`Q = (H + conj H)/2` is real symmetric positive definite and works.
The converse direction is immediate from `optNorm ≤ familyGain (cplx Q)`. -/
theorem rhoR_lt_one_iff_exists_real_metric {A : Matrix n n ℝ}
    (hA : IsHurwitz A) (B : Matrix n n ℝ) :
    rhoR A B < 1 ↔
      ∃ Q : Matrix n n ℝ, Q.PosDef ∧
        (⨆ ω : ℝ, metricGain (cplx Q) (resolvent A B ω)) < 1 := by
  have hS := isCompact_resolventFamily hA B
  have h0 : (0 : Matrix n n ℂ) ∈ resolventFamily A B :=
    Set.mem_union_right _ (Set.mem_singleton _)
  have hmem : ∀ ω, resolvent A B ω ∈ resolventFamily A B :=
    fun ω => Set.mem_union_left _ (Set.mem_range_self _)
  unfold rhoR
  rw [covRadius_eq_optNorm hS h0]
  constructor
  · intro hlt
    have : Nonempty {H : Matrix n n ℂ // H.PosDef} := ⟨⟨1, Matrix.PosDef.one⟩⟩
    obtain ⟨⟨H, hH⟩, hHlt⟩ := exists_lt_of_ciInf_lt hlt
    set γ := familyGain H (resolventFamily A B) with hγ
    have hγ0 : 0 ≤ γ := familyGain_nonneg _ _
    have hbH : ∀ (ω : ℝ) (z : n → ℂ), qf H (resolvent A B ω *ᵥ z) ≤ γ ^ 2 * qf H z := by
      intro ω z
      rw [← qf_conj]
      calc qf ((resolvent A B ω)ᴴ * H * resolvent A B ω) z
          ≤ metricGain H (resolvent A B ω) ^ 2 * qf H z := qf_le_metricGain_sq hH _ z
        _ ≤ γ ^ 2 * qf H z :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (metricGain_nonneg _ _)
              (metricGain_le_familyGain hS hH (hmem ω)) 2) (qf_nonneg hH z)
    let Q : Matrix n n ℝ := H.map Complex.re
    have hQmat : cplx Q = (1 / 2 : ℝ) • (H + H.map (starRingEnd ℂ)) := by
      ext i j
      apply Complex.ext <;> simp [Q, cplx] <;> ring
    have hQq : ∀ z, qf (cplx Q) z = (qf H z + qf H (star z)) / 2 := by
      intro z
      rw [hQmat, qf_smul_left, qf_add_left, qf_map_conj]
      ring
    have hbQ : ∀ (ω : ℝ) (z : n → ℂ),
        qf (cplx Q) (resolvent A B ω *ᵥ z) ≤ γ ^ 2 * qf (cplx Q) z := by
      intro ω z
      rw [hQq, hQq]
      have h1 := hbH ω z
      have h2 := hbH (-ω) (star z)
      rw [resolvent_neg hA, map_conj_mulVec] at h2
      have e : γ ^ 2 * ((qf H z + qf H (star z)) / 2)
          = (γ ^ 2 * qf H z + γ ^ 2 * qf H (star z)) / 2 := by ring
      rw [e]
      linarith
    have hQpd : Q.PosDef := by
      have hQh : Q.IsHermitian := by
        ext i j
        have h := hH.isHermitian.apply i j
        simp only [Q, Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial]
        rw [← h, Complex.star_def, Complex.conj_re]
      refine Matrix.PosDef.of_dotProduct_mulVec_pos hQh fun x hx => ?_
      have hxc : (fun i => (x i : ℂ)) ≠ 0 := by
        intro h
        apply hx
        funext i
        have hi := congrFun h i
        simpa using hi
      have h1 := qf_pos hH hxc
      have hstar : star (fun i => (x i : ℂ)) = fun i => (x i : ℂ) := by
        funext i
        simp
      have h2 : qf (cplx Q) (fun i => (x i : ℂ)) = qf H (fun i => (x i : ℂ)) := by
        rw [hQq, hstar]
        ring
      rw [star_trivial, ← qf_cplx_ofReal, h2]
      exact h1
    have hQc := posDef_cplx_of_posDef hQpd
    refine ⟨Q, hQpd, lt_of_le_of_lt ?_ hHlt⟩
    refine Real.iSup_le (fun ω => ?_) hγ0
    unfold metricGain
    refine Real.iSup_le (fun y => ?_) hγ0
    calc Real.sqrt (qf ((resolvent A B ω)ᴴ * cplx Q * resolvent A B ω) y.1 / qf (cplx Q) y.1)
        ≤ Real.sqrt (γ ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [div_le_iff₀ (qf_pos hQc y.2), qf_conj]
          exact hbQ ω y.1
      _ = γ := Real.sqrt_sq hγ0
  · rintro ⟨Q, hQ, hlt⟩
    have hQc := posDef_cplx_of_posDef hQ
    exact lt_of_le_of_lt
      ((optNorm_le_familyGain _ hQc).trans (familyGain_resolventFamily_le hA B hQc)) hlt

omit [DecidableEq n] in
theorem cplx_transpose (M : Matrix n n ℝ) : cplx Mᵀ = (cplx M)ᴴ := by
  ext i j
  simp [cplx, Matrix.conjTranspose_apply]

omit [DecidableEq n] in
theorem cplx_add (M N : Matrix n n ℝ) : cplx (M + N) = cplx M + cplx N := by
  ext i j
  simp [cplx]

omit [DecidableEq n] in
theorem cplx_neg (M : Matrix n n ℝ) : cplx (-M) = -cplx M := by
  ext i j
  simp [cplx]

omit [DecidableEq n] in
theorem cplx_mul (M N : Matrix n n ℝ) : cplx (M * N) = cplx M * cplx N := by
  first
    | exact Matrix.map_mul

omit [DecidableEq n] in
theorem qf_neg_left (M : Matrix n n ℂ) (z : n → ℂ) : qf (-M) z = -qf M z := by
  unfold qf
  rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]

omit [DecidableEq n] in
theorem transpose_eq_of_posDef {P : Matrix n n ℝ} (hP : P.PosDef) : Pᵀ = P := by
  have h := hP.isHermitian
  rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- Riccati stability forces `A` Hurwitz: for `A v = μ v`,
`vᴴ(AᵀP + PA)v = 2 Re μ · vᴴPv`, while
`AᵀP + PA = -(R + Q + (BᵀP)ᵀQ⁻¹(BᵀP))` with `R, Q ≻ 0`. -/
theorem RiccatiStable.isHurwitz {A B : Matrix n n ℝ} (h : RiccatiStable A B) :
    IsHurwitz A := by
  obtain ⟨P, Q, hP, hQ, hR⟩ := h
  intro μ hμ
  obtain ⟨v, hv, hAv⟩ := exists_eigvec_of_mem_spectrum hμ
  have hPt := transpose_eq_of_posDef hP
  have hPc := posDef_cplx_of_posDef hP
  have hQc := posDef_cplx_of_posDef hQ
  have hRc := posDef_cplx_of_posDef hR
  have hQic := posDef_cplx_of_posDef hQ.inv
  have hid : Aᵀ * P + P * A
      = -((-(Aᵀ * P + P * A + Q + P * B * Q⁻¹ * Bᵀ * P)) + Q
          + (Bᵀ * P)ᵀ * Q⁻¹ * (Bᵀ * P)) := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hPt]
    noncomm_ring
  have e1 : star v ⬝ᵥ (((cplx A)ᴴ * cplx P) *ᵥ v)
      = star μ * (star v ⬝ᵥ (cplx P *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hAv,
      star_smul, smul_dotProduct, smul_eq_mul]
  have e2 : star v ⬝ᵥ ((cplx P * cplx A) *ᵥ v) = μ * (star v ⬝ᵥ (cplx P *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hlhs : qf (cplx (Aᵀ * P + P * A)) v = 2 * μ.re * qf (cplx P) v := by
    have hc : cplx (Aᵀ * P + P * A) = (cplx A)ᴴ * cplx P + cplx P * cplx A := by
      rw [cplx_add, cplx_mul, cplx_mul, cplx_transpose]
    rw [hc, qf_add_left]
    unfold qf
    rw [e1, e2]
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  have hrhs : qf (cplx (Aᵀ * P + P * A)) v < 0 := by
    rw [hid]
    have hY : 0 ≤ qf (cplx ((Bᵀ * P)ᵀ * Q⁻¹ * (Bᵀ * P))) v := by
      have hc : cplx ((Bᵀ * P)ᵀ * Q⁻¹ * (Bᵀ * P))
          = (cplx (Bᵀ * P))ᴴ * cplx Q⁻¹ * cplx (Bᵀ * P) := by
        simp only [cplx_mul, cplx_transpose]
      rw [hc, qf_conj]
      exact qf_nonneg hQic _
    have h1 := qf_pos hRc hv
    have h2 := qf_pos hQc hv
    rw [cplx_neg, cplx_add, cplx_add, qf_neg_left, qf_add_left, qf_add_left]
    linarith
  have hPv := qf_pos hPc hv
  rw [hlhs] at hrhs
  nlinarith

omit [DecidableEq n] in
/-- Hermitian swap: `uᴴ H w = conj (wᴴ H u)`. -/
theorem dotProduct_mulVec_swap {H : Matrix n n ℂ} (hH : H.IsHermitian) (u w : n → ℂ) :
    star u ⬝ᵥ (H *ᵥ w) = star (star w ⬝ᵥ (H *ᵥ u)) := by
  rw [Matrix.star_dotProduct, Matrix.star_mulVec, hH.eq, ← Matrix.dotProduct_mulVec]

omit [DecidableEq n] in
theorem qf_sub_of_isHermitian {H : Matrix n n ℂ} (hH : H.IsHermitian) (u w : n → ℂ) :
    qf H (u - w) = qf H u + qf H w - 2 * (star w ⬝ᵥ (H *ᵥ u)).re := by
  have hc := dotProduct_mulVec_swap hH u w
  unfold qf
  rw [star_sub, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub, hc]
  simp only [Complex.sub_re, Complex.star_def, Complex.conj_re]
  ring

omit [DecidableEq n] in
/-- Comparison of quadratic forms: `qf K ≤ C · qf H` for `H ≻ 0`. -/
theorem exists_qf_le_mul {H : Matrix n n ℂ} (hH : H.PosDef) (K : Matrix n n ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : n → ℂ, qf K z ≤ C * qf H z := by
  have hK : IsCompact (Metric.sphere (0 : n → ℂ) 1) := isCompact_sphere 0 1
  by_cases hKne : (Metric.sphere (0 : n → ℂ) 1).Nonempty
  swap
  · refine ⟨1, one_pos, fun z => ?_⟩
    have hz : z = 0 := by
      by_contra hz
      apply hKne
      refine ⟨‖z‖⁻¹ • z, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
    subst hz
    simp [qf]
  obtain ⟨w0, hw0K, hmin⟩ := hK.exists_isMinOn hKne (continuous_qf H).continuousOn
  have hw0 : w0 ≠ 0 := by
    intro h
    have h1 := mem_sphere_zero_iff_norm.mp hw0K
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hm : 0 < qf H w0 := qf_pos hH hw0
  obtain ⟨M, hM⟩ := hK.bddAbove_image (continuous_qf K).continuousOn
  have hMx : 0 ≤ max M 0 := le_max_right _ _
  refine ⟨max M 0 / qf H w0 + 1, add_pos_of_nonneg_of_pos (div_nonneg hMx hm.le) one_pos,
    fun z => ?_⟩
  by_cases hz : z = 0
  · subst hz
    simp [qf]
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hwK : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : n → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnz.ne']
  have h1 : qf K (‖z‖⁻¹ • z) ≤ max M 0 := (hM ⟨_, hwK, rfl⟩).trans (le_max_left _ _)
  have h2 : qf H w0 ≤ qf H (‖z‖⁻¹ • z) := hmin hwK
  rw [qf_smul] at h1 h2
  have hs : 0 < ‖z‖⁻¹ ^ 2 := by positivity
  have hqH : 0 ≤ qf H z := qf_nonneg hH z
  have hkey : ‖z‖⁻¹ ^ 2 * qf K z ≤ ‖z‖⁻¹ ^ 2 * ((max M 0 / qf H w0 + 1) * qf H z) := by
    have e2 : ‖z‖⁻¹ ^ 2 * ((max M 0 / qf H w0 + 1) * qf H z)
        = max M 0 / qf H w0 * (‖z‖⁻¹ ^ 2 * qf H z) + ‖z‖⁻¹ ^ 2 * qf H z := by ring
    calc ‖z‖⁻¹ ^ 2 * qf K z ≤ max M 0 := h1
      _ = max M 0 / qf H w0 * qf H w0 := (div_mul_cancel₀ _ hm.ne').symm
      _ ≤ max M 0 / qf H w0 * (‖z‖⁻¹ ^ 2 * qf H z) :=
          mul_le_mul_of_nonneg_left h2 (div_nonneg hMx hm.le)
      _ ≤ ‖z‖⁻¹ ^ 2 * ((max M 0 / qf H w0 + 1) * qf H z) := by
          rw [e2]
          linarith [mul_nonneg hs.le hqH]
  exact le_of_mul_le_mul_left hkey hs

/-- Dissipation inequality behind the elementary half of Lemma brl:
if `aᴴp + pa + q + (bᴴp)ᴴ qi (bᴴp) = -r`, `q qi = 1`, and
`(cI - a) x = b u` with `Re c = 0`, then `xᴴqx + xᴴrx ≤ uᴴqu`. -/
theorem riccati_dissipation {a b p q qi r : Matrix n n ℂ} (hp : p.IsHermitian)
    (hq : q.IsHermitian) (hqi : qi.IsHermitian) (hqqi : q * qi = 1)
    (hqnn : ∀ z, 0 ≤ qf q z)
    (hid : aᴴ * p + p * a + q + (bᴴ * p)ᴴ * qi * (bᴴ * p) = -r)
    {c : ℂ} (hc : c.re = 0) {x u : n → ℂ}
    (hx : (c • (1 : Matrix n n ℂ) - a) *ᵥ x = b *ᵥ u) :
    qf q x + qf r x ≤ qf q u := by
  have hax : a *ᵥ x = c • x - b *ᵥ u := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hx
    rw [← hx]
    abel
  have hT1 : qf (aᴴ * p + p * a) x = -2 * (star x ⬝ᵥ (p *ᵥ (b *ᵥ u))).re := by
    rw [qf_add_left]
    unfold qf
    have e1 : star x ⬝ᵥ ((aᴴ * p) *ᵥ x) = star (star x ⬝ᵥ (p *ᵥ (a *ᵥ x))) := by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      exact dotProduct_mulVec_swap hp (a *ᵥ x) x
    have e2 : star x ⬝ᵥ ((p * a) *ᵥ x) = star x ⬝ᵥ (p *ᵥ (a *ᵥ x)) := by
      rw [Matrix.mulVec_mulVec]
    rw [e1, e2, hax, Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
    have him := im_star_dotProduct_mulVec_self hp x
    simp only [Complex.star_def, Complex.conj_re, Complex.sub_re, Complex.mul_re, hc, him]
    ring
  obtain ⟨v, hv⟩ : ∃ v, v = bᴴ *ᵥ (p *ᵥ x) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = qi *ᵥ v := ⟨_, rfl⟩
  have hqw : q *ᵥ w = v := by
    rw [hw, Matrix.mulVec_mulVec, hqqi, Matrix.one_mulVec]
  have hcross : star w ⬝ᵥ (q *ᵥ u) = star x ⬝ᵥ (p *ᵥ (b *ᵥ u)) := by
    rw [dotProduct_mulVec_swap hq w u, hqw, hv, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
      dotProduct_mulVec_swap hp (b *ᵥ u) x, star_star]
  have hqfw : qf q w = qf ((bᴴ * p)ᴴ * qi * (bᴴ * p)) x := by
    rw [qf_conj]
    unfold qf
    rw [hqw, ← Matrix.mulVec_mulVec, ← hv, hw, Matrix.star_mulVec, hqi.eq,
      ← Matrix.dotProduct_mulVec]
  have h0 := hqnn (u - w)
  rw [qf_sub_of_isHermitian hq, hcross, hqfw] at h0
  have hrx : qf r x = -(qf (aᴴ * p + p * a) x + qf q x
      + qf ((bᴴ * p)ᴴ * qi * (bᴴ * p)) x) := by
    rw [← neg_neg r, ← hid, qf_neg_left, qf_add_left, qf_add_left]
  rw [hrx, hT1]
  linarith

/-- Elementary half of Lemma brl: Riccati stability gives the frequency
bound with the same `Q`, uniformly `≤ (C/(C+1))^{1/2} < 1`. -/
theorem boundedReal_of_riccatiStable {A B : Matrix n n ℝ} (h : RiccatiStable A B) :
    ∃ Q : Matrix n n ℝ, Q.PosDef ∧
      (⨆ ω : ℝ, metricGain (cplx Q) (resolvent A B ω)) < 1 := by
  have hA := h.isHurwitz
  obtain ⟨P, Q, hP, hQ, hR⟩ := h
  set R := -(Aᵀ * P + P * A + Q + P * B * Q⁻¹ * Bᵀ * P) with hRdef
  have hPc := posDef_cplx_of_posDef hP
  have hQc := posDef_cplx_of_posDef hQ
  have hRc := posDef_cplx_of_posDef hR
  have hQic := posDef_cplx_of_posDef hQ.inv
  have hQdet : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ.det_pos.ne'
  have hqqi : cplx Q * cplx Q⁻¹ = 1 := by
    rw [← cplx_mul, Matrix.mul_nonsing_inv Q hQdet]
    ext i j
    by_cases hij : i = j <;> simp [cplx, Matrix.one_apply, hij]
  have hid : (cplx A)ᴴ * cplx P + cplx P * cplx A + cplx Q
      + ((cplx B)ᴴ * cplx P)ᴴ * cplx Q⁻¹ * ((cplx B)ᴴ * cplx P) = -cplx R := by
    rw [hRdef, cplx_neg, neg_neg]
    simp only [cplx_add, cplx_mul, cplx_transpose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    rw [hPc.isHermitian.eq]
    noncomm_ring
  have hdiss : ∀ (ω : ℝ) (u : n → ℂ),
      qf (cplx Q) (resolvent A B ω *ᵥ u) + qf (cplx R) (resolvent A B ω *ᵥ u)
        ≤ qf (cplx Q) u := by
    intro ω u
    refine riccati_dissipation hPc.isHermitian hQc.isHermitian hQic.isHermitian hqqi
      (qf_nonneg hQc) hid (c := (ω : ℂ) * Complex.I) (by simp) ?_
    unfold resolvent
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_resolvent_ne_zero hA ω)),
      Matrix.one_mul]
  obtain ⟨C, hC, hcmp⟩ := exists_qf_le_mul hRc (cplx Q)
  refine ⟨Q, hQ, ?_⟩
  have hgain : ∀ (ω : ℝ) (u : n → ℂ),
      qf (cplx Q) (resolvent A B ω *ᵥ u) ≤ C / (C + 1) * qf (cplx Q) u := by
    intro ω u
    have h1 := hdiss ω u
    have h2 := hcmp (resolvent A B ω *ᵥ u)
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hC.le]
  have hγ2nn : 0 ≤ C / (C + 1) := div_nonneg hC.le (by linarith)
  have hbound : (⨆ ω : ℝ, metricGain (cplx Q) (resolvent A B ω)) ≤ Real.sqrt (C / (C + 1)) := by
    refine Real.iSup_le (fun ω => ?_) (Real.sqrt_nonneg _)
    unfold metricGain
    refine Real.iSup_le (fun y => ?_) (Real.sqrt_nonneg _)
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (qf_pos hQc y.2), qf_conj]
    exact hgain ω y.1
  have hlt : Real.sqrt (C / (C + 1)) < 1 := by
    have h := Real.sqrt_lt_sqrt hγ2nn ((div_lt_one (by linarith : (0 : ℝ) < C + 1)).mpr
      (by linarith : C < C + 1))
    rwa [Real.sqrt_one] at h
  exact lt_of_le_of_lt hbound hlt

omit [DecidableEq n] in
theorem sumElim_dotProduct (x u y w : n → ℝ) :
    Sum.elim x u ⬝ᵥ Sum.elim y w = x ⬝ᵥ y + u ⬝ᵥ w := by
  simp [dotProduct, Fintype.sum_sum_type]

/-- Schur step: the strict LMI gives the strict Riccati inequality.  For
`x ≠ 0` take `u = Q⁻¹BᵀPx`, which zeroes the second block row. -/
theorem ari_of_lmi_real {X P B Q : Matrix n n ℝ} (hX : Xᵀ = X) (hPt : Pᵀ = P)
    (hQ : Q.PosDef)
    (h : (-(Matrix.fromBlocks X (P * B) (Bᵀ * P) (-Q))).PosDef) :
    (-(X + P * B * Q⁻¹ * Bᵀ * P)).PosDef := by
  have hQdet : IsUnit Q.det := isUnit_iff_ne_zero.mpr hQ.det_pos.ne'
  have hQt : Q⁻¹ᵀ = Q⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, transpose_eq_of_posDef hQ]
  have hherm : (-(X + P * B * Q⁻¹ * Bᵀ * P)).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_neg,
      Matrix.transpose_add, hX]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hPt, hQt, Matrix.mul_assoc]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun x hx => ?_
  obtain ⟨u, hu⟩ : ∃ u, u = Q⁻¹ *ᵥ (Bᵀ *ᵥ (P *ᵥ x)) := ⟨_, rfl⟩
  have hQu : Q *ᵥ u = Bᵀ *ᵥ (P *ᵥ x) := by
    rw [hu, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQdet, Matrix.one_mulVec]
  have hz : (Sum.elim x u : n ⊕ n → ℝ) ≠ 0 := by
    intro h0
    apply hx
    funext i
    exact congrFun h0 (Sum.inl i)
  have hpos := h.dotProduct_mulVec_pos hz
  have e1 : (P * B * Q⁻¹ * Bᵀ * P) *ᵥ x = (P * B) *ᵥ u := by
    rw [hu]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have e2 : (Bᵀ * P) *ᵥ x + (-Q) *ᵥ u = 0 := by
    rw [Matrix.neg_mulVec, hQu, ← Matrix.mulVec_mulVec, add_neg_cancel]
  simp only [star_trivial] at hpos ⊢
  rw [Matrix.neg_mulVec, Matrix.fromBlocks_mulVec, dotProduct_neg] at hpos
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at hpos
  rw [sumElim_dotProduct, e2, dotProduct_zero, add_zero, dotProduct_add] at hpos
  rw [Matrix.neg_mulVec, dotProduct_neg, Matrix.add_mulVec, dotProduct_add, e1]
  linarith

omit [DecidableEq n] in
theorem trace_fromBlocks' (A B C D : Matrix n n ℂ) :
    (Matrix.fromBlocks A B C D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

omit [DecidableEq n] in
/-- `Re tr(W Φ(p)) = Re tr(p N)` with `N = W₁₁aᴴ + aW₁₁ + W₁₂bᴴ + bW₂₁`. -/
theorem trace_kyp_pairing (W11 W12 W21 W22 a b p : Matrix n n ℂ) :
    (Matrix.fromBlocks W11 W12 W21 W22
        * Matrix.fromBlocks (aᴴ * p + p * a) (p * b) (bᴴ * p) 0).trace
      = (p * (W11 * aᴴ + a * W11 + W12 * bᴴ + b * W21)).trace := by
  rw [Matrix.fromBlocks_multiply, trace_fromBlocks']
  have h1 : (W11 * (aᴴ * p)).trace = (p * (W11 * aᴴ)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have h2 : (W11 * (p * a)).trace = (p * (a * W11)).trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h3 : (W12 * (bᴴ * p)).trace = (p * (W12 * bᴴ)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have h4 : (W21 * (p * b)).trace = (p * (b * W21)).trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
  simp only [Matrix.mul_add, Matrix.trace_add, Matrix.mul_zero, add_zero]
  rw [h1, h2, h3, h4]
  try ring

omit [DecidableEq n] in
/-- A vanishing pairing against every Hermitian `p` forces the KYP constraint. -/
theorem kyp_constraint {W11 W12 W21 W22 a b : Matrix n n ℂ} (h11 : W11ᴴ = W11)
    (h21 : W12ᴴ = W21)
    (hpair : ∀ p : Matrix n n ℂ, p.IsHermitian →
      (Matrix.fromBlocks W11 W12 W21 W22
        * Matrix.fromBlocks (aᴴ * p + p * a) (p * b) (bᴴ * p) 0).trace.re = 0) :
    W11 * aᴴ + a * W11 + W12 * bᴴ + b * W21 = 0 := by
  have h12 : W21ᴴ = W12 := by rw [← h21, conjTranspose_conjTranspose]
  obtain ⟨N, hN⟩ : ∃ N, N = W11 * aᴴ + a * W11 + W12 * bᴴ + b * W21 := ⟨_, rfl⟩
  have hNh : N.IsHermitian := by
    show Nᴴ = N
    rw [hN]
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, h11, h12, h21]
    abel
  have h := hpair N hNh
  rw [trace_kyp_pairing, ← hN] at h
  have hreal : star ((N * N).trace) = (N * N).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hNh.eq]
  have him : ((N * N).trace).im = 0 := Complex.conj_eq_iff_im.mp hreal
  have hNN : (Nᴴ * N).trace = 0 := by
    rw [hNh.eq]
    exact Complex.ext h him
  rw [← hN]
  exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hNN

omit [DecidableEq n] in
/-- `xᴴ (z zᴴ) x ≥ 0`. -/
theorem qf_rankOne_nonneg (z x : n → ℂ) : 0 ≤ qf (rankOne z) x := by
  have e : star x ⬝ᵥ (rankOne z *ᵥ x) = (star x ⬝ᵥ z) * (star z ⬝ᵥ x) := by
    simp only [rankOne, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.star_apply]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have e2 : star x ⬝ᵥ z = star (star z ⬝ᵥ x) := by
    simp only [dotProduct, Pi.star_apply, star_sum, star_mul', star_star]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  unfold qf
  rw [e, e2]
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  nlinarith [sq_nonneg (star z ⬝ᵥ x).re, sq_nonneg (star z ⬝ᵥ x).im]

/-- A nonnegative combination of rank-one matrices is positive semidefinite. -/
theorem posSemidef_sum_smul_rankOne {ι : Type*} [Fintype ι] (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (z : ι → n → ℂ) : (∑ i, c i • rankOne (z i)).PosSemidef := by
  have hherm : (∑ i, c i • rankOne (z i)).IsHermitian := by
    show (∑ i, c i • rankOne (z i))ᴴ = ∑ i, c i • rankOne (z i)
    rw [conjTranspose_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [conjTranspose_smul, star_trivial, conjTranspose_rankOne]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun x => ?_
  refine Complex.nonneg_iff.mpr ⟨?_, (im_star_dotProduct_mulVec_self hherm x).symm⟩
  show 0 ≤ qf (∑ i, c i • rankOne (z i)) x
  have hqt : ∀ M : Matrix n n ℂ, qf M x = (M * rankOne x).trace.re := fun M => by
    rw [trace_mul_rankOne]
    rfl
  rw [hqt, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re, smul_eq_mul, ← hqt]
  exact mul_nonneg (hc i) (qf_rankOne_nonneg _ _)

/-- Separation step of KYP (theorem of alternatives for the KYP LMI).  The
compact convex set `conv{(Ψ(zzᴴ), Re tr(zzᴴ M₀)) : ‖z‖ = 1}` either meets
`{0} × [0, ∞)`, giving the balancing matrix `W`, or is strictly separated
from it; the separating functional gives a Hermitian `H` and a multiplier
`β ≥ 0`, with `β > 0` (since `β = 0` contradicts the zero lower-right block)
and `p = H/β` solving the LMI. -/
theorem kyp_alternative (a b q : Matrix n n ℂ) (hq : q.IsHermitian) :
    (∃ p : Matrix n n ℂ, p.IsHermitian ∧
      (-(Matrix.fromBlocks (aᴴ * p + p * a + q) (p * b) (bᴴ * p) (-q))).PosDef) ∨
    ∃ W11 W12 W21 W22 : Matrix n n ℂ, (Matrix.fromBlocks W11 W12 W21 W22).PosSemidef ∧
      Matrix.fromBlocks W11 W12 W21 W22 ≠ 0 ∧
      (q * W22).trace.re ≤ (q * W11).trace.re ∧
      ∀ p : Matrix n n ℂ, p.IsHermitian →
        (Matrix.fromBlocks W11 W12 W21 W22
          * Matrix.fromBlocks (aᴴ * p + p * a) (p * b) (bᴴ * p) 0).trace.re = 0 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · left
    refine ⟨0, Matrix.isHermitian_zero, ?_⟩
    refine posDef_of_qf_pos ?_ fun x hx => absurd (Subsingleton.elim x 0) hx
    show _ = _
    ext i
    exact isEmptyElim i
  obtain ⟨i0⟩ := hn
  -- the dual map Ψ and the linear map T
  let Ψ : Matrix (n ⊕ n) (n ⊕ n) ℂ → Matrix n n ℂ := fun Z =>
    Z.toBlocks₁₁ * aᴴ + a * Z.toBlocks₁₁ + Z.toBlocks₁₂ * bᴴ + b * Z.toBlocks₂₁
  have hΨadd : ∀ Z Z', Ψ (Z + Z') = Ψ Z + Ψ Z' := by
    intro Z Z'
    have h11 : (Z + Z').toBlocks₁₁ = Z.toBlocks₁₁ + Z'.toBlocks₁₁ := by ext i j; rfl
    have h12 : (Z + Z').toBlocks₁₂ = Z.toBlocks₁₂ + Z'.toBlocks₁₂ := by ext i j; rfl
    have h21 : (Z + Z').toBlocks₂₁ = Z.toBlocks₂₁ + Z'.toBlocks₂₁ := by ext i j; rfl
    simp only [Ψ, h11, h12, h21, Matrix.add_mul, Matrix.mul_add]
    abel
  have hΨsmul : ∀ (c : ℝ) Z, Ψ (c • Z) = c • Ψ Z := by
    intro c Z
    have h11 : (c • Z).toBlocks₁₁ = c • Z.toBlocks₁₁ := by ext i j; rfl
    have h12 : (c • Z).toBlocks₁₂ = c • Z.toBlocks₁₂ := by ext i j; rfl
    have h21 : (c • Z).toBlocks₂₁ = c • Z.toBlocks₂₁ := by ext i j; rfl
    simp only [Ψ, h11, h12, h21, Matrix.smul_mul, Matrix.mul_smul, smul_add]
  have hΨherm : ∀ Z : Matrix (n ⊕ n) (n ⊕ n) ℂ, Zᴴ = Z → Ψ Z ∈ hermSub := by
    intro Z hZ
    have h11 : Z.toBlocks₁₁ᴴ = Z.toBlocks₁₁ := by
      ext i j
      have h := congrFun (congrFun hZ (Sum.inl i)) (Sum.inl j)
      simpa [Matrix.toBlocks₁₁, Matrix.conjTranspose_apply] using h
    have h12 : Z.toBlocks₁₂ᴴ = Z.toBlocks₂₁ := by
      ext i j
      have h := congrFun (congrFun hZ (Sum.inr i)) (Sum.inl j)
      simpa [Matrix.toBlocks₁₂, Matrix.toBlocks₂₁, Matrix.conjTranspose_apply] using h
    have h21 : Z.toBlocks₂₁ᴴ = Z.toBlocks₁₂ := by
      rw [← h12, conjTranspose_conjTranspose]
    show (Ψ Z)ᴴ = Ψ Z
    simp only [Ψ, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, h11, h12,
      h21]
    abel
  let M0 : Matrix (n ⊕ n) (n ⊕ n) ℂ := Matrix.fromBlocks q 0 0 (-q)
  let T : Matrix (n ⊕ n) (n ⊕ n) ℂ →ₗ[ℝ] (n → n → ℂ) × ℝ :=
    { toFun := fun Z => ((fun i j => Ψ Z i j), (Z * M0).trace.re)
      map_add' := fun Z Z' => by
        show ((fun i j => Ψ (Z + Z') i j), ((Z + Z') * M0).trace.re)
          = ((fun i j => Ψ Z i j), (Z * M0).trace.re) + ((fun i j => Ψ Z' i j), (Z' * M0).trace.re)
        rw [Prod.mk_add_mk, hΨadd, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
        rfl
      map_smul' := fun c Z => by
        show ((fun i j => Ψ (c • Z) i j), ((c • Z) * M0).trace.re)
          = c • ((fun i j => Ψ Z i j), (Z * M0).trace.re)
        rw [Prod.smul_mk, hΨsmul, Matrix.smul_mul, Matrix.trace_smul, Complex.smul_re]
        rfl }
  have hT : Continuous T := LinearMap.continuous_of_finiteDimensional T
  have hR : Continuous fun z : n ⊕ n → ℂ => rankOne z := by
    unfold rankOne
    fun_prop
  let G : (n ⊕ n → ℂ) → (n → n → ℂ) × ℝ := fun z => T (rankOne z)
  have hG : Continuous G := hT.comp hR
  let C : Set ((n → n → ℂ) × ℝ) := ({0} : Set (n → n → ℂ)) ×ˢ Set.Ici (0 : ℝ)
  have hCconv : Convex ℝ C := (convex_singleton 0).prod (convex_Ici 0)
  have hCcl : IsClosed C := isClosed_singleton.prod isClosed_Ici
  have hScpt : IsCompact (convexHull ℝ (G '' Metric.sphere (0 : n ⊕ n → ℂ) 1)) :=
    isCompact_convexHull_of_isCompact ((isCompact_sphere 0 1).image hG)
  by_cases hmeet : ∃ x ∈ convexHull ℝ (G '' Metric.sphere (0 : n ⊕ n → ℂ) 1), x ∈ C
  · -- a balancing matrix exists
    right
    obtain ⟨x, hxS, hx1, hx2⟩ := hmeet
    have hx1' : x.1 = 0 := Set.mem_singleton_iff.mp hx1
    have hx2' : 0 ≤ x.2 := Set.mem_Ici.mp hx2
    obtain ⟨ι, _, pts, w, hrange, -, hwpos, hw1, hsum⟩ := eq_pos_convex_span_of_mem_convexHull hxS
    have hp : ∀ i, pts i ∈ G '' Metric.sphere (0 : n ⊕ n → ℂ) 1 := fun i => hrange ⟨i, rfl⟩
    choose zz hzz hGz using hp
    have hGz' : ∀ i, T (rankOne (zz i)) = pts i := hGz
    obtain ⟨W, hWdef⟩ : ∃ W : Matrix (n ⊕ n) (n ⊕ n) ℂ, W = ∑ i, w i • rankOne (zz i) :=
      ⟨_, rfl⟩
    have hTW : T W = x := by
      rw [hWdef, ← hsum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hGz' i]
    have hΨW : Ψ W = 0 := by
      have h1 : (T W).1 = 0 := by rw [hTW]; exact hx1'
      ext i j
      exact congrFun (congrFun h1 i) j
    have hW2 : 0 ≤ (W * M0).trace.re := by
      have h2 : (W * M0).trace.re = x.2 := by
        show (T W).2 = x.2
        rw [hTW]
      rw [h2]
      exact hx2'
    have hWpsd : W.PosSemidef := by
      rw [hWdef]
      exact posSemidef_sum_smul_rankOne w (fun i => (hwpos i).le) zz
    have hne : ∀ i, zz i ≠ 0 := by
      intro i h
      have h1 := mem_sphere_zero_iff_norm.mp (hzz i)
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    obtain ⟨j0⟩ : Nonempty ι := by
      by_contra hne'
      rw [not_nonempty_iff] at hne'
      simp at hw1
    have htr1 : ∀ i, 0 < (rankOne (zz i)).trace.re := by
      intro i
      have e : (rankOne (zz i)).trace = star (zz i) ⬝ᵥ ((1 : Matrix (n ⊕ n) (n ⊕ n) ℂ) *ᵥ zz i) := by
        rw [← trace_mul_rankOne, Matrix.one_mul]
      rw [e]
      exact qf_pos Matrix.PosDef.one (hne i)
    have htr : 0 < W.trace.re := by
      rw [hWdef, Matrix.trace_sum, Complex.re_sum]
      refine Finset.sum_pos (fun i _ => ?_) ⟨j0, Finset.mem_univ _⟩
      rw [Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
      exact mul_pos (hwpos i) (htr1 i)
    have htrM : (W * M0).trace = (q * W.toBlocks₁₁).trace - (q * W.toBlocks₂₂).trace := by
      show (W * Matrix.fromBlocks q 0 0 (-q)).trace = _
      conv_lhs => rw [← Matrix.fromBlocks_toBlocks W]
      rw [Matrix.fromBlocks_multiply, trace_fromBlocks']
      simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.trace_neg]
      rw [Matrix.trace_mul_comm W.toBlocks₁₁, Matrix.trace_mul_comm W.toBlocks₂₂]
      ring
    refine ⟨W.toBlocks₁₁, W.toBlocks₁₂, W.toBlocks₂₁, W.toBlocks₂₂, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.fromBlocks_toBlocks]
      exact hWpsd
    · rw [Matrix.fromBlocks_toBlocks]
      intro h0
      rw [h0] at htr
      simp at htr
    · rw [htrM, Complex.sub_re] at hW2
      linarith
    · intro p _
      rw [trace_kyp_pairing]
      have h0 : W.toBlocks₁₁ * aᴴ + a * W.toBlocks₁₁ + W.toBlocks₁₂ * bᴴ + b * W.toBlocks₂₁ = 0 :=
        hΨW
      rw [h0, Matrix.mul_zero, Matrix.trace_zero, Complex.zero_re]
  · -- strict separation
    left
    have hdisj : Disjoint (convexHull ℝ (G '' Metric.sphere (0 : n ⊕ n → ℂ) 1)) C :=
      Set.disjoint_left.mpr fun x hxS hxC => hmeet ⟨x, hxS, hxC⟩
    obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
      geometric_hahn_banach_compact_closed (convex_convexHull ℝ _) hScpt hCconv hCcl hdisj
    have hv : v < 0 := by
      have h := hfv (0, 0) (Set.mk_mem_prod (Set.mem_singleton 0) (Set.mem_Ici.mpr le_rfl))
      rwa [Prod.mk_zero_zero, map_zero] at h
    obtain ⟨β, hβdef⟩ : ∃ β, β = f ((0 : n → n → ℂ), (1 : ℝ)) := ⟨_, rfl⟩
    have hf0t : ∀ t : ℝ, f ((0 : n → n → ℂ), t) = t * β := by
      intro t
      have e : ((0 : n → n → ℂ), t) = t • ((0 : n → n → ℂ), (1 : ℝ)) := by simp
      rw [e, map_smul, smul_eq_mul, hβdef]
    have hβ : 0 ≤ β := by
      by_contra hneg
      have hb : β < 0 := not_le.mp hneg
      have hmem : ((0 : n → n → ℂ), v / β) ∈ C :=
        Set.mk_mem_prod (Set.mem_singleton 0) (div_nonneg_of_nonpos hv.le hb.le)
      have h := hfv _ hmem
      rw [hf0t, div_mul_cancel₀ v hb.ne] at h
      exact lt_irrefl v h
    let Φt : Matrix n n ℂ →ₗ[ℝ] (n → n → ℂ) :=
      { toFun := fun A i j => A i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let L : Matrix n n ℂ →ₗ[ℝ] ℝ :=
      (f : (n → n → ℂ) × ℝ →ₗ[ℝ] ℝ) ∘ₗ ((LinearMap.inl ℝ (n → n → ℂ) ℝ) ∘ₗ Φt)
    obtain ⟨H, hHerm, hrep⟩ := exists_hermitian_trace_rep L
    have hsplit : ∀ Z, f (T Z) = L (Ψ Z) + (T Z).2 * β := by
      intro Z
      have e : T Z = (Φt (Ψ Z), (0 : ℝ)) + (T Z).2 • ((0 : n → n → ℂ), (1 : ℝ)) := by
        refine Prod.ext ?_ ?_
        · show (fun i j => Ψ Z i j) = Φt (Ψ Z) + (T Z).2 • (0 : n → n → ℂ)
          rw [smul_zero, add_zero]
          rfl
        · show (T Z).2 = 0 + (T Z).2 * 1
          ring
      conv_lhs => rw [e]
      rw [map_add, map_smul, smul_eq_mul, ← hβdef]
      all_goals rfl
    have hfz : ∀ z : n ⊕ n → ℂ, f (T (rankOne z))
        = qf (Matrix.fromBlocks (aᴴ * H + H * a) (H * b) (bᴴ * H) 0) z + β * qf M0 z := by
      intro z
      rw [hsplit]
      have hΨh := hΨherm _ (conjTranspose_rankOne z)
      have h1 : L (Ψ (rankOne z))
          = qf (Matrix.fromBlocks (aᴴ * H + H * a) (H * b) (bᴴ * H) 0) z := by
        rw [hrep _ hΨh]
        have hp := trace_kyp_pairing (rankOne z).toBlocks₁₁ (rankOne z).toBlocks₁₂
          (rankOne z).toBlocks₂₁ (rankOne z).toBlocks₂₂ a b H
        rw [Matrix.fromBlocks_toBlocks] at hp
        have e : (H * Ψ (rankOne z)).trace
            = (rankOne z * Matrix.fromBlocks (aᴴ * H + H * a) (H * b) (bᴴ * H) 0).trace :=
          hp.symm
        rw [e, Matrix.trace_mul_comm, trace_mul_rankOne]
        rfl
      have h2 : (T (rankOne z)).2 = qf M0 z := by
        show (rankOne z * M0).trace.re = _
        rw [Matrix.trace_mul_comm, trace_mul_rankOne]
        rfl
      rw [h1, h2]
      ring
    have hfu' : ∀ z ∈ Metric.sphere (0 : n ⊕ n → ℂ) 1, f (T (rankOne z)) < u :=
      fun z hz => hfu _ (subset_convexHull ℝ _ ⟨z, hz, rfl⟩)
    have hu0 : u < 0 := huv.trans hv
    have hβpos : 0 < β := by
      rcases hβ.lt_or_eq with hpos | hzero
      · exact hpos
      exfalso
      let w0 : n ⊕ n → ℂ := Sum.elim 0 (Pi.single i0 1)
      have hw0 : w0 ≠ 0 := by
        intro h
        have := congrFun h (Sum.inr i0)
        simp [w0] at this
      have hq0 : qf (Matrix.fromBlocks (aᴴ * H + H * a) (H * b) (bᴴ * H) 0) w0 = 0 := by
        simp [qf, w0, Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
      have hnw : 0 < ‖w0‖ := norm_pos_iff.mpr hw0
      have hunit : ‖w0‖⁻¹ • w0 ∈ Metric.sphere (0 : n ⊕ n → ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnw.ne']
      have h := hfu' _ hunit
      rw [hfz, ← hzero, zero_mul, add_zero, qf_smul, hq0, mul_zero] at h
      linarith
    obtain ⟨p, hpdef⟩ : ∃ p : Matrix n n ℂ, p = β⁻¹ • H := ⟨_, rfl⟩
    have hp : p.IsHermitian := by
      show pᴴ = p
      rw [hpdef, conjTranspose_smul, star_trivial, hHerm.eq]
    refine ⟨p, hp, ?_⟩
    have hL : Matrix.fromBlocks (aᴴ * p + p * a + q) (p * b) (bᴴ * p) (-q)
        = β⁻¹ • (Matrix.fromBlocks (aᴴ * H + H * a) (H * b) (bᴴ * H) 0 + β • M0) := by
      show _ = β⁻¹ • (Matrix.fromBlocks (aᴴ * H + H * a) (H * b) (bᴴ * H) 0
        + β • Matrix.fromBlocks q 0 0 (-q))
      rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_add, Matrix.fromBlocks_smul, hpdef]
      rw [Matrix.fromBlocks_inj]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp [smul_add, smul_smul, inv_mul_cancel₀ hβpos.ne', Matrix.mul_smul, Matrix.smul_mul]
    have hherm : (Matrix.fromBlocks (aᴴ * p + p * a + q) (p * b) (bᴴ * p) (-q)).IsHermitian := by
      show (Matrix.fromBlocks (aᴴ * p + p * a + q) (p * b) (bᴴ * p) (-q))ᴴ = _
      rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_inj]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        (simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
          conjTranspose_neg, hp.eq, hq.eq]; try abel)
    have hneg_unit : ∀ z ∈ Metric.sphere (0 : n ⊕ n → ℂ) 1,
        qf (Matrix.fromBlocks (aᴴ * p + p * a + q) (p * b) (bᴴ * p) (-q)) z < 0 := by
      intro z hz
      rw [hL, qf_smul_left, qf_add_left, qf_smul_left, ← hfz z]
      exact mul_neg_of_pos_of_neg (inv_pos.mpr hβpos) ((hfu' z hz).trans hu0)
    have hherm' : (-(Matrix.fromBlocks (aᴴ * p + p * a + q) (p * b) (bᴴ * p) (-q))).IsHermitian := by
      show (-(Matrix.fromBlocks (aᴴ * p + p * a + q) (p * b) (bᴴ * p) (-q)))ᴴ = _
      rw [conjTranspose_neg, hherm.eq]
    refine posDef_of_qf_pos hherm' fun z hz => ?_
    have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hunit : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : n ⊕ n → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnz.ne']
    have h := hneg_unit _ hunit
    rw [qf_smul] at h
    have hs : 0 < ‖z‖⁻¹ ^ 2 := by positivity
    rw [qf_neg_left]
    nlinarith

omit [DecidableEq n] in
/-- `tr(Xᴴ q X)` is the sum of the column quadratic forms. -/
theorem trace_conjTranspose_mul_mul {r : Type*} [Fintype r] (q : Matrix n n ℂ)
    (X : Matrix n r ℂ) :
    (Xᴴ * q * X).trace = ∑ k, star (fun i => X i k) ⬝ᵥ (q *ᵥ fun i => X i k) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    dotProduct, Matrix.mulVec, Pi.star_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

omit [DecidableEq n] in
theorem trace_re_eq_sum_qf {r : Type*} [Fintype r] (q : Matrix n n ℂ) (X : Matrix n r ℂ) :
    (Xᴴ * q * X).trace.re = ∑ k, qf q (fun i => X i k) := by
  rw [trace_conjTranspose_mul_mul, Complex.re_sum]
  rfl

omit [DecidableEq n] in
/-- Unitary invariance of `tr(Xᴴ q X)`. -/
theorem trace_conj_unitary {r : Type*} [Fintype r] [DecidableEq r] (q : Matrix n n ℂ)
    (X : Matrix n r ℂ) {V : Matrix r r ℂ} (hV : V * Vᴴ = 1) :
    ((X * V)ᴴ * q * (X * V)).trace = (Xᴴ * q * X).trace := by
  have e : (X * V)ᴴ * q * (X * V) = Vᴴ * ((Xᴴ * q * X) * V) := by
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm Vᴴ, Matrix.mul_assoc (Xᴴ * q * X) V Vᴴ, hV, Matrix.mul_one]

/-- Columns of `V` are eigenvectors when `X V = V diag(d)`. -/
theorem mulVec_col_of_mul_diagonal {r : Type*} [Fintype r] [DecidableEq r]
    {X V : Matrix r r ℂ} {d : r → ℂ} (h : X * V = V * diagonal d) (m : r) :
    X *ᵥ (fun i => V i m) = d m • (fun i => V i m) := by
  ext i
  have h1 := congrFun (congrFun h i) m
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at h1
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [h1]
  ring

/-- KYP extraction when `aF + bH = FC` with `C` skew-Hermitian: over an
orthonormal eigenbasis of `-iC` every column is a frequency vector. -/
theorem kyp_trace_ineq_skew {r : Type*} [Fintype r] [DecidableEq r] {a b q : Matrix n n ℂ}
    {γ : ℝ}
    (hfreq : ∀ (ω : ℝ) (x u : n → ℂ),
      (((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - a) *ᵥ x = b *ᵥ u →
        qf q x ≤ γ ^ 2 * qf q u)
    {F H : Matrix n r ℂ} {C : Matrix r r ℂ} (hC : Cᴴ = -C) (hZ : a * F + b * H = F * C) :
    (Fᴴ * q * F).trace.re ≤ γ ^ 2 * (Hᴴ * q * H).trace.re := by
  set M : Matrix r r ℂ := (-Complex.I) • C with hMdef
  have hM : M.IsHermitian := by
    show Mᴴ = M
    rw [hMdef, conjTranspose_smul, hC]
    first
      | simp
      | simp [Complex.star_def]
  have hCM : C = Complex.I • M := by
    rw [hMdef, smul_smul]
    simp
  set V : Matrix r r ℂ := (hM.eigenvectorUnitary : Matrix r r ℂ) with hVdef
  have hVs : V * Vᴴ = 1 := by
    first
      | exact Matrix.mem_unitaryGroup_iff.mp hM.eigenvectorUnitary.2
      | exact Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.2
      | exact unitary.mul_star_self_of_mem hM.eigenvectorUnitary.2
  have hsV : Vᴴ * V = 1 := by
    first
      | exact Matrix.mem_unitaryGroup_iff'.mp hM.eigenvectorUnitary.2
      | exact Unitary.star_mul_self_of_mem hM.eigenvectorUnitary.2
      | exact unitary.star_mul_self_of_mem hM.eigenvectorUnitary.2
  have hspec : M = V * diagonal (RCLike.ofReal ∘ hM.eigenvalues) * Vᴴ := by
    have h := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hMV : M * V = V * diagonal (RCLike.ofReal ∘ hM.eigenvalues) := by
    conv_lhs => rw [hspec]
    rw [Matrix.mul_assoc _ Vᴴ V, hsV, Matrix.mul_one]
  have hCV : C * V = V * diagonal (fun m => Complex.I * (RCLike.ofReal ∘ hM.eigenvalues) m) := by
    rw [hCM, Matrix.smul_mul, hMV]
    ext i j
    simp only [Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
    ring
  have hstep : ∀ m, qf q (F *ᵥ (fun i => V i m)) ≤ γ ^ 2 * qf q (H *ᵥ (fun i => V i m)) := by
    intro m
    have hcm : C *ᵥ (fun i => V i m)
        = (Complex.I * (RCLike.ofReal ∘ hM.eigenvalues) m) • (fun i => V i m) :=
      mulVec_col_of_mul_diagonal hCV m
    have hω : Complex.I * (RCLike.ofReal ∘ hM.eigenvalues) m
        = ((hM.eigenvalues m : ℝ) : ℂ) * Complex.I := by
      rw [mul_comm]
      rfl
    have e : a *ᵥ (F *ᵥ (fun i => V i m)) + b *ᵥ (H *ᵥ (fun i => V i m))
        = F *ᵥ (C *ᵥ (fun i => V i m)) := by
      simp only [Matrix.mulVec_mulVec]
      rw [← Matrix.add_mulVec, hZ]
    rw [hcm, Matrix.mulVec_smul] at e
    apply hfreq (hM.eigenvalues m)
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← hω, ← e]
    abel
  have colF : ∀ m, (fun i => (F * V) i m) = F *ᵥ (fun i => V i m) := by
    intro m
    funext i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have colH : ∀ m, (fun i => (H * V) i m) = H *ᵥ (fun i => V i m) := by
    intro m
    funext i
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [← trace_conj_unitary q F hVs, ← trace_conj_unitary q H hVs, trace_re_eq_sum_qf,
    trace_re_eq_sum_qf, Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  show qf q (fun i => (F * V) i m) ≤ γ ^ 2 * qf q (fun i => (H * V) i m)
  rw [colF m, colH m]
  exact hstep m

/-- KYP extraction when `FᴴF = diag(d)` (orthogonal columns): zero the
columns of `H` where `d = 0`, then `C = diag(d⁺) Fᴴ Z'` is skew-Hermitian
and `Z' = F C`. -/
theorem kyp_trace_ineq_orth {r : Type*} [Fintype r] [DecidableEq r] {a b q : Matrix n n ℂ}
    (hq : q.PosDef) {γ : ℝ}
    (hfreq : ∀ (ω : ℝ) (x u : n → ℂ),
      (((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - a) *ᵥ x = b *ᵥ u →
        qf q x ≤ γ ^ 2 * qf q u)
    {F H : Matrix n r ℂ} {d : r → ℝ} (hd : Fᴴ * F = diagonal (fun k => ((d k : ℝ) : ℂ)))
    (hcon : (a * F + b * H) * Fᴴ + F * (a * F + b * H)ᴴ = 0) :
    (Fᴴ * q * F).trace.re ≤ γ ^ 2 * (Hᴴ * q * H).trace.re := by
  let p : r → ℂ := fun k => if d k = 0 then 0 else 1
  let dinv : r → ℂ := fun k => if d k = 0 then 0 else (((d k)⁻¹ : ℝ) : ℂ)
  have hfk : ∀ k, d k = 0 → ∀ i, F i k = 0 := by
    intro k hk i
    by_contra hne
    have hcol : (fun i => F i k) ≠ 0 := fun h0 => hne (congrFun h0 i)
    have h1 := qf_pos Matrix.PosDef.one hcol
    have h2 : qf 1 (fun i => F i k) = d k := by
      have hkk := congrFun (congrFun hd k) k
      simp only [diagonal_apply_eq] at hkk
      have e : star (fun i => F i k) ⬝ᵥ (fun i => F i k) = (Fᴴ * F) k k := by
        simp [Matrix.mul_apply, dotProduct, Matrix.conjTranspose_apply]
      unfold qf
      rw [Matrix.one_mulVec, e, hkk, Complex.ofReal_re]
    rw [h2, hk] at h1
    exact lt_irrefl 0 h1
  have hFp : F * diagonal p = F := by
    ext i k
    rw [Matrix.mul_diagonal]
    by_cases hk : d k = 0
    · simp [p, hk, hfk k hk i]
    · simp [p, hk]
  have hpp : diagonal p * diagonal p = diagonal p := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext k
    by_cases hk : d k = 0 <;> simp [p, hk]
  have hpH : (diagonal p)ᴴ = diagonal p := by
    rw [diagonal_conjTranspose]
    congr 1
    funext k
    by_cases hk : d k = 0 <;> simp [p, hk]
  have hDinvH : (diagonal dinv)ᴴ = diagonal dinv := by
    rw [diagonal_conjTranspose]
    congr 1
    funext k
    by_cases hk : d k = 0 <;> first | simp [dinv, hk] | simp [dinv, hk, Complex.star_def]
  have hDinv : diagonal (fun k => ((d k : ℝ) : ℂ)) * diagonal dinv = diagonal p := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext k
    by_cases hk : d k = 0
    · simp [p, dinv, hk]
    · show (d k : ℂ) * (if d k = 0 then 0 else (((d k)⁻¹ : ℝ) : ℂ))
          = (if d k = 0 then 0 else 1)
      rw [if_neg hk, if_neg hk, ← Complex.ofReal_mul, mul_inv_cancel₀ hk, Complex.ofReal_one]
  have hinvD : diagonal dinv * diagonal (fun k => ((d k : ℝ) : ℂ)) = diagonal p := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext k
    by_cases hk : d k = 0
    · simp [p, dinv, hk]
    · show (if d k = 0 then 0 else (((d k)⁻¹ : ℝ) : ℂ)) * (d k : ℂ)
          = (if d k = 0 then 0 else 1)
      rw [if_neg hk, if_neg hk, ← Complex.ofReal_mul, inv_mul_cancel₀ hk, Complex.ofReal_one]
  have hDF : diagonal p * Fᴴ = Fᴴ := by
    have h := congrArg conjTranspose hFp
    rwa [conjTranspose_mul, hpH] at h
  set Z := a * F + b * H with hZdef
  have hZ' : a * F + b * (H * diagonal p) = Z * diagonal p := by
    rw [hZdef, Matrix.add_mul, Matrix.mul_assoc a F (diagonal p), hFp,
      Matrix.mul_assoc b H (diagonal p)]
  have hcon' : (Z * diagonal p) * Fᴴ + F * (Z * diagonal p)ᴴ = 0 := by
    rw [Matrix.mul_assoc Z (diagonal p) Fᴴ, hDF, conjTranspose_mul, hpH,
      ← Matrix.mul_assoc F (diagonal p) Zᴴ, hFp]
    exact hcon
  set Z' := Z * diagonal p with hZ'def
  have hZ'p : Z' * diagonal p = Z' := by
    rw [hZ'def, Matrix.mul_assoc Z (diagonal p) (diagonal p), hpp]
  have hpZ : diagonal p * Z'ᴴ = Z'ᴴ := by
    have h := congrArg conjTranspose hZ'p
    rwa [conjTranspose_mul, hpH] at h
  have hc1 : Z' * Fᴴ = -(F * Z'ᴴ) := eq_neg_of_add_eq_zero_left hcon'
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = -(Z'ᴴ * F * diagonal dinv) := ⟨_, rfl⟩
  have hY : Z' = F * Y := by
    have h1 : Z' * Fᴴ * F = -(F * Z'ᴴ * F) := by
      rw [hc1, Matrix.neg_mul]
    have h2 : Z' * Fᴴ * F * diagonal dinv = Z' := by
      rw [Matrix.mul_assoc Z' Fᴴ F, hd,
        Matrix.mul_assoc Z' (diagonal fun k => ((d k : ℝ) : ℂ)) (diagonal dinv), hDinv, hZ'p]
    rw [hYdef]
    calc Z' = Z' * Fᴴ * F * diagonal dinv := h2.symm
      _ = -(F * Z'ᴴ * F) * diagonal dinv := by rw [h1]
      _ = F * -(Z'ᴴ * F * diagonal dinv) := by
          simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  have hC : diagonal dinv * Fᴴ * Z' = diagonal p * Y := by
    conv_lhs => rw [hY]
    rw [Matrix.mul_assoc (diagonal dinv) Fᴴ (F * Y), ← Matrix.mul_assoc Fᴴ F Y, hd,
      ← Matrix.mul_assoc (diagonal dinv), hinvD]
  have hFC : F * (diagonal dinv * Fᴴ * Z') = Z' := by
    rw [hC, ← Matrix.mul_assoc F (diagonal p) Y, hFp, ← hY]
  have hskew : (diagonal dinv * Fᴴ * Z')ᴴ = -(diagonal dinv * Fᴴ * Z') := by
    have key : diagonal dinv * Fᴴ * (Z' * Fᴴ) * F * diagonal dinv
        = diagonal dinv * Fᴴ * (-(F * Z'ᴴ)) * F * diagonal dinv := by
      rw [hc1]
    have lhs : diagonal dinv * Fᴴ * (Z' * Fᴴ) * F * diagonal dinv
        = diagonal dinv * Fᴴ * Z' := by
      calc _ = diagonal dinv * Fᴴ * Z' * ((Fᴴ * F) * diagonal dinv) := by
            simp only [Matrix.mul_assoc]
        _ = diagonal dinv * Fᴴ * Z' := by
            rw [hd, hDinv, Matrix.mul_assoc (diagonal dinv * Fᴴ) Z' (diagonal p), hZ'p]
    have rhs : diagonal dinv * Fᴴ * (-(F * Z'ᴴ)) * F * diagonal dinv
        = -(Z'ᴴ * F * diagonal dinv) := by
      calc _ = -((diagonal dinv * (Fᴴ * F)) * Z'ᴴ * F * diagonal dinv) := by
            simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
        _ = -(Z'ᴴ * F * diagonal dinv) := by
            rw [hd, hinvD, hpZ]
    rw [lhs, rhs] at key
    conv_rhs => rw [key]
    simp only [neg_neg, conjTranspose_mul, conjTranspose_conjTranspose, hDinvH,
      Matrix.mul_assoc]
  have hle := kyp_trace_ineq_skew hfreq hskew (hZ'.trans hFC.symm)
  have hcolH : ∀ k, qf q (fun i => (H * diagonal p) i k) ≤ qf q (fun i => H i k) := by
    intro k
    by_cases hk : d k = 0
    · have e : (fun i => (H * diagonal p) i k) = 0 := by
        funext i
        simp [Matrix.mul_diagonal, p, hk]
      have hq0 : qf q 0 = 0 := by simp [qf]
      rw [e, hq0]
      exact qf_nonneg hq _
    · have e : (fun i => (H * diagonal p) i k) = fun i => H i k := by
        funext i
        simp [Matrix.mul_diagonal, p, hk]
      rw [e]
  have hHH : ((H * diagonal p)ᴴ * q * (H * diagonal p)).trace.re ≤ (Hᴴ * q * H).trace.re := by
    rw [trace_re_eq_sum_qf, trace_re_eq_sum_qf]
    exact Finset.sum_le_sum fun k _ => hcolH k
  exact hle.trans (mul_le_mul_of_nonneg_left hHH (sq_nonneg γ))

/-- Core of the KYP extraction: for rectangular `F, H` with
`(aF + bH)Fᴴ + F(aF + bH)ᴴ = 0`, `Re tr(FᴴqF) ≤ γ² Re tr(HᴴqH)`.  Rotate by
the eigenvector unitary of `FᴴF` and apply `kyp_trace_ineq_orth`. -/
theorem kyp_trace_ineq {r : Type*} [Fintype r] [DecidableEq r] {a b q : Matrix n n ℂ}
    (hq : q.PosDef) {γ : ℝ}
    (hfreq : ∀ (ω : ℝ) (x u : n → ℂ),
      (((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - a) *ᵥ x = b *ᵥ u →
        qf q x ≤ γ ^ 2 * qf q u)
    {F H : Matrix n r ℂ} (hcon : (a * F + b * H) * Fᴴ + F * (a * F + b * H)ᴴ = 0) :
    (Fᴴ * q * F).trace.re ≤ γ ^ 2 * (Hᴴ * q * H).trace.re := by
  have hG : (Fᴴ * F).IsHermitian := by
    show (Fᴴ * F)ᴴ = Fᴴ * F
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  set U : Matrix r r ℂ := (hG.eigenvectorUnitary : Matrix r r ℂ) with hUdef
  have hUs : U * Uᴴ = 1 := by
    first
      | exact Matrix.mem_unitaryGroup_iff.mp hG.eigenvectorUnitary.2
      | exact Unitary.mul_star_self_of_mem hG.eigenvectorUnitary.2
      | exact unitary.mul_star_self_of_mem hG.eigenvectorUnitary.2
  have hsU : Uᴴ * U = 1 := by
    first
      | exact Matrix.mem_unitaryGroup_iff'.mp hG.eigenvectorUnitary.2
      | exact Unitary.star_mul_self_of_mem hG.eigenvectorUnitary.2
      | exact unitary.star_mul_self_of_mem hG.eigenvectorUnitary.2
  have hspec : Fᴴ * F = U * diagonal (RCLike.ofReal ∘ hG.eigenvalues) * Uᴴ := by
    have h := hG.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hd : (F * U)ᴴ * (F * U) = diagonal (fun k => ((hG.eigenvalues k : ℝ) : ℂ)) := by
    calc (F * U)ᴴ * (F * U) = Uᴴ * (Fᴴ * F) * U := by
          rw [conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Uᴴ * (U * diagonal (RCLike.ofReal ∘ hG.eigenvalues) * Uᴴ) * U :=
          congrArg (fun X => Uᴴ * X * U) hspec
      _ = diagonal (RCLike.ofReal ∘ hG.eigenvalues) := by
          simp only [← Matrix.mul_assoc]
          rw [hsU, Matrix.one_mul, Matrix.mul_assoc _ Uᴴ U, hsU, Matrix.mul_one]
      _ = _ := rfl
  have hcon' : (a * (F * U) + b * (H * U)) * (F * U)ᴴ
      + (F * U) * (a * (F * U) + b * (H * U))ᴴ = 0 := by
    have e1 : a * (F * U) + b * (H * U) = (a * F + b * H) * U := by
      simp only [Matrix.add_mul, Matrix.mul_assoc]
    rw [e1]
    simp only [conjTranspose_mul]
    have e2 : (a * F + b * H) * U * (Uᴴ * Fᴴ) = (a * F + b * H) * Fᴴ := by
      rw [Matrix.mul_assoc (a * F + b * H) U, ← Matrix.mul_assoc U Uᴴ, hUs, Matrix.one_mul]
    have e3 : F * U * (Uᴴ * (a * F + b * H)ᴴ) = F * (a * F + b * H)ᴴ := by
      rw [Matrix.mul_assoc F U, ← Matrix.mul_assoc U Uᴴ, hUs, Matrix.one_mul]
    rw [e2, e3]
    exact hcon
  have h := kyp_trace_ineq_orth hq hfreq (d := hG.eigenvalues) hd hcon'
  rwa [trace_conj_unitary q F hUs, trace_conj_unitary q H hUs] at h

/-- Extraction step of KYP: `W = YYᴴ` with row blocks `F, H`; then
`tr(qW₁₁) ≤ γ² tr(qW₂₂)` (`kyp_trace_ineq`) and the trace hypothesis force
all columns of `F, H` to vanish. -/
theorem kyp_extraction {a b q : Matrix n n ℂ} (ha : ∀ μ ∈ spectrum ℂ a, μ.re < 0)
    (hq : q.PosDef) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < 1)
    (hfreq : ∀ (ω : ℝ) (x u : n → ℂ),
      (((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - a) *ᵥ x = b *ᵥ u →
        qf q x ≤ γ ^ 2 * qf q u)
    {W11 W12 W21 W22 : Matrix n n ℂ} (hW : (Matrix.fromBlocks W11 W12 W21 W22).PosSemidef)
    (hcon : W11 * aᴴ + a * W11 + W12 * bᴴ + b * W21 = 0)
    (htr : (q * W22).trace.re ≤ (q * W11).trace.re) :
    Matrix.fromBlocks W11 W12 W21 W22 = 0 := by
  obtain ⟨B, hWB⟩ := exists_eq_conjTranspose_mul_self hW
  let F : Matrix n (n ⊕ n) ℂ := Matrix.of fun i k => star (B k (Sum.inl i))
  let H : Matrix n (n ⊕ n) ℂ := Matrix.of fun i k => star (B k (Sum.inr i))
  have e11 : W11 = F * Fᴴ := by
    ext i j
    have h := congrFun (congrFun hWB (Sum.inl i)) (Sum.inl j)
    simpa [F, Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  have e12 : W12 = F * Hᴴ := by
    ext i j
    have h := congrFun (congrFun hWB (Sum.inl i)) (Sum.inr j)
    simpa [F, H, Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  have e21 : W21 = H * Fᴴ := by
    ext i j
    have h := congrFun (congrFun hWB (Sum.inr i)) (Sum.inl j)
    simpa [F, H, Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  have e22 : W22 = H * Hᴴ := by
    ext i j
    have h := congrFun (congrFun hWB (Sum.inr i)) (Sum.inr j)
    simpa [H, Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  have hcon' : (a * F + b * H) * Fᴴ + F * (a * F + b * H)ᴴ = 0 := by
    rw [← hcon, e11, e12, e21]
    simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_assoc]
    abel
  have hineq := kyp_trace_ineq hq hfreq hcon'
  have tr11 : (q * W11).trace = (Fᴴ * q * F).trace := by
    rw [e11, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have tr22 : (q * W22).trace = (Hᴴ * q * H).trace := by
    rw [e22, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [tr11, tr22] at htr
  have hcolF := trace_conjTranspose_mul_mul q F
  have hcolH := trace_conjTranspose_mul_mul q H
  have hnnF : ∀ k, 0 ≤ qf q (fun i => F i k) := fun k => qf_nonneg hq _
  have hnnH : ∀ k, 0 ≤ qf q (fun i => H i k) := fun k => qf_nonneg hq _
  have hreF : (Fᴴ * q * F).trace.re = ∑ k, qf q (fun i => F i k) := by
    rw [hcolF, Complex.re_sum]
    rfl
  have hreH : (Hᴴ * q * H).trace.re = ∑ k, qf q (fun i => H i k) := by
    rw [hcolH, Complex.re_sum]
    rfl
  have hHnn : 0 ≤ (Hᴴ * q * H).trace.re := by
    rw [hreH]
    exact Finset.sum_nonneg fun k _ => hnnH k
  have hγ2 : γ ^ 2 < 1 := by nlinarith
  have hH0 : (Hᴴ * q * H).trace.re = 0 := by nlinarith
  have hF0 : (Fᴴ * q * F).trace.re = 0 := by
    have hFnn : 0 ≤ (Fᴴ * q * F).trace.re := by
      rw [hreF]
      exact Finset.sum_nonneg fun k _ => hnnF k
    nlinarith
  have colzero : ∀ (X : Matrix n (n ⊕ n) ℂ),
      ∑ k, qf q (fun i => X i k) = 0 → X = 0 := by
    intro X hX
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => qf_nonneg hq _)).mp hX
    ext i k
    by_contra hne
    have hcol : (fun i => X i k) ≠ 0 := by
      intro h0
      exact hne (congrFun h0 i)
    have := qf_pos hq hcol
    rw [hall k (Finset.mem_univ _)] at this
    exact lt_irrefl _ this
  have hF : F = 0 := colzero F (hreF ▸ hF0)
  have hH : H = 0 := colzero H (hreH ▸ hH0)
  rw [e11, e12, e21, e22, hF, hH]
  simp

omit [DecidableEq n] in
theorem isHermitian_map_re {M : Matrix n n ℂ} (h : M.IsHermitian) :
    (M.map Complex.re).IsHermitian := by
  ext i j
  have hij := congrFun (congrFun h.eq i) j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial]
  rw [← hij, Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re]

omit [DecidableEq n] in
/-- Real vectors only see the real part: `Re(wᴴ M w) = wᵀ (Re M) w`. -/
theorem qf_ofReal (M : Matrix n n ℂ) (w : n → ℝ) :
    qf M (fun i => (w i : ℂ)) = w ⬝ᵥ (M.map Complex.re *ᵥ w) := by
  simp [qf, dotProduct, Matrix.mulVec, Complex.re_sum, Complex.mul_re]

omit [DecidableEq n] in
/-- Realification: for real data, `P = Re p` solves the real LMI whenever
the complex Hermitian `p` solves the complex one. -/
theorem lmi_real_of_complex {A B Q : Matrix n n ℝ} {p : Matrix n n ℂ} (hp : p.IsHermitian)
    (h : (-(Matrix.fromBlocks ((cplx A)ᴴ * p + p * cplx A + cplx Q) (p * cplx B)
      ((cplx B)ᴴ * p) (-cplx Q))).PosDef) :
    ∃ P : Matrix n n ℝ, Pᵀ = P ∧
      (-(Matrix.fromBlocks (Aᵀ * P + P * A + Q) (P * B) (Bᵀ * P) (-Q))).PosDef := by
  refine ⟨p.map Complex.re, ?_, ?_⟩
  · have hs := isHermitian_map_re hp
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at hs
  · have hre : (-(Matrix.fromBlocks ((cplx A)ᴴ * p + p * cplx A + cplx Q) (p * cplx B)
        ((cplx B)ᴴ * p) (-cplx Q))).map Complex.re
        = -(Matrix.fromBlocks (Aᵀ * p.map Complex.re + p.map Complex.re * A + Q)
            (p.map Complex.re * B) (Bᵀ * p.map Complex.re) (-Q)) := by
      ext (i | i) (j | j) <;>
        simp [Matrix.mul_apply, Complex.re_sum, Complex.mul_re, cplx,
          Matrix.conjTranspose_apply]
    rw [← hre]
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (isHermitian_map_re h.isHermitian)
      fun w hw => ?_
    rw [star_trivial, ← qf_ofReal]
    refine qf_pos h ?_
    intro h0
    apply hw
    funext i
    have hi := congrFun h0 i
    simpa using hi

/-- KYP core: the frequency bound gives a symmetric `P` satisfying the strict
LMI.  Assembled from the four steps above. -/
theorem exists_lmi_of_boundedReal {A B : Matrix n n ℝ} (hA : IsHurwitz A)
    {Q : Matrix n n ℝ} (hQ : Q.PosDef)
    (hsup : (⨆ ω : ℝ, metricGain (cplx Q) (resolvent A B ω)) < 1) :
    ∃ P : Matrix n n ℝ, Pᵀ = P ∧
      (-(Matrix.fromBlocks (Aᵀ * P + P * A + Q) (P * B) (Bᵀ * P) (-Q))).PosDef := by
  have hQc := posDef_cplx_of_posDef hQ
  have hbdd : BddAbove (Set.range fun ω => metricGain (cplx Q) (resolvent A B ω)) :=
    ⟨familyGain (cplx Q) (resolventFamily A B), by
      rintro _ ⟨ω, rfl⟩
      exact metricGain_le_familyGain (isCompact_resolventFamily hA B) hQc
        (Set.mem_union_left _ (Set.mem_range_self ω))⟩
  have hfreq : ∀ (ω : ℝ) (x u : n → ℂ),
      (((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - cplx A) *ᵥ x = cplx B *ᵥ u →
        qf (cplx Q) x
          ≤ (⨆ ω : ℝ, metricGain (cplx Q) (resolvent A B ω)) ^ 2 * qf (cplx Q) u := by
    intro ω x u hxu
    have hdet := det_resolvent_ne_zero hA ω
    have hx : x = resolvent A B ω *ᵥ u := by
      unfold resolvent
      rw [← Matrix.mulVec_mulVec, ← hxu, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
    rw [hx, ← qf_conj]
    calc qf ((resolvent A B ω)ᴴ * cplx Q * resolvent A B ω) u
        ≤ metricGain (cplx Q) (resolvent A B ω) ^ 2 * qf (cplx Q) u :=
          qf_le_metricGain_sq hQc _ u
      _ ≤ (⨆ ω : ℝ, metricGain (cplx Q) (resolvent A B ω)) ^ 2 * qf (cplx Q) u :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (metricGain_nonneg _ _) (le_ciSup hbdd ω) 2) (qf_nonneg hQc u)
  rcases kyp_alternative (cplx A) (cplx B) (cplx Q) hQc.isHermitian with
    ⟨p, hp, hlmi⟩ | ⟨W11, W12, W21, W22, hW, hne, htr, hpair⟩
  · exact lmi_real_of_complex hp hlmi
  · exfalso
    have hblocks := hW.isHermitian.eq
    rw [Matrix.fromBlocks_conjTranspose] at hblocks
    obtain ⟨h11, -, h21, -⟩ := Matrix.fromBlocks_inj.mp hblocks
    have hcon := kyp_constraint h11 h21 hpair
    exact hne (kyp_extraction hA hQc (Real.iSup_nonneg fun _ => metricGain_nonneg _ _)
      hsup hfreq hW hcon htr)

/-- KYP half of Lemma brl, from the LMI core and the Schur step. -/
theorem exists_ari_of_boundedReal {A B : Matrix n n ℝ} (hA : IsHurwitz A)
    {Q : Matrix n n ℝ} (hQ : Q.PosDef)
    (hsup : (⨆ ω : ℝ, metricGain (cplx Q) (resolvent A B ω)) < 1) :
    ∃ P : Matrix n n ℝ, Pᵀ = P ∧
      (-(Aᵀ * P + P * A + Q + P * B * Q⁻¹ * Bᵀ * P)).PosDef := by
  obtain ⟨P, hPt, hlmi⟩ := exists_lmi_of_boundedReal hA hQ hsup
  have hX : (Aᵀ * P + P * A + Q)ᵀ = Aᵀ * P + P * A + Q := by
    rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hPt, transpose_eq_of_posDef hQ]
    abel
  exact ⟨P, hPt, ari_of_lmi_real hX hPt hQ hlmi⟩

omit [DecidableEq n] in
theorem qf_add_of_isHermitian {H : Matrix n n ℂ} (hH : H.IsHermitian) (u w : n → ℂ) :
    qf H (u + w) = qf H u + qf H w + 2 * (star w ⬝ᵥ (H *ᵥ u)).re := by
  have hc := dotProduct_mulVec_swap hH u w
  unfold qf
  rw [star_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hc]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

/-- Powers of a matrix with spectrum in the open unit disk send every vector
to `0` (Gelfand's formula in the `ℓ∞` operator norm). -/
theorem tendsto_pow_mulVec_zero {S : Matrix n n ℂ} (h : ∀ μ ∈ spectrum ℂ S, ‖μ‖ < 1)
    (x : n → ℂ) : Filter.Tendsto (fun k : ℕ => (S ^ k) *ᵥ x) Filter.atTop (nhds 0) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 : ∀ k : ℕ, (S ^ k) *ᵥ x = 0 := fun k => Subsingleton.elim _ _
    simp only [h0]
    exact tendsto_const_nhds
  obtain ⟨μ0, hμ0, hρ⟩ := exists_mem_spectrum_norm_eq_specRad S
  have hρ1 : specRad S < 1 := hρ ▸ h μ0 hμ0
  have hρ0 : 0 ≤ specRad S := specRad_nonneg S
  have hr0 : 0 ≤ (specRad S + 1) / 2 := by linarith
  have hr1 : (specRad S + 1) / 2 < 1 := by linarith
  have hρr : specRad S < (specRad S + 1) / 2 := by linarith
  obtain ⟨r, hr⟩ : ∃ r : NNReal, (r : ℝ) = (specRad S + 1) / 2 := ⟨⟨_, hr0⟩, rfl⟩
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℂ _
  have hsr : spectralRadius ℂ S < (r : ENNReal) :=
    spectrum.spectralRadius_lt_of_forall_lt S fun z hz => by
      rw [← NNReal.coe_lt_coe, coe_nnnorm, hr]
      exact (norm_le_specRad hz).trans_lt hρr
  have hG := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius S
  have hev : ∀ᶠ k : ℕ in Filter.atTop, (‖S ^ k‖₊ : ENNReal) ^ (1 / (k : ℝ))
      < (r : ENNReal) :=
    hG.eventually (eventually_lt_nhds hsr)
  have hbound : ∀ᶠ k : ℕ in Filter.atTop,
      ‖(S ^ k) *ᵥ x‖ ≤ ((specRad S + 1) / 2) ^ k * ‖x‖ := by
    filter_upwards [hev, Filter.eventually_ge_atTop 1] with k hk hk1
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
    have h1 : (‖S ^ k‖₊ : ENNReal) < (r : ENNReal) ^ k := by
      have h2 := ENNReal.rpow_lt_rpow hk hkpos
      rwa [← ENNReal.rpow_mul, one_div_mul_cancel hkpos.ne', ENNReal.rpow_one,
        ENNReal.rpow_natCast] at h2
    have h3 : ‖S ^ k‖ ≤ ((specRad S + 1) / 2) ^ k := by
      rw [← ENNReal.coe_pow, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] at h1
      simpa [hr] using h1.le
    calc ‖(S ^ k) *ᵥ x‖ ≤ ‖S ^ k‖ * ‖x‖ := by
          first
            | exact Matrix.linfty_opNorm_mulVec _ _
            | exact Matrix.linfty_opNNNorm_mulVec _ _
      _ ≤ ((specRad S + 1) / 2) ^ k * ‖x‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
  exact squeeze_zero_norm' hbound
    (by simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const ‖x‖)

/-- Lyapunov: Hurwitz `A` and `AᵀP + PA ≺ 0` force `P ≻ 0`.  Cayley transform
`S = 2(I - A)⁻¹ - I`, the one-step identity
`qf_P(Sx) = qf_P(x) - 2 qf_L((I - A)⁻¹x)`, spectrum of `S` in the unit disk,
and `Sᵏx → 0`. -/
theorem posDef_of_lyapunov {A : Matrix n n ℝ} (hA : IsHurwitz A) {P : Matrix n n ℝ}
    (hPt : Pᵀ = P) (hL : (-(Aᵀ * P + P * A)).PosDef) : P.PosDef := by
  have hp : (cplx P).IsHermitian := by
    show _ = _
    rw [← cplx_transpose, hPt]
  have hl := posDef_cplx_of_posDef hL
  have hid : (cplx A)ᴴ * cplx P + cplx P * cplx A = -cplx (-(Aᵀ * P + P * A)) := by
    simp only [cplx_neg, cplx_add, cplx_mul, cplx_transpose, neg_neg]
  have hU : IsUnit (1 - cplx A).det := by
    have hns : (1 : ℂ) ∉ spectrum ℂ (cplx A) := by
      intro hmem
      have h1 := hA 1 hmem
      norm_num at h1
    rw [spectrum.mem_iff, not_not, Matrix.isUnit_iff_isUnit_det, map_one] at hns
    exact hns
  obtain ⟨T, hTdef⟩ : ∃ T, T = (1 - cplx A)⁻¹ := ⟨_, rfl⟩
  have hUT : (1 - cplx A) * T = 1 := by
    rw [hTdef]
    exact Matrix.mul_nonsing_inv _ hU
  have hx_eq : ∀ x, x = T *ᵥ x - cplx A *ᵥ (T *ᵥ x) := by
    intro x
    calc x = ((1 - cplx A) * T) *ᵥ x := by rw [hUT, Matrix.one_mulVec]
      _ = T *ᵥ x - cplx A *ᵥ (T *ᵥ x) := by
          rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
  obtain ⟨S, hSdef⟩ : ∃ S, S = (2 : ℂ) • T - 1 := ⟨_, rfl⟩
  have hS : ∀ x, S *ᵥ x = T *ᵥ x + cplx A *ᵥ (T *ᵥ x) := by
    intro x
    have hx := hx_eq x
    rw [hSdef, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    generalize T *ᵥ x = y at hx ⊢
    rw [hx, two_smul]
    abel
  have hstep : ∀ x, qf (cplx P) (S *ᵥ x) = qf (cplx P) x
      - 2 * qf (cplx (-(Aᵀ * P + P * A))) (T *ᵥ x) := by
    intro x
    have hx := hx_eq x
    rw [hS x]
    generalize T *ᵥ x = y at hx ⊢
    rw [hx, qf_add_of_isHermitian hp, qf_sub_of_isHermitian hp]
    have hq : qf ((cplx A)ᴴ * cplx P + cplx P * cplx A) y
        = 2 * (star (cplx A *ᵥ y) ⬝ᵥ (cplx P *ᵥ y)).re := by
      rw [qf_add_left]
      unfold qf
      have e1 : star y ⬝ᵥ (((cplx A)ᴴ * cplx P) *ᵥ y)
          = star (cplx A *ᵥ y) ⬝ᵥ (cplx P *ᵥ y) := by
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
      have e2 : star y ⬝ᵥ ((cplx P * cplx A) *ᵥ y)
          = star (star (cplx A *ᵥ y) ⬝ᵥ (cplx P *ᵥ y)) := by
        rw [← Matrix.mulVec_mulVec]
        exact dotProduct_mulVec_swap hp y (cplx A *ᵥ y)
      rw [e1, e2, Complex.star_def, Complex.conj_re]
      ring
    have hl' : qf ((cplx A)ᴴ * cplx P + cplx P * cplx A) y
        = -qf (cplx (-(Aᵀ * P + P * A))) y := by
      rw [hid, qf_neg_left]
    linarith
  have hSspec : ∀ μ ∈ spectrum ℂ S, ‖μ‖ < 1 := by
    intro μ hμ
    obtain ⟨v, hv, hSv⟩ := exists_eigvec_of_mem_spectrum hμ
    have hxv := hx_eq v
    rw [hS v] at hSv
    generalize hy : T *ᵥ v = y at hxv hSv
    have hy0 : y ≠ 0 := by
      intro h
      rw [h, Matrix.mulVec_zero, sub_zero] at hxv
      exact hv hxv
    rw [hxv, smul_sub] at hSv
    have key : (1 + μ) • (cplx A *ᵥ y) = (μ - 1) • y := by
      rw [add_smul, one_smul, sub_smul, one_smul]
      have h2 := congrArg (fun z => z + μ • (cplx A *ᵥ y) - y) hSv
      calc cplx A *ᵥ y + μ • (cplx A *ᵥ y)
          = y + cplx A *ᵥ y + μ • (cplx A *ᵥ y) - y := by abel
        _ = μ • y - μ • (cplx A *ᵥ y) + μ • (cplx A *ᵥ y) - y := h2
        _ = μ • y - y := by abel
    have hμ1 : 1 + μ ≠ 0 := by
      intro h
      rw [h, zero_smul] at key
      have h2 : μ - 1 = -2 := by linear_combination h
      rw [h2] at key
      exact hy0 ((smul_eq_zero.mp key.symm).resolve_left (by norm_num))
    have hay : cplx A *ᵥ y = ((μ - 1) / (1 + μ)) • y := by
      rw [div_eq_inv_mul, mul_smul, ← key, smul_smul, inv_mul_cancel₀ hμ1, one_smul]
    have hlam := hA _ (mem_spectrum_of_eigvec hy0 hay)
    have hN : 0 < Complex.normSq (1 + μ) := Complex.normSq_pos.mpr hμ1
    rw [Complex.div_re, ← add_div, div_lt_iff₀ hN, zero_mul] at hlam
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.sub_im,
      Complex.add_im, Complex.one_im] at hlam
    have hsq : ‖μ‖ ^ 2 < 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith
    nlinarith [norm_nonneg μ]
  have hpPD : ∀ x : n → ℂ, x ≠ 0 → 0 < qf (cplx P) x := by
    intro x hx
    have hanti : Antitone (fun k : ℕ => qf (cplx P) ((S ^ k) *ᵥ x)) :=
      antitone_nat_of_succ_le fun k => by
        show qf (cplx P) ((S ^ (k + 1)) *ᵥ x) ≤ qf (cplx P) ((S ^ k) *ᵥ x)
        rw [pow_succ', ← Matrix.mulVec_mulVec, hstep]
        linarith [qf_nonneg hl (T *ᵥ ((S ^ k) *ᵥ x))]
    have hlim : Filter.Tendsto (fun k : ℕ => qf (cplx P) ((S ^ k) *ᵥ x)) Filter.atTop
        (nhds 0) := by
      have h1 := ((continuous_qf (cplx P)).tendsto 0).comp (tendsto_pow_mulVec_zero hSspec x)
      have hq0 : qf (cplx P) 0 = 0 := by simp [qf]
      rw [hq0] at h1
      exact h1
    have h1 := hanti.le_of_tendsto hlim 1
    simp only [pow_one] at h1
    rw [hstep] at h1
    have hTx : T *ᵥ x ≠ 0 := by
      intro h
      apply hx
      rw [hx_eq x, h, Matrix.mulVec_zero, sub_zero]
    linarith [qf_pos hl hTx]
  have hPh : P.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hPt]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hPh fun x hx => ?_
  have hxc : (fun i => (x i : ℂ)) ≠ 0 := by
    intro h
    apply hx
    funext i
    have hi := congrFun h i
    simpa using hi
  rw [star_trivial, ← qf_cplx_ofReal]
  exact hpPD _ hxc

/-- Converse half of Lemma brl, from the KYP and Lyapunov leaves. -/
theorem riccatiStable_of_boundedReal {A B : Matrix n n ℝ} (hA : IsHurwitz A)
    {Q : Matrix n n ℝ} (hQ : Q.PosDef)
    (hsup : (⨆ ω : ℝ, metricGain (cplx Q) (resolvent A B ω)) < 1) :
    RiccatiStable A B := by
  obtain ⟨P, hPt, hR⟩ := exists_ari_of_boundedReal hA hQ hsup
  have hY : ((Bᵀ * P)ᴴ * Q⁻¹ * (Bᵀ * P)).PosSemidef :=
    hQ.inv.posSemidef.conjTranspose_mul_mul_same _
  have hsum : ((-(Aᵀ * P + P * A + Q + P * B * Q⁻¹ * Bᵀ * P)) + Q
      + (Bᵀ * P)ᴴ * Q⁻¹ * (Bᵀ * P)).PosDef :=
    (hR.add hQ).add_posSemidef hY
  have hid : (-(Aᵀ * P + P * A + Q + P * B * Q⁻¹ * Bᵀ * P)) + Q
      + (Bᵀ * P)ᴴ * Q⁻¹ * (Bᵀ * P) = -(Aᵀ * P + P * A) := by
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.transpose_transpose, hPt]
    noncomm_ring
  rw [hid] at hsum
  exact ⟨P, Q, posDef_of_lyapunov hA hPt hsum, hQ, hR⟩

/-- Lemma lem:brl. -/
theorem riccatiStable_iff_boundedReal (A B : Matrix n n ℝ) :
    RiccatiStable A B ↔
      IsHurwitz A ∧ ∃ Q : Matrix n n ℝ, Q.PosDef ∧
        (⨆ ω : ℝ, metricGain (cplx Q) (resolvent A B ω)) < 1 := by
  constructor
  · intro h
    exact ⟨h.isHurwitz, boundedReal_of_riccatiStable h⟩
  · rintro ⟨hA, Q, hQ, hsup⟩
    exact riccatiStable_of_boundedReal hA hQ hsup

/-- Schur complement step, (eq:lmi) ⇔ (eq:ric).  The reverse direction is the
Schur complement `ari_of_lmi_real`; the forward direction goes through
Lemma lem:brl, whose KYP half produces a symmetric LMI solution `P`, and the
Lyapunov step makes `P` positive definite. -/
theorem riccatiStable_iff_lmiFeasible (A B : Matrix n n ℝ) :
    RiccatiStable A B ↔ LMIFeasible A B := by
  have hXsym : ∀ P Q : Matrix n n ℝ, Pᵀ = P → Q.PosDef →
      (Aᵀ * P + P * A + Q)ᵀ = Aᵀ * P + P * A + Q := by
    intro P Q hPt hQ
    rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hPt, transpose_eq_of_posDef hQ]
    abel
  constructor
  · intro h
    obtain ⟨hA, Q, hQ, hsup⟩ := (riccatiStable_iff_boundedReal A B).1 h
    obtain ⟨P, hPt, hlmi⟩ := exists_lmi_of_boundedReal hA hQ hsup
    have hR := ari_of_lmi_real (hXsym P Q hPt hQ) hPt hQ hlmi
    have hY : ((Bᵀ * P)ᴴ * Q⁻¹ * (Bᵀ * P)).PosSemidef :=
      hQ.inv.posSemidef.conjTranspose_mul_mul_same _
    have hsum : ((-(Aᵀ * P + P * A + Q + P * B * Q⁻¹ * Bᵀ * P)) + Q
        + (Bᵀ * P)ᴴ * Q⁻¹ * (Bᵀ * P)).PosDef :=
      (hR.add hQ).add_posSemidef hY
    have hid : (-(Aᵀ * P + P * A + Q + P * B * Q⁻¹ * Bᵀ * P)) + Q
        + (Bᵀ * P)ᴴ * Q⁻¹ * (Bᵀ * P) = -(Aᵀ * P + P * A) := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
        Matrix.transpose_transpose, hPt]
      noncomm_ring
    rw [hid] at hsum
    exact ⟨P, Q, posDef_of_lyapunov hA hPt hsum, hQ, hlmi⟩
  · rintro ⟨P, Q, hP, hQ, hlmi⟩
    have hPt : Pᵀ = P := transpose_eq_of_posDef hP
    exact ⟨P, Q, hP, hQ, ari_of_lmi_real (hXsym P Q hPt hQ) hPt hQ hlmi⟩

omit [DecidableEq n] in
theorem qf_sub_left (M N : Matrix n n ℂ) (z : n → ℂ) : qf (M - N) z = qf M z - qf N z := by
  unfold qf
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

omit [DecidableEq n] in
/-- The pairing step `metricGain H X ≤ γ ↔ Xᴴ H X ⪯ γ² H`. -/
theorem metricGain_le_iff {H X : Matrix n n ℂ} (hH : H.PosDef) {γ : ℝ}
    (hγ : 0 ≤ γ) :
    metricGain H X ≤ γ ↔ ((γ ^ 2 : ℝ) • H - Xᴴ * H * X).PosSemidef := by
  have h1 : (Xᴴ * H * X).IsHermitian :=
    (hH.posSemidef.conjTranspose_mul_mul_same X).isHermitian
  have h2 : ((γ ^ 2 : ℝ) • H).IsHermitian := by
    show _ = _
    rw [conjTranspose_smul, star_trivial, hH.isHermitian.eq]
  have hHerm : ((γ ^ 2 : ℝ) • H - Xᴴ * H * X).IsHermitian := h2.sub h1
  have hqM : ∀ z, qf ((γ ^ 2 : ℝ) • H - Xᴴ * H * X) z
      = γ ^ 2 * qf H z - qf (Xᴴ * H * X) z := by
    intro z
    rw [qf_sub_left, qf_smul_left]
  constructor
  · intro hle
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun x => ?_
    have hx : qf (Xᴴ * H * X) x ≤ γ ^ 2 * qf H x :=
      (qf_le_metricGain_sq hH X x).trans
        (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (metricGain_nonneg _ _) hle 2) (qf_nonneg hH x))
    refine Complex.nonneg_iff.mpr ⟨?_, (im_star_dotProduct_mulVec_self hHerm x).symm⟩
    show 0 ≤ qf ((γ ^ 2 : ℝ) • H - Xᴴ * H * X) x
    rw [hqM]
    linarith
  · intro hpsd
    unfold metricGain
    refine Real.iSup_le (fun y => ?_) hγ
    have h : 0 ≤ qf ((γ ^ 2 : ℝ) • H - Xᴴ * H * X) y.1 :=
      (Complex.nonneg_iff.mp (hpsd.dotProduct_mulVec_nonneg y.1)).1
    rw [hqM] at h
    calc Real.sqrt (qf (Xᴴ * H * X) y.1 / qf H y.1) ≤ Real.sqrt (γ ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [div_le_iff₀ (qf_pos hH y.2)]
          linarith
      _ = γ := Real.sqrt_sq hγ


/-- Congruence invariance of the metric gain: changing coordinates by an
invertible `T` conjugates the operator. -/
theorem metricGain_congr {H T : Matrix n n ℂ} (hH : H.PosDef) (hT : IsUnit T.det)
    (X : Matrix n n ℂ) :
    metricGain (Tᴴ * H * T) X = metricGain H (T * X * T⁻¹) := by
  have hinj : Function.Injective T.mulVec := by
    intro u v h
    have h' := congrArg (fun w => T⁻¹ *ᵥ w) h
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T hT] using h'
  have hH' : (Tᴴ * H * T).PosDef := hH.conjTranspose_mul_mul_same hinj
  have hB : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T hT
  have hD : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hT
  have hA : ∀ M : Matrix n n ℂ, Tᴴ * (T⁻¹ᴴ * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hB, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have hC : ∀ M : Matrix n n ℂ, T⁻¹ᴴ * (Tᴴ * M) = M := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hD, Matrix.conjTranspose_one,
      Matrix.one_mul]
  apply le_antisymm
  · have h0 := metricGain_nonneg H (T * X * T⁻¹)
    rw [metricGain_le_iff hH' h0]
    have hP := ((metricGain_le_iff hH h0).mp le_rfl).conjTranspose_mul_mul_same T
    have hid : Tᴴ * ((metricGain H (T * X * T⁻¹) ^ 2 : ℝ) • H
        - (T * X * T⁻¹)ᴴ * H * (T * X * T⁻¹)) * T
        = (metricGain H (T * X * T⁻¹) ^ 2 : ℝ) • (Tᴴ * H * T) - Xᴴ * (Tᴴ * H * T) * X := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.conjTranspose_mul, Matrix.mul_assoc, hB, Matrix.mul_one, hA]
    rwa [hid] at hP
  · have h0 := metricGain_nonneg (Tᴴ * H * T) X
    rw [metricGain_le_iff hH h0]
    have hP := ((metricGain_le_iff hH' h0).mp le_rfl).conjTranspose_mul_mul_same T⁻¹
    have hid : T⁻¹ᴴ * ((metricGain (Tᴴ * H * T) X ^ 2 : ℝ) • (Tᴴ * H * T)
        - Xᴴ * (Tᴴ * H * T) * X) * T⁻¹
        = (metricGain (Tᴴ * H * T) X ^ 2 : ℝ) • H - (T * X * T⁻¹)ᴴ * H * (T * X * T⁻¹) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.conjTranspose_mul, Matrix.mul_assoc, hD, Matrix.mul_one, hC]
    rwa [hid] at hP

/-- Bridge to the paper's notation: `metricGain (R R) X = ‖R X R⁻¹‖₂`. -/
theorem metricGain_eq_norm2 {R : Matrix n n ℂ} (hR : R.PosDef)
    (X : Matrix n n ℂ) :
    metricGain (R * R) X = norm2 (R * X * R⁻¹) := by
  have hRR : R * R = Rᴴ * 1 * R := by rw [hR.isHermitian.eq, Matrix.mul_one]
  rw [hRR, metricGain_congr Matrix.PosDef.one (isUnit_iff_ne_zero.mpr hR.det_pos.ne') X,
    metricGain_one]

/-- Theorem thm:main. -/
theorem riccatiStable_iff (A B : Matrix n n ℝ) :
    RiccatiStable A B ↔ IsHurwitz A ∧ rhoR A B < 1 := by
  rw [riccatiStable_iff_boundedReal]
  constructor
  · rintro ⟨hA, hQ⟩
    exact ⟨hA, (rhoR_lt_one_iff_exists_real_metric hA B).2 hQ⟩
  · rintro ⟨hA, h⟩
    exact ⟨hA, (rhoR_lt_one_iff_exists_real_metric hA B).1 h⟩

/-- Corollary cor:finitecert: finite obstruction.
The forward half uses attainment (`covRadius_sq_feasible`) at `t = ρ_R² ≥ 1`,
then discards the terms with `X_j = 0` (this only lowers the right side; if
every nonzero `z_j` had `X_j = 0` the balance would force `∑ z_j z_jᴴ ⪯ 0`). -/
theorem not_riccatiStable_iff (A B : Matrix n n ℝ) :
    ¬ RiccatiStable A B ↔
      ¬ IsHurwitz A ∨
        ∃ (m : ℕ) (ω : Fin m → ℝ) (z : Fin m → n → ℂ),
          m ≤ Fintype.card n ^ 2 + 1 ∧ (∃ j, z j ≠ 0) ∧
          (∑ j, rankOne (resolvent A B (ω j) *ᵥ z j)
              - ∑ j, rankOne (z j)).PosSemidef := by
  constructor
  · intro hns
    by_cases hA : IsHurwitz A
    · right
      have hge : 1 ≤ rhoR A B := by
        by_contra hlt
        push_neg at hlt
        exact hns ((riccatiStable_iff A B).2 ⟨hA, hlt⟩)
      have hK := isCompact_resolventFamily hA B
      have hz0 : (0 : Matrix n n ℂ) ∈ resolventFamily A B :=
        Set.mem_union_right _ (Set.mem_singleton _)
      have hopt : rhoR A B = optNorm (resolventFamily A B) := covRadius_eq_optNorm hK hz0
      have hpos : 0 < optNorm (resolventFamily A B) := by rw [← hopt]; linarith
      have hfeas := covFeasible_optNorm_sq hK hz0 hpos
      rw [← hopt] at hfeas
      obtain ⟨-, m, X, z, hm, hX, hz, hbal⟩ := hfeas
      have hc1 : 0 ≤ rhoR A B ^ 2 - 1 := by nlinarith
      have hr0 : rankOne (0 : n → ℂ) = 0 := by
        ext i j
        simp [rankOne, Matrix.vecMulVec_apply]
      have hsel : ∀ j, ∃ (ω : ℝ) (w : n → ℂ) (d : ℝ),
          rankOne (resolvent A B ω *ᵥ w) = rankOne (X j *ᵥ z j) ∧
          rankOne w = (1 - d) • rankOne (z j) ∧ 0 ≤ d := by
        intro j
        rcases hX j with ⟨ω, hω⟩ | h0
        · exact ⟨ω, z j, 0, by rw [hω], by rw [sub_zero, one_smul], le_rfl⟩
        · refine ⟨0, 0, 1, ?_, ?_, zero_le_one⟩
          · rw [Set.mem_singleton_iff.mp h0, Matrix.mulVec_zero, Matrix.zero_mulVec]
          · rw [hr0, sub_self, zero_smul]
      choose ω w d hGw hw hd using hsel
      refine ⟨m, ω, w, hm, ?_, ?_⟩
      · by_contra hall
        push_neg at hall
        have hzero : ∀ j, rankOne (X j *ᵥ z j) = 0 := fun j => by
          rw [← hGw j, hall j, Matrix.mulVec_zero, hr0]
        rw [Finset.sum_eq_zero (fun j _ => hzero j), zero_sub] at hbal
        have htr := (Complex.nonneg_iff.mp hbal.trace_nonneg).1
        have hq : ∀ j, ((rankOne (z j)).trace).re = qf 1 (z j) := fun j => by
          rw [← Matrix.one_mul (rankOne (z j)), trace_mul_rankOne]
          rfl
        rw [Matrix.trace_neg, Matrix.trace_smul, Matrix.trace_sum, Complex.neg_re, smul_eq_mul,
          Complex.re_ofReal_mul, Complex.re_sum] at htr
        simp only [hq] at htr
        obtain ⟨j0, hj0⟩ := hz
        have hsumpos : 0 < ∑ j, qf 1 (z j) :=
          Finset.sum_pos' (fun j _ => qf_nonneg Matrix.PosDef.one _)
            ⟨j0, Finset.mem_univ _, qf_pos Matrix.PosDef.one hj0⟩
        have hρ : 0 < rhoR A B ^ 2 := by nlinarith
        nlinarith
      · have hE : (∑ j, (rhoR A B ^ 2 - 1) • rankOne (z j)).PosSemidef :=
          posSemidef_sum_smul_rankOne (fun _ => rhoR A B ^ 2 - 1) (fun _ => hc1) z
        have hD : (∑ j, d j • rankOne (z j)).PosSemidef := posSemidef_sum_smul_rankOne d hd z
        have hsplit : ∑ j, rankOne (w j)
            = ∑ j, (rhoR A B ^ 2) • rankOne (z j) - ∑ j, (rhoR A B ^ 2 - 1) • rankOne (z j)
              - ∑ j, d j • rankOne (z j) := by
          rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hw j, ← sub_smul, ← sub_smul]
          congr 1
          ring
        have hid : ∑ j, rankOne (resolvent A B (ω j) *ᵥ w j) - ∑ j, rankOne (w j)
            = (∑ j, rankOne (X j *ᵥ z j) - ((rhoR A B ^ 2 : ℝ) : ℂ) • ∑ j, rankOne (z j))
              + ∑ j, (rhoR A B ^ 2 - 1) • rankOne (z j) + ∑ j, d j • rankOne (z j) := by
          rw [Finset.sum_congr rfl (fun j _ => hGw j), hsplit, Complex.coe_smul,
            Finset.smul_sum]
          abel
        rw [hid]
        exact (hbal.add hE).add hD
    · exact Or.inl hA
  · rintro (hA | ⟨m, ω, z, hm, hz, hbal⟩)
    · exact fun hR => hA hR.isHurwitz
    · intro hR
      have hA : IsHurwitz A := hR.isHurwitz
      have hlt : rhoR A B < 1 := ((riccatiStable_iff A B).1 hR).2
      have hfeas : CovFeasible (resolventFamily A B) 1 := by
        refine ⟨zero_le_one, m, fun j => resolvent A B (ω j), z, hm,
          fun _ => Set.mem_union_left _ (Set.mem_range_self _), hz, ?_⟩
        simpa using hbal
      have hbdd : BddAbove {t : ℝ | CovFeasible (resolventFamily A B) t} :=
        ⟨_, fun t ht => covFeasible_le_sup_norm (isCompact_resolventFamily hA B) ht⟩
      have h1 : (1 : ℝ) ≤ sSup {t : ℝ | CovFeasible (resolventFamily A B) t} :=
        le_csSup hbdd hfeas
      have h2 : (1 : ℝ) ≤ rhoR A B := by
        unfold rhoR covRadius
        simpa using Real.sqrt_le_sqrt h1
      exact absurd hlt (not_lt.mpr h2)

/-- Proposition prop:bounds, (eq:resolventword). -/
theorem specRad_resolvent_prod_rpow_le_rhoR {A : Matrix n n ℝ}
    (hA : IsHurwitz A) (B : Matrix n n ℝ) {k : ℕ} (hk : 0 < k)
    (ω : Fin k → ℝ) :
    specRad (List.ofFn fun j => resolvent A B (ω j)).prod ^ ((k : ℝ)⁻¹)
      ≤ rhoR A B :=
  specRad_prod_rpow_le_covRadius (isCompact_resolventFamily hA B)
    (Set.mem_union_right _ (Set.mem_singleton _)) hk _
    (fun _ => Set.mem_union_left _ (Set.mem_range_self _))

/-- Proposition prop:bounds, left inequality of (eq:sandwich) (case `k = 1`). -/
theorem specRad_resolvent_le_rhoR {A : Matrix n n ℝ} (hA : IsHurwitz A)
    (B : Matrix n n ℝ) (ω : ℝ) :
    specRad (resolvent A B ω) ≤ rhoR A B := by
  have h := specRad_resolvent_prod_rpow_le_rhoR hA B (k := 1) one_pos
    (fun _ => ω)
  simpa [List.ofFn_succ] using h

/-- Proposition prop:bounds, right inequality of (eq:sandwich) (`H = I`). -/
theorem rhoR_le_sup_norm2 {A : Matrix n n ℝ} (hA : IsHurwitz A)
    (B : Matrix n n ℝ) :
    rhoR A B ≤ ⨆ ω : ℝ, norm2 (resolvent A B ω) := by
  have hI : (1 : Matrix n n ℂ).PosDef := Matrix.PosDef.one
  have h1 : rhoR A B ≤ familyGain 1 (resolventFamily A B) :=
    (covRadius_le_optNorm (isCompact_resolventFamily hA B)).trans
      (optNorm_le_familyGain _ hI)
  have h2 := familyGain_resolventFamily_le hA B hI
  simp only [metricGain_one] at h2
  exact h1.trans h2

/-- `G_{A,B}(0) = -A⁻¹B`.  Route: `cplx` is a ring hom on matrices,
so it commutes with `⁻¹` (via `RingHom.map_det`, `RingHom.map_adjugate`),
and `(0 • 1 - A)⁻¹ = -A⁻¹`. -/
theorem resolvent_zero {A : Matrix n n ℝ} (hA : IsHurwitz A)
    (B : Matrix n n ℝ) :
    resolvent A B 0 = -cplx (A⁻¹ * B) := by
  unfold resolvent cplx
  rw [Complex.ofReal_zero, zero_mul, zero_smul, zero_sub, inv_neg_eq, Matrix.neg_mul,
    Matrix.map_mul, map_inv_eq]

/-- Remark (Verriest recovery): `r(A⁻¹B) ≤ ρ_R(A,B)`, via `G(0) = -A⁻¹B`. -/
theorem specRad_inv_mul_le_rhoR {A : Matrix n n ℝ} (hA : IsHurwitz A)
    (B : Matrix n n ℝ) :
    specRad (cplx (A⁻¹ * B)) ≤ rhoR A B := by
  have h := specRad_resolvent_le_rhoR hA B 0
  rwa [resolvent_zero hA B, specRad_neg] at h

omit [DecidableEq n] in
theorem posSemidef_smul_of_nonneg {M : Matrix n n ℂ} (hM : M.PosSemidef) {r : ℝ} (hr : 0 ≤ r) :
    (r • M).PosSemidef := by
  have hh : (r • M).IsHermitian := by
    show (r • M)ᴴ = r • M
    rw [conjTranspose_smul, star_trivial, hM.isHermitian.eq]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hh fun x => ?_
  refine Complex.nonneg_iff.mpr ⟨?_, (im_star_dotProduct_mulVec_self hh x).symm⟩
  show 0 ≤ qf (r • M) x
  rw [qf_smul_left]
  exact mul_nonneg hr (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg x)).1

omit [DecidableEq n] in
/-- Scaling identity for balances. -/
theorem balance_smul {m : ℕ} (c t : ℝ) (Y : Fin m → Matrix n n ℂ) (z : Fin m → n → ℂ) :
    ∑ j, rankOne (((c : ℂ) • Y j) *ᵥ z j) - ((c ^ 2 * t : ℝ) : ℂ) • ∑ j, rankOne (z j)
      = (c ^ 2) • (∑ j, rankOne (Y j *ᵥ z j) - (t : ℂ) • ∑ j, rankOne (z j)) := by
  have h1 : ∀ j, rankOne (((c : ℂ) • Y j) *ᵥ z j) = (c ^ 2) • rankOne (Y j *ᵥ z j) := by
    intro j
    rw [Matrix.smul_mulVec, rankOne_smul, ← Complex.coe_smul]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [h1]
  rw [← Finset.smul_sum, smul_sub]
  congr 1
  rw [← Complex.coe_smul (c ^ 2) ((t : ℂ) • ∑ j, rankOne (z j)), smul_smul, Complex.ofReal_mul]

omit [DecidableEq n] in
/-- Feasibility under scaling of the family by a nonzero real `c`. -/
theorem covFeasible_scale {S S' : Set (Matrix n n ℂ)} {c : ℝ} (hc : c ≠ 0)
    (hS : ∀ X, X ∈ S' ↔ ∃ Y ∈ S, X = (c : ℂ) • Y) (t : ℝ) :
    CovFeasible S' (c ^ 2 * t) ↔ CovFeasible S t := by
  have hc2 : 0 < c ^ 2 := by positivity
  constructor
  · rintro ⟨h0, m, X, z, hm, hX, hz, hbal⟩
    choose Y hY hXY using fun j => (hS (X j)).mp (hX j)
    have hXe : X = fun j => (c : ℂ) • Y j := funext hXY
    subst hXe
    refine ⟨le_of_mul_le_mul_left (by rw [mul_zero]; exact h0) hc2, m, Y, z, hm, hY, hz, ?_⟩
    rw [balance_smul] at hbal
    have h := posSemidef_smul_of_nonneg hbal (inv_nonneg.mpr hc2.le)
    rwa [smul_smul, inv_mul_cancel₀ hc2.ne', one_smul] at h
  · rintro ⟨h0, m, Y, z, hm, hY, hz, hbal⟩
    refine ⟨mul_nonneg hc2.le h0, m, fun j => (c : ℂ) • Y j, z, hm,
      fun j => (hS _).mpr ⟨Y j, hY j, rfl⟩, hz, ?_⟩
    show (∑ j, rankOne (((c : ℂ) • Y j) *ᵥ z j)
      - ((c ^ 2 * t : ℝ) : ℂ) • ∑ j, rankOne (z j)).PosSemidef
    rw [balance_smul]
    exact posSemidef_smul_of_nonneg hbal hc2.le

omit [DecidableEq n] in
open scoped Pointwise in
/-- Homogeneity of the covariance radius. -/
theorem covRadius_scale {S S' : Set (Matrix n n ℂ)} {c : ℝ} (hc : c ≠ 0)
    (hS : ∀ X, X ∈ S' ↔ ∃ Y ∈ S, X = (c : ℂ) • Y) :
    covRadius S' = |c| * covRadius S := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  unfold covRadius
  have hset : {t | CovFeasible S' t} = (c ^ 2) • {t | CovFeasible S t} := by
    ext t'
    constructor
    · intro h
      refine ⟨t' / c ^ 2, (covFeasible_scale hc hS _).mp ?_, ?_⟩
      · have e : c ^ 2 * (t' / c ^ 2) = t' := by field_simp
        rw [e]
        exact h
      · show c ^ 2 * (t' / c ^ 2) = t'
        field_simp
    · rintro ⟨t, ht, rfl⟩
      exact (covFeasible_scale hc hS t).mpr ht
  rw [hset, Real.sSup_smul_of_nonneg (sq_nonneg c), smul_eq_mul,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem inv_smul_eq (c : ℂ) (hc : c ≠ 0) (M : Matrix n n ℂ) : (c • M)⁻¹ = c⁻¹ • M⁻¹ := by
  by_cases h : IsUnit M.det
  · apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul,
      Matrix.nonsing_inv_mul M h]
  · have h' : ¬ IsUnit (c • M).det := by
      rw [Matrix.det_smul]
      intro hu
      apply h
      rw [isUnit_iff_ne_zero] at hu ⊢
      intro h0
      apply hu
      rw [h0, mul_zero]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h', Matrix.nonsing_inv_apply_not_isUnit _ h,
      smul_zero]

omit [DecidableEq n] in
theorem cplx_smul (c : ℝ) (M : Matrix n n ℝ) : cplx (c • M) = (c : ℂ) • cplx M := by
  ext i j
  simp [cplx]

/-- Remark: joint scaling invariance, `G_{αA,αB}(ω) = G_{A,B}(ω/α)`. -/
theorem rhoR_scale (A B : Matrix n n ℝ) {α : ℝ} (hα : 0 < α) :
    rhoR (α • A) (α • B) = rhoR A B := by
  have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have key : ∀ ω : ℝ, resolvent (α • A) (α • B) ω = resolvent A B (ω / α) := by
    intro ω
    unfold resolvent
    have hM : ((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - (α : ℂ) • cplx A
        = (α : ℂ) • ((((ω / α : ℝ) : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - cplx A) := by
      rw [smul_sub, smul_smul]
      congr 2
      push_cast
      field_simp
    rw [cplx_smul, cplx_smul, hM, inv_smul_eq _ hα', Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, inv_mul_cancel₀ hα', one_smul]
  have hfam : resolventFamily (α • A) (α • B) = resolventFamily A B := by
    ext X
    constructor
    · rintro (⟨ω, rfl⟩ | h0)
      · exact Set.mem_union_left _ ⟨ω / α, (key ω).symm⟩
      · exact Set.mem_union_right _ h0
    · rintro (⟨ω, rfl⟩ | h0)
      · refine Set.mem_union_left _ ⟨ω * α, ?_⟩
        rw [key, mul_div_assoc, div_self hα.ne', mul_one]
      · exact Set.mem_union_right _ h0
  unfold rhoR
  rw [hfam]

/-- An invertible matrix acts injectively. -/
theorem mulVec_injective_of_isUnit {T : Matrix n n ℂ} (hT : IsUnit T.det) :
    Function.Injective T.mulVec := by
  intro u v h
  have h' := congrArg (fun w => T⁻¹ *ᵥ w) h
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T hT] using h'

/-- Similar matrices have the same spectrum. -/
theorem spectrum_conj (M S : Matrix n n ℂ) (hS : IsUnit S.det) :
    spectrum ℂ (S⁻¹ * M * S) = spectrum ℂ M := by
  ext μ
  simp only [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, Algebra.algebraMap_eq_smul_one]
  have hconj : μ • (1 : Matrix n n ℂ) - S⁻¹ * M * S = S⁻¹ * (μ • 1 - M) * S := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.nonsing_inv_mul S hS]
  have hd : S⁻¹.det * S.det = 1 := by
    rw [← Matrix.det_mul, Matrix.nonsing_inv_mul S hS, Matrix.det_one]
  rw [hconj, Matrix.det_mul, Matrix.det_mul, mul_right_comm, hd, one_mul]

/-- The complexification of a real invertible matrix is invertible. -/
theorem isUnit_det_cplx {T : Matrix n n ℝ} (hT : IsUnit T.det) : IsUnit (cplx T).det := by
  have hd : algebraMap ℝ ℂ T.det = (cplx T).det := RingHom.map_det _ T
  rw [← hd]
  exact hT.map _

/-- The resolvent of a similar pair is the conjugated resolvent. -/
theorem resolvent_similar (A B T : Matrix n n ℝ) (hT : IsUnit T.det) (ω : ℝ) :
    resolvent (T⁻¹ * A * T) (T⁻¹ * B * T) ω
      = (cplx T)⁻¹ * resolvent A B ω * cplx T := by
  have hS := isUnit_det_cplx hT
  have hinv : cplx T⁻¹ = (cplx T)⁻¹ := map_inv_eq (algebraMap ℝ ℂ) T
  unfold resolvent
  simp only [cplx_mul, hinv]
  have hN : ((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - (cplx T)⁻¹ * cplx A * cplx T
      = (cplx T)⁻¹ * (((ω : ℂ) * Complex.I) • (1 : Matrix n n ℂ) - cplx A) * cplx T := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.nonsing_inv_mul _ hS]
  rw [hN, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hS]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cplx T) (cplx T)⁻¹, Matrix.mul_nonsing_inv _ hS, Matrix.one_mul]

/-- Conjugating a family does not increase the optimal common norm. -/
theorem optNorm_le_of_conj {F F' : Set (Matrix n n ℂ)} {T : Matrix n n ℂ}
    (hT : IsUnit T.det) (hF : IsCompact F)
    (h : ∀ X' ∈ F', ∃ X ∈ F, X' = T⁻¹ * X * T) : optNorm F' ≤ optNorm F := by
  haveI : Nonempty {H : Matrix n n ℂ // H.PosDef} := ⟨⟨1, Matrix.PosDef.one⟩⟩
  show optNorm F' ≤ ⨅ H : {H : Matrix n n ℂ // H.PosDef}, familyGain H.1 F
  refine le_ciInf fun H => ?_
  have hH' : (Tᴴ * H.1 * T).PosDef :=
    H.2.conjTranspose_mul_mul_same (mulVec_injective_of_isUnit hT)
  refine (optNorm_le_familyGain F' hH').trans ?_
  refine Real.iSup_le (fun X' => ?_) (familyGain_nonneg _ _)
  obtain ⟨X, hX, hXX⟩ := h X'.1 X'.2
  rw [hXX, metricGain_congr H.2 hT]
  have hc : T * (T⁻¹ * X * T) * T⁻¹ = X := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv T hT, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv T hT, Matrix.one_mul]
  rw [hc]
  exact metricGain_le_familyGain hF H.2 hX

/-- Remark: similarity invariance (from the variational formula). -/
theorem rhoR_similar {A : Matrix n n ℝ} (hA : IsHurwitz A)
    (B T : Matrix n n ℝ) (hT : IsUnit T.det) :
    rhoR (T⁻¹ * A * T) (T⁻¹ * B * T) = rhoR A B := by
  have hS := isUnit_det_cplx hT
  have hinv : cplx T⁻¹ = (cplx T)⁻¹ := map_inv_eq (algebraMap ℝ ℂ) T
  have hA' : IsHurwitz (T⁻¹ * A * T) := by
    intro μ hμ
    apply hA
    rw [cplx_mul, cplx_mul, hinv, spectrum_conj _ _ hS] at hμ
    exact hμ
  have hfam : ∀ X' ∈ resolventFamily (T⁻¹ * A * T) (T⁻¹ * B * T),
      ∃ X ∈ resolventFamily A B, X' = (cplx T)⁻¹ * X * cplx T := by
    rintro _ (⟨ω, rfl⟩ | h0)
    · exact ⟨_, Set.mem_union_left _ ⟨ω, rfl⟩, resolvent_similar A B T hT ω⟩
    · refine ⟨0, Set.mem_union_right _ (Set.mem_singleton _), ?_⟩
      rw [Set.mem_singleton_iff.mp h0, Matrix.mul_zero, Matrix.zero_mul]
  have hfam2 : ∀ X ∈ resolventFamily A B,
      ∃ X' ∈ resolventFamily (T⁻¹ * A * T) (T⁻¹ * B * T),
        X = (cplx T)⁻¹⁻¹ * X' * (cplx T)⁻¹ := by
    rintro _ (⟨ω, rfl⟩ | h0)
    · refine ⟨_, Set.mem_union_left _ ⟨ω, rfl⟩, ?_⟩
      rw [resolvent_similar A B T hT ω, Matrix.nonsing_inv_nonsing_inv _ hS]
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS, Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS, Matrix.one_mul]
    · refine ⟨0, Set.mem_union_right _ (Set.mem_singleton _), ?_⟩
      rw [Set.mem_singleton_iff.mp h0, Matrix.mul_zero, Matrix.zero_mul]
  have h0 : ∀ A' B' : Matrix n n ℝ, (0 : Matrix n n ℂ) ∈ resolventFamily A' B' :=
    fun _ _ => Set.mem_union_right _ (Set.mem_singleton _)
  unfold rhoR
  rw [covRadius_eq_optNorm (isCompact_resolventFamily hA' _) (h0 _ _),
    covRadius_eq_optNorm (isCompact_resolventFamily hA B) (h0 _ _)]
  exact le_antisymm (optNorm_le_of_conj hS (isCompact_resolventFamily hA B) hfam)
    (optNorm_le_of_conj (Matrix.isUnit_nonsing_inv_det _ hS)
      (isCompact_resolventFamily hA' _) hfam2)

/-- Homogeneity in `B`, used in Example ex:2d: `ρ_R(A, cB) = |c| ρ_R(A,B)`. -/
theorem rhoR_smul_right (A B : Matrix n n ℝ) (c : ℝ) :
    rhoR A (c • B) = |c| * rhoR A B := by
  rcases eq_or_ne c 0 with rfl | hc
  · have hfam : resolventFamily A ((0 : ℝ) • B) = {0} := by
      ext X
      simp [resolventFamily, resolvent, cplx, eq_comm]
    unfold rhoR
    rw [hfam, abs_zero, zero_mul]
    apply le_antisymm _ (Real.sqrt_nonneg _)
    calc covRadius ({0} : Set (Matrix n n ℂ)) ≤ optNorm {0} :=
          covRadius_le_optNorm isCompact_singleton
      _ ≤ familyGain 1 {0} := optNorm_le_familyGain _ Matrix.PosDef.one
      _ ≤ 0 := Real.iSup_le (fun X => by rw [Set.mem_singleton_iff.mp X.2, metricGain_zero])
          le_rfl
  · have key : ∀ ω : ℝ, resolvent A (c • B) ω = (c : ℂ) • resolvent A B ω := by
      intro ω
      unfold resolvent
      rw [cplx_smul, Matrix.mul_smul]
    have hmem : ∀ X, X ∈ resolventFamily A (c • B) ↔ ∃ Y ∈ resolventFamily A B, X = (c : ℂ) • Y := by
      intro X
      constructor
      · rintro (⟨ω, rfl⟩ | h0)
        · exact ⟨_, Set.mem_union_left _ ⟨ω, rfl⟩, key ω⟩
        · refine ⟨0, Set.mem_union_right _ (Set.mem_singleton _), ?_⟩
          rw [Set.mem_singleton_iff.mp h0, smul_zero]
      · rintro ⟨Y, (⟨ω, rfl⟩ | h0), rfl⟩
        · exact Set.mem_union_left _ ⟨ω, key ω⟩
        · rw [Set.mem_singleton_iff.mp h0, smul_zero]
          exact Set.mem_union_right _ (Set.mem_singleton _)
    unfold rhoR
    exact covRadius_scale hc hmem

/-- Discussion: the bisection identity `ρ_R(A,B) < γ ⇔ (A, B/γ)` Riccati-stable,
for Hurwitz `A` and `γ > 0`. -/
theorem rhoR_lt_iff {A : Matrix n n ℝ} (hA : IsHurwitz A)
    (B : Matrix n n ℝ) {γ : ℝ} (hγ : 0 < γ) :
    rhoR A B < γ ↔ RiccatiStable A (γ⁻¹ • B) := by
  rw [riccatiStable_iff, rhoR_smul_right, abs_of_pos (inv_pos.mpr hγ)]
  constructor
  · intro h
    exact ⟨hA, by rw [inv_mul_lt_iff₀ hγ]; simpa using h⟩
  · rintro ⟨-, h⟩
    rwa [inv_mul_lt_iff₀ hγ, mul_one] at h


/-- `zᴴ z = ∑ |z_i|²`. -/
theorem qf_one_sum (w : n → ℂ) : qf 1 w = ∑ i, ‖w i‖ ^ 2 := by
  unfold qf
  rw [Matrix.one_mulVec]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.star_def, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Frobenius bound `‖Mz‖² ≤ ‖M‖_F² ‖z‖²` (Cauchy-Schwarz row by row). -/
theorem qf_one_mulVec_le (M : Matrix n n ℂ) (z : n → ℂ) :
    qf 1 (M *ᵥ z) ≤ (∑ i, ∑ j, ‖M i j‖ ^ 2) * qf 1 z := by
  rw [qf_one_sum, qf_one_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖(M *ᵥ z) i‖ ≤ ∑ j, ‖M i j‖ * ‖z j‖ := by
    simp only [Matrix.mulVec, dotProduct]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖M i j‖) (fun j => ‖z j‖)
  calc ‖(M *ᵥ z) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ * ‖z j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ j, ‖M i j‖ ^ 2) * ∑ j, ‖z j‖ ^ 2 := h2

/-- Remark rem:single: `ρ_cov({0, X}) = r(X)`.  The lower bound is the case
`k = 1` of Lemma lem:word.  For the upper bound, given `s > r(X)` put
`Y = X/s`; the powers `Yᵏ` tend to `0`, so `‖Y^{N+1}‖_F ≤ 1` for some `N`, and
the truncated Stein sum `H = ∑_{k ≤ N} (Yᵏ)ᴴ Yᵏ` satisfies
`H - Yᴴ H Y = I - (Y^{N+1})ᴴ Y^{N+1} ⪰ 0`, i.e. `‖X‖_H ≤ s`. -/
theorem covRadius_pair (X : Matrix n n ℂ) :
    covRadius ({0, X} : Set (Matrix n n ℂ)) = specRad X := by
  have hK : IsCompact ({0, X} : Set (Matrix n n ℂ)) := (Set.toFinite _).isCompact
  have h0 : (0 : Matrix n n ℂ) ∈ ({0, X} : Set (Matrix n n ℂ)) := Set.mem_insert _ _
  have hX : X ∈ ({0, X} : Set (Matrix n n ℂ)) := Set.mem_insert_of_mem _ (Set.mem_singleton X)
  apply le_antisymm
  · rw [covRadius_eq_optNorm hK h0]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hr0 := specRad_nonneg X
    have hs : 0 < specRad X + ε := by linarith
    set s := specRad X + ε with hsdef
    set Y : Matrix n n ℂ := (s⁻¹ : ℝ) • X with hYdef
    have hXY : X = s • Y := by
      rw [hYdef, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
    have hY : ∀ μ ∈ spectrum ℂ Y, ‖μ‖ < 1 := by
      intro μ hμ
      obtain ⟨v, hv, hYv⟩ := exists_eigvec_of_mem_spectrum hμ
      have hXv : X *ᵥ v = ((s : ℂ) * μ) • v := by
        rw [hXY, Matrix.smul_mulVec, hYv, ← Complex.coe_smul, smul_smul]
      have h1 := norm_le_specRad (mem_spectrum_of_eigvec hv hXv)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le] at h1
      by_contra hge
      push_neg at hge
      nlinarith
    have hentry : ∀ i j, Filter.Tendsto (fun k : ℕ => (Y ^ k) i j) Filter.atTop (nhds 0) := by
      intro i j
      have h := tendsto_pi_nhds.1 (tendsto_pow_mulVec_zero hY (Pi.single j 1)) i
      have hc : ∀ k : ℕ, ((Y ^ k) *ᵥ Pi.single j 1) i = (Y ^ k) i j := fun k => by
        simp [Matrix.mulVec, dotProduct, Pi.single_apply]
      simpa [hc] using h
    have hfrob : Filter.Tendsto (fun k : ℕ => ∑ i, ∑ j, ‖(Y ^ k) i j‖ ^ 2) Filter.atTop
        (nhds 0) := by
      have h := tendsto_finset_sum (Finset.univ : Finset n) fun i _ =>
        tendsto_finset_sum (Finset.univ : Finset n) fun j _ => ((hentry i j).norm.pow 2)
      have hz : (∑ i : n, ∑ j : n, ‖(0 : ℂ)‖ ^ 2) = 0 := by simp
      rw [hz] at h
      exact h
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hfrob.eventually (eventually_le_nhds one_pos))
    have hK1 : ∑ i, ∑ j, ‖(Y ^ (N + 1)) i j‖ ^ 2 ≤ 1 := hN (N + 1) (Nat.le_succ N)
    have hf : ∀ k, ((Y ^ k)ᴴ * Y ^ k).PosSemidef := fun k => by
      first
        | exact Matrix.posSemidef_conjTranspose_mul_self _
        | simpa using Matrix.PosDef.one.posSemidef.conjTranspose_mul_mul_same (Y ^ k)
    set H : Matrix n n ℂ := ∑ k ∈ Finset.range (N + 1), (Y ^ k)ᴴ * Y ^ k with hHdef
    have hH : H.PosDef := by
      rw [hHdef, Finset.sum_range_succ', pow_zero, Matrix.conjTranspose_one, Matrix.one_mul,
        add_comm]
      exact Matrix.PosDef.one.add_posSemidef (Finset.sum_induction _
        (fun M : Matrix n n ℂ => M.PosSemidef) (fun _ _ ha hb => ha.add hb)
        Matrix.PosSemidef.zero (fun k _ => hf (k + 1)))
    have hshift : Yᴴ * H * Y
        = ∑ k ∈ Finset.range (N + 1), (Y ^ (k + 1))ᴴ * Y ^ (k + 1) := by
      rw [hHdef, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_succ, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    have htel : H - ∑ k ∈ Finset.range (N + 1), (Y ^ (k + 1))ᴴ * Y ^ (k + 1)
        = 1 - (Y ^ (N + 1))ᴴ * Y ^ (N + 1) := by
      rw [hHdef, ← Finset.sum_sub_distrib]
      have h := Finset.sum_range_sub' (fun k => (Y ^ k)ᴴ * Y ^ k) (N + 1)
      simp only [pow_zero, Matrix.conjTranspose_one, Matrix.one_mul] at h
      exact h
    have hherm : (1 - (Y ^ (N + 1))ᴴ * Y ^ (N + 1)).IsHermitian := by
      show _ = _
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose]
    have hPSD : (1 - (Y ^ (N + 1))ᴴ * Y ^ (N + 1)).PosSemidef := by
      refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun z => ?_
      refine Complex.nonneg_iff.mpr ⟨?_, (im_star_dotProduct_mulVec_self hherm z).symm⟩
      show 0 ≤ qf (1 - (Y ^ (N + 1))ᴴ * Y ^ (N + 1)) z
      have hq : qf ((Y ^ (N + 1))ᴴ * Y ^ (N + 1)) z = qf 1 (Y ^ (N + 1) *ᵥ z) := by
        rw [← qf_conj, Matrix.mul_one]
      have hb := qf_one_mulVec_le (Y ^ (N + 1)) z
      have hq0 := qf_nonneg Matrix.PosDef.one z
      rw [qf_sub_left, hq]
      nlinarith
    have hP : (((1 : ℝ) ^ 2) • H - Yᴴ * H * Y).PosSemidef := by
      rw [one_pow, one_smul, hshift, htel]
      exact hPSD
    have hgainX : metricGain H X ≤ s := by
      rw [metricGain_le_iff hH hs.le]
      have hid : (s ^ 2 : ℝ) • H - Xᴴ * H * X
          = (s ^ 2 : ℝ) • (((1 : ℝ) ^ 2) • H - Yᴴ * H * Y) := by
        rw [hXY, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.smul_mul,
          Matrix.mul_smul, smul_smul, smul_sub, one_pow, one_smul, ← pow_two]
      rw [hid]
      exact posSemidef_smul_of_nonneg hP (sq_nonneg s)
    have hfam : familyGain H ({0, X} : Set (Matrix n n ℂ)) ≤ s := by
      refine Real.iSup_le (fun Z => ?_) hs.le
      rcases Z.2 with h | h
      · rw [h, metricGain_zero]
        exact hs.le
      · have h' : Z.1 = X := h
        rw [h']
        exact hgainX
    exact (optNorm_le_familyGain _ hH).trans hfam
  · have h := specRad_prod_rpow_le_covRadius hK h0 (k := 1) one_pos (fun _ => X) (fun _ => hX)
    simpa [List.ofFn_succ] using h


/-- For `H = I` the squared gain is the spectral radius of `YᴴY`. -/
theorem metricGain_one_sq [Nonempty n] (Y : Matrix n n ℂ) :
    metricGain 1 Y ^ 2 = specRad (Yᴴ * Y) := by
  have hPpsd : (Yᴴ * Y).PosSemidef := by
    first
      | exact Matrix.posSemidef_conjTranspose_mul_self Y
      | simpa using Matrix.PosDef.one.posSemidef.conjTranspose_mul_mul_same Y
  have hP : (Yᴴ * Y).IsHermitian := hPpsd.isHermitian
  have hs0 := specRad_nonneg (Yᴴ * Y)
  have hro : ∀ x : ℝ, (RCLike.ofReal x : ℂ) = (x : ℂ) := fun _ => rfl
  apply le_antisymm
  · have hle : metricGain 1 Y ≤ Real.sqrt (specRad (Yᴴ * Y)) := by
      rw [metricGain_le_iff Matrix.PosDef.one (Real.sqrt_nonneg _), Real.sq_sqrt hs0,
        Matrix.mul_one]
      set V : Matrix n n ℂ := (hP.eigenvectorUnitary : Matrix n n ℂ) with hVdef
      have hVs : V * Vᴴ = 1 := by
        first
          | exact Matrix.mem_unitaryGroup_iff.mp hP.eigenvectorUnitary.2
          | exact Unitary.mul_star_self_of_mem hP.eigenvectorUnitary.2
      have hsV : Vᴴ * V = 1 := by
        first
          | exact Matrix.mem_unitaryGroup_iff'.mp hP.eigenvectorUnitary.2
          | exact Unitary.star_mul_self_of_mem hP.eigenvectorUnitary.2
      have hspec : Yᴴ * Y = V * diagonal (RCLike.ofReal ∘ hP.eigenvalues) * Vᴴ := by
        have h := hP.spectral_theorem
        rw [Unitary.conjStarAlgAut_apply] at h
        exact h
      have hPV : (Yᴴ * Y) * V = V * diagonal (RCLike.ofReal ∘ hP.eigenvalues) := by
        conv_lhs => rw [hspec]
        rw [Matrix.mul_assoc _ Vᴴ V, hsV, Matrix.mul_one]
      have hlam : ∀ i, hP.eigenvalues i ≤ specRad (Yᴴ * Y) := by
        intro i
        have hc0 : V *ᵥ Pi.single i 1 ≠ 0 := by
          intro h
          have h2 := congrArg (fun w => Vᴴ *ᵥ w) h
          simp only [Matrix.mulVec_mulVec, hsV, Matrix.one_mulVec, Matrix.mulVec_zero] at h2
          have h3 := congrFun h2 i
          simp at h3
        have hPc : (Yᴴ * Y) *ᵥ (V *ᵥ Pi.single i 1)
            = ((hP.eigenvalues i : ℝ) : ℂ) • (V *ᵥ Pi.single i 1) := by
          rw [Matrix.mulVec_mulVec, hPV, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
          congr 1
          funext k
          rw [Matrix.mulVec_diagonal]
          by_cases hk : k = i
          · subst hk
            simp [hro]
          · simp [hk, Pi.single_apply]
        have h := norm_le_specRad (mem_spectrum_of_eigvec hc0 hPc)
        rw [Complex.norm_real, Real.norm_eq_abs] at h
        exact (le_abs_self _).trans h
      have hD : diagonal (fun i => ((specRad (Yᴴ * Y) - hP.eigenvalues i : ℝ) : ℂ))
          = (specRad (Yᴴ * Y) : ℝ) • (1 : Matrix n n ℂ)
            - diagonal (RCLike.ofReal ∘ hP.eigenvalues) := by
        ext i j
        by_cases hij : i = j
        · subst hij
          simp [Matrix.diagonal_apply, hro]
        · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
      have hdiag : (specRad (Yᴴ * Y) : ℝ) • (1 : Matrix n n ℂ) - Yᴴ * Y
          = V * diagonal (fun i => ((specRad (Yᴴ * Y) - hP.eigenvalues i : ℝ) : ℂ)) * Vᴴ := by
        rw [hD, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
          Matrix.smul_mul, hVs, ← hspec]
      rw [hdiag]
      exact (Matrix.posSemidef_diagonal_iff.mpr fun i =>
        Complex.zero_le_real.mpr (sub_nonneg.mpr (hlam i))).mul_mul_conjTranspose_same V
    have hm0 := metricGain_nonneg 1 Y
    calc metricGain 1 Y ^ 2 ≤ Real.sqrt (specRad (Yᴴ * Y)) ^ 2 :=
          pow_le_pow_left₀ hm0 hle 2
      _ = specRad (Yᴴ * Y) := Real.sq_sqrt hs0
  · obtain ⟨μ, hμ, hnorm⟩ := exists_mem_spectrum_norm_eq_specRad (Yᴴ * Y)
    obtain ⟨v, hv, hPv⟩ := exists_eigvec_of_mem_spectrum hμ
    have hq1 : star v ⬝ᵥ v = ((qf 1 v : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [qf]
      · rw [Complex.ofReal_im]
        have h := im_star_dotProduct_mulVec_self (Matrix.isHermitian_one) v
        simpa using h
    have hqpos : 0 < qf 1 v := qf_pos Matrix.PosDef.one hv
    have hval : star v ⬝ᵥ ((Yᴴ * Y) *ᵥ v) = μ * ((qf 1 v : ℝ) : ℂ) := by
      rw [hPv, dotProduct_smul, smul_eq_mul, hq1]
    have him : μ.im = 0 := by
      have h := im_star_dotProduct_mulVec_self hP v
      rw [hval] at h
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_right hqpos.ne'
    have hre : qf (Yᴴ * Y) v = μ.re * qf 1 v := by
      show (star v ⬝ᵥ ((Yᴴ * Y) *ᵥ v)).re = _
      rw [hval]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have hre0 : 0 ≤ μ.re := by
      have h := (Complex.nonneg_iff.mp (hPpsd.dotProduct_mulVec_nonneg v)).1
      have h' : 0 ≤ qf (Yᴴ * Y) v := h
      rw [hre] at h'
      nlinarith
    have hsq : ‖μ‖ ^ 2 = μ.re ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, him]
      ring
    have hμre : ‖μ‖ = μ.re := by
      rw [← Real.sqrt_sq (norm_nonneg μ), hsq, Real.sqrt_sq hre0]
    have hb := qf_le_metricGain_sq Matrix.PosDef.one Y v
    rw [Matrix.mul_one, hre] at hb
    rw [← hnorm, hμre]
    exact le_of_mul_le_mul_right hb hqpos

/-- The squared metric gain is the spectral radius of `H⁻¹XᴴHX`. -/
theorem metricGain_sq_eq_specRad [Nonempty n] {H : Matrix n n ℂ} (hH : H.PosDef)
    (X : Matrix n n ℂ) : metricGain H X ^ 2 = specRad (H⁻¹ * (Xᴴ * H * X)) := by
  obtain ⟨R, hR, hRR⟩ := exists_posDef_sqrt hH
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hR.det_pos.ne'
  have hRh : Rᴴ = R := hR.isHermitian.eq
  have hRih : (R⁻¹)ᴴ = R⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hRh]
  rw [← hRR, metricGain_eq_norm2 hR X, ← metricGain_one, metricGain_one_sq]
  have hconj : (R * R)⁻¹ * (Xᴴ * (R * R) * X)
      = R⁻¹ * ((R * X * R⁻¹)ᴴ * (R * X * R⁻¹)) * R := by
    rw [Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hRih, hRh]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul R hRu, Matrix.mul_one]
  rw [hconj]
  unfold specRad
  rw [spectrum_conj _ _ hRu]


/-- Spectral norm squared is at most the squared Frobenius norm `tr(YᴴY)`. -/
theorem metricGain_one_sq_le_frob (Y : Matrix n n ℂ) :
    metricGain 1 Y ^ 2 ≤ (Yᴴ * Y).trace.re := by
  have hF : (Yᴴ * Y).trace.re = ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.star_def, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  rw [hF]
  have hF0 : 0 ≤ ∑ i, ∑ j, ‖Y i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hle : metricGain 1 Y ≤ Real.sqrt (∑ i, ∑ j, ‖Y i j‖ ^ 2) := by
    unfold metricGain
    refine Real.iSup_le (fun z => ?_) (Real.sqrt_nonneg _)
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (qf_pos Matrix.PosDef.one z.2), qf_conj]
    exact qf_one_mulVec_le Y z.1
  calc metricGain 1 Y ^ 2 ≤ Real.sqrt (∑ i, ∑ j, ‖Y i j‖ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (metricGain_nonneg _ _) hle 2
    _ = ∑ i, ∑ j, ‖Y i j‖ ^ 2 := Real.sq_sqrt hF0

/-- The squared metric gain is at most `Re tr(H⁻¹XᴴHX)`. -/
theorem metricGain_sq_le_trace {H : Matrix n n ℂ} (hH : H.PosDef) (X : Matrix n n ℂ) :
    metricGain H X ^ 2 ≤ (H⁻¹ * (Xᴴ * H * X)).trace.re := by
  obtain ⟨R, hR, hRR⟩ := exists_posDef_sqrt hH
  have hRu : IsUnit R.det := isUnit_iff_ne_zero.mpr hR.det_pos.ne'
  have hRh : Rᴴ = R := hR.isHermitian.eq
  have hRih : (R⁻¹)ᴴ = R⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hRh]
  rw [← hRR, metricGain_eq_norm2 hR X, ← metricGain_one]
  have hconj : (R * R)⁻¹ * (Xᴴ * (R * R) * X)
      = R⁻¹ * ((R * X * R⁻¹)ᴴ * (R * X * R⁻¹)) * R := by
    rw [Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hRih, hRh]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul R hRu, Matrix.mul_one]
  rw [hconj, Matrix.trace_mul_comm, ← Matrix.mul_assoc R R⁻¹, Matrix.mul_nonsing_inv R hRu,
    Matrix.one_mul]
  exact metricGain_one_sq_le_frob _

end Main

/-! ## Section 4: the two-dimensional example

All numerical claims were rechecked in floating point before being stated:
`sup r(G) ≈ 0.27171`, `ρ_R ≈ 0.45278`, `sup ‖G‖₂ ≈ 0.50238`,
`(5/2)·0.27171 ≈ 0.6793`, `(5/2)·0.45278 ≈ 1.1319`, and identity
(eq:example_exact) holds to ~3e-16 over a grid of frequencies.
Rigorous enclosures need explicit rational-function bounds in `ω`;
the identity (eq:example_exact) is a polynomial identity provable with
`field_simp`/`ring` after reducing to 2×2 closed forms. -/

section Example

def exA : Matrix (Fin 2) (Fin 2) ℝ := !![-3, 3; -3, -1]
def exB : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1/2; -1/2, -1/2]
def exQ : Matrix (Fin 2) (Fin 2) ℝ := !![28, -5; -5, 13]

/-- Eigenvalues `-2 ± 2√2 i`. -/
theorem exA_isHurwitz : IsHurwitz exA := by
  intro μ hμ
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    Algebra.algebraMap_eq_smul_one] at hμ
  have hdet : (μ • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA).det = μ ^ 2 + 4 * μ + 12 := by
    rw [Matrix.det_fin_two]
    simp [exA] <;> ring
  rw [hdet] at hμ
  have h1 := congrArg Complex.re hμ
  have h2 := congrArg Complex.im hμ
  simp [pow_two] at h1 h2
  have hy2 : μ.im * μ.im = μ.re * μ.re + 4 * μ.re + 12 := by
    first | linarith | nlinarith [h1] | linear_combination -h1 | linear_combination h1
  have hy0 : μ.im * (2 * μ.re + 4) = 0 := by
    first | linarith | nlinarith [h2] | linear_combination h2 | linear_combination -h2
  rcases mul_eq_zero.mp hy0 with h | h
  · rw [h, mul_zero] at hy2
    nlinarith [sq_nonneg (μ.re + 2)]
  · linarith

theorem exQ_posDef : exQ.PosDef := by
  have hH : exQ.IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [exQ]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH fun x hx => ?_
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx (funext fun i => by fin_cases i <;> simp [h.1, h.2])
  have e : star x ⬝ᵥ (exQ *ᵥ x)
      = 3 * x 0 ^ 2 + 12 * x 1 ^ 2 + (5 * x 0 - x 1) ^ 2 := by
    simp [exQ, dotProduct, Matrix.mulVec, Fin.sum_univ_two] <;> ring
  rw [e]
  have h0 := sq_nonneg (x 0)
  have h1 := sq_nonneg (x 1)
  have h2 := sq_nonneg (5 * x 0 - x 1)
  rcases hx' with h | h
  · have : 0 < x 0 ^ 2 := lt_of_le_of_ne h0 (Ne.symm (pow_ne_zero 2 h))
    linarith
  · have : 0 < x 1 ^ 2 := lt_of_le_of_ne h1 (Ne.symm (pow_ne_zero 2 h))
    linarith

/-! ### Spectral bounds for the example

Every eigenvalue `μ` of `G(ω) = (iωI - A)⁻¹B` satisfies
`det(B - μ(iωI - A)) = 0`, which for this pair is
`D μ² + c μ - 3/4 = 0` with `D = 12 - ω² + 4ωi` and `c = (1 - ωi)/2`.
Since `|D|² = (12 - ω²)² + 16ω² ≥ 128` grows like `ω⁴` while `|c|` grows like
`|ω|`, this forces `|μ| ≤ 9/25` uniformly in `ω`. -/

/-- Eigenvalue scaling, `r(cX) ≤ c r(X)` for `c > 0`. -/
theorem specRad_smul_le {n : Type*} [Fintype n] [DecidableEq n] (c : ℝ) (hc : 0 < c)
    (X : Matrix n n ℂ) : specRad ((c : ℂ) • X) ≤ c * specRad X := by
  show sSup ((fun μ : ℂ => ‖μ‖) '' spectrum ℂ ((c : ℂ) • X)) ≤ c * specRad X
  refine Real.sSup_le ?_ (mul_nonneg hc.le (specRad_nonneg X))
  rintro _ ⟨μ, hμ, rfl⟩
  show ‖μ‖ ≤ c * specRad X
  obtain ⟨v, hv, hXv⟩ := exists_eigvec_of_mem_spectrum hμ
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have h : X *ᵥ v = ((c : ℂ)⁻¹ * μ) • v := by
    have h1 := congrArg (fun w => ((c : ℂ)⁻¹) • w) hXv
    simp only [Matrix.smul_mulVec, smul_smul] at h1
    rwa [inv_mul_cancel₀ hc0, one_smul] at h1
  have h2 := norm_le_specRad (mem_spectrum_of_eigvec hv h)
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hc.le,
    inv_mul_le_iff₀ hc] at h2
  exact h2

/-- `G_{A,cB} = c G_{A,B}`. -/
theorem resolvent_ex_smul (c ω : ℝ) :
    resolvent exA (c • exB) ω = (c : ℂ) • resolvent exA exB ω := by
  unfold resolvent
  rw [cplx_smul, Matrix.mul_smul]

/-- Uniform spectral bound `r(G(ω)) ≤ 9/25` for the example. -/
theorem specRad_resolvent_ex_le (ω : ℝ) : specRad (resolvent exA exB ω) ≤ 9 / 25 := by
  show sSup ((fun μ : ℂ => ‖μ‖) '' spectrum ℂ (resolvent exA exB ω)) ≤ 9 / 25
  refine Real.sSup_le ?_ (by norm_num)
  rintro _ ⟨μ, hμ, rfl⟩
  show ‖μ‖ ≤ 9 / 25
  obtain ⟨v, hv, hGv⟩ := exists_eigvec_of_mem_spectrum hμ
  have hdet0 := det_resolvent_ne_zero exA_isHurwitz ω
  have hBv : cplx exB *ᵥ v
      = μ • ((((ω : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA) *ᵥ v) := by
    have h := congrArg
      (fun w => (((ω : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA) *ᵥ w) hGv
    simp only [resolvent, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet0), Matrix.one_mul,
      Matrix.mulVec_smul] at h
    exact h
  have hzero : (cplx exB
      - μ • (((ω : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA)) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hBv, sub_self]
  have hdet : (cplx exB
      - μ • (((ω : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, hzero⟩
  have hpoly : (cplx exB
      - μ • (((ω : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA)).det
      = (((12 - ω ^ 2 : ℝ) : ℂ) + ((4 * ω : ℝ) : ℂ) * Complex.I) * μ ^ 2
        + (((1 / 2 : ℝ) : ℂ) + ((-(1 / 2) * ω : ℝ) : ℂ) * Complex.I) * μ
        - ((3 / 4 : ℝ) : ℂ) := by
    rw [Matrix.det_fin_two]
    simp [exA, exB, Matrix.one_apply]
    push_cast
    first
      | ring1
      | linear_combination (μ ^ 2 * (ω : ℂ) ^ 2) * Complex.I_sq
      | linear_combination (-(μ ^ 2 * (ω : ℂ) ^ 2)) * Complex.I_sq
  rw [hpoly] at hdet
  set D : ℂ := ((12 - ω ^ 2 : ℝ) : ℂ) + ((4 * ω : ℝ) : ℂ) * Complex.I with hD
  set c : ℂ := ((1 / 2 : ℝ) : ℂ) + ((-(1 / 2) * ω : ℝ) : ℂ) * Complex.I with hc
  have hDn : ‖D‖ ^ 2 = (12 - ω ^ 2) ^ 2 + (4 * ω) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hD, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
      Complex.I_re, Complex.I_im]
    ring
  have hcn : ‖c‖ ^ 2 = (1 / 2) ^ 2 + (-(1 / 2) * ω) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hc, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
      Complex.I_re, Complex.I_im]
    ring
  have hkey : ‖D‖ * ‖μ‖ ^ 2 ≤ ‖c‖ * ‖μ‖ + 3 / 4 := by
    have he : D * μ ^ 2 = ((3 / 4 : ℝ) : ℂ) - c * μ := by linear_combination hdet
    have hn := congrArg norm he
    rw [norm_mul, norm_pow] at hn
    rw [hn]
    calc ‖((3 / 4 : ℝ) : ℂ) - c * μ‖ ≤ ‖((3 / 4 : ℝ) : ℂ)‖ + ‖c * μ‖ := norm_sub_le _ _
      _ = ‖c‖ * ‖μ‖ + 3 / 4 := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
          ring
  by_contra hr
  push_neg at hr
  have ha0 := norm_nonneg D
  have hb0 := norm_nonneg c
  have hr0 : 0 < ‖μ‖ := by linarith
  have h1 : ‖D‖ * ‖μ‖ ^ 2 < (‖c‖ + 25 / 12) * ‖μ‖ := by nlinarith
  have h2 : ‖D‖ * ‖μ‖ < ‖c‖ + 25 / 12 := by nlinarith
  have h3 : (9 / 25) * ‖D‖ < ‖c‖ + 25 / 12 := by nlinarith
  have h4 : ((9 / 25) * ‖D‖) ^ 2 < (‖c‖ + 25 / 12) ^ 2 := by
    have : 0 ≤ (9 / 25) * ‖D‖ := by positivity
    nlinarith
  nlinarith [sq_nonneg (ω ^ 2 - 593 / 100), sq_nonneg (‖c‖ - 25 / 12)]

/-- The resolvent at `ω = 3`, verified by multiplying back. -/
def exG3 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![23 / 102 + 5 / 51 * Complex.I, -8 / 51 + 13 / 102 * Complex.I;
     -7 / 34 + 11 / 34 * Complex.I, -2 / 17 - 1 / 34 * Complex.I]

/-- The resolvent at `ω = -3` (the complex conjugate of `exG3`). -/
def exGm3 : Matrix (Fin 2) (Fin 2) ℂ :=
  !![23 / 102 - 5 / 51 * Complex.I, -8 / 51 - 13 / 102 * Complex.I;
     -7 / 34 - 11 / 34 * Complex.I, -2 / 17 + 1 / 34 * Complex.I]

/-- `G(-3) G(3)`, with trace `2/9` and determinant `1/272`. -/
def exW : Matrix (Fin 2) (Fin 2) ℂ :=
  !![41 / 306 - 5 / 204 * Complex.I, -5 / 612 + 13 / 204 * Complex.I;
     -(7 / 51) * Complex.I, 3 / 34 + 5 / 204 * Complex.I]

theorem resolvent_ex_3 : resolvent exA exB 3 = exG3 := by
  have hdet := det_resolvent_ne_zero exA_isHurwitz 3
  have hmul : ((((3 : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA) * exG3
      = cplx exB := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [exG3, exA, exB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num
  unfold resolvent
  rw [← hmul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mul]

theorem resolvent_ex_m3 : resolvent exA exB (-3) = exGm3 := by
  have hdet := det_resolvent_ne_zero exA_isHurwitz (-3)
  have hmul : ((((-3 : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA) * exGm3
      = cplx exB := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
      simp [exGm3, exA, exB, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num
  unfold resolvent
  rw [← hmul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
    Matrix.one_mul]

theorem exGm3_mul_exG3 : exGm3 * exG3 = exW := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [exGm3, exG3, exW, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- The larger eigenvalue `1/9 + √(191/22032)` of `G(-3) G(3)`. -/
theorem exW_mem_spectrum {s : ℝ} (hs : s ^ 2 = 191 / 22032) :
    (((1 / 9 + s : ℝ)) : ℂ) ∈ spectrum ℂ exW := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    Algebra.algebraMap_eq_smul_one, Matrix.det_fin_two]
  apply Complex.ext <;> simp [exW, Matrix.one_apply] <;>
    first
      | ring1
      | linear_combination hs
      | linear_combination -hs
      | linear_combination (-1 : ℝ) * hs
      | nlinarith [hs]

/-- Lower bound `ρ_R(A, B) ≥ 2/5` from the word `G(-3) G(3)` (Lemma lem:word, `k = 2`). -/
theorem two_fifths_le_rhoR_ex : (2 / 5 : ℝ) ≤ rhoR exA exB := by
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 ≤ s ∧ s ^ 2 = 191 / 22032 :=
    ⟨_, Real.sqrt_nonneg _, Real.sq_sqrt (by norm_num)⟩
  have hs1 : (11 / 225 : ℝ) ≤ s := by nlinarith
  have hW : resolvent exA exB (-3) * resolvent exA exB 3 = exW := by
    rw [resolvent_ex_m3, resolvent_ex_3, exGm3_mul_exG3]
  have hspec : 4 / 25 ≤ specRad exW := by
    have h := norm_le_specRad (exW_mem_spectrum hs)
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)] at h
    linarith
  have h := specRad_resolvent_prod_rpow_le_rhoR exA_isHurwitz exB (k := 2) two_pos ![-3, 3]
  have hprod : (List.ofFn fun j : Fin 2 => resolvent exA exB (![-3, 3] j)).prod
      = resolvent exA exB (-3) * resolvent exA exB 3 := by
    simp [List.ofFn_succ]
  rw [hprod, hW] at h
  have h45 : (4 / 25 : ℝ) ^ (((2 : ℕ) : ℝ)⁻¹) = 2 / 5 := by
    rw [show (4 / 25 : ℝ) = (2 / 5) ^ ((2 : ℕ) : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
      mul_inv_cancel₀ (by norm_num), Real.rpow_one]
  calc (2 / 5 : ℝ) = (4 / 25) ^ (((2 : ℕ) : ℝ)⁻¹) := h45.symm
    _ ≤ specRad exW ^ (((2 : ℕ) : ℝ)⁻¹) := Real.rpow_le_rpow (by norm_num) hspec (by positivity)
    _ ≤ rhoR exA exB := h

/-- `B⁻¹` for the example. -/
def exBinv : Matrix (Fin 2) (Fin 2) ℝ := !![2 / 3, -2 / 3; -2 / 3, -4 / 3]

theorem cplx_exB_mul_inv : cplx exB * cplx exBinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [exB, exBinv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num

theorem cplx_exBinv_mul : cplx exBinv * cplx exB = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [exB, exBinv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> norm_num

theorem cplx_exB_herm : (cplx exB)ᴴ = cplx exB := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [exB]

/-- The symmetry behind (eq:example_exact): `Q B⁻¹ (-iωI - A)` is symmetric. -/
theorem exQ_intertwine_poly (ω : ℝ) :
    ((((-ω : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA)ᵀ
        * cplx exBinv * cplx exQ
      = cplx exQ * cplx exBinv
        * ((((-ω : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA) := by
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [exA, exQ, exBinv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

theorem resolvent_ex_conjTranspose (ω : ℝ) :
    (resolvent exA exB ω)ᴴ
      = cplx exB * (((((-ω : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
          - cplx exA)ᵀ)⁻¹ := by
  have hMN : ((((ω : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA))ᴴ
      = ((((-ω : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA)ᵀ := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [exA, Matrix.one_apply]
  unfold resolvent
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, cplx_exB_herm, hMN]

/-- `G(ω)ᴴ Q = Q G(-ω)` for the example. -/
theorem resolvent_ex_intertwine (ω : ℝ) :
    (resolvent exA exB ω)ᴴ * cplx exQ = cplx exQ * resolvent exA exB (-ω) := by
  have hN := isUnit_iff_ne_zero.mpr (det_resolvent_ne_zero exA_isHurwitz (-ω))
  have hP := exQ_intertwine_poly ω
  set N : Matrix (Fin 2) (Fin 2) ℂ :=
    (((-ω : ℝ) : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA with hNdef
  have hNt : IsUnit Nᵀ.det := by rw [Matrix.det_transpose]; exact hN
  have hres : resolvent exA exB (-ω) = N⁻¹ * cplx exB := rfl
  rw [resolvent_ex_conjTranspose, hres]
  have key : cplx exB * (Nᵀ)⁻¹ * (cplx exQ * cplx exBinv * N) * N⁻¹ * cplx exB
      = cplx exQ * (N⁻¹ * cplx exB) := by
    rw [← hP]
    simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hNt]
    rw [← Matrix.mul_assoc (cplx exB) (cplx exBinv), cplx_exB_mul_inv, Matrix.one_mul]
  have lhs : cplx exB * (Nᵀ)⁻¹ * (cplx exQ * cplx exBinv * N) * N⁻¹ * cplx exB
      = cplx exB * (Nᵀ)⁻¹ * cplx exQ := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hN, cplx_exBinv_mul,
      Matrix.mul_one]
  exact lhs.symm.trans key

/-- (eq:example_exact). -/
theorem example_exact (ω : ℝ) :
    metricGain (cplx exQ) (resolvent exA exB ω) ^ 2
      = specRad (resolvent exA exB (-ω) * resolvent exA exB ω) := by
  have hQc := posDef_cplx_of_posDef exQ_posDef
  have hQu : IsUnit (cplx exQ).det := isUnit_iff_ne_zero.mpr hQc.det_pos.ne'
  rw [metricGain_sq_eq_specRad hQc, resolvent_ex_intertwine, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul_cancel_left _ _ hQu]

/-- `iωI - A` for the example. -/
def exM (ω : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((ω : ℂ) * Complex.I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - cplx exA

theorem resolvent_ex_adj (ω : ℝ) :
    resolvent exA exB ω = (exM ω).det⁻¹ • ((exM ω).adjugate * cplx exB) := by
  show (exM ω)⁻¹ * cplx exB = _
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_mul]

/-- `tr(G(-ω) G(ω)) = (73 + 7ω²) / (4|det(iωI - A)|²)`. -/
theorem trace_ex_W (ω : ℝ) :
    (resolvent exA exB (-ω) * resolvent exA exB ω).trace.re
      = (73 / 4 + 7 / 4 * ω ^ 2) / ((12 - ω ^ 2) ^ 2 + 16 * ω ^ 2) := by
  rw [resolvent_ex_adj, resolvent_ex_adj, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul, smul_eq_mul]
  have hw2 : ((ω : ℂ) ^ 2).re = ω ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hw2i : ((ω : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
  have hw3 : ((ω : ℂ) ^ 3).re = ω ^ 3 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hw3i : ((ω : ℂ) ^ 3).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
  have hw4 : ((ω : ℂ) ^ 4).re = ω ^ 4 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hw4i : ((ω : ℂ) ^ 4).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
  have hdet : (exM (-ω)).det * (exM ω).det = (((12 - ω ^ 2) ^ 2 + 16 * ω ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.det_fin_two, Matrix.det_fin_two]
    apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im] <;>
      simp [exM, exA, hw2, hw2i, hw3, hw3i, hw4, hw4i] <;> ring
  have htr : ((exM (-ω)).adjugate * cplx exB * ((exM ω).adjugate * cplx exB)).trace
      = ((73 / 4 + 7 / 4 * ω ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.trace_fin_two]
    apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im] <;>
      simp [Matrix.adjugate_fin_two, exM, exA, exB, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.vecMul, dotProduct, Matrix.map_apply, hw2, hw2i, hw3, hw3i, hw4, hw4i] <;> ring
  rw [htr, ← mul_inv, hdet, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re,
    inv_mul_eq_div]

/-- `‖G(ω)‖_Q ≤ 12/25` for every `ω`. -/
theorem metricGain_ex_le (ω : ℝ) :
    metricGain (cplx exQ) (resolvent exA exB ω) ≤ 12 / 25 := by
  have hQc := posDef_cplx_of_posDef exQ_posDef
  have hQu : IsUnit (cplx exQ).det := isUnit_iff_ne_zero.mpr hQc.det_pos.ne'
  have h := metricGain_sq_le_trace hQc (resolvent exA exB ω)
  rw [resolvent_ex_intertwine, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul_cancel_left _ _ hQu, trace_ex_W] at h
  have hP : 0 < (12 - ω ^ 2) ^ 2 + 16 * ω ^ 2 := by nlinarith [sq_nonneg (ω ^ 2 - 4)]
  have hT : (73 / 4 + 7 / 4 * ω ^ 2) / ((12 - ω ^ 2) ^ 2 + 16 * ω ^ 2) ≤ 144 / 625 := by
    rw [div_le_iff₀ hP]
    nlinarith [sq_nonneg (ω ^ 2 - 8983 / 1152)]
  have hm0 := metricGain_nonneg (cplx exQ) (resolvent exA exB ω)
  nlinarith

/-- `‖G(3)‖₂ > 12/25`, from the vector `(1, -i/2)`. -/
theorem twelve_25_lt_norm2_exG3 : (12 / 25 : ℝ) < norm2 exG3 := by
  rw [← metricGain_one]
  by_contra h
  push_neg at h
  have hP := (metricGain_le_iff Matrix.PosDef.one (by norm_num : (0 : ℝ) ≤ 12 / 25)).mp h
  have h0 : 0 ≤ qf (((12 / 25 : ℝ) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - exG3ᴴ * 1 * exG3)
      ![1, -(1 / 2) * Complex.I] :=
    (Complex.nonneg_iff.mp (hP.dotProduct_mulVec_nonneg _)).1
  rw [qf_sub_left, qf_smul_left, qf_conj, qf_one_sum, qf_one_sum] at h0
  simp [exG3, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.sq_norm,
    Complex.normSq_apply] at h0 <;> norm_num at h0 <;> linarith

/-- Exact evaluation of `ρ_R` in the example. -/
theorem rhoR_example :
    rhoR exA exB
      = ⨆ ω : ℝ, Real.sqrt (specRad (resolvent exA exB (-ω) * resolvent exA exB ω)) := by
  apply le_antisymm
  · have hQc := posDef_cplx_of_posDef exQ_posDef
    have h1 : rhoR exA exB ≤ familyGain (cplx exQ) (resolventFamily exA exB) :=
      (covRadius_le_optNorm (isCompact_resolventFamily exA_isHurwitz exB)).trans
        (optNorm_le_familyGain _ hQc)
    have h2 := familyGain_resolventFamily_le exA_isHurwitz exB hQc
    have h3 : ∀ ω : ℝ, metricGain (cplx exQ) (resolvent exA exB ω)
        = Real.sqrt (specRad (resolvent exA exB (-ω) * resolvent exA exB ω)) := fun ω => by
      rw [← example_exact ω, Real.sqrt_sq (metricGain_nonneg _ _)]
    simp only [h3] at h2
    exact h1.trans h2
  · refine ciSup_le fun ω => ?_
    have h := specRad_resolvent_prod_rpow_le_rhoR exA_isHurwitz exB (k := 2) two_pos ![-ω, ω]
    have hprod : (List.ofFn fun j : Fin 2 => resolvent exA exB (![-ω, ω] j)).prod
        = resolvent exA exB (-ω) * resolvent exA exB ω := by
      simp [List.ofFn_succ]
    have he : (((2 : ℕ) : ℝ)⁻¹) = 1 / 2 := by norm_num
    rw [hprod, he] at h
    rw [Real.sqrt_eq_rpow]
    exact h

/-- Strict outer bounds in (eq:sandwich) for the example. -/
theorem example_strict_sandwich :
    (⨆ ω : ℝ, specRad (resolvent exA exB ω)) < rhoR exA exB ∧
      rhoR exA exB < ⨆ ω : ℝ, norm2 (resolvent exA exB ω) := by
  refine ⟨?_, ?_⟩
  · calc (⨆ ω : ℝ, specRad (resolvent exA exB ω)) ≤ 9 / 25 :=
          ciSup_le specRad_resolvent_ex_le
      _ < 2 / 5 := by norm_num
      _ ≤ rhoR exA exB := two_fifths_le_rhoR_ex
  · have hQc := posDef_cplx_of_posDef exQ_posDef
    have h1 : rhoR exA exB ≤ familyGain (cplx exQ) (resolventFamily exA exB) :=
      (covRadius_le_optNorm (isCompact_resolventFamily exA_isHurwitz exB)).trans
        (optNorm_le_familyGain _ hQc)
    have h2 := familyGain_resolventFamily_le exA_isHurwitz exB hQc
    have h3 : (⨆ ω : ℝ, metricGain (cplx exQ) (resolvent exA exB ω)) ≤ 12 / 25 :=
      ciSup_le metricGain_ex_le
    have hbdd : BddAbove (Set.range fun ω : ℝ => norm2 (resolvent exA exB ω)) := by
      refine ⟨familyGain 1 (resolventFamily exA exB), ?_⟩
      rintro _ ⟨ω, rfl⟩
      show norm2 (resolvent exA exB ω) ≤ _
      rw [← metricGain_one]
      exact metricGain_le_familyGain (isCompact_resolventFamily exA_isHurwitz exB)
        Matrix.PosDef.one (Set.mem_union_left _ ⟨ω, rfl⟩)
    have h4 : norm2 exG3 ≤ ⨆ ω : ℝ, norm2 (resolvent exA exB ω) := by
      rw [← resolvent_ex_3]
      exact le_ciSup hbdd 3
    have h5 := twelve_25_lt_norm2_exG3
    linarith

/-- `(A, (5/2)B)` is strongly delay-independent stable but not Riccati-stable. -/
theorem example_gap :
    (⨆ ω : ℝ, specRad (resolvent exA ((5 / 2 : ℝ) • exB) ω)) < 1 ∧
      ¬ RiccatiStable exA ((5 / 2 : ℝ) • exB) := by
  constructor
  · have h : ∀ ω : ℝ, specRad (resolvent exA ((5 / 2 : ℝ) • exB) ω) ≤ 9 / 10 := fun ω => by
      rw [resolvent_ex_smul]
      calc specRad (((5 / 2 : ℝ) : ℂ) • resolvent exA exB ω)
          ≤ (5 / 2) * specRad (resolvent exA exB ω) := specRad_smul_le _ (by norm_num) _
        _ ≤ (5 / 2) * (9 / 25) :=
          mul_le_mul_of_nonneg_left (specRad_resolvent_ex_le ω) (by norm_num)
        _ = 9 / 10 := by norm_num
    calc (⨆ ω : ℝ, specRad (resolvent exA ((5 / 2 : ℝ) • exB) ω)) ≤ 9 / 10 := ciSup_le h
      _ < 1 := by norm_num
  · intro hR
    have h1 := ((riccatiStable_iff exA _).1 hR).2
    rw [rhoR_smul_right, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 2)] at h1
    have h2 := two_fifths_le_rhoR_ex
    linarith

end Example

end RiccatiStability
