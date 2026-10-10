/-
  De Cock–De Moor conjecture: complete Lean 4 + Mathlib formalization
  following DeCockDeMoor_Direct_Algebraic_Proof.tex (no density argument).
-/
import Mathlib

open Matrix

namespace DeCockDeMoor

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Part 1. The algebraic reduction (no sorry) -/

section Reduction

variable {K : Type*} [Field K]

/-- Conjugate matrices have the same characteristic polynomial.
Direct proof: conjugation commutes with the characteristic matrix. -/
lemma charpoly_conj (U X : Matrix n n K) (hU : IsUnit U.det) :
    (U⁻¹ * X * U).charpoly = X.charpoly := by
  have h1 : (Polynomial.C : K →+* Polynomial K).mapMatrix U⁻¹ *
      (Polynomial.C : K →+* Polynomial K).mapMatrix U = 1 := by
    rw [← map_mul, Matrix.nonsing_inv_mul _ hU, map_one]
  have hs : (Polynomial.C : K →+* Polynomial K).mapMatrix U⁻¹ *
      Matrix.scalar n (Polynomial.X : Polynomial K) *
      (Polynomial.C : K →+* Polynomial K).mapMatrix U =
      Matrix.scalar n (Polynomial.X : Polynomial K) := by
    rw [mul_assoc,
      (Matrix.scalar_commute (Polynomial.X : Polynomial K) (fun r' => Commute.all _ r')
        ((Polynomial.C : K →+* Polynomial K).mapMatrix U)).eq,
      ← mul_assoc, h1, one_mul]
  have hc : Matrix.charmatrix (U⁻¹ * X * U) =
      (Polynomial.C : K →+* Polynomial K).mapMatrix U⁻¹ * Matrix.charmatrix X *
      (Polynomial.C : K →+* Polynomial K).mapMatrix U := by
    unfold Matrix.charmatrix
    rw [mul_sub, sub_mul, hs, map_mul, map_mul]
  have hd : ((Polynomial.C : K →+* Polynomial K).mapMatrix U⁻¹).det *
      ((Polynomial.C : K →+* Polynomial K).mapMatrix U).det = 1 := by
    rw [← Matrix.det_mul, h1, Matrix.det_one]
  rw [Matrix.charpoly, Matrix.charpoly, hc, Matrix.det_mul, Matrix.det_mul]
  linear_combination (Matrix.charmatrix X).det * hd

theorem reduction (P Q R F : Matrix n n K)
    (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (I1 : R * Q⁻¹ * Rᵀ = P - F * P * Fᵀ)
    (I2 : F * (P + Q⁻¹) * Fᵀ = P) :
    IsUnit R.det ∧ IsUnit (1 + P * Q).det ∧
      ∃ U : Matrix n n K, IsUnit U.det ∧
        U⁻¹ * (P⁻¹ * R * Q⁻¹ * Rᵀ) * U = (1 + P * Q)⁻¹ := by
  -- F is nonsingular, from (I2)
  have hF : IsUnit F.det := by
    have h := congrArg Matrix.det I2
    simp only [Matrix.det_mul, Matrix.det_transpose] at h
    refine isUnit_iff_ne_zero.mpr (fun h0 => ?_)
    simp only [h0, zero_mul, mul_zero] at h
    exact (isUnit_iff_ne_zero.mp hP) h.symm
  have hFi : F⁻¹ * F = 1 := Matrix.nonsing_inv_mul F hF
  have hPi : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hQi : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
  have hQinv : IsUnit (Q⁻¹).det := Matrix.isUnit_nonsing_inv_det Q hQ
  -- (P + Q⁻¹) Fᵀ = F⁻¹ P
  have key2 : (P + Q⁻¹) * Fᵀ = F⁻¹ * P := by
    calc (P + Q⁻¹) * Fᵀ = (F⁻¹ * F) * ((P + Q⁻¹) * Fᵀ) := by rw [hFi, one_mul]
      _ = F⁻¹ * (F * (P + Q⁻¹) * Fᵀ) := by simp only [mul_assoc]
      _ = F⁻¹ * P := by rw [I2]
  -- P - F P Fᵀ = F Q⁻¹ Fᵀ
  have key1 : P - F * P * Fᵀ = F * Q⁻¹ * Fᵀ := by
    rw [sub_eq_iff_eq_add]
    calc P = F * (P + Q⁻¹) * Fᵀ := I2.symm
      _ = F * Q⁻¹ * Fᵀ + F * P * Fᵀ := by rw [mul_add, add_mul]; abel
  -- explicit inverse of I + PQ
  have hA : (1 + P * Q) * Q⁻¹ = P + Q⁻¹ := by
    rw [add_mul, one_mul, mul_assoc, hQi, mul_one, add_comm]
  have hY : (1 + P * Q) * (Q⁻¹ * Fᵀ * P⁻¹ * F) = 1 := by
    calc (1 + P * Q) * (Q⁻¹ * Fᵀ * P⁻¹ * F)
        = (1 + P * Q) * Q⁻¹ * Fᵀ * P⁻¹ * F := by simp only [mul_assoc]
      _ = (P + Q⁻¹) * Fᵀ * P⁻¹ * F := by rw [hA]
      _ = F⁻¹ * P * P⁻¹ * F := by rw [key2]
      _ = 1 := by rw [mul_assoc F⁻¹ P P⁻¹, hPi, mul_one, hFi]
  have hPQunit : IsUnit (1 + P * Q).det := Matrix.isUnit_det_of_right_inverse hY
  have hYinv : (1 + P * Q)⁻¹ = Q⁻¹ * Fᵀ * P⁻¹ * F := Matrix.inv_eq_right_inv hY
  -- R is nonsingular
  have hRunit : IsUnit R.det := by
    have h : R * Q⁻¹ * Rᵀ = F * Q⁻¹ * Fᵀ := I1.trans key1
    have h2 := congrArg Matrix.det h
    simp only [Matrix.det_mul, Matrix.det_transpose] at h2
    have hrhs : IsUnit (F.det * (Q⁻¹).det * F.det) := (hF.mul hQinv).mul hF
    rw [← h2] at hrhs
    exact isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hrhs)
  -- the target matrix in factored form
  have hX : P⁻¹ * R * Q⁻¹ * Rᵀ = P⁻¹ * (F * Q⁻¹ * Fᵀ) := by
    rw [← key1, ← I1]; simp only [mul_assoc]
  have hU : IsUnit (P⁻¹ * F).det := by
    rw [Matrix.det_mul]; exact (Matrix.isUnit_nonsing_inv_det P hP).mul hF
  refine ⟨hRunit, hPQunit, P⁻¹ * F, hU, ?_⟩
  rw [hYinv, hX]
  calc (P⁻¹ * F)⁻¹ * (P⁻¹ * (F * Q⁻¹ * Fᵀ)) * (P⁻¹ * F)
      = ((P⁻¹ * F)⁻¹ * (P⁻¹ * F)) * (Q⁻¹ * Fᵀ * P⁻¹ * F) := by simp only [mul_assoc]
    _ = Q⁻¹ * Fᵀ * P⁻¹ * F := by rw [Matrix.nonsing_inv_mul _ hU, one_mul]

end Reduction

/-! ## Part 2. Statement of the conjecture over ℝ -/

/-- `α ∈ σ(A)`, eigenvalues taken over `ℂ`. -/
def IsEig (A : Matrix n n ℝ) (α : ℂ) : Prop :=
  (A.map (algebraMap ℝ ℂ) - α • (1 : Matrix n n ℂ)).det = 0

/-- The nonresonance hypothesis of Section 2. -/
def Nonresonant (A B : Matrix n n ℝ) : Prop :=
  (∀ α β : ℂ, IsEig A α → IsEig A β → α * β ≠ 1) ∧
  (∀ α β : ℂ, IsEig B α → IsEig B β → α * β ≠ 1) ∧
  (∀ α β : ℂ, IsEig A α → IsEig B β → α * β ≠ 1)


/-! ## Part 3. Polynomial evaluations, vectors, telescoping (any field) -/

section Core

variable {K : Type*} [Field K]

/-- `q_B(z) = Σ_k c_k z^{N-k}`, the reversal of `p_B`. -/
noncomputable def qpoly (B : Matrix n n K) : Polynomial K :=
  ∑ k ∈ Finset.range (Fintype.card n + 1),
    Polynomial.C (B.charpoly.coeff k) * Polynomial.X ^ (Fintype.card n - k)

/-- `p_B(M)` -/
noncomputable def pM (B M : Matrix n n K) : Matrix n n K := Polynomial.aeval M B.charpoly
/-- `q_B(M)` -/
noncomputable def qM (B M : Matrix n n K) : Matrix n n K := Polynomial.aeval M (qpoly B)
/-- `F = φ_B(A) = p_B(A) q_B(A)⁻¹` -/
noncomputable def Fm (B A : Matrix n n K) : Matrix n n K := pM B A * (qM B A)⁻¹

/-- the all-ones vector, used to turn vectors into matrices -/
def oneV : n → K := fun _ => 1

lemma pM_sum (B M : Matrix n n K) :
    pM B M = ∑ k ∈ Finset.range (Fintype.card n + 1), B.charpoly.coeff k • M ^ k := by
  unfold pM
  rw [Polynomial.aeval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim]

lemma qM_sum (B M : Matrix n n K) :
    qM B M = ∑ k ∈ Finset.range (Fintype.card n + 1),
      B.charpoly.coeff k • M ^ (Fintype.card n - k) := by
  unfold qM qpoly
  simp only [map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, Algebra.smul_def]

lemma coeff_top (B : Matrix n n K) : B.charpoly.coeff (Fintype.card n) = 1 := by
  have h := (Matrix.charpoly_monic B).coeff_natDegree
  rwa [Matrix.charpoly_natDegree_eq_dim] at h

lemma pM_self (B : Matrix n n K) : pM B B = 0 := Matrix.aeval_self_charpoly B

lemma aeval_tr (M : Matrix n n K) (f : Polynomial K) :
    (Polynomial.aeval M f)ᵀ = Polynomial.aeval Mᵀ f := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range, Matrix.transpose_sum]
  simp only [Matrix.transpose_smul, Matrix.transpose_pow]

lemma pM_tr_self (B : Matrix n n K) : pM B Bᵀ = 0 := by
  unfold pM
  rw [← aeval_tr, Matrix.aeval_self_charpoly, Matrix.transpose_zero]

lemma pM_tr (B M : Matrix n n K) : (pM B M)ᵀ = pM B Mᵀ := aeval_tr M _
lemma qM_tr (B M : Matrix n n K) : (qM B M)ᵀ = qM B Mᵀ := aeval_tr M _

lemma qM_pM_comm (B M : Matrix n n K) : qM B M * pM B M = pM B M * qM B M := by
  unfold qM pM; rw [← map_mul, ← map_mul, mul_comm]

lemma qM_comm_pow (B M : Matrix n n K) (m : ℕ) : qM B M * M ^ m = M ^ m * qM B M := by
  unfold qM
  have h : Polynomial.aeval M (qpoly B) * Polynomial.aeval M ((Polynomial.X : Polynomial K) ^ m) =
      Polynomial.aeval M ((Polynomial.X : Polynomial K) ^ m) * Polynomial.aeval M (qpoly B) := by
    rw [← map_mul, ← map_mul, mul_comm]
  simpa only [map_pow, Polynomial.aeval_X] using h

lemma qM_mul_Fm (B A : Matrix n n K) (hq : IsUnit (qM B A).det) :
    qM B A * Fm B A = pM B A := by
  unfold Fm
  rw [← mul_assoc, qM_pM_comm, mul_assoc, Matrix.mul_nonsing_inv _ hq, mul_one]

/-! ### Cancellation helpers -/

lemma cancel_left (U X : Matrix n n K) (hU : IsUnit U.det) (h : U * X = 0) : X = 0 := by
  calc X = (U⁻¹ * U) * X := by rw [Matrix.nonsing_inv_mul _ hU, one_mul]
    _ = U⁻¹ * (U * X) := by rw [mul_assoc]
    _ = 0 := by rw [h, mul_zero]

lemma cancel_right (U X : Matrix n n K) (hU : IsUnit U.det) (h : X * U = 0) : X = 0 := by
  calc X = X * (U * U⁻¹) := by rw [Matrix.mul_nonsing_inv _ hU, mul_one]
    _ = (X * U) * U⁻¹ := by rw [mul_assoc]
    _ = 0 := by rw [h, zero_mul]

lemma cancel_both (U X Y : Matrix n n K) (hU : IsUnit U.det)
    (h : U * X * Uᵀ = U * Y * Uᵀ) : X = Y := by
  have hUt : IsUnit Uᵀ.det := by rwa [Matrix.det_transpose]
  have key : ∀ Z : Matrix n n K, Z = U⁻¹ * (U * Z * Uᵀ) * (Uᵀ)⁻¹ := by
    intro Z
    calc Z = (U⁻¹ * U) * Z * (Uᵀ * (Uᵀ)⁻¹) := by
          rw [Matrix.nonsing_inv_mul _ hU, Matrix.mul_nonsing_inv _ hUt, one_mul, mul_one]
      _ = U⁻¹ * (U * Z * Uᵀ) * (Uᵀ)⁻¹ := by simp only [mul_assoc]
  rw [key X, key Y, h]

lemma left_inv_unique (G G' H : Matrix n n K) (h1 : G * H = 1) (h2 : G' * H = 1) : G = G' := by
  rw [← Matrix.inv_eq_left_inv h1, ← Matrix.inv_eq_left_inv h2]

/-! ### Vector / rank-one lemmas -/

lemma dp_def (x y : n → K) : x ⬝ᵥ y = ∑ i, x i * y i := rfl

lemma mv_def (M : Matrix n n K) (x : n → K) (i : n) : (M *ᵥ x) i = ∑ j, M i j * x j := rfl

lemma vm_def (x : n → K) (M : Matrix n n K) (j : n) : (x ᵥ* M) j = ∑ i, x i * M i j := rfl

lemma vmv_mul (x y : n → K) (M : Matrix n n K) :
    vecMulVec x y * M = vecMulVec x (y ᵥ* M) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, vm_def, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma vmv_tr (x y : n → K) : (vecMulVec x y)ᵀ = vecMulVec y x := by
  ext i j; simp [Matrix.vecMulVec_apply, mul_comm]

lemma mul_vmv (M : Matrix n n K) (x y : n → K) :
    M * vecMulVec x y = vecMulVec (M *ᵥ x) y := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, mv_def, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma vmv_mul_vmv (x y z u : n → K) :
    vecMulVec x y * vecMulVec z u = (y ⬝ᵥ z) • vecMulVec x u := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, dp_def, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => by ring)

lemma vmv_eq_zero (x : n → K) (h : vecMulVec x (oneV : n → K) = 0) : x = 0 := by
  funext i
  have := congrFun (congrFun h i) i
  simpa [Matrix.vecMulVec_apply, oneV] using this

lemma dot_tr (M : Matrix n n K) (x y : n → K) : (Mᵀ *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (M *ᵥ y) := by
  simp only [dp_def, mv_def, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

lemma mulVec_single_col (M : Matrix n n K) (a : n) :
    M *ᵥ Pi.single a 1 = fun r => M r a := by
  funext r
  rw [mv_def]
  simp [Pi.single_apply]

/-! ### Telescoping for Stein equations -/

lemma stein_iter (M X Y C : Matrix n n K) (h : X - M * X * Y = C) (k : ℕ) :
    X = M ^ k * X * Y ^ k + ∑ j ∈ Finset.range k, M ^ j * C * Y ^ j := by
  have hX : X = M * X * Y + C := by rw [← h]; abel
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    calc X = M ^ k * X * Y ^ k + ∑ j ∈ Finset.range k, M ^ j * C * Y ^ j := ih
      _ = M ^ k * (M * X * Y + C) * Y ^ k + ∑ j ∈ Finset.range k, M ^ j * C * Y ^ j := by
          rw [← hX]
      _ = M ^ (k + 1) * X * Y ^ (k + 1) +
            (∑ j ∈ Finset.range k, M ^ j * C * Y ^ j + M ^ k * C * Y ^ k) := by
          rw [pow_succ M k, pow_succ' Y k]; noncomm_ring

lemma stein_kill (M X Y C Z : Matrix n n K) (h : X - M * X * Y = C) (k : ℕ)
    (hz : ∀ j < k, C * (Y ^ j * Z) = 0) : X * Z = M ^ k * X * Y ^ k * Z := by
  have hzero : ∀ j ∈ Finset.range k, M ^ j * C * Y ^ j * Z = 0 := by
    intro j hj
    rw [mul_assoc, mul_assoc, hz j (Finset.mem_range.mp hj), mul_zero]
  conv_lhs => rw [stein_iter M X Y C h k]
  rw [add_mul, Finset.sum_mul, Finset.sum_eq_zero hzero, add_zero]

lemma q_tele (B M X Y C : Matrix n n K) (h : X - M * X * Y = C) :
    qM B M * X = M ^ Fintype.card n * X * pM B Y +
      ∑ k ∈ Finset.range (Fintype.card n + 1), B.charpoly.coeff k •
        (M ^ (Fintype.card n - k) * ∑ j ∈ Finset.range k, M ^ j * C * Y ^ j) := by
  rw [qM_sum, pM_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ Fintype.card n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have e : M ^ (Fintype.card n - k) * X = M ^ Fintype.card n * X * Y ^ k +
      M ^ (Fintype.card n - k) * ∑ j ∈ Finset.range k, M ^ j * C * Y ^ j := by
    conv_lhs => rw [stein_iter M X Y C h k]
    rw [mul_add, ← mul_assoc, ← mul_assoc, pow_sub_mul_pow M hk']
  rw [smul_mul_assoc, e, smul_add, mul_smul_comm]

lemma q_kill (B M X Y C Z : Matrix n n K) (h : X - M * X * Y = C)
    (hz : ∀ j < Fintype.card n, C * (Y ^ j * Z) = 0) :
    qM B M * X * Z = M ^ Fintype.card n * X * pM B Y * Z := by
  rw [q_tele B M X Y C h, add_mul, Finset.sum_mul, Finset.sum_eq_zero, add_zero]
  intro k hk
  have hk' : k ≤ Fintype.card n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hzero : ∀ j ∈ Finset.range k, M ^ j * C * Y ^ j * Z = 0 := by
    intro j hj
    have hj' : j < Fintype.card n := lt_of_lt_of_le (Finset.mem_range.mp hj) hk'
    rw [mul_assoc, mul_assoc, hz j hj', mul_zero]
  rw [smul_mul_assoc, mul_assoc, Finset.sum_mul, Finset.sum_eq_zero hzero, mul_zero, smul_zero]

lemma comm_pow (X Y D : Matrix n n K) (h : X * D = D * Y) (i : ℕ) :
    X ^ i * D = D * Y ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc X ^ (i + 1) * D = X ^ i * (X * D) := by rw [pow_succ, mul_assoc]
      _ = X ^ i * (D * Y) := by rw [h]
      _ = (X ^ i * D) * Y := by rw [mul_assoc]
      _ = (D * Y ^ i) * Y := by rw [ih]
      _ = D * Y ^ (i + 1) := by rw [pow_succ, mul_assoc]

/-- Uniqueness consequence: the solution of `Q - BᵀQB = wwᵀ` is symmetric. -/
lemma stein_symm (B Q : Matrix n n K) (w : n → K)
    (hQ : Q - Bᵀ * Q * B = vecMulVec w w) (hq : IsUnit (qM B Bᵀ).det) : Qᵀ = Q := by
  have hT : Qᵀ - Bᵀ * Qᵀ * B = vecMulVec w w := by
    have := congrArg Matrix.transpose hQ
    rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, vmv_tr, ← mul_assoc] at this
    exact this
  have hX : (Q - Qᵀ) - Bᵀ * (Q - Qᵀ) * B = 0 := by
    have e : (Q - Qᵀ) - Bᵀ * (Q - Qᵀ) * B = (Q - Bᵀ * Q * B) - (Qᵀ - Bᵀ * Qᵀ * B) := by
      noncomm_ring
    rw [e, hQ, hT, sub_self]
  have hk := q_kill B Bᵀ (Q - Qᵀ) B 0 1 hX (fun j _ => by rw [zero_mul])
  rw [pM_self, mul_zero, zero_mul, mul_one] at hk
  exact (sub_eq_zero.mp (cancel_left _ _ hq hk)).symm

/-! ## Part 4. Krylov bases: observability, the transfer matrix `K`, the vector `s` -/

/-- index of `a : n` in `0, …, N-1` -/
noncomputable def idx (a : n) : ℕ := ((Fintype.equivFin n) a : ℕ)

lemma idx_lt (a : n) : idx a < Fintype.card n := ((Fintype.equivFin n) a).isLt

lemma idx_symm (m : ℕ) (hm : m < Fintype.card n) :
    idx ((Fintype.equivFin n).symm ⟨m, hm⟩) = m := by
  simp [idx]

/-- columns `(Bᵀ)^i w`, `0 ≤ i < N` -/
noncomputable def ObT (B : Matrix n n K) (w : n → K) : Matrix n n K :=
  Matrix.of fun r a => ((Bᵀ) ^ idx a *ᵥ w) r

lemma ObT_row (B : Matrix n n K) (w x : n → K) (a : n) :
    ((ObT B w)ᵀ *ᵥ x) a = w ⬝ᵥ (B ^ idx a *ᵥ x) := by
  have h : ((ObT B w)ᵀ *ᵥ x) a = ((Bᵀ) ^ idx a *ᵥ w) ⬝ᵥ x := by
    simp only [mv_def, dp_def, ObT, Matrix.transpose_apply, Matrix.of_apply]
  rw [h, ← Matrix.transpose_pow, dot_tr]

/-- Lemma 2.7 (observability). -/
lemma obs_unit (B Q : Matrix n n K) (w : n → K)
    (hQ : Q - Bᵀ * Q * B = vecMulVec w w) (hq : IsUnit (qM B Bᵀ).det)
    (hQu : IsUnit Q.det) : IsUnit (ObT B w).det := by
  rw [← Matrix.det_transpose, isUnit_iff_ne_zero]
  intro h0
  obtain ⟨x, hx0, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr h0
  have hdot : ∀ m < Fintype.card n, w ⬝ᵥ (B ^ m *ᵥ x) = 0 := by
    intro m hm
    have h1 := congrFun hx ((Fintype.equivFin n).symm ⟨m, hm⟩)
    rw [ObT_row, idx_symm] at h1
    exact h1
  have hz : ∀ j < Fintype.card n,
      vecMulVec w w * (B ^ j * vecMulVec x (oneV : n → K)) = 0 := by
    intro j hj
    rw [mul_vmv (B ^ j) x oneV, vmv_mul_vmv, hdot j hj, zero_smul]
  have hk := q_kill B Bᵀ Q B (vecMulVec w w) (vecMulVec x oneV) hQ hz
  rw [pM_self, mul_zero, zero_mul] at hk
  have h1 : Q * vecMulVec x (oneV : n → K) = 0 :=
    cancel_left _ _ hq (by rw [← mul_assoc]; exact hk)
  exact hx0 (vmv_eq_zero x (cancel_left _ _ hQu h1))

/-- columns `A^i v` -/
noncomputable def Kr (A : Matrix n n K) (v : n → K) : Matrix n n K :=
  Matrix.of fun r a => (A ^ idx a *ᵥ v) r

/-- the transfer matrix `K` with `K (Bᵀ)^i w = A^i v` for `i < N` -/
noncomputable def Kmat (A B : Matrix n n K) (v w : n → K) : Matrix n n K :=
  Kr A v * (ObT B w)⁻¹

lemma Kmat_spec (A B : Matrix n n K) (v w : n → K) (hO : IsUnit (ObT B w).det)
    (m : ℕ) (hm : m < Fintype.card n) :
    Kmat A B v w *ᵥ ((Bᵀ) ^ m *ᵥ w) = A ^ m *ᵥ v := by
  have hidx := idx_symm m hm
  have hcol : ObT B w *ᵥ Pi.single ((Fintype.equivFin n).symm ⟨m, hm⟩) 1 = (Bᵀ) ^ m *ᵥ w := by
    rw [mulVec_single_col]; funext r
    simp only [ObT, Matrix.of_apply, hidx]
  have hKO : Kmat A B v w * ObT B w = Kr A v := by
    unfold Kmat; rw [mul_assoc, Matrix.nonsing_inv_mul _ hO, mul_one]
  rw [← hcol, Matrix.mulVec_mulVec, hKO, mulVec_single_col]
  funext r
  simp only [Kr, Matrix.of_apply, hidx]

/-- Lemma 3.1 (transfer), one-sided. -/
lemma transfer (A B : Matrix n n K) (v w : n → K) (hO : IsUnit (ObT B w).det)
    (m : ℕ) (hm : m < Fintype.card n) (y : n → K) :
    Kmat A B v w * ((Bᵀ) ^ m * vecMulVec w y) = A ^ m * vecMulVec v y := by
  rw [mul_vmv ((Bᵀ) ^ m) w y, mul_vmv (Kmat A B v w) ((Bᵀ) ^ m *ᵥ w) y,
    Kmat_spec A B v w hO m hm, ← mul_vmv (A ^ m) v y]

/-- Lemma 3.1 (transfer), two-sided. -/
lemma transfer2 (A B : Matrix n n K) (v w : n → K) (hO : IsUnit (ObT B w).det)
    (x y : ℕ) (hx : x < Fintype.card n) (hy : y < Fintype.card n) :
    A ^ x * vecMulVec v v * Aᵀ ^ y =
      Kmat A B v w * ((Bᵀ) ^ x * vecMulVec w w * B ^ y) * (Kmat A B v w)ᵀ := by
  have h1 := transfer A B v w hO x hx v
  have h2 := transfer A B v w hO y hy w
  have h3 : vecMulVec w v * Aᵀ ^ y = vecMulVec w w * B ^ y * (Kmat A B v w)ᵀ := by
    have h4 := congrArg Matrix.transpose h2
    simp only [Matrix.transpose_mul, vmv_tr, Matrix.transpose_pow,
      Matrix.transpose_transpose] at h4
    rw [← h4]
  calc A ^ x * vecMulVec v v * Aᵀ ^ y
      = Kmat A B v w * ((Bᵀ) ^ x * vecMulVec w v) * Aᵀ ^ y := by rw [h1]
    _ = Kmat A B v w * ((Bᵀ) ^ x * (vecMulVec w v * Aᵀ ^ y)) := by simp only [mul_assoc]
    _ = Kmat A B v w * ((Bᵀ) ^ x * (vecMulVec w w * B ^ y * (Kmat A B v w)ᵀ)) := by rw [h3]
    _ = Kmat A B v w * ((Bᵀ) ^ x * vecMulVec w w * B ^ y) * (Kmat A B v w)ᵀ := by
        simp only [mul_assoc]

/-- the vector `s` with `wᵀ B^i s = δ_{i,N-1}` -/
noncomputable def svec (B : Matrix n n K) (w : n → K) : n → K :=
  ((ObT B w)ᵀ)⁻¹ *ᵥ (fun a => if idx a = Fintype.card n - 1 then (1 : K) else 0)

lemma svec_spec (B : Matrix n n K) (w : n → K) (hO : IsUnit (ObT B w).det)
    (m : ℕ) (hm : m < Fintype.card n) :
    w ⬝ᵥ (B ^ m *ᵥ svec B w) = if m = Fintype.card n - 1 then 1 else 0 := by
  have hOt : IsUnit ((ObT B w)ᵀ).det := by rwa [Matrix.det_transpose]
  have h1 : (ObT B w)ᵀ *ᵥ svec B w =
      (fun a => if idx a = Fintype.card n - 1 then (1 : K) else 0) := by
    unfold svec; rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hOt, Matrix.one_mulVec]
  have h2 := congrFun h1 ((Fintype.equivFin n).symm ⟨m, hm⟩)
  simp only [ObT_row, idx_symm] at h2
  exact h2

/-- the vectors `(Bᵀ)^i w`, `i < N`, span: a matrix killing all of them is zero -/
lemma span_zero (B : Matrix n n K) (w : n → K) (hO : IsUnit (ObT B w).det)
    (X : Matrix n n K)
    (h : ∀ m < Fintype.card n, X * ((Bᵀ) ^ m * vecMulVec w (oneV : n → K)) = 0) : X = 0 := by
  have hcol : ∀ a : n, X *ᵥ ((Bᵀ) ^ idx a *ᵥ w) = 0 := by
    intro a
    have h1 := h (idx a) (idx_lt a)
    rw [mul_vmv ((Bᵀ) ^ idx a) w oneV, mul_vmv X] at h1
    exact vmv_eq_zero _ h1
  have hXO : X * ObT B w = 0 := by
    ext r a
    have h1 := congrFun (hcol a) r
    rw [mv_def] at h1
    simp only [Matrix.mul_apply, ObT, Matrix.of_apply, Matrix.zero_apply]
    exact h1
  exact cancel_right _ _ hO hXO

/-! ## Part 5. The first identity (I1) -/

/-- Proposition 3.2 (intertwining): `q(A) R = K q(Bᵀ) Q`. -/
lemma intertwine (A B P Q R : Matrix n n K) (v w : n → K) (hO : IsUnit (ObT B w).det)
    (hR : R - A * R * B = vecMulVec v w) (hQ : Q - Bᵀ * Q * B = vecMulVec w w) :
    qM B A * R = Kmat A B v w * (qM B Bᵀ * Q) := by
  rw [q_tele B A R B _ hR, q_tele B Bᵀ Q B _ hQ, pM_self, mul_zero, mul_zero, zero_add,
    zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ Fintype.card n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [mul_smul_comm]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' : j < k := Finset.mem_range.mp hj
  have hlt : Fintype.card n - k + j < Fintype.card n := by omega
  calc A ^ (Fintype.card n - k) * (A ^ j * vecMulVec v w * B ^ j)
      = A ^ (Fintype.card n - k + j) * vecMulVec v w * B ^ j := by
        simp only [pow_add, mul_assoc]
    _ = Kmat A B v w * ((Bᵀ) ^ (Fintype.card n - k + j) * vecMulVec w w) * B ^ j := by
        rw [transfer A B v w hO _ hlt w]
    _ = Kmat A B v w * ((Bᵀ) ^ (Fintype.card n - k) * ((Bᵀ) ^ j * vecMulVec w w * B ^ j)) := by
        simp only [pow_add, mul_assoc]

/-- expansion of `q(M) X q(Y) - p(M) X p(Y)` as a double sum -/
lemma pair_expand (B M X Y : Matrix n n K) :
    qM B M * X * qM B Y - pM B M * X * pM B Y =
      ∑ a ∈ Finset.range (Fintype.card n + 1), ∑ b ∈ Finset.range (Fintype.card n + 1),
        (B.charpoly.coeff a * B.charpoly.coeff b) •
          (M ^ (Fintype.card n - a) * X * Y ^ (Fintype.card n - b) - M ^ b * X * Y ^ a) := by
  have e1 : qM B M * X * qM B Y =
      ∑ a ∈ Finset.range (Fintype.card n + 1), ∑ b ∈ Finset.range (Fintype.card n + 1),
        (B.charpoly.coeff a * B.charpoly.coeff b) •
          (M ^ (Fintype.card n - a) * X * Y ^ (Fintype.card n - b)) := by
    rw [qM_sum, qM_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
  have e2 : pM B M * X * pM B Y =
      ∑ a ∈ Finset.range (Fintype.card n + 1), ∑ b ∈ Finset.range (Fintype.card n + 1),
        (B.charpoly.coeff a * B.charpoly.coeff b) • (M ^ b * X * Y ^ a) := by
    rw [Finset.sum_comm, pM_sum, pM_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_comm (B.charpoly.coeff a) (B.charpoly.coeff b)]
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [smul_sub]

/-- the telescoped form of `M^(N-a) X Y^(N-b) - M^b X Y^a` -/
noncomputable def Tm (N : ℕ) (M C Y : Matrix n n K) (a b : ℕ) : Matrix n n K :=
  if a + b ≤ N then -∑ l ∈ Finset.range (N - a - b), M ^ (b + l) * C * Y ^ (l + a)
  else ∑ l ∈ Finset.range (a + b - N), M ^ (N - a + l) * C * Y ^ (l + (N - b))

lemma pair_term (N : ℕ) (M X Y C : Matrix n n K) (h : X - M * X * Y = C) (a b : ℕ)
    (ha : a ≤ N) (hb : b ≤ N) :
    M ^ (N - a) * X * Y ^ (N - b) - M ^ b * X * Y ^ a = Tm N M C Y a b := by
  unfold Tm
  by_cases hab : a + b ≤ N
  · rw [if_pos hab]
    have hs := stein_iter M X Y C h (N - a - b)
    have hp1 : M ^ (N - a) = M ^ b * M ^ (N - a - b) := by
      rw [← pow_add]; congr 1; omega
    have hp2 : Y ^ (N - b) = Y ^ (N - a - b) * Y ^ a := by
      rw [← pow_add]; congr 1; omega
    have e1 : M ^ b * X * Y ^ a = M ^ (N - a) * X * Y ^ (N - b) +
        ∑ l ∈ Finset.range (N - a - b), M ^ (b + l) * C * Y ^ (l + a) := by
      conv_lhs => rw [hs]
      rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      · rw [hp1, hp2]; simp only [mul_assoc]
      · refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [pow_add M b l, pow_add Y l a]; simp only [mul_assoc]
    rw [e1]; abel
  · rw [if_neg hab]
    have hs := stein_iter M X Y C h (a + b - N)
    have hp1 : M ^ b = M ^ (N - a) * M ^ (a + b - N) := by
      rw [← pow_add]; congr 1; omega
    have hp2 : Y ^ a = Y ^ (a + b - N) * Y ^ (N - b) := by
      rw [← pow_add]; congr 1; omega
    have e2 : M ^ (N - a) * X * Y ^ (N - b) = M ^ b * X * Y ^ a +
        ∑ l ∈ Finset.range (a + b - N), M ^ (N - a + l) * C * Y ^ (l + (N - b)) := by
      conv_lhs => rw [hs]
      rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      · rw [hp1, hp2]; simp only [mul_assoc]
      · refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [pow_add M (N - a) l, pow_add Y l (N - b)]; simp only [mul_assoc]
    rw [e2]; abel

lemma Tm_transfer (A B : Matrix n n K) (v w : n → K) (hO : IsUnit (ObT B w).det)
    (a b : ℕ) (ha : a ≤ Fintype.card n) (hb : b ≤ Fintype.card n) :
    Tm (Fintype.card n) A (vecMulVec v v) Aᵀ a b =
      Kmat A B v w * Tm (Fintype.card n) Bᵀ (vecMulVec w w) B a b * (Kmat A B v w)ᵀ := by
  unfold Tm
  by_cases hab : a + b ≤ Fintype.card n
  · rw [if_pos hab, if_pos hab, mul_neg, neg_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hl' := Finset.mem_range.mp hl
    exact transfer2 A B v w hO (b + l) (l + a) (by omega) (by omega)
  · rw [if_neg hab, if_neg hab, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l hl => ?_)
    have hl' := Finset.mem_range.mp hl
    exact transfer2 A B v w hO (Fintype.card n - a + l) (l + (Fintype.card n - b))
      (by omega) (by omega)

/-- Proposition 3.3. -/
lemma schur_cohn (A B P Q : Matrix n n K) (v w : n → K) (hO : IsUnit (ObT B w).det)
    (hP : P - A * P * Aᵀ = vecMulVec v v) (hQ : Q - Bᵀ * Q * B = vecMulVec w w) :
    qM B A * P * qM B Aᵀ - pM B A * P * pM B Aᵀ =
      Kmat A B v w * (qM B Bᵀ * Q * qM B B) * (Kmat A B v w)ᵀ := by
  have hB : qM B Bᵀ * Q * qM B B = qM B Bᵀ * Q * qM B B - pM B Bᵀ * Q * pM B B := by
    rw [pM_self, mul_zero, sub_zero]
  rw [hB, pair_expand, pair_expand, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have ha' : a ≤ Fintype.card n := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hb' : b ≤ Fintype.card n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  rw [pair_term _ A P Aᵀ _ hP a b ha' hb', pair_term _ Bᵀ Q B _ hQ a b ha' hb',
    mul_smul_comm, smul_mul_assoc, Tm_transfer A B v w hO a b ha' hb']

/-- Theorem 3.4: identity (I1). -/
theorem I1_generic (A B P Q R : Matrix n n K) (v w : n → K)
    (hqA : IsUnit (qM B A).det) (hqB : IsUnit (qM B Bᵀ).det)
    (hP : P - A * P * Aᵀ = vecMulVec v v) (hQ : Q - Bᵀ * Q * B = vecMulVec w w)
    (hR : R - A * R * B = vecMulVec v w) (hQu : IsUnit Q.det) :
    R * Q⁻¹ * Rᵀ = P - Fm B A * P * (Fm B A)ᵀ := by
  have hO := obs_unit B Q w hQ hqB hQu
  have hQs := stein_symm B Q w hQ hqB
  have hint := intertwine A B P Q R v w hO hR hQ
  have hsc := schur_cohn A B P Q v w hO hP hQ
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQu
  have htqB : (qM B Bᵀ)ᵀ = qM B B := by rw [qM_tr, Matrix.transpose_transpose]
  apply cancel_both (qM B A) _ _ hqA
  calc qM B A * (R * Q⁻¹ * Rᵀ) * (qM B A)ᵀ
      = (qM B A * R) * Q⁻¹ * (qM B A * R)ᵀ := by
        rw [Matrix.transpose_mul (qM B A) R]; simp only [mul_assoc]
    _ = Kmat A B v w * (qM B Bᵀ * Q) * Q⁻¹ * (Kmat A B v w * (qM B Bᵀ * Q))ᵀ := by
        rw [hint]
    _ = Kmat A B v w * (qM B Bᵀ * (Q * Q⁻¹) * Q * qM B B) * (Kmat A B v w)ᵀ := by
        rw [Matrix.transpose_mul (Kmat A B v w), Matrix.transpose_mul (qM B Bᵀ) Q, hQs, htqB]
        simp only [mul_assoc]
    _ = Kmat A B v w * (qM B Bᵀ * Q * qM B B) * (Kmat A B v w)ᵀ := by
        rw [hQQ, mul_one]
    _ = qM B A * P * qM B Aᵀ - pM B A * P * pM B Aᵀ := hsc.symm
    _ = qM B A * (P - Fm B A * P * (Fm B A)ᵀ) * (qM B A)ᵀ := by
        have e : qM B A * (P - Fm B A * P * (Fm B A)ᵀ) * (qM B A)ᵀ =
            qM B A * P * (qM B A)ᵀ - (qM B A * Fm B A) * P * (qM B A * Fm B A)ᵀ := by
          rw [Matrix.transpose_mul (qM B A) (Fm B A)]; noncomm_ring
        rw [e, qM_mul_Fm B A hqA, qM_tr, pM_tr]

/-! ## Part 6. The second identity (I2) -/

/-- the Bezoutian `D = Σ_k c_k Σ_{j<k} (Bᵀ)^j w wᵀ B^{k-1-j}` -/
noncomputable def Dm (B : Matrix n n K) (w : n → K) : Matrix n n K :=
  ∑ k ∈ Finset.range (Fintype.card n + 1), B.charpoly.coeff k •
    ∑ j ∈ Finset.range k, (Bᵀ) ^ j * vecMulVec w w * B ^ (k - 1 - j)

lemma pow_sub_pow_sum (M Y : Matrix n n K) (k : ℕ) :
    ∑ j ∈ Finset.range k, M ^ j * (Y - M) * Y ^ (k - 1 - j) = Y ^ k - M ^ k := by
  have h : ∀ j ∈ Finset.range k, M ^ j * (Y - M) * Y ^ (k - 1 - j) =
      M ^ j * Y ^ (k - j) - M ^ (j + 1) * Y ^ (k - (j + 1)) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have e1 : k - j = (k - 1 - j) + 1 := by omega
    have e2 : k - (j + 1) = k - 1 - j := by omega
    rw [e1, e2, pow_succ' Y (k - 1 - j), pow_succ M j]
    noncomm_ring
  calc ∑ j ∈ Finset.range k, M ^ j * (Y - M) * Y ^ (k - 1 - j)
      = ∑ j ∈ Finset.range k, (M ^ j * Y ^ (k - j) - M ^ (j + 1) * Y ^ (k - (j + 1))) :=
        Finset.sum_congr rfl h
    _ = M ^ 0 * Y ^ (k - 0) - M ^ k * Y ^ (k - k) :=
        Finset.sum_range_sub' (fun j => M ^ j * Y ^ (k - j)) k
    _ = Y ^ k - M ^ k := by simp

/-- Lemma 4.1(ii): `p(A) = -K D`. -/
lemma pA_eq (A B : Matrix n n K) (v w : n → K) (hO : IsUnit (ObT B w).det)
    (hB : B = A + vecMulVec v w) : pM B A = -(Kmat A B v w * Dm B w) := by
  have hBA : B - A = vecMulVec v w := by rw [hB, add_sub_cancel_left]
  have h1 : pM B B - pM B A = ∑ k ∈ Finset.range (Fintype.card n + 1), B.charpoly.coeff k •
      ∑ j ∈ Finset.range k, A ^ j * vecMulVec v w * B ^ (k - 1 - j) := by
    rw [pM_sum, pM_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← smul_sub, ← pow_sub_pow_sum A B k, hBA]
  have h2 : Kmat A B v w * Dm B w = ∑ k ∈ Finset.range (Fintype.card n + 1),
      B.charpoly.coeff k • ∑ j ∈ Finset.range k, A ^ j * vecMulVec v w * B ^ (k - 1 - j) := by
    unfold Dm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [mul_smul_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjN : j < Fintype.card n := by
      have := Finset.mem_range.mp hj; have := Finset.mem_range.mp hk; omega
    calc Kmat A B v w * ((Bᵀ) ^ j * vecMulVec w w * B ^ (k - 1 - j))
        = Kmat A B v w * ((Bᵀ) ^ j * vecMulVec w w) * B ^ (k - 1 - j) := by
          simp only [mul_assoc]
      _ = A ^ j * vecMulVec v w * B ^ (k - 1 - j) := by rw [transfer A B v w hO j hjN w]
  rw [pM_self, zero_sub] at h1
  rw [h2, ← h1, neg_neg]

/-- Lemma 4.1(i): `Dᵀ = D`. -/
lemma Dm_symm (B : Matrix n n K) (w : n → K) : (Dm B w)ᵀ = Dm B w := by
  unfold Dm
  rw [Matrix.transpose_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.transpose_smul, Matrix.transpose_sum]
  congr 1
  calc ∑ j ∈ Finset.range k, ((Bᵀ) ^ j * vecMulVec w w * B ^ (k - 1 - j))ᵀ
      = ∑ j ∈ Finset.range k,
          (Bᵀ) ^ (k - 1 - j) * vecMulVec w w * B ^ (k - 1 - (k - 1 - j)) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hj' := Finset.mem_range.mp hj
        have e : k - 1 - (k - 1 - j) = j := by omega
        rw [e]
        simp only [Matrix.transpose_mul, Matrix.transpose_pow, Matrix.transpose_transpose,
          vmv_tr, mul_assoc]
    _ = ∑ j ∈ Finset.range k, (Bᵀ) ^ j * vecMulVec w w * B ^ (k - 1 - j) :=
        Finset.sum_range_reflect (fun j => (Bᵀ) ^ j * vecMulVec w w * B ^ (k - 1 - j)) k

/-- Lemma 4.1(i): `Bᵀ D = D B`. -/
lemma Dm_comm (B : Matrix n n K) (w : n → K) : Bᵀ * Dm B w = Dm B w * B := by
  have tel : ∀ k : ℕ,
      Bᵀ * (∑ j ∈ Finset.range k, (Bᵀ) ^ j * vecMulVec w w * B ^ (k - 1 - j)) -
        (∑ j ∈ Finset.range k, (Bᵀ) ^ j * vecMulVec w w * B ^ (k - 1 - j)) * B =
      (Bᵀ) ^ k * vecMulVec w w - vecMulVec w w * B ^ k := by
    intro k
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    calc ∑ j ∈ Finset.range k, (Bᵀ * ((Bᵀ) ^ j * vecMulVec w w * B ^ (k - 1 - j)) -
            (Bᵀ) ^ j * vecMulVec w w * B ^ (k - 1 - j) * B)
        = ∑ j ∈ Finset.range k, ((Bᵀ) ^ (j + 1) * vecMulVec w w * B ^ (k - (j + 1)) -
            (Bᵀ) ^ j * vecMulVec w w * B ^ (k - j)) := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          have hj' := Finset.mem_range.mp hj
          have e1 : k - (j + 1) = k - 1 - j := by omega
          have e2 : k - j = (k - 1 - j) + 1 := by omega
          rw [e1, e2, pow_succ' (Bᵀ) j, pow_succ B (k - 1 - j)]
          simp only [mul_assoc]
      _ = (Bᵀ) ^ k * vecMulVec w w * B ^ (k - k) - (Bᵀ) ^ 0 * vecMulVec w w * B ^ (k - 0) :=
          Finset.sum_range_sub (fun j => (Bᵀ) ^ j * vecMulVec w w * B ^ (k - j)) k
      _ = (Bᵀ) ^ k * vecMulVec w w - vecMulVec w w * B ^ k := by simp
  have key : Bᵀ * Dm B w - Dm B w * B =
      pM B Bᵀ * vecMulVec w w - vecMulVec w w * pM B B := by
    unfold Dm
    rw [pM_sum, pM_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [mul_smul_comm, smul_mul_assoc, ← smul_sub, tel k]
  rw [pM_self, pM_tr_self, zero_mul, mul_zero, sub_zero, sub_eq_zero] at key
  exact key

lemma qM_Dm_comm (B : Matrix n n K) (w : n → K) :
    qM B Bᵀ * Dm B w = Dm B w * qM B B := by
  rw [qM_sum, qM_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [smul_mul_assoc, mul_smul_comm, comm_pow _ _ _ (Dm_comm B w)]

/-- Lemma 4.1(iii): `D s = w`, in matrix form. -/
lemma Dm_s (B : Matrix n n K) (w : n → K) (hO : IsUnit (ObT B w).det)
    (hN : 0 < Fintype.card n) :
    Dm B w * vecMulVec (svec B w) (oneV : n → K) = vecMulVec w oneV := by
  have term : ∀ k j : ℕ, k ≤ Fintype.card n → j < k →
      (Bᵀ) ^ j * vecMulVec w w * B ^ (k - 1 - j) * vecMulVec (svec B w) (oneV : n → K) =
        (if k - 1 - j = Fintype.card n - 1 then (1 : K) else 0) •
          ((Bᵀ) ^ j * vecMulVec w oneV) := by
    intro k j hk hj
    rw [mul_assoc, mul_vmv (B ^ (k - 1 - j)) (svec B w) oneV,
      mul_assoc ((Bᵀ) ^ j) (vecMulVec w w), vmv_mul_vmv,
      svec_spec B w hO (k - 1 - j) (by omega), mul_smul_comm]
  unfold Dm
  rw [Finset.sum_mul, Finset.sum_eq_single (Fintype.card n)]
  · rw [smul_mul_assoc, Finset.sum_mul, Finset.sum_eq_single 0]
    · rw [term _ _ le_rfl hN, if_pos (by omega), one_smul, pow_zero, one_mul, coeff_top,
        one_smul]
    · intro j hj hj0
      have hj' := Finset.mem_range.mp hj
      rw [term _ _ le_rfl hj', if_neg (by omega), zero_smul]
    · intro h0; exact absurd (Finset.mem_range.mpr hN) h0
  · intro k hk hkN
    have hk' : k ≤ Fintype.card n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [smul_mul_assoc, Finset.sum_mul, Finset.sum_eq_zero, smul_zero]
    intro j hj
    have hj' := Finset.mem_range.mp hj
    rw [term _ _ hk' hj', if_neg (by omega), zero_smul]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

/-- `D B^i s = (Bᵀ)^i w`, in matrix form. -/
lemma Dm_Bs (B : Matrix n n K) (w : n → K) (hO : IsUnit (ObT B w).det)
    (hN : 0 < Fintype.card n) (i : ℕ) :
    Dm B w * (B ^ i * vecMulVec (svec B w) (oneV : n → K)) = (Bᵀ) ^ i * vecMulVec w oneV := by
  rw [← mul_assoc, ← comm_pow _ _ _ (Dm_comm B w) i, mul_assoc, Dm_s B w hO hN]

lemma Dm_unit (B : Matrix n n K) (w : n → K) (hO : IsUnit (ObT B w).det)
    (hN : 0 < Fintype.card n) : IsUnit (Dm B w).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  obtain ⟨x, hx0, hx⟩ := (Matrix.exists_vecMul_eq_zero_iff).mpr h0
  have hXD : vecMulVec (oneV : n → K) x * Dm B w = 0 := by
    rw [vmv_mul, hx]; ext i j; simp [Matrix.vecMulVec_apply]
  have hX : vecMulVec (oneV : n → K) x = 0 := by
    apply span_zero B w hO
    intro m _
    rw [← Dm_Bs B w hO hN m, ← mul_assoc, hXD, zero_mul]
  apply hx0
  have h1 := congrArg Matrix.transpose hX
  rw [vmv_tr, Matrix.transpose_zero] at h1
  exact vmv_eq_zero x h1

/-- Lemma 4.1(iv), first half: `Q B^i s = (Bᵀ)^{N-1-i} Q B^{N-1} s`. -/
lemma Q_s_shift (B Q : Matrix n n K) (w : n → K) (hO : IsUnit (ObT B w).det)
    (hQ : Q - Bᵀ * Q * B = vecMulVec w w) (i : ℕ) (hi : i ≤ Fintype.card n - 1) :
    Q * (B ^ i * vecMulVec (svec B w) (oneV : n → K)) =
      (Bᵀ) ^ (Fintype.card n - 1 - i) *
        (Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K))) := by
  have hz : ∀ j < Fintype.card n - 1 - i,
      vecMulVec w w * (B ^ j * (B ^ i * vecMulVec (svec B w) (oneV : n → K))) = 0 := by
    intro j hj
    rw [← mul_assoc (B ^ j), ← pow_add, mul_vmv (B ^ (j + i)) (svec B w) oneV, vmv_mul_vmv,
      svec_spec B w hO (j + i) (by omega), if_neg (by omega), zero_smul]
  rw [stein_kill Bᵀ Q B (vecMulVec w w) _ hQ (Fintype.card n - 1 - i) hz, mul_assoc,
    mul_assoc, ← mul_assoc (B ^ (Fintype.card n - 1 - i)), ← pow_add,
    show Fintype.card n - 1 - i + i = Fintype.card n - 1 by omega]

/-- Lemma 4.1(iv), second half: `q(Bᵀ) Q B^{N-1} s = w`. -/
lemma qU (B Q : Matrix n n K) (w : n → K) (hO : IsUnit (ObT B w).det)
    (hQ : Q - Bᵀ * Q * B = vecMulVec w w) (hN : 0 < Fintype.card n) :
    qM B Bᵀ * (Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K))) =
      vecMulVec w oneV := by
  have hQ' : Q = Bᵀ * Q * B + vecMulVec w w := by rw [← hQ]; abel
  have hW : vecMulVec w w * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K)) =
      vecMulVec w oneV := by
    rw [mul_vmv (B ^ (Fintype.card n - 1)) (svec B w) oneV, vmv_mul_vmv,
      svec_spec B w hO (Fintype.card n - 1) (by omega), if_pos rfl, one_smul]
  have hBB : B * B ^ (Fintype.card n - 1) = B ^ Fintype.card n := by
    rw [← pow_succ']; congr 1; omega
  -- (a)  U = Bᵀ Q B^N s + w
  have ha : Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K)) =
      Bᵀ * (Q * (B ^ Fintype.card n * vecMulVec (svec B w) (oneV : n → K))) +
        vecMulVec w oneV := by
    have e1 : Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K)) =
        (Bᵀ * Q * B + vecMulVec w w) *
          (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K)) := by
      conv_lhs => rw [hQ']
    rw [e1, add_mul, hW, mul_assoc, mul_assoc, ← mul_assoc B, hBB]
  -- (b)  B^N = -Σ_{k<N} c_k B^k
  have hp : ∑ k ∈ Finset.range (Fintype.card n + 1), B.charpoly.coeff k • B ^ k = 0 := by
    rw [← pM_sum]; exact pM_self B
  rw [Finset.sum_range_succ, coeff_top, one_smul] at hp
  have hBN : B ^ Fintype.card n = -∑ k ∈ Finset.range (Fintype.card n),
      B.charpoly.coeff k • B ^ k := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hp
  -- (c)
  have hsum : Bᵀ * (Q * (B ^ Fintype.card n * vecMulVec (svec B w) (oneV : n → K))) =
      -∑ k ∈ Finset.range (Fintype.card n), B.charpoly.coeff k •
        ((Bᵀ) ^ (Fintype.card n - k) *
          (Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K)))) := by
    rw [hBN, neg_mul, Finset.sum_mul, mul_neg, mul_neg, Finset.mul_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have hk' := Finset.mem_range.mp hk
    rw [smul_mul_assoc, mul_smul_comm, mul_smul_comm, Q_s_shift B Q w hO hQ k (by omega),
      ← mul_assoc Bᵀ ((Bᵀ) ^ (Fintype.card n - 1 - k)), ← pow_succ' (Bᵀ),
      show Fintype.card n - 1 - k + 1 = Fintype.card n - k by omega]
  have hq : qM B Bᵀ * (Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K))) =
      ∑ k ∈ Finset.range (Fintype.card n), B.charpoly.coeff k •
        ((Bᵀ) ^ (Fintype.card n - k) *
          (Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K)))) +
      Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K)) := by
    rw [qM_sum, Finset.sum_mul, Finset.sum_range_succ, coeff_top, Nat.sub_self, pow_zero,
      one_smul, one_mul]
    congr 1
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [smul_mul_assoc]
  have hU2 : Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K)) =
      -∑ k ∈ Finset.range (Fintype.card n), B.charpoly.coeff k •
        ((Bᵀ) ^ (Fintype.card n - k) *
          (Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K)))) +
        vecMulVec w oneV := by
    rw [← hsum]; exact ha
  rw [hq]
  calc ∑ k ∈ Finset.range (Fintype.card n), B.charpoly.coeff k •
        ((Bᵀ) ^ (Fintype.card n - k) *
          (Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K)))) +
        Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K))
      = ∑ k ∈ Finset.range (Fintype.card n), B.charpoly.coeff k •
          ((Bᵀ) ^ (Fintype.card n - k) *
            (Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K)))) +
        (-∑ k ∈ Finset.range (Fintype.card n), B.charpoly.coeff k •
          ((Bᵀ) ^ (Fintype.card n - k) *
            (Q * (B ^ (Fintype.card n - 1) * vecMulVec (svec B w) (oneV : n → K)))) +
          vecMulVec w oneV) := by
        rw [← hU2]
    _ = vecMulVec w oneV := by abel

/-- Proposition 4.2: `D Q⁻¹ D = q(Bᵀ) Q q(B)`. -/
lemma prop_S (B Q : Matrix n n K) (w : n → K) (hO : IsUnit (ObT B w).det)
    (hQ : Q - Bᵀ * Q * B = vecMulVec w w) (hQu : IsUnit Q.det) (hN : 0 < Fintype.card n) :
    Dm B w * Q⁻¹ * Dm B w = qM B Bᵀ * Q * qM B B := by
  have hD := Dm_unit B w hO hN
  -- J = q(Bᵀ) Q D⁻¹ reverses the Krylov basis
  have hJ : ∀ i < Fintype.card n,
      qM B Bᵀ * Q * (Dm B w)⁻¹ * ((Bᵀ) ^ i * vecMulVec w (oneV : n → K)) =
        (Bᵀ) ^ (Fintype.card n - 1 - i) * vecMulVec w oneV := by
    intro i hi
    have h1 : (Dm B w)⁻¹ * ((Bᵀ) ^ i * vecMulVec w (oneV : n → K)) =
        B ^ i * vecMulVec (svec B w) oneV := by
      rw [← Dm_Bs B w hO hN i, ← mul_assoc, Matrix.nonsing_inv_mul _ hD, one_mul]
    rw [mul_assoc (qM B Bᵀ * Q), h1, mul_assoc (qM B Bᵀ), Q_s_shift B Q w hO hQ i (by omega),
      ← mul_assoc (qM B Bᵀ), qM_comm_pow, mul_assoc, qU B Q w hO hQ hN]
  have hJJ : (qM B Bᵀ * Q * (Dm B w)⁻¹) * (qM B Bᵀ * Q * (Dm B w)⁻¹) = 1 := by
    rw [← sub_eq_zero]
    apply span_zero B w hO
    intro m hm
    rw [sub_mul, one_mul, mul_assoc (qM B Bᵀ * Q * (Dm B w)⁻¹) (qM B Bᵀ * Q * (Dm B w)⁻¹),
      hJ m hm, hJ (Fintype.card n - 1 - m) (by omega),
      show Fintype.card n - 1 - (Fintype.card n - 1 - m) = m by omega, sub_self]
  have hDq : (Dm B w)⁻¹ * qM B Bᵀ = qM B B * (Dm B w)⁻¹ := by
    calc (Dm B w)⁻¹ * qM B Bᵀ = (Dm B w)⁻¹ * (qM B Bᵀ * Dm B w) * (Dm B w)⁻¹ := by
          rw [mul_assoc, mul_assoc, Matrix.mul_nonsing_inv _ hD, mul_one]
      _ = (Dm B w)⁻¹ * (Dm B w * qM B B) * (Dm B w)⁻¹ := by rw [qM_Dm_comm]
      _ = qM B B * (Dm B w)⁻¹ := by
          rw [← mul_assoc, Matrix.nonsing_inv_mul _ hD, one_mul]
  have hGH : (qM B Bᵀ * Q * qM B B) * ((Dm B w)⁻¹ * Q * (Dm B w)⁻¹) = 1 := by
    rw [← hJJ]
    calc (qM B Bᵀ * Q * qM B B) * ((Dm B w)⁻¹ * Q * (Dm B w)⁻¹)
        = qM B Bᵀ * Q * (qM B B * (Dm B w)⁻¹) * (Q * (Dm B w)⁻¹) := by simp only [mul_assoc]
      _ = qM B Bᵀ * Q * ((Dm B w)⁻¹ * qM B Bᵀ) * (Q * (Dm B w)⁻¹) := by rw [hDq]
      _ = (qM B Bᵀ * Q * (Dm B w)⁻¹) * (qM B Bᵀ * Q * (Dm B w)⁻¹) := by simp only [mul_assoc]
  have hDH : (Dm B w * Q⁻¹ * Dm B w) * ((Dm B w)⁻¹ * Q * (Dm B w)⁻¹) = 1 := by
    have hQi : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQu
    have hDi : Dm B w * (Dm B w)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hD
    calc (Dm B w * Q⁻¹ * Dm B w) * ((Dm B w)⁻¹ * Q * (Dm B w)⁻¹)
        = Dm B w * (Q⁻¹ * ((Dm B w * (Dm B w)⁻¹) * Q)) * (Dm B w)⁻¹ := by
          simp only [mul_assoc]
      _ = 1 := by rw [hDi, one_mul, hQi, mul_one, hDi]
  exact left_inv_unique _ _ _ hDH hGH

/-- Theorem 4.3: identity (I2). -/
theorem I2_generic (A B P Q : Matrix n n K) (v w : n → K) (hB : B = A + vecMulVec v w)
    (hqA : IsUnit (qM B A).det) (hqB : IsUnit (qM B Bᵀ).det)
    (hP : P - A * P * Aᵀ = vecMulVec v v) (hQ : Q - Bᵀ * Q * B = vecMulVec w w)
    (hQu : IsUnit Q.det) (hN : 0 < Fintype.card n) :
    Fm B A * (P + Q⁻¹) * (Fm B A)ᵀ = P := by
  have hO := obs_unit B Q w hQ hqB hQu
  have hsc := schur_cohn A B P Q v w hO hP hQ
  have hS := prop_S B Q w hO hQ hQu hN
  have hpa := pA_eq A B v w hO hB
  have h1 : pM B A * Q⁻¹ * pM B Aᵀ =
      Kmat A B v w * (qM B Bᵀ * Q * qM B B) * (Kmat A B v w)ᵀ := by
    rw [← pM_tr, hpa, Matrix.transpose_neg, Matrix.transpose_mul, Dm_symm, ← hS]
    noncomm_ring
  apply cancel_both (qM B A) _ _ hqA
  calc qM B A * (Fm B A * (P + Q⁻¹) * (Fm B A)ᵀ) * (qM B A)ᵀ
      = (qM B A * Fm B A) * (P + Q⁻¹) * (qM B A * Fm B A)ᵀ := by
        rw [Matrix.transpose_mul (qM B A) (Fm B A)]; simp only [mul_assoc]
    _ = pM B A * (P + Q⁻¹) * pM B Aᵀ := by rw [qM_mul_Fm B A hqA, pM_tr]
    _ = pM B A * P * pM B Aᵀ + pM B A * Q⁻¹ * pM B Aᵀ := by noncomm_ring
    _ = pM B A * P * pM B Aᵀ + (qM B A * P * qM B Aᵀ - pM B A * P * pM B Aᵀ) := by
        rw [h1, hsc]
    _ = qM B A * P * qM B Aᵀ := by abel
    _ = qM B A * P * (qM B A)ᵀ := by rw [qM_tr]

end Core

/-! ## Part 7. From nonresonance to invertibility of `q_B(M)` -/

/-- `p_B(t) = det(t I - B)` -/
lemma eval_charpoly' (B : Matrix n n ℂ) (t : ℂ) :
    B.charpoly.eval t = (t • (1 : Matrix n n ℂ) - B).det := by
  rw [Matrix.charpoly, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.charmatrix_apply_eq]
  · simp [Matrix.charmatrix_apply_ne B i j h, Matrix.one_apply_ne h]

lemma qM_isUnit_complex (M B : Matrix n n ℂ)
    (h : ∀ α β : ℂ, (M - α • (1 : Matrix n n ℂ)).det = 0 →
      (B - β • (1 : Matrix n n ℂ)).det = 0 → α * β ≠ 1) :
    IsUnit (qM B M).det := by
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [Matrix.det_isEmpty]; exact isUnit_one
  haveI := hn
  rw [← Matrix.isUnit_iff_isUnit_det]
  by_contra hnu
  have h0 : (0 : ℂ) ∈ spectrum ℂ (qM B M) := by
    rw [spectrum.mem_iff, map_zero, zero_sub, IsUnit.neg_iff]; exact hnu
  have hnon : (spectrum ℂ M).Nonempty :=
    spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ M
  unfold qM at h0
  rw [spectrum.map_polynomial_aeval_of_nonempty M _ hnon] at h0
  obtain ⟨μ, hμ, hev⟩ := h0
  have hdetM : (M - μ • (1 : Matrix n n ℂ)).det = 0 := by
    rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero, not_not] at hμ
    rw [← neg_sub, Matrix.det_neg, hμ, mul_zero]
  have hsum : ∑ k ∈ Finset.range (Fintype.card n + 1),
      B.charpoly.coeff k * μ ^ (Fintype.card n - k) = 0 := by
    simpa [qpoly, Polynomial.eval_finset_sum] using hev
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [Finset.sum_eq_single (Fintype.card n)] at hsum
    · rw [coeff_top, Nat.sub_self, pow_zero, mul_one] at hsum; exact one_ne_zero hsum
    · intro k hk hkN
      have hk' := Finset.mem_range.mp hk
      rw [zero_pow (by omega), mul_zero]
    · intro hc; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) hc
  have hp : B.charpoly.eval μ⁻¹ = 0 := by
    rw [Polynomial.eval_eq_sum_range, Matrix.charpoly_natDegree_eq_dim]
    have e : ∑ k ∈ Finset.range (Fintype.card n + 1), B.charpoly.coeff k * μ⁻¹ ^ k =
        μ⁻¹ ^ Fintype.card n * ∑ k ∈ Finset.range (Fintype.card n + 1),
          B.charpoly.coeff k * μ ^ (Fintype.card n - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k ≤ Fintype.card n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [pow_sub₀ μ hμ0 hk', inv_pow, inv_pow]
      field_simp
    rw [e, hsum, mul_zero]
  have hdetB : (B - μ⁻¹ • (1 : Matrix n n ℂ)).det = 0 := by
    have e := eval_charpoly' B μ⁻¹
    rw [hp] at e
    rw [← neg_sub, Matrix.det_neg, ← e, mul_zero]
  exact h μ μ⁻¹ hdetM hdetB (mul_inv_cancel₀ hμ0)

lemma mapC_smul (c : ℝ) (X : Matrix n n ℝ) :
    (algebraMap ℝ ℂ).mapMatrix (c • X) = (algebraMap ℝ ℂ c) • (algebraMap ℝ ℂ).mapMatrix X := by
  ext i j; simp

lemma qM_map (B M : Matrix n n ℝ) :
    (qM B M).map (algebraMap ℝ ℂ) = qM (B.map (algebraMap ℝ ℂ)) (M.map (algebraMap ℝ ℂ)) := by
  simp only [← RingHom.mapMatrix_apply]
  rw [qM_sum, qM_sum, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [mapC_smul, map_pow]
  simp only [RingHom.mapMatrix_apply, Matrix.charpoly_map, Polynomial.coeff_map]

lemma qM_isUnit_real (M B : Matrix n n ℝ)
    (h : ∀ α β : ℂ, IsEig M α → IsEig B β → α * β ≠ 1) : IsUnit (qM B M).det := by
  have hc := qM_isUnit_complex (M.map (algebraMap ℝ ℂ)) (B.map (algebraMap ℝ ℂ)) h
  rw [← qM_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at hc
  rw [isUnit_iff_ne_zero] at hc ⊢
  intro h0; apply hc; rw [h0, map_zero]

lemma isEig_transpose (B : Matrix n n ℝ) (β : ℂ) : IsEig Bᵀ β ↔ IsEig B β := by
  unfold IsEig
  rw [← Matrix.det_transpose (B.map (algebraMap ℝ ℂ) - β • (1 : Matrix n n ℂ))]
  simp [Matrix.transpose_sub, Matrix.transpose_map, Matrix.transpose_smul, Matrix.transpose_one]

/-! ## Part 8. The identities (I1), (I2) and the main theorem -/

/-- `φ_B(A) = p_B(A) q_B(A)⁻¹` -/
noncomputable def phiB (A B : Matrix n n ℝ) : Matrix n n ℝ := Fm B A

theorem identity_I1 (A : Matrix n n ℝ) (v w : n → ℝ) (P Q R : Matrix n n ℝ)
    (hNR : Nonresonant A (A + vecMulVec v w))
    (hP : P - A * P * Aᵀ = vecMulVec v v)
    (hQ : Q - (A + vecMulVec v w)ᵀ * Q * (A + vecMulVec v w) = vecMulVec w w)
    (hR : R - A * R * (A + vecMulVec v w) = vecMulVec v w)
    (hPu : IsUnit P.det) (hQu : IsUnit Q.det) :
    R * Q⁻¹ * Rᵀ =
      P - phiB A (A + vecMulVec v w) * P * (phiB A (A + vecMulVec v w))ᵀ := by
  have hqA := qM_isUnit_real A (A + vecMulVec v w) hNR.2.2
  have hqB := qM_isUnit_real (A + vecMulVec v w)ᵀ (A + vecMulVec v w)
    (fun α β ha hb => hNR.2.1 α β ((isEig_transpose _ α).mp ha) hb)
  exact I1_generic A (A + vecMulVec v w) P Q R v w hqA hqB hP hQ hR hQu

theorem identity_I2 (A : Matrix n n ℝ) (v w : n → ℝ) (P Q R : Matrix n n ℝ)
    (hNR : Nonresonant A (A + vecMulVec v w))
    (hP : P - A * P * Aᵀ = vecMulVec v v)
    (hQ : Q - (A + vecMulVec v w)ᵀ * Q * (A + vecMulVec v w) = vecMulVec w w)
    (hR : R - A * R * (A + vecMulVec v w) = vecMulVec v w)
    (hPu : IsUnit P.det) (hQu : IsUnit Q.det) :
    phiB A (A + vecMulVec v w) * (P + Q⁻¹) * (phiB A (A + vecMulVec v w))ᵀ = P := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact Subsingleton.elim _ _
  have hN : 0 < Fintype.card n := Fintype.card_pos
  have hqA := qM_isUnit_real A (A + vecMulVec v w) hNR.2.2
  have hqB := qM_isUnit_real (A + vecMulVec v w)ᵀ (A + vecMulVec v w)
    (fun α β ha hb => hNR.2.1 α β ((isEig_transpose _ α).mp ha) hb)
  exact I2_generic A (A + vecMulVec v w) P Q v w rfl hqA hqB hP hQ hQu hN

/-! ## Part 9. Main theorem (Theorem 2.1, with similarity on the whole domain) -/

theorem decock_demoor (A : Matrix n n ℝ) (v w : n → ℝ) (P Q R : Matrix n n ℝ)
    (hNR : Nonresonant A (A + vecMulVec v w))
    (hP : P - A * P * Aᵀ = vecMulVec v v)
    (hQ : Q - (A + vecMulVec v w)ᵀ * Q * (A + vecMulVec v w) = vecMulVec w w)
    (hR : R - A * R * (A + vecMulVec v w) = vecMulVec v w)
    (hPu : IsUnit P.det) (hQu : IsUnit Q.det) :
    IsUnit R.det ∧ IsUnit (1 + P * Q).det ∧
      (P⁻¹ * R * Q⁻¹ * Rᵀ).charpoly = ((1 + P * Q)⁻¹).charpoly ∧
      ∃ U : Matrix n n ℝ, IsUnit U.det ∧
        U⁻¹ * (P⁻¹ * R * Q⁻¹ * Rᵀ) * U = (1 + P * Q)⁻¹ := by
  obtain ⟨h1, h2, U, hU, hsim⟩ :=
    reduction P Q R (phiB A (A + vecMulVec v w)) hPu hQu
      (identity_I1 A v w P Q R hNR hP hQ hR hPu hQu)
      (identity_I2 A v w P Q R hNR hP hQ hR hPu hQu)
  refine ⟨h1, h2, ?_, U, hU, hsim⟩
  rw [← hsim, charpoly_conj U _ hU]

end DeCockDeMoor
