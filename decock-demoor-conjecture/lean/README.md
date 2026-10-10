# Lean 4 formalization of Theorem 2.2

Supplementary material for J. Humpherys, *The De Cock–De Moor Conjecture: Proof, Normal Form, and Indefinite Angles*.

This folder contains a formal proof, in Lean 4 with the Mathlib library, of the main theorem of the paper (Theorem 2.2) for real data. It depends only on Mathlib.

## What is verified

Let `A` be a real `n × n` matrix, let `v, w` be real vectors, and set `B = A + v wᵀ`. Let `P, Q, R` be any real matrices satisfying

```
P − A P Aᵀ = v vᵀ,     Q − Bᵀ Q B = w wᵀ,     R − A R B = v wᵀ.
```

Assume nonresonance, meaning `αβ ≠ 1` whenever `α, β` are complex eigenvalues of `A` and `A`, of `B` and `B`, or of `A` and `B`. Assume that `P` and `Q` are nonsingular. Then the following hold.

* `R Q⁻¹ Rᵀ = P − F P Fᵀ` and `F (P + Q⁻¹) Fᵀ = P`, where `F = p_B(A) q_B(A)⁻¹`. These are the identities (4) of the paper.
* `R` and `I + PQ` are nonsingular.
* `P⁻¹ R Q⁻¹ Rᵀ` and `(I + PQ)⁻¹` have the same characteristic polynomial, and there is a nonsingular real `U` with `U⁻¹ (P⁻¹ R Q⁻¹ Rᵀ) U = (I + PQ)⁻¹`. The proof constructs `U = P⁻¹ F`, as in the paper.

`P, Q, R` are arbitrary solutions of the Stein equations, so uniqueness is not assumed. Eigenvalues are the complex roots `α` of `det(A − αI) = 0` (definition `IsEig`), and nonresonance is the definition `Nonresonant`.

| Lean declaration | Content | Paper |
|---|---|---|
| `decock_demoor` | nonsingularity, equal characteristic polynomials, similarity | Theorem 2.2 |
| `identity_I1`, `identity_I2` | the two identities | identities (4) in Theorem 2.2 |
| `reduction` | the two identities imply the conclusions, over any field | final step of the proof of Theorem 2.2 (Section 4) |
| `I1_generic`, `I2_generic`, `prop_S` | the identities over an arbitrary field, with the needed invertibility as hypotheses | auxiliary |

## What is not formalized

Proposition 2.1 (disjointness of the spectra), Theorems 2.3 and 2.4, and the results of Sections 5 to 8 are not formalized. The complex-data remark is not formalized either.

## Proof route

The formal proof does not follow the density argument of Section 4. It proves the two identities directly for arbitrary solutions of the Stein equations, using a telescoping consequence of the Cayley–Hamilton theorem, Krylov bases built from observability, and a Bezoutian matrix. It then applies the same algebraic reduction as the paper. Docstring labels such as "Lemma 2.7", "Proposition 3.2", or "Theorem 4.3" refer to the internal blueprint used to write the formalization and not to the paper. The header "Theorem 2.1" in Part 9 refers to the main theorem in the numbering of arXiv:2608.29479v1, which is Theorem 2.2 of the paper.

## Verification record

The file `DeCockDeMoor/Basic.lean` was built against Mathlib tag `v4.19.0` (toolchain `leanprover/lean4:v4.19.0`) in Google Colab with the notebook in this folder. The build completed with no errors and no `sorry`. For each of `reduction`, `identity_I1`, `identity_I2`, and `decock_demoor`, `#print axioms` lists only the three standard axioms of Lean's classical mathematics:

```
[propext, Classical.choice, Quot.sound]
```

## Files

* `DeCockDeMoor/Basic.lean`: the formalization.
* `DeCockDeMoor.lean`: library root.
* `lakefile.toml`, `lean-toolchain`: project configuration, pinned to Mathlib `v4.19.0`.
* `CheckAxioms.lean`: prints the axioms used by the main declarations.
* `DeCockDeMoor_Lean4_Build_and_Check_Colab.ipynb`: a self-contained notebook that installs Lean and Mathlib, writes the same source (embedded, byte-identical), builds it, and prints the axioms.

## Building locally

With `elan` installed:

```
lake update
lake exe cache get
lake build
lake env lean CheckAxioms.lean
```

The first build downloads the precompiled Mathlib cache and takes about 5 to 15 minutes.
