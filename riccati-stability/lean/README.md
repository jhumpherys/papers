# Riccati Stability Without Auxiliary Matrices, formalized in Lean

[![Lean build](https://github.com/jhumpherys/papers/actions/workflows/riccati-lean.yml/badge.svg)](https://github.com/jhumpherys/papers/actions/workflows/riccati-lean.yml)

This repository contains a formalization in the Lean 4 proof assistant of every result in

> Jeffrey Humpherys, *Riccati Stability Without Auxiliary Matrices*.

The formalization depends only on the [Mathlib](https://github.com/leanprover-community/mathlib4) library. The proofs contain no `sorry`, and every result listed below depends only on the three standard axioms of Lean's logic, `propext`, `Classical.choice` and `Quot.sound`.

## Building

Install Lean through [elan](https://github.com/leanprover/elan), then from this folder run

```
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```

The first command downloads precompiled Mathlib, which avoids building it from source. The second checks every proof. The third prints the axioms each main result depends on.

The versions are pinned. The Lean toolchain is `v4.35.0-rc4` (file `lean-toolchain`) and Mathlib is commit `321b3b85cb86b65144d78546020d53650b0d9071` (files `lakefile.toml` and `lake-manifest.json`). The GitHub workflow `.github/workflows/riccati-lean.yml` at the root of this repository repeats the build and the axiom check on every push.

## Files

| File | Contents |
|---|---|
| `RiccatiStability.lean` | Definitions and all proofs |
| `AxiomCheck.lean` | `#print axioms` for each result of the paper |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Build configuration and pinned versions |

## Definitions

A formal proof is only as good as its statements, so the definitions are collected at the top of `RiccatiStability.lean` for comparison with the paper.

| Paper | Lean |
|---|---|
| Riccati stability (eq:ric) | `RiccatiStable` |
| Block LMI (eq:lmi) | `LMIFeasible` |
| Hurwitz matrix | `IsHurwitz` |
| Resolvent $G_{A,B}(\omega)=(i\omega I-A)^{-1}B$ (eq:G) | `resolvent` |
| Resolvent family $\Sigma_{A,B}$ | `resolventFamily` |
| Spectral radius $r(X)$ | `specRad` |
| Spectral norm $\lVert X\rVert_2$ | `norm2` |
| $\lVert H^{1/2}XH^{-1/2}\rVert_2$ | `metricGain H X` (see `metricGain_eq_norm2`) |
| Optimal common ellipsoidal norm, right side of (eq:covdual) | `optNorm` |
| Feasible $t$ in Definition def:cov | `CovFeasible` |
| Covariance radius $\rho_{\rm cov}$ | `covRadius` |
| $\rho_R(A,B)$ (eq:rhoR) | `rhoR` |

Two choices differ in form from the paper but not in content. The metric gain is defined through the quadratic form $z\mapsto z^HHz$ rather than through $H^{1/2}$, and `metricGain_eq_norm2` proves that it equals $\lVert H^{1/2}XH^{-1/2}\rVert_2$. Lean's matrix inverse returns zero on singular matrices, so every result involving the resolvent assumes `IsHurwitz A`, as the paper does.

## Results

| Paper | Lean theorem |
|---|---|
| Lemma brl | `riccatiStable_iff_boundedReal` |
| (eq:lmi) is equivalent to (eq:ric) | `riccatiStable_iff_lmiFeasible` |
| Supremum in Definition def:cov is finite and attained | `covFeasible_le_sup_norm`, `covRadius_sq_feasible` |
| Theorem covdual | `covRadius_eq_optNorm` |
| Remark rem:single | `covRadius_pair` |
| Lemma word | `specRad_prod_rpow_le_covRadius` |
| Compactness of $\Sigma_{A,B}$ | `isCompact_resolventFamily` |
| Theorem main | `riccatiStable_iff` |
| Corollary finitecert | `not_riccatiStable_iff` |
| Proposition bounds, (eq:sandwich) | `specRad_resolvent_le_rhoR`, `rhoR_le_sup_norm2` |
| Proposition bounds, (eq:resolventword) | `specRad_resolvent_prod_rpow_le_rhoR` |
| Remark after Proposition bounds | `specRad_inv_mul_le_rhoR`, `rhoR_scale`, `rhoR_similar` |
| Example ex:2d, $A$ is Hurwitz | `exA_isHurwitz` |
| Example ex:2d, (eq:example_exact) | `example_exact` |
| Example ex:2d, exact formula for $\rho_R(A,B)$ | `rhoR_example` |
| Example ex:2d, strict outer bounds | `example_strict_sandwich` |
| Example ex:2d, $\rho_R(A,cB)=\lvert c\rvert\rho_R(A,B)$ | `rhoR_smul_right` |
| Example ex:2d, $(A,\tfrac52B)$ is strongly delay-independent stable but not Riccati-stable | `example_gap` |
| Section 5, bisection on $\gamma$ | `rhoR_lt_iff` |

The decimal approximations in the example are not formalized. The claims they support, namely the strict inequalities, the exact formula for $\rho_R(A,B)$ and the gap at $c=5/2$, are proved from exact rational bounds. For instance, `metricGain_ex_le` shows $\lVert Q^{1/2}G(\omega)Q^{-1/2}\rVert_2\le 12/25$ for all $\omega$, `two_fifths_le_rhoR_ex` shows $\rho_R(A,B)\ge 2/5$, and `twelve_25_lt_norm2_exG3` shows $\lVert G(3)\rVert_2>12/25$.

The attainment result `covRadius_sq_feasible` assumes $n\ge1$, written `[Nonempty n]`. For $n=0$ there is no nonzero vector, so no $t$ is feasible and the supremum is not attained.

## Acknowledgment

The formalization was produced with the assistance of Anthropic Claude and checked by Lean.

## License

Apache 2.0, see `LICENSE`.
