# StrongShock: Lean 4 formalization

Supplementary material for the manuscript *Spectral stability for strong ideal-gas shock layers*.
Section 10 of the manuscript describes the formalization. Numbers below refer to the manuscript.

The formalization depends only on the Lean 4 core and Mathlib.

* Lean toolchain `leanprover/lean4:v4.34.1` (file `lean-toolchain`)
* Mathlib `v4.34.1` (files `lakefile.toml`, `lake-manifest.json`)

## Building

With [elan](https://github.com/leanprover/elan) installed,

```
lake exe cache get     # download prebuilt Mathlib
lake build             # check every proof in this project
lake env lean Check.lean
```

The last command prints the axioms used by each main result. Every one of them depends only on
`propext`, `Classical.choice`, and `Quot.sound`, the standard axioms of Lean and Mathlib. The
sources contain no `sorry`, `admit`, or `axiom`. A full build of this project takes about two
minutes on two cores once the Mathlib cache is in place. A transcript is in
`verification_log.txt`.

The notebook `strong_shock_lean_verification.ipynb`, included with this formalization, performs
the same steps on Google Colab without any local setup.

## Correspondence with the manuscript

| Manuscript | Lean file and declaration |
|---|---|
| Profile coordinates `(s, z)`, coefficients (4.1)-(4.3), the quadratic `𝒯` (5.9) | `Basic.lean` |
| Section 4, cancellation of the thermal mass coupling | `EnergyIdentity.lean`, `thermal_cancel` |
| Proposition 5.1 and Appendix A, the weighted pointwise identity, for an arbitrary weight | `EnergyIdentity.lean`, `energy_identity_weighted` |
| Lemma 2.1, explicit limiting profile | `Becker.lean`, `becker` |
| Lemma 2.2, slope interval | `Profile.lean`, `SZTraj.slope_interval` |
| Lemma 2.2, sharp bounds above the reference line and below `ν = 1`, upstream limit | `SlopeSharp.lean`, `sharp_above`, `sharp_below`, `z_lt_one`, `z_bot_above`, `z_bot_below` |
| Downstream slope relation (6.7) | `SlopeSharp.lean`, `rho_root` |
| Lemma 6.1 and Proposition 6.2, the constant weight | `Coercivity.lean`, `Tcal_bounds`, `lower_coercive` |
| Proposition 6.3, interpolation of the energy matrix | `Coercivity.lean`, `var_decomp` |
| Proposition 6.5, the variable weight | `Coercivity.lean`, `var_coercive` |
| Lemma 6.4, the endpoint polynomial `Π_ν` (1.8) | `Endpoint.lean`, `PiP_strip`, `PiP_mono`, `PiP_t_pos`, `rhoE_spec` |
| The boundary `Γ_E` (1.9), the region `ℛ` (1.10), and the endpoint condition (6.16) | `Endpoint.lean`, `GammaE`, `InR`, `endpoint` |
| Lemma 7.1, vanishing of the flux, including the degenerate weight for `ν < 1` | `WeightedDecay.lean`, `fluxW_tendsto`; `SlopeSharp.lean`, `one_sub_z_lower` |
| Proposition 7.2, exclusion of nonzero frequencies | `WeightedExclusion.lean`, `exclusionW`; `Main.lean`, `nonzero_lower`, `nonzero_above`, `nonzero_below`, `thm_nonzero` |
| Proposition 8.1, zero frequency | `ZeroFrequency.lean`, `zero_frequency`; `Main.lean`, `zero_core` |
| Theorem 1.1, Evans-function form | `Main.lean`, `evans_R` |
| Corollary 1.2 and Section 9 | `Finite.lean`, `finite_shock`; `Main.lean`, `cor_finite` |
| Appendix C, air and monatomic gases | `Main.lean`, the example for air and `monatomic_in_R` |

The thermal weight is written as `ω = W²/2`. The constant weight is `W = a_*` and the variable
weight (6.9) is `W = a + 4c/3`. The formalization uses the rescaled thermal variable `ξ/√2`, which
makes every coefficient of the energy form rational.

## Results used as hypotheses

The following results of Humpherys, Lyng, and Zumbrun (Arch. Ration. Mech. Anal. 194, 2009), or
standard facts about ordinary differential equations, are not available in Mathlib. They appear as
explicit hypotheses of the theorems and never as axioms.

1. `LimitingProfile`. A solution of (2.3) between the endstates, with the endstate limits and a
   positive downstream limit of the normalized slope `z = -V'/(a s)`. The file `Becker.lean` shows
   that this structure is inhabited.
2. `Admissible`. For nonzero spectral parameter, decay `O(e^{ωx})` upstream for every
   `ω < min{1, 1/ν}`, and decay downstream.
3. `ZeroAdmissible`. At zero frequency, decay upstream, and downstream limits in the
   positive-characteristic subspace with decaying derivatives.
4. `VariationalUnique` and `AllVariationalUnique`. Downstream decaying solutions of the variational
   equation (8.1) are multiples of the profile tangent.
5. For finite shocks, an integrated Evans function `D(λ, (Γ, ν), ς)` that is jointly continuous
   through `ς = 0`, satisfies a uniform high-frequency bound, and whose zeros in the closed right
   half-plane at `ς = 0` produce nontrivial admissible solutions (`EvansZeroSolution`).

The upstream limit of the slope, the sharp slope bounds, and the upstream rate at which the
variable weight degenerates for `ν < 1` are proved, not assumed.
