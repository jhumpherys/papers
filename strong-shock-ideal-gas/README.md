# Spectral Stability for Strong Ideal-Gas Shock Layers

Jeffrey Humpherys

* Lean formalization: [`lean/`](lean)

[![Lean build](https://github.com/jhumpherys/papers/actions/workflows/strong-shock-lean.yml/badge.svg)](https://github.com/jhumpherys/papers/actions/workflows/strong-shock-lean.yml)

The `lean` folder contains a Lean 4 formalization, depending only on Mathlib, of the arguments of the paper. It covers the cancellation of the thermal mass coupling, the energy identity, the coercivity estimates on the reference line and on the explicit transport region, the exclusion of nonzero frequencies, the zero-frequency argument, and the passage to sufficiently strong finite shocks. Every main result depends only on the standard axioms of Lean. Asymptotic and Evans-function results of Humpherys, Lyng, and Zumbrun (2009) enter as explicit hypotheses. See [`lean/README.md`](lean/README.md) for build instructions, a table matching each result to its formal statement, and the list of hypotheses.
