# Spectral Stability for Strong Ideal-Gas Shock Layers

Jeffrey Humpherys

* Lean formalization: [`lean/`](lean), archived at Zenodo (DOI to be added)

[![Lean build](https://github.com/jhumpherys/papers/actions/workflows/strong-shock-lean.yml/badge.svg)](https://github.com/jhumpherys/papers/actions/workflows/strong-shock-lean.yml)

The `lean` folder contains a Lean 4 formalization of the arguments of the paper, depending only on Mathlib. It covers:

* the cancellation of the thermal mass coupling;
* the weighted energy identity, for an arbitrary thermal weight;
* the sharp slope bounds and the upstream limit of the profile slope;
* coercivity with the constant weight, and with the variable weight that follows the profile;
* the endpoint polynomial and the explicit region of the main theorem;
* the vanishing of the energy flux, including the degenerate weight below unit transport ratio;
* the exclusion of nonzero frequencies and the zero-frequency argument;
* the passage to sufficiently strong finite shocks.

Every main result depends only on the standard axioms of Lean. Asymptotic and Evans-function results of Humpherys, Lyng, and Zumbrun (2009) enter as explicit hypotheses. See [`lean/README.md`](lean/README.md) for build instructions, a table matching each result to its formal statement, and the list of hypotheses. The notebook `lean/strong_shock_lean_verification.ipynb` rebuilds and checks everything on Google Colab.
