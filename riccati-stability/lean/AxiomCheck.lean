import RiccatiStability

/-!
Prints the axioms used by each result of the paper.  Run with

  lake env lean AxiomCheck.lean

after `lake build`.  Every line should read
`depends on axioms: [propext, Classical.choice, Quot.sound]`.
A `sorryAx` entry would indicate an unproved step.
-/

-- Lemma brl and the LMI form
#print axioms RiccatiStability.riccatiStable_iff_boundedReal
#print axioms RiccatiStability.riccatiStable_iff_lmiFeasible
-- Section 2
#print axioms RiccatiStability.covFeasible_le_sup_norm
#print axioms RiccatiStability.covRadius_sq_feasible
#print axioms RiccatiStability.covRadius_eq_optNorm
#print axioms RiccatiStability.covRadius_pair
#print axioms RiccatiStability.specRad_prod_rpow_le_covRadius
-- Section 3
#print axioms RiccatiStability.isCompact_resolventFamily
#print axioms RiccatiStability.riccatiStable_iff
#print axioms RiccatiStability.not_riccatiStable_iff
#print axioms RiccatiStability.specRad_resolvent_le_rhoR
#print axioms RiccatiStability.rhoR_le_sup_norm2
#print axioms RiccatiStability.specRad_resolvent_prod_rpow_le_rhoR
#print axioms RiccatiStability.specRad_inv_mul_le_rhoR
#print axioms RiccatiStability.rhoR_scale
#print axioms RiccatiStability.rhoR_similar
#print axioms RiccatiStability.rhoR_smul_right
-- Section 4
#print axioms RiccatiStability.exA_isHurwitz
#print axioms RiccatiStability.two_fifths_le_rhoR_ex
#print axioms RiccatiStability.example_exact
#print axioms RiccatiStability.metricGain_ex_le
#print axioms RiccatiStability.twelve_25_lt_norm2_exG3
#print axioms RiccatiStability.rhoR_example
#print axioms RiccatiStability.example_strict_sandwich
#print axioms RiccatiStability.example_gap
-- Section 5
#print axioms RiccatiStability.rhoR_lt_iff
-- Bridge to the paper's notation
#print axioms RiccatiStability.metricGain_eq_norm2
