import Cs15569Complete

#print axioms FourCorner.Cs15569Completion.no_minus_two
#print axioms FourCorner.Cs15569Completion.unit_offset_deep
#print axioms FourCorner.Cs15569Completion.actual_dyadic_splitting
#print axioms FourCorner.Cs15569Completion.actual_dyadic_direct_sum
#print axioms FourCorner.Cs15569Completion.actual_H_halving
#print axioms FourCorner.Cs15569Completion.actual_H_mod_two
#print axioms FourCorner.Cs15569Completion.actual_H_mod_eight
#print axioms FourCorner.Cs15569Completion.actual_H_kummer_kernel
#print axioms FourCorner.Cs15569Completion.raw_source_actual_pair
#print axioms FourCorner.Cs15569Completion.actual_pair_complete_coset
#print axioms FourCorner.Cs15569Completion.entire_compensated_P_class
#print axioms FourCorner.Cs15569Completion.actual_H_depth_three
#print axioms FourCorner.Cs15569Completion.phiEight
#print axioms FourCorner.Cs15569Completion.phiEight_parameter
#print axioms FourCorner.Cs15569Completion.actual_source_coefficient_parities
#print axioms FourCorner.Cs15569Completion.three_forces_odd_coefficients
#print axioms FourCorner.Cs15569Completion.actual_depth_three_square_sign
#print axioms FourCorner.Cs15569Completion.coefficient_odd_depth_three
#print axioms FourCorner.Cs15569Completion.actual_source_torsion_labels
#print axioms FourCorner.Cs15569Completion.red113_eight_H
#print axioms FourCorner.Cs15569Completion.actual_source_four_abscissae
#print axioms FourCorner.Cs15569Completion.integral_abscissa_of_red113
#print axioms FourCorner.Cs15569Completion.actual_pair_exclusion
#print axioms FourCorner.Cs15569Completion.cs15569_source_exclusion
#print axioms FourCorner.Cs15569Completion.cs15569_source_exclusion_cast
#print axioms FourCorner.Cs15569Completion.cs15569_layer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    logInfo m!"AUDIT_IMPORT {m}"
