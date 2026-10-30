import HasseUniformNoPoint

#check @FourCorner.HasseUniformNoPoint.hp_uniform
#check @FourCorner.HasseUniformNoPoint.hp_uniform_literal
#check @FourCorner.HasseUniformNoPoint.hp_uniform_four_squares
#print FourCorner.HasseNorms.Domain
#print FourCorner.HasseNorms.Loc
#print FourCorner.HasseObstructionArithmetic.T
#print axioms FourCorner.HasseProjectivePoint.rationalPoint_nonempty_iff_literal_squares
#print axioms FourCorner.HasseAnchorChoice.tangentData
#print axioms FourCorner.HasseOddSymbol.rationalSign_eq_oddSign
#print axioms FourCorner.HasseDyadicSymbol.rationalSign_eq_dyadicSign
#print axioms FourCorner.HasseWR.global_wsupport
#print axioms FourCorner.HasseConstantCorrection.correctedSign_parameter_finite_product
#print axioms FourCorner.HasseCorrectedOddProduct.correctedOdd_product
#print axioms FourCorner.HasseDyadicUnitOneRow.tangentSign_unitOne
#print axioms FourCorner.HasseUnitFifteenRow.tangentSign_unitFifteen
#print axioms FourCorner.HasseFinalDyadic.correctedDyadic_T_product
#print axioms FourCorner.HasseUniformNoPoint.obstruction_zero
#print axioms FourCorner.HasseUniformNoPoint.hp_uniform
#print axioms FourCorner.HasseUniformNoPoint.hp_uniform_literal
#print axioms FourCorner.HasseUniformNoPoint.hp_uniform_four_squares

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    logInfo m!"AUDIT_IMPORT {m}"
