import OriginalCoverExact
#check @FourCorner.OriginalCoverCompletion.OrderedSource.prop_ell_original_cover
#print axioms FourCorner.OriginalCoverCompletion.OrderedSource.prop_ell_original_cover
#print axioms FourCorner.OriginalCoverCompletion.OrderedSource.originalCoordinateMap_injective
#print axioms FourCorner.OriginalCoverCompletion.OrderedSource.originalFieldEmbedding
#print axioms FourCorner.OriginalCoverCompletion.OrderedSource.sourceQ_literal_square
#print axioms FourCorner.OriginalCoverCompletion.OrderedSource.returnedRootField_eq_top
#print axioms FourCorner.OriginalCoverCompletion.OrderedSource.returnedXY_independent
#print axioms FourCorner.OriginalCoverCompletion.OrderedSource.source_adjoin_q_eq_top
#print axioms FourCorner.OriginalCoverCompletion.OrderedSource.source_finrank_over_original
#print axioms FourCorner.OriginalCoverCompletion.OrderedSource.source_finrank
#print axioms FourCorner.OriginalCoverCompletion.original_radicand_nonsquare
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    logInfo m!"AUDIT_IMPORT {m}"
