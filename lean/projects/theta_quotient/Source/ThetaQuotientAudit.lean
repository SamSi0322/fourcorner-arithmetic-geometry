import ThetaQuotient
#check @FourCorner.ThetaQuotient.prop_theta_quotient
#print axioms FourCorner.ThetaQuotient.prop_theta_quotient
#print axioms FourCorner.ThetaQuotient.quotient_certificate
#print axioms FourCorner.ThetaSourceGenus.genus_five
#print axioms FourCorner.ThetaSourceGenus.source_connected
#print axioms FourCorner.ThetaBoundary.rational_boundary_card
#print axioms FourCorner.ThetaDeckInvolution.sigma_projection
#print axioms FourCorner.ThetaDeckInvolution.no_fixed_point
#print axioms FourCorner.ThetaProjectionFiniteEtale.projection_finite
#print axioms FourCorner.ThetaProjectionFiniteEtale.projection_etale
#print axioms FourCorner.ThetaProjectionDegree.projection_degree_two
#print axioms FourCorner.ThetaProjectionDegree.projection_surjective
#print axioms FourCorner.ThetaOriginImage.origin_image
#print axioms FourCorner.ThetaActualQuotient.invariant_universal
#print axioms FourCorner.ThetaActualQuotient.kernelPairSchemeIso
#print axioms FourCorner.ThetaActualQuotient.identity_graph_fst
#print axioms FourCorner.ThetaActualQuotient.identity_graph_snd
#print axioms FourCorner.ThetaActualQuotient.involution_graph_fst
#print axioms FourCorner.ThetaActualQuotient.involution_graph_snd
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    logInfo m!"AUDIT_IMPORT {m}"
