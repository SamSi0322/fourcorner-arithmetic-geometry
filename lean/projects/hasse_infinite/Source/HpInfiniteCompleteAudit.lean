import HpInfiniteComplete

#print axioms FourCorner.HpInfiniteComplete.hp_infinite
#print axioms FourCorner.HpLiteralGeometricNonisoAudit.original_family_infinite_geometric_classes
#print axioms FourCorner.HpLiteralFamilyConstituents.all_members
#print axioms FourCorner.HpLiteralFieldIdentification.literal_model_iso
#print axioms FourCorner.HpLiteralGeometric.geometric_globalDifferentials_five
#print axioms FourCorner.HpLiteralPoints.family_no_literal_point
#print FourCorner.HpInfiniteComplete.MemberConclusion
#print FourCorner.HpLiteralGeometricNoniso.geometricSetoid
#print FourCorner.HpLiteralGeometricNoniso.geometricObject
#print FourCorner.HpGeometricIsoFibres.familyParameter
#print FourCorner.HasseNorms.Domain
#print FourCorner.HasseNorms.Loc
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for m in env.header.moduleNames do
    logInfo m!"AUDIT_IMPORT {m}"
