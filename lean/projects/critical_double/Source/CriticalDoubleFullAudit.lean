import CriticalDoubleFull

#check @FourCorner.CriticalDoubleFull.prop_crit_double
#check @FourCorner.CriticalDoubleFull.finite_statement
#check @FourCorner.CriticalDoubleGeometry.normalized_root_square
#check @FourCorner.CriticalNormalizationDiagram.normalized_root_generates
#check @FourCorner.CriticalNormalizationDiagram.field_diagram
#check @FourCorner.CriticalDoubleOriginalMap.map_generic
#check @FourCorner.CriticalDoubleOriginalMap.baseFieldEquiv
#check @FourCorner.CriticalDoubleModel.fieldEquiv
#check @FourCorner.CriticalPointNaturality.image_place
#check @FourCorner.CriticalSchemeBoundaryCount.boundaryEquiv
#check @FourCorner.CriticalSchemeBoundaryCount.count
#print FourCorner.CriticalDoubleFullGeometry.Geometry
#print FourCorner.CriticalDoubleFullGeometry.DegreeTwo
#print FourCorner.CriticalDoubleFullGeometry.GeometricGenusOne
#print FourCorner.CriticalDoubleFull.NativeNormalization
#print FourCorner.CriticalDoubleFull.PrimeStatement
#print FourCorner.CriticalLiteralCount.PositivePoints
#print FourCorner.CriticalSchemeBoundaryCount.BoundaryPoints
#print axioms FourCorner.CriticalDoubleFull.prop_crit_double
#print axioms FourCorner.CriticalDoubleFull.native_normalization
#print axioms FourCorner.CriticalDoubleFull.finite_statement
#print axioms FourCorner.CriticalDoubleFullGeometry.geometry
#print axioms FourCorner.CriticalDoubleGeometry.normalized_root_square
#print axioms FourCorner.CriticalNormalizationDiagram.normalized_root_generates
#print axioms FourCorner.CriticalNormalizationDiagram.field_diagram
#print axioms FourCorner.CriticalDoubleOriginalMap.map_generic
#print axioms FourCorner.CriticalDoubleOriginalMap.baseFieldEquiv
#print axioms FourCorner.CriticalDoubleModel.fieldEquiv
#print axioms FourCorner.CriticalPointNaturality.native_comap
#print axioms FourCorner.CriticalPointNaturality.image_place
#print axioms FourCorner.CriticalSchemeBoundaryCount.boundaryEquiv
#print axioms FourCorner.CriticalSchemeBoundaryCount.boundary_count
#print axioms FourCorner.CriticalSchemeBoundaryCount.boundary_count_mod_eight
#print axioms FourCorner.CriticalSchemeBoundaryCount.count
#print axioms FourCorner.CriticalLiteralSchemeCharacter.literal_character
#print axioms FourCorner.CriticalLiteralSchemeCharacter.same_point_homogeneous
#print axioms FourCorner.CriticalNativeGeometricGenus.cover_genus_one
#print axioms FourCorner.CriticalNativeGeometricGenus.base_genus_one
#print axioms FourCorner.CriticalGlobalFibreCount.total_count
#print axioms FourCorner.CriticalProjectiveCharacter.rescale
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 for m in env.header.moduleNames do
  logInfo m!"AUDIT_IMPORT {m}"
