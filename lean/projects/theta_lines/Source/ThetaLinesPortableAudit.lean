import ThetaLinesFullAssembly
import Lean.Util.CollectAxioms

#print axioms FourCorner.ThetaLinesFullAssembly.theta_lines_full

private def canonicalType : Lean.Expr → Lean.Expr
 | .forallE _ d b bi => .forallE .anonymous (canonicalType d) (canonicalType b) bi
 | .lam _ d b bi => .lam .anonymous (canonicalType d) (canonicalType b) bi
 | .letE _ t v b nd => .letE .anonymous (canonicalType t) (canonicalType v) (canonicalType b) nd
 | .app f a => .app (canonicalType f) (canonicalType a)
 | .mdata _ e => canonicalType e
 | .proj n i e => .proj n i (canonicalType e)
 | e => e

open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let owned := #[`BinaryDehomogenization,
  `DivisorPicPrincipal,
  `DoubleRootPolynomial,
  `DoubleZeroDifferential,
  `ThetaBitangentAxes,
  `ThetaBitangentAxisIdentities,
  `ThetaBitangentCases,
  `ThetaBitangentContacts,
  `ThetaBitangentCore,
  `ThetaBitangentCountWave36,
  `ThetaBitangentExhaustionWave36,
  `ThetaBitangentGaloisWave36,
  `ThetaBitangentGeneric,
  `ThetaBitangentProjectiveChartsWave36,
  `ThetaBitangentQuadraticIndependence,
  `HalfCanonicalDifferential,
  `ThetaStdTotallySplit,
  `NativeBinaryP1,
  `NativeCurveModelExistence,
  `NativeFunctionFieldFunctor,
  `NativeStalkFieldNaturality,
  `OddThetaDivisorClassification,
  `P2M.Sol.S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq,
  `P2M.Sol.S_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch,
  `PicEffectiveRepresentatives,
  `PicEllOneOfConstants,
  `QuarticSingletonZero,
  `QuarticTwoDoublePoints,
  `RiemannRochWithGenusFF,
  `SemilinearDifferentialOrder,
  `SemilinearPicAndEll,
  `SmallSquareSpaceBound,
  `Theorems.Thm_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq,
  `ThetaActualHalfCanonicalContacts,
  `ThetaActualLineDifferentials,
  `ThetaActualOddThetaClasses,
  `ThetaAffineContactConstants,
  `ThetaAffineContactOrder,
  `ThetaAssociatedLineAlgebra,
  `ThetaCanonicalLinePointValues,
  `ThetaChartCanonicalFrames,
  `ThetaChartTangentVanishing,
  `ThetaContactDifferentialDivisors,
  `ThetaContactLSpaceGeometry,
  `ThetaContactOddness,
  `ThetaContactPairFrames,
  `ThetaContactTangencyCertificates,
  `ThetaDActualDifferential,
  `ThetaDActualFieldCover,
  `ThetaDCanonicalInfinityDivisor,
  `ThetaDCanonicalPlaneBasis,
  `ThetaDChartNaturality,
  `ThetaDChartPlaceRegularity,
  `ThetaDCoordinateBasicOpens,
  `ThetaDExactChartTransitions,
  `ThetaDExactModel,
  `ThetaDFieldCoordinates,
  `ThetaDFiniteDifferential,
  `ThetaDFourInfinityPlaces,
  `ThetaDGenusThree,
  `ThetaDGeometricChartPoints,
  `ThetaDGeometricModel,
  `ThetaDGlobalCanonicalCandidate,
  `ThetaDGlobalSheafBasis,
  `ThetaDHyperplaneLocalOrders,
  `ThetaDInfinityLocalParameter,
  `ThetaDInfinityPoints,
  `ThetaDNativeProjRatios,
  `ThetaDNativeProjSections,
  `ThetaDNativeSections,
  `ThetaDNaturalGlobalDifferentials,
  `ThetaDOriginalChartOpens,
  `ThetaDOriginalCoordinateSections,
  `ThetaDPlaneChartSections,
  `ThetaDPlaneRegularForms,
  `ThetaDProjectiveInfinityCover,
  `ThetaDSectionComparison,
  `ThetaDifferentialChartIdentity,
  `ThetaEtaleAllPlaces,
  `ThetaFiniteGenericDegree,
  `ThetaFlatIntegralDescent,
  `ThetaGaloisCanonicalCorrespondence,
  `ThetaGaloisCanonicalPlane,
  `ThetaGaloisFieldAction,
  `ThetaGaloisPointPlace,
  `ThetaGaloisSchemeField,
  `ThetaGenericRankFraction,
  `ThetaGeometricChartEvaluation,
  `ThetaGeometricContactPoints,
  `ThetaGeometricPointCoordinateEvaluation,
  `ThetaGeometricResidueCoordinates,
  `ThetaHalfCanonicalRootSupport,
  `ThetaHalfCanonicalSquareContact,
  `ThetaLineAlgebraDecomposition,
  `ThetaLineFixedFields,
  `ThetaLineGeometricPoints,
  `ThetaLineOrbits,
  `ThetaLineRootPointCharts,
  `ThetaLineSplittingField,
  `ThetaLineStabilizers,
  `ThetaLinesAbsoluteGalois,
  `ThetaLinesContactPoints,
  `ThetaLinesDualLines,
  `ThetaLinesFullAssembly,
  `ThetaLinesGaloisAction,
  `ThetaLinesPolynomialContacts,
  `ThetaLinesProjectiveClassification,
  `ThetaLinesProjectiveLines,
  `ThetaLinesSchemePoints,
  `ThetaLiteralBinaryRestrictions,
  `ThetaLiteralRootJets,
  `ThetaLocalLineDerivatives,
  `ThetaNativeDualCanonicalLines,
  `ThetaNativeFunctionFieldMap,
  `ThetaNativeLineGaloisSet,
  `ThetaOddGaloisActionHom,
  `ThetaOddNativeGaloisEquiv,
  `ThetaOddNativeLineEquiv,
  `ThetaOddNativeSquareContact,
  `ThetaOddThetaCanonicalLines,
  `ThetaOrbitEvaluation,
  `ThetaOrderTwoDerivativeEvaluation,
  `ThetaProjectiveRootPlaceEmbedding,
  `ThetaRegularFunctionDifferential,
  `ThetaRestrictionHasTwoRoots,
  `ThetaRootCanonicalSections,
  `ThetaRootOrderDoubleJets,
  `ThetaUnramifiedPlaceIndex,
  `ThetaValuationTangencyOrder,
  `ThetaVanishingDifferentialOrder,
  `ThetaVerticalContactConstants,
  `ThetaVerticalContactOrder]
 let allowed := #[`propext,`Classical.choice,`Quot.sound]
 let mut count : Nat := 0
 let mut allPending : Array Name := #[]
 for (n,_) in env.constants.toList do
  if let some idx := env.getModuleIdxFor? n then
   if owned.contains env.header.moduleNames[idx.toNat]! then
    for ax in (← collectAxioms n) do
     unless allowed.contains ax do throwError "Nonstandard axiom {ax} in {n}"
    count := count+1
    allPending := allPending.push n
 logInfo m!"ALL_OWNED_DECLARATIONS {count}"
 let mut allSeen : NameSet := {}
 while !allPending.isEmpty do
  let n := allPending.back!
  allPending := allPending.pop
  unless allSeen.contains n do
   allSeen := allSeen.insert n
   match env.find? n with
   | none => throwError "Unresolved all-owned type/value dependency {n}"
   | some c =>
    for dep in c.getUsedConstantsAsSet.toList do allPending := allPending.push dep
 logInfo m!"ALL_OWNED_FULL_TYPE_VALUE_CLOSURE {allSeen.size}"
 let endpoint := `FourCorner.ThetaLinesFullAssembly.theta_lines_full
 let mut pending := #[endpoint]
 let mut seen : NameSet := {}
 let forbidden := #[`FourCorner.ThetaDGlobalSheafBasis.globalEquiv,
  `FourCorner.ThetaDOriginalCoordinateSections.planeGlobalSectionEquiv,
  `MilneJVScheme.JacobianSchemeData,`GoodReductionJacobian.trivialPic0Designation,
  `sorryAx,`Lean.ofReduceBool]
 while !pending.isEmpty do
  let n := pending.back!
  pending := pending.pop
  unless seen.contains n do
   seen := seen.insert n
   for bad in forbidden do
    if bad.isPrefixOf n then throwError "Forbidden endpoint dependency {n}"
   match env.find? n with
   | none => throwError "Unresolved endpoint dependency {n}"
   | some c =>
    for dep in c.getUsedConstantsAsSet.toList do pending := pending.push dep
 logInfo m!"ENDPOINT_FULL_TYPE_VALUE_CLOSURE {seen.size}"
 for n in #[endpoint,`FourCorner.ThetaOddNativeSquareContact.intrinsic_odd_iff_square,
   `FourCorner.ThetaRootOrderDoubleJets.root_double_at] do
  let ci ← getConstInfo n
  let payload := Json.mkObj [("declaration",toJson n.toString),
   ("level_parameters",toJson (ci.levelParams.map Name.toString)),
   ("kernel_type",toJson (toString (repr (canonicalType ci.type))))]
  logInfo m!"TYPE_PIN {payload.compress}"
 for m in env.header.moduleNames do logInfo m!"PORTABLE_IMPORT {m}"
