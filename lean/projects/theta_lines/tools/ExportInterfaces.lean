import ThetaLinesFullAssembly
import Lean.Util.CollectAxioms

open Lean
private def encodeName : Name → Json
 | .anonymous => Json.arr #[toJson "anonymous"]
 | .str p s => Json.arr #[toJson "str",encodeName p,toJson s]
 | .num p n => Json.arr #[toJson "num",encodeName p,toJson n]
private def encodeLevel : Level → Json
 | .zero => Json.arr #[toJson "zero"]
 | .succ l => Json.arr #[toJson "succ",encodeLevel l]
 | .max l k => Json.arr #[toJson "max",encodeLevel l,encodeLevel k]
 | .imax l k => Json.arr #[toJson "imax",encodeLevel l,encodeLevel k]
 | .param n => Json.arr #[toJson "param",encodeName n]
 | .mvar n => Json.arr #[toJson "mvar",toJson (toString (repr n))]
private def replaceNamePrefix (n a b : Name) : Name :=
 if n==a then b else match n with
 | .str p s => .str (replaceNamePrefix p a b) s
 | .num p i => .num (replaceNamePrefix p a b) i
 | .anonymous => .anonymous
private def normalizeName (n : Name) : Name := Id.run do
 let mut n := n
 for (a,b) in [(`_private.Mathlib.RingTheory.Flat.Rank,`_private.ThetaStdRingFlatRank),
  (`_private.Mathlib.AlgebraicGeometry.Morphisms.FlatRank,`_private.ThetaStdSchemeFlatRank),
  (`_private.Mathlib.RingTheory.Finiteness.ModuleFinitePresentation,`_private.ThetaStdModuleFinitePresentation),
  (`_private.FourCorner.ThetaBitangentAxes,`_private.ThetaBitangentAxes),
  (`_private.FourCorner.ThetaBitangentAxisIdentities,`_private.ThetaBitangentAxisIdentities),
  (`_private.FourCorner.ThetaBitangentCases,`_private.ThetaBitangentCases),
  (`_private.FourCorner.ThetaBitangentContacts,`_private.ThetaBitangentContacts),
  (`_private.FourCorner.ThetaBitangentCore,`_private.ThetaBitangentCore),
  (`_private.FourCorner.ThetaBitangentCountWave36,`_private.ThetaBitangentCountWave36),
  (`_private.FourCorner.ThetaBitangentExhaustionWave36,`_private.ThetaBitangentExhaustionWave36),
  (`_private.FourCorner.ThetaBitangentGaloisWave36,`_private.ThetaBitangentGaloisWave36),
  (`_private.FourCorner.ThetaBitangentGeneric,`_private.ThetaBitangentGeneric),
  (`_private.FourCorner.ThetaBitangentProjectiveChartsWave36,`_private.ThetaBitangentProjectiveChartsWave36),
  (`_private.FourCorner.ThetaBitangentQuadraticIndependence,`_private.ThetaBitangentQuadraticIndependence),
  (`_private.Mathlib.RingTheory.TotallySplit,`_private.ThetaStdTotallySplit)] do
  n := replaceNamePrefix n a b
 return n
private structure Dag where
 nodes : Array Json := #[]
 memo : Std.HashMap Expr Nat := {}
private partial def encodeExpr (e : Expr) : StateM Dag Nat := do
 if let some i := (←get).memo[e]? then return i
 let node ← match e with
 | .bvar i => pure (Json.arr #[toJson "bvar",toJson i])
 | .fvar i => pure (Json.arr #[toJson "fvar",toJson (toString (repr i))])
 | .mvar i => pure (Json.arr #[toJson "mvar",toJson (toString (repr i))])
 | .sort l => pure (Json.arr #[toJson "sort",encodeLevel l])
 | .const n ls => pure (Json.arr #[toJson "const",encodeName (normalizeName n),toJson (ls.map encodeLevel)])
 | .app f a => do
   let f ← encodeExpr f
   let a ← encodeExpr a
   pure (Json.arr #[toJson "app",toJson f,toJson a])
 | .lam _ t b bi => do
   let t ← encodeExpr t
   let b ← encodeExpr b
   pure (Json.arr #[toJson "lam",toJson t,toJson b,toJson (toString (repr bi))])
 | .forallE _ t b bi => do
   let t ← encodeExpr t
   let b ← encodeExpr b
   pure (Json.arr #[toJson "forall",toJson t,toJson b,toJson (toString (repr bi))])
 | .letE _ t v b nd => do
   let t ← encodeExpr t
   let v ← encodeExpr v
   let b ← encodeExpr b
   pure (Json.arr #[toJson "let",toJson t,toJson v,toJson b,toJson nd])
 | .lit (.natVal n) => pure (Json.arr #[toJson "nat",toJson n])
 | .lit (.strVal s) => pure (Json.arr #[toJson "strlit",toJson s])
 | .mdata _ e => return (←encodeExpr e)
 | .proj n i e => do
   let e ← encodeExpr e
   pure (Json.arr #[toJson "proj",encodeName (normalizeName n),toJson i,toJson e])
 let i := (←get).nodes.size
 modify fun s=>{s with nodes:=s.nodes.push node,memo:=s.memo.insert e i}
 return i
open Lean Elab Command in
run_cmd do
 let env ← getEnv
 let mods := #[`BinaryDehomogenization,`DivisorPicPrincipal,`DoubleRootPolynomial,`DoubleZeroDifferential,`ThetaBitangentAxes,`ThetaBitangentAxisIdentities,`ThetaBitangentCases,`ThetaBitangentContacts,`ThetaBitangentCore,`ThetaBitangentCountWave36,`ThetaBitangentExhaustionWave36,`ThetaBitangentGaloisWave36,`ThetaBitangentGeneric,`ThetaBitangentProjectiveChartsWave36,`ThetaBitangentQuadraticIndependence,`HalfCanonicalDifferential,`ThetaStdTotallySplit,`NativeBinaryP1,`NativeCurveModelExistence,`NativeFunctionFieldFunctor,`NativeStalkFieldNaturality,`OddThetaDivisorClassification,`P2M.Sol.S_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq,`P2M.Sol.S_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch,`PicEffectiveRepresentatives,`PicEllOneOfConstants,`QuarticSingletonZero,`QuarticTwoDoublePoints,`RiemannRochWithGenusFF,`SemilinearDifferentialOrder,`SemilinearPicAndEll,`SmallSquareSpaceBound,`Theorems.Thm_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq,`ThetaActualHalfCanonicalContacts,`ThetaActualLineDifferentials,`ThetaActualOddThetaClasses,`ThetaAffineContactConstants,`ThetaAffineContactOrder,`ThetaAssociatedLineAlgebra,`ThetaCanonicalLinePointValues,`ThetaChartCanonicalFrames,`ThetaChartTangentVanishing,`ThetaContactDifferentialDivisors,`ThetaContactLSpaceGeometry,`ThetaContactOddness,`ThetaContactPairFrames,`ThetaContactTangencyCertificates,`ThetaDActualDifferential,`ThetaDActualFieldCover,`ThetaDCanonicalInfinityDivisor,`ThetaDCanonicalPlaneBasis,`ThetaDChartNaturality,`ThetaDChartPlaceRegularity,`ThetaDCoordinateBasicOpens,`ThetaDExactChartTransitions,`ThetaDExactModel,`ThetaDFieldCoordinates,`ThetaDFiniteDifferential,`ThetaDFourInfinityPlaces,`ThetaDGenusThree,`ThetaDGeometricChartPoints,`ThetaDGeometricModel,`ThetaDGlobalCanonicalCandidate,`ThetaDGlobalSheafBasis,`ThetaDHyperplaneLocalOrders,`ThetaDInfinityLocalParameter,`ThetaDInfinityPoints,`ThetaDNativeProjRatios,`ThetaDNativeProjSections,`ThetaDNativeSections,`ThetaDNaturalGlobalDifferentials,`ThetaDOriginalChartOpens,`ThetaDOriginalCoordinateSections,`ThetaDPlaneChartSections,`ThetaDPlaneRegularForms,`ThetaDProjectiveInfinityCover,`ThetaDSectionComparison,`ThetaDifferentialChartIdentity,`ThetaEtaleAllPlaces,`ThetaFiniteGenericDegree,`ThetaFlatIntegralDescent,`ThetaGaloisCanonicalCorrespondence,`ThetaGaloisCanonicalPlane,`ThetaGaloisFieldAction,`ThetaGaloisPointPlace,`ThetaGaloisSchemeField,`ThetaGenericRankFraction,`ThetaGeometricChartEvaluation,`ThetaGeometricContactPoints,`ThetaGeometricPointCoordinateEvaluation,`ThetaGeometricResidueCoordinates,`ThetaHalfCanonicalRootSupport,`ThetaHalfCanonicalSquareContact,`ThetaLineAlgebraDecomposition,`ThetaLineFixedFields,`ThetaLineGeometricPoints,`ThetaLineOrbits,`ThetaLineRootPointCharts,`ThetaLineSplittingField,`ThetaLineStabilizers,`ThetaLinesAbsoluteGalois,`ThetaLinesContactPoints,`ThetaLinesDualLines,`ThetaLinesFullAssembly,`ThetaLinesGaloisAction,`ThetaLinesPolynomialContacts,`ThetaLinesProjectiveClassification,`ThetaLinesProjectiveLines,`ThetaLinesSchemePoints,`ThetaLiteralBinaryRestrictions,`ThetaLiteralRootJets,`ThetaLocalLineDerivatives,`ThetaNativeDualCanonicalLines,`ThetaNativeFunctionFieldMap,`ThetaNativeLineGaloisSet,`ThetaOddGaloisActionHom,`ThetaOddNativeGaloisEquiv,`ThetaOddNativeLineEquiv,`ThetaOddNativeSquareContact,`ThetaOddThetaCanonicalLines,`ThetaOrbitEvaluation,`ThetaOrderTwoDerivativeEvaluation,`ThetaProjectiveRootPlaceEmbedding,`ThetaRegularFunctionDifferential,`ThetaRestrictionHasTwoRoots,`ThetaRootCanonicalSections,`ThetaRootOrderDoubleJets,`ThetaUnramifiedPlaceIndex,`ThetaValuationTangencyOrder,`ThetaVanishingDifferentialOrder,`ThetaVerticalContactConstants,`ThetaVerticalContactOrder,`ThetaStdRingFlatRank,`ThetaStdSchemeFlatRank,`ThetaStdModuleFinitePresentation]
 let action : StateM Dag (Array Json) := do
  let mut entries := #[]
  for (n,ci) in env.constants.toList do
   if let some idx := env.getModuleIdxFor? n then
    if mods.contains env.header.moduleNames[idx.toNat]! then
     let ty ← encodeExpr ci.type
     let val ← if ci.isTheorem then pure none else match ci.value? true with
      | none => pure none
      | some e => do
       let i ← encodeExpr e
       pure (some i)
     entries := entries.push (Json.mkObj [("declaration",toJson (normalizeName n).toString),
      ("level_parameters",toJson (ci.levelParams.map Name.toString)),("type",toJson ty),("value",toJson val)])
  return entries
 let (entries,dag) := action.run {}
 logInfo m!"COMPACT_INTERFACES {(Json.mkObj [("entries",toJson entries),("nodes",toJson dag.nodes)]).compress}"
