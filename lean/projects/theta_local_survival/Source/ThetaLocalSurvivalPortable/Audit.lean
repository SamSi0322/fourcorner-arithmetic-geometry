import ThetaLocalSurvivalPortable.ThetaLocalSurvival
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
#print FourCorner.ThetaLocalSurvival.StrongTopology.theta_local_survival
#print axioms FourCorner.ThetaLocalSurvival.StrongTopology.theta_local_survival
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let owned := #[`ThetaLocalSurvivalPortable.EtaleLocallyQuasiFinite,`ThetaLocalSurvivalPortable.ActualAbelianMultiplication,`ThetaLocalSurvivalPortable.SquareZeroScalars,`ThetaLocalSurvivalPortable.ActualInfinitesimalPoints,`ThetaLocalSurvivalPortable.AffinePointAlgebra,`ThetaLocalSurvivalPortable.AffinePointTopology,`ThetaLocalSurvivalPortable.LocalizationPointHomeomorph,`ThetaLocalSurvivalPortable.SchemePointTopology,`ThetaLocalSurvivalPortable.PointSupportContinuity,`ThetaLocalSurvivalPortable.OpenImmersionPoints,`ThetaLocalSurvivalPortable.PolynomialPointTopology,`ThetaLocalSurvivalPortable.GeneratorPointEmbedding,`ThetaLocalSurvivalPortable.ParametricPolynomialLift,`ThetaLocalSurvivalPortable.EtaleSquarePresentation,`ThetaLocalSurvivalPortable.PolynomialStrictDerivative,`ThetaLocalSurvivalPortable.PolynomialImplicitNeighborhood,`ThetaLocalSurvivalPortable.ImplicitGraphChart,`ThetaLocalSurvivalPortable.PresentationImplicitSystem,`ThetaLocalSurvivalPortable.EtaleAffinePointLocalHomeomorph,`ThetaLocalSurvivalPortable.StrongAffineAtlas,`ThetaLocalSurvivalPortable.EtaleSchemePointLocalHomeomorph,`ThetaLocalSurvivalPortable.MonicRootBound,`ThetaLocalSurvivalPortable.CompactGraphProjection,`ThetaLocalSurvivalPortable.FiniteAlgebraPointBounds,`ThetaLocalSurvivalPortable.FiniteAlgebraPointFibres,`ThetaLocalSurvivalPortable.FiniteEtaleAffineCovering,`ThetaLocalSurvivalPortable.FiniteEtaleAffineSchemeCovering,`ThetaLocalSurvivalPortable.FiniteEtaleFullAffinePreimage,`ThetaLocalSurvivalPortable.CoveringOpenCharts,`ThetaLocalSurvivalPortable.FiniteEtaleSchemeCovering,`ThetaLocalSurvivalPortable.FreePolynomialPoints,`ThetaLocalSurvivalPortable.SmoothAffineEtaleCoordinate,`ThetaLocalSurvivalPortable.SmoothCurveNeighborhoods,`ThetaLocalSurvivalPortable.FiniteClosedBoundaryPoints,`ThetaLocalSurvivalPortable.GaloisTensorInvariant,`ThetaLocalSurvivalPortable.GaloisTensorProfinite,`ThetaLocalSurvivalPortable.GeometricSchemeAction,`ThetaLocalSurvivalPortable.GeometricAffineCharts,`ThetaLocalSurvivalPortable.GaloisAffineCompatibility,`ThetaLocalSurvivalPortable.GeometricGaloisFibres,`ThetaLocalSurvivalPortable.NoetherianConnectedComponents,`ThetaLocalSurvivalPortable.ClosedOrbitComponentDescent,`ThetaLocalSurvivalPortable.RationalComponentDescent,`ThetaLocalSurvivalPortable.DescendedComponentScheme,`ThetaLocalSurvivalPortable.AugmentedDerivations,`ThetaLocalSurvivalPortable.InfinitesimalAffineChart,`ThetaLocalSurvivalPortable.NaturalDerivationAddition,`ThetaLocalSurvivalPortable.InfinitesimalGroupLinearization,`ThetaLocalSurvivalPortable.AffineIdentityChart,`ThetaLocalSurvivalPortable.SquareZeroIdealDerivations,`ThetaLocalSurvivalPortable.ActualSquareZeroKernels,`ThetaLocalSurvivalPortable.SquareZeroKernelDivision,`ThetaLocalSurvivalPortable.SquareZeroGroupCorrection,`ThetaLocalSurvivalPortable.SquareZeroOpenLifting,`ThetaLocalSurvivalPortable.MultiplicationChartFormalEtale,`ThetaLocalSurvivalPortable.ActualMultiplicationFiniteEtale,`ThetaLocalSurvivalPortable.AbelianMultiplicationEndpoint,`ThetaLocalSurvivalPortable.MultiplicationComponentEndpoint,`ThetaLocalSurvivalPortable.MultiplicationComponentLocalCharts,`ThetaLocalSurvivalPortable.MultiplicationComponentFinitePlaces,`ThetaLocalSurvivalPortable.MultiplicationComponentRealPath,`ThetaLocalSurvivalPortable.ThetaLocalSurvival]
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  let mut pending : Array Name := #[]
  let mut count : Nat := 0
  for (n,ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if owned.contains env.header.moduleNames[idx.toNat]! then
        if (ci.isUnsafe || ci.isPartial) && (n.toString.splitOn "._unsafe_rec").length>1 then
          logInfo m!"AUDIT_EXCLUDED_COMPILER_RUNTIME_AUXILIARY {n}"
        else
          for a in (← collectAxioms n) do
            unless allowed.contains a do throwError "Nonstandard axiom {a} in {n}"
          logInfo m!"AUDIT_AXIOMS {n} {(← collectAxioms n).toList}"
          pending := pending.push n
          count := count+1
  unless count >= 62 do throwError "Missing owned declarations {count}"
  logInfo m!"AUDIT_DECLARATIONS {count}"
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      for bad in #[`sorryAx,`Lean.ofReduceBool,`Lean.trustCompiler,
          `MilneJVScheme.JacobianSchemeData,`GoodReductionJacobian.trivialPic0Designation] do
        if bad.isPrefixOf n then throwError "Forbidden dependency {n}"
      let some ci := env.find? n | throwError "Unresolved constant {n}"
      if ci.isUnsafe || ci.isPartial then throwError "Unsafe or partial dependency {n}"
      if ci matches .axiomInfo _ then
        unless allowed.contains n do throwError "Nonstandard raw axiom {n}"
      for x in ci.getUsedConstantsAsSet.toList do pending := pending.push x
  logInfo m!"AUDIT_FULL_TYPE_VALUE_CLOSURE {seen.size}"
  for m in env.header.moduleNames do logInfo m!"AUDIT_IMPORT {m}"
