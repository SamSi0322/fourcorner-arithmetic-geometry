import ThetaCoverClassPortable.NativeRealPath
import Lean.Util.CollectAxioms
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for n in #[`FourCorner.ThetaLiteralModels.C, `FourCorner.ThetaActualPoints.originC,
      `FourCorner.ThetaProjectiveModel.chartIso, `FourCorner.ThetaLiteralModels.cToBase,
      `FourCorner.ThetaProjectiveModel.toBase, `FourCorner.ThetaActualPoints.boundaryPoint] do
    let some c := env.find? n | throwError "Missing original declaration {n}"
    match c with
    | .defnInfo d => logInfo m!"ORIGINAL_DEFINITION_FINGERPRINT {n} {d.type.hash} {d.value.hash}"
    | _ => throwError "Expected original definition {n}"
#print axioms FourCorner.ThetaSurvivingNativeRealPath.actualPoint_origin
