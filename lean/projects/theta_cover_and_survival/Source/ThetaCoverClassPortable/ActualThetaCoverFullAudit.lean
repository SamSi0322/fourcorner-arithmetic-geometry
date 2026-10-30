import ThetaCoverClassPortable.ThetaCoverClassFullStatement
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let owned := #[`ThetaCoverClassPortable.ActualThetaCoverData,`ThetaCoverClassPortable.ThetaCoverClassFullStatement]
  let allowed := #[`propext,`Classical.choice,`Quot.sound]
  let mut pending : Array Name := #[]
  let mut count : Nat := 0
  for (n,_) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if owned.contains env.header.moduleNames[idx.toNat]! then
        let ax ← collectAxioms n
        for a in ax do unless allowed.contains a do throwError "Nonstandard axiom {a} in {n}"
        logInfo m!"AUDIT_AXIOMS {n} {ax.toList}"
        pending := pending.push n
        count := count + 1
  logInfo m!"AUDIT_DECLARATIONS {count}"
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      for bad in #[`MilneJVScheme.JacobianSchemeData,`GoodReductionJacobian.trivialPic0Designation,
          `GoodReductionJacobian.trivialRelativeGroupLaw,
          `ThetaDGlobalSheafBasis.globalEquiv,`oldplaneGlobalSectionEquiv,`sorryAx] do
        if bad.isPrefixOf n then throwError "Forbidden generic gap, classification, or placeholder {n}"
      for suffix in ["ThetaDGlobalSheafBasis.globalEquiv", "oldplaneGlobalSectionEquiv"] do
        if n.toString.endsWith suffix then throwError "Forbidden old nonnatural global equivalence {n}"
      let some c := env.find? n | throwError "Unresolved constant {n}"
      if c.isUnsafe || c.isPartial then throwError "Unsafe or partial constant {n}"
      if c matches .axiomInfo _ then
        unless allowed.contains n do throwError "Raw nonstandard axiom {n}"
      for dep in c.getUsedConstantsAsSet.toList do pending := pending.push dep
  logInfo m!"AUDIT_FULL_TYPE_VALUE_CLOSURE {seen.size}"
  logInfo "AUDIT_ZERO_UNSAFE_PARTIAL_PLACEHOLDERS true"
  for m in env.header.moduleNames do logInfo m!"AUDIT_IMPORT {m}"
