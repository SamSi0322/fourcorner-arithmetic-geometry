import Lake
open Lake DSL
package fourcorner_elliptic_foundations where
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`maxHeartbeats, (4000000 : Nat)⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩, ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩]
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"
lean_lib ReplayImports where
  srcDir := "source"
lean_lib ReductionImports where
  srcDir := "source"
lean_lib EllipticCurves where
  srcDir := "source"
  globs := #[.submodules `EllipticCurves]
lean_lib OddTorsion where
  srcDir := "source"
lean_lib SplitKummerChecks where
  srcDir := "source"
@[default_target]
lean_lib FoundationCheck where
  srcDir := "source"
