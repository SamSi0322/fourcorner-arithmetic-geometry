import Lake
open Lake DSL
package fourcorner_uniform_torsion where
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`maxHeartbeats, (2000000 : Nat)⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩, ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩]
require fourcorner_paper from "../.."
require fourcorner_elliptic_foundations from "../../vendor/elliptic_foundations"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"
lean_lib UniformTorsion where
  srcDir := "source"
  globs := #[.one `UniformCurve, .one `UniformDoubling, .one `UniformGroupAdapter,
    .one `UniformDyadic, .one `UniformDyadicRat, .one `UniformDyadicVal,
    .one `UniformDyadicFamily, .one `UniformNonsingular, .one `UniformLocalBridge,
    .one `UniformNoOdd, .one `UniformGroupCore, .one `UniformTorsion,
    .one `UniformRankZero, .one `UniformStrictInterval, .one `UniformStrictQuotient]
@[default_target]
lean_lib UniformFullCheck where
  srcDir := "source"
