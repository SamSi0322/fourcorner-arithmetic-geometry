Complete theta-cover-class and actual-Jacobian theta-survival sources

Toolchain: leanprover/lean4:v4.33.1
Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d

Mathematical endpoints:
  FourCorner.ThetaCoverClassFullStatement.prop_theta_cover_class
    import ThetaCoverClassPortable.ThetaCoverClassFullStatement
  FourCorner.ThetaSurvivingActualJacobians.cor_theta_surviving_covers
    import ThetaCoverClassPortable.ActualTwoJacobianSurvival

The source package contains 2050 consumption/provenance modules, one separate surviving-corollary validation module, and one portable entry: 2052 Lean sources. The completed Lake build uses these sources and the pinned standard dependencies. There are no private filesystem dependencies or bundled binaries.

Run python3 verify.py with the pinned Lake on PATH. VERIFY_WORKERS controls independent replay workers (default 4). Verification records an explicit full source/setup/native/runtime and toolchain baseline, runs every source ordinarily and cold, compares each emitted main/server/private olean part with the actual Lake output, and cryptographically rechecks the complete input baseline at the end. Replays never replace the Lake baseline objects. IR parts are fixed native/runtime inputs; generated IR output identity is not claimed.

Completed validation: 4104 strict source compiler runs; 2052 ordinary/cold/main-Lake object triples identical; six module-system modules also have 18 complete main/server/private triples independently byte,size,SHA checked. All 47309 input files have a matching final posthash. In the same combined import context the accepted 51 cover declarations have 109937 full type/value dependencies; the accepted 246 surviving declarations have 112640. Both scopes use only propext, Classical.choice, Quot.sound, with zero unsafe/partial/unresolved/placeholders. Ten inherited raw compiler partial auxiliaries are outside these accepted logical closures; no claim of zero partial declarations throughout every imported module is made.

The original mathematical declaration types and proof/RHS text are preserved. MODULE_MAPPING.json records source hashes and isolated import names. SOURCE_CONFIGURATION_PORTS.json records exact original producer frontend settings, observed generated-instance attribute relocations, and eight explicitly preserved original local-instance names. Full original/current types and values and related consumers were checked for the name ports. The publisher verifier additionally includes the independently satisfied split-output predicate; the completed batch used the preserved executed verifier, without rerunning core proofs after this validation-only strengthening.

Root acceptance verifies the complete numbered statements prop:theta-cover-class and cor:theta-surviving-covers. Copyright and source license notices are retained. See ROOT_ACCEPTANCE_SUMMARY.json for acceptance evidence hashes and scope.
