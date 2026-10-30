# Actual common-source odd-row lemma

This source project proves `lem:cs-odd-row` on the actual permitted whole-H
elliptic reduction probes and complete actual rational sources. The entry audits
the actual source construction from the two ordered Kummer slots and direct sum,
the genuine neutral/cyclic characters, actual generator coordinates and double,
the distinguished W parity, every W+2H coset, and the all-depth wrong-return and
even-label exclusions. The main declaration is
`FourCorner.CommonSource.common_source_odd_row`.

Install as `lean/projects/common_source` in the accompanying development tree.
Its direct source dependencies are root `fourcorner_paper` at `../..` and sibling
`fourcorner_small_curves` at `../small_curves`, with real Mordell-Weil/ordered
Kummer infrastructure inherited from that package's EllipticFoundations vendor.
The 46 reused parent sources are pinned individually in
`SHARED_SOURCE_DEPENDENCIES.json`. Only the 32 missing proof/support sources and
one verification entry are supplied; no parent copies or compiled artifacts.

New private module file paths under FourCorner.CommonSource* are relocated to
CSFoundation.CommonSource* to avoid the parent FourCorner library's broad glob.
Only affected import lines change; declaration namespaces, statements, hypotheses
and all proof bodies are byte-identical. `IMPORT_ONLY_ADAPTATION.json` records each
path/import change and original/package/body hashes. The checked
`OddTranslationsReplay` is used; the old CommonSourceOddLocalTranslations module
is excluded to avoid duplicate declarations.

With pinned Lean 4.33.1 run `LEAN_NUM_THREADS=1 lake --keep-toolchain --no-cache build`.
Then run `lake --keep-toolchain --no-cache env lean -t0 -Ddebug.skipKernelTC=false -R Source Source/CommonSourcePackage.lean`.
The entry prints the 35 transitive axiom lists in `AUDIT_DECLARATIONS.json`; only
propext, Classical.choice and Quot.sound are permitted. The same cold command on
`Source/OddRowFull.lean` checks the main source. Exact `.one` module globs preserve
parent source ownership. Nine standard git dependencies retain their pinned
revisions. Private paths, historical prompts/logs and binary caches are excluded.

The development parent small_curves library uses exact ownership for its 17
existing FourCorner modules (roots empty, explicit `.one` globs), preventing it
from claiming seven root-only modules. `PARENT_LIBRARY_OWNERSHIP.json` records the
configuration hashes and complete list. All parent mathematical source bytes and
dependency pins are unchanged. This is a configuration prerequisite, not a copied
parent library or a modified mathematical proof.
