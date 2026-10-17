# Development and verification notes

The public area inequality, exact open-disk equality characterization and planar Pólya–Szegő result no longer take the initial conditional delivery's `PaperExternals` argument. The missing analytic and geometric obligations are supplied by the proof chain used by the final unconditional roots. The original standard definitions and all five public target names are retained.

Some source module documentation contains `SOURCE_DRAFT`, `NOT COMPILED` or other development-time labels. Those labels describe the historical writing stage. A neutral comment identifies that history; the mathematical explanations, explicit assumptions of intermediate lemmas, attribution and `#guard_msgs` expected output remain intact. Consult [verification/README.md](verification/README.md), the frozen source records and the exact-commit CI result for this revision.

The two audits check full types and the standard three-axiom sets. Comparator checks the five public statements in separate Challenge/Solution environments, then the bundled kernels replay the proofs. These are distinct checks. `PlanarBucklingChallenge` contains intentional specification holes and is not imported into the proof environment.

The 185-target build order covers 104 own modules and 81 pinned EllipticPDE modules. Own libraries explicitly use `-j1` and `Elab.async=false`. EllipticPDE retains its own pinned options; cross-target ordering is not a promise that its internal Lean processing uses the same options. The initial Mathlib cache step and Comparator sandbox also have their own execution behavior.

The Windows-native EllipticPDE source records match the clean checkout byte for byte. All 81 differ from the publishing Git blobs only by CRLF versus LF; normalized SHA256 agrees for every module. This is recorded as a source-byte mapping, not raw SHA identity. Release comment changes and any line-ending changes likewise have explicit native-to-release mappings and require the final same-commit Linux build and replay.

The workflow structures and pinned actions derive from the user's reference repository at `b70cda58ddc4f4761a5a857b056310e713412386`. The Comparator wrapper derives from PalomarTemplate `2891de4c48955af824969a263d31b25e7a9a1406`; the fixed v0.4 metadata contract is from PalomarSubmission `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`. A successful reference run is evidence for that reference commit only. This project's CI evidence is always attached to its own exact commit.

Private repository preparation, successful Linux CI, public repository availability and Palomar registry acceptance are separate states. The workflows perform verification; they do not publish or submit the repository.

The current submission files are `PlanarBucklingChallenge.lean` and `PlanarBucklingSolution.lean`. Their unique root components avoid the pinned dependency's generic submission roots. Historical native evidence retains `Challenge`/`Solution`; the failed first Linux run is recorded in `verification/linux-ci/first184-before-module-collision.json`. This routing repair does not itself establish new Linux or Comparator success.
