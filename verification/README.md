# Verification record and boundaries

The development-native verification record covers the complete 182-module proof closure and the historical literal modules `Challenge`, `Solution` and `SubmissionSolutionAudit`. The released package uses the unchanged statement/proof payloads under the unique roots `PlanarBucklingChallenge` and `PlanarBucklingSolution`, with the audit import updated accordingly: still 185 targets altogether. The historical native records retain their original names and hashes; they are not a claim of native verification of the renamed module environment. Local success is tied to the recorded source and dependency identities, compiler commands, successful native exits and validated output artifacts.

`UnconditionalAreaFinalAudit.lean` audits 14 internal roots. `SubmissionSolutionAudit.lean` audits the five literal public declarations. Both print complete `@` types and enforce the exact standard axiom set `propext`, `Quot.sound`, `Classical.choice`. A matching `#guard_msgs` consumes its expected information message, so absence of 14 or five printed axiom lines is not by itself a failure or a success record. The immutable guard source and the actual successful compiler result must be considered together.

The five intentionally omitted proofs in `PlanarBucklingChallenge.lean` specify the problem. `PlanarBucklingSolution.lean` is checked independently and does not import `PlanarBucklingChallenge`. Native compilation and axiom guards are supplemented by genuine Comparator checking of every target's type against the separate specification, and by Lean/NanoDa/con-ron replay.

`SHA256SUMS` freezes the released sources and configuration used for the checks. The provenance records preserve the locally checked source identities and any native-to-release change, including neutral historical-documentation comments and line endings. A different release SHA is never represented as the original native SHA.

For the 81 pinned EllipticPDE modules, the successful native source SHA equals the Windows checkout SHA for all 81. Its HEAD is `ec784093f30308ef770ff855ce624725adf6f870` and the checkout was clean. Raw Git blobs use LF while that native checkout uses CRLF: raw byte equality is 0/81, and CRLF-to-LF normalized SHA equality is 81/81. There is no non-line-ending source difference in those modules. The per-module mapping retains both hashes and the Git blob identity.

A final Linux checkout builds the actual released bytes using the fixed dependency pins. The Lean verification Action builds the 185 targets and runs both audits. Palomar checks validates metadata, license and source integrity and runs the five-target Comparator wrapper with the bundled three kernels. Both recheck the source checksums and Git differences after verification. Their result is read from the run for the exact commit; this document does not assert that a particular Actions run succeeded.

The reviewed target list specifies cross-module order. Own-package Lean commands use `-j1` and `Elab.async=false`; dependency-package internals and the sandbox retain their own settings. This is an execution-resource boundary, not a claim that any dependency proof is exempt from kernel checking.

AI-assisted review and local verification are disclosed in `formalization.yaml`. No independent human review is recorded. Repository visibility and Palomar acceptance are not inferred from compilation or CI.

## Module-root collision repair

The first Linux run for commit `77b0e5afdbfd0603cbd9ee0953edda3771fc5015` built the first 184 reviewed targets successfully, including the old own `Solution`. The last audit then encountered an ambiguous bare `Solution` import supplied by both the project and EllipticPdes. It failed before Comparator or any independent-kernel replay. The [recorded prefix evidence](linux-ci/first184-before-module-collision.json) and source provenance preserve that failure. The unique-root migration changes filenames, module routing and one audit import; the new exact commit still requires both workflows and genuine five-target/three-kernel checks.
