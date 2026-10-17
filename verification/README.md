# Verification record and boundaries

The local verification record covers the complete 182-module proof closure, followed by the separately compiled `Challenge`, `Solution` and `SubmissionSolutionAudit`: 185 targets altogether. Local success is tied to the recorded source and dependency identities, compiler commands, successful native exits and validated output artifacts.

`UnconditionalAreaFinalAudit.lean` audits 14 internal roots. `SubmissionSolutionAudit.lean` audits the five literal public declarations. Both print complete `@` types and enforce the exact standard axiom set `propext`, `Quot.sound`, `Classical.choice`. A matching `#guard_msgs` consumes its expected information message, so absence of 14 or five printed axiom lines is not by itself a failure or a success record. The immutable guard source and the actual successful compiler result must be considered together.

The five intentionally omitted proofs in `Challenge.lean` specify the problem. `Solution.lean` is checked independently and does not import `Challenge`. Native compilation and axiom guards are supplemented by genuine Comparator checking of every target's type against the separate specification, and by Lean/NanoDa/con-ron replay.

`SHA256SUMS` freezes the released sources and configuration used for the checks. The provenance records preserve the locally checked source identities and any native-to-release change, including neutral historical-documentation comments and line endings. A different release SHA is never represented as the original native SHA.

For the 81 pinned EllipticPDE modules, the successful native source SHA equals the Windows checkout SHA for all 81. Its HEAD is `ec784093f30308ef770ff855ce624725adf6f870` and the checkout was clean. Raw Git blobs use LF while that native checkout uses CRLF: raw byte equality is 0/81, and CRLF-to-LF normalized SHA equality is 81/81. There is no non-line-ending source difference in those modules. The per-module mapping retains both hashes and the Git blob identity.

A final Linux checkout builds the actual released bytes using the fixed dependency pins. The Lean verification Action builds the 185 targets and runs both audits. Palomar checks validates metadata, license and source integrity and runs the five-target Comparator wrapper with the bundled three kernels. Both recheck the source checksums and Git differences after verification. Their result is read from the run for the exact commit; this document does not assert that a particular Actions run succeeded.

The reviewed target list specifies cross-module order. Own-package Lean commands use `-j1` and `Elab.async=false`; dependency-package internals and the sandbox retain their own settings. This is an execution-resource boundary, not a claim that any dependency proof is exempt from kernel checking.

AI-assisted review and local verification are disclosed in `formalization.yaml`. No independent human review is recorded. Repository visibility and Palomar acceptance are not inferred from compilation or CI.
