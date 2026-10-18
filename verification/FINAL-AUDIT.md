# Final statement and semantic audit

This AI-assisted review rechecked the formal statements against the privately supplied source manuscript, including its definitions of the variational eigenvalues, `cor:area` and `conj:PS`. It does not claim independent human review. The manuscript is not distributed in the current repository tree. Its locally reviewed source is identified by SHA-256 `d0d04dbc3ba3cc46f78930000c52a43f7447c2f160ba1c4d6fa17abdbeb6aea6` in the provenance record.

## Statement correspondence

| Source statement | Public Lean declaration | Hypotheses and conclusion |
| --- | --- | --- |
| `cor:area`, inequality | `BucklingChallenge.area_inequality` | Every open planar set with finite positive area satisfies the sharp area inequality. |
| `cor:area`, equality | `BucklingChallenge.area_equality_iff` | Equality is equivalent to exact set equality with an open disk of positive radius. |
| `conj:PS` | `BucklingChallenge.polya_szego_buckling` | The disk of prescribed equal area minimizes the buckling eigenvalue, with equality precisely for a translated disk. This covers the classical smooth bounded case. |

The first two declarations require only `IsOpen Ω`, `0 < volume Ω` and `volume Ω < ⊤`. The fixed-area formulation additionally specifies a positive radius and equality of areas. There is no added connectedness, boundedness, boundary regularity or eigenfunction sign hypothesis. No external Faber–Krahn theorem package is a public theorem input.

## Definitions and possible degeneracies

- The specification and solution contain the same 20 mathematical definitions, checked as identical text after line-ending normalization. `Plane` is the Euclidean plane; `pderiv` uses the actual Fréchet derivative.
- `H01` and `H02` are closures of the value/derivative graphs of smooth compactly supported test functions in finite products of the actual `L²(Ω)` spaces. These are the concrete Sobolev closure models used by the source definition. The finite-product norm gives the same closure topology as the usual Sobolev norm; integration-by-parts and weak-derivative bridges preserve the derivative relations.
- The solution proves `H01_eq`, `H02_eq`, `dirichletEig_eq` and `bucklingEig_eq` with the objects used by the proof. It proves square integrability of test functions and their first and second derivatives, so the specification's `toL2` zero fallback cannot change these graphs.
- Rayleigh infima use the actual mass, gradient and Laplacian energies. The density and test-function lemmas supply nonempty admissible classes on nonempty open sets; a real infimum over an empty class is not used to obtain the target result.
- Bessel functions are defined by their power series, and `j01` and `j11` by their positive-zero infima. The bridges identify these with the proof's `jq` and `jk`. The proved Bessel-zero properties establish `0 < jq < jk`; the Dirichlet constant `π * jq²` is distinguished from the buckling constant `π * jk²`.

## Analytic obligations and equality

`DirichletFKAreaProduct.global_lower_bound` produces the sharp Dirichlet bound. The ground-state, weak PDE, positivity, polarization and reflection proofs produce the almost-everywhere disk rigidity. `faberKrahn_holds_without_E12` and `paperExternals_holds_without_E12` assemble these as closed theorems. Intermediate lemmas with a Faber–Krahn premise receive this proved lower bound; it is not an unproved hypothesis at the final interface.

The exact equality case uses two separate steps in `RequestProject/Core4.lean`: an open set almost everywhere equal to a disk is contained in that disk, and every proper nonempty open subset of the disk has strictly greater buckling eigenvalue. The latter argument uses `H02` minimizing sequences, uniform control of their continuous representatives, and positivity of the disk profile at any omitted interior point. Thus a punctured disk is not silently identified with a disk.

## Trusted proof boundary

The five omitted proofs in `PlanarBucklingChallenge.lean` are specification placeholders. The solution is compiled separately and does not import that module. The 14 internal and five public audit targets enforce the exact axiom set `propext`, `Classical.choice`, `Quot.sound`; the five public proofs admit no additional axioms.

The release checks build the 185-target source closure, print the complete audited types, compare all five solution statements with the isolated specification, and replay the exported solution through Lean, NanoDa and con-ron. The additional Official Palomar mechanical preflight runs the registry's complete pinned verifier, including the outer build sandbox. Consult the GitHub Actions workflows for the exact commit being reviewed. This document is a semantic review and does not substitute for those actual kernel runs or for Palomar registry acceptance.

The documentation and manuscript-removal update left all 104 project Lean files unchanged. The subsequent [filesystem compatibility repair](PALOMAR-COMPATIBILITY.md) also leaves those files unchanged and includes the 81 required EllipticPDE modules as exact copies of their pinned upstream Git blobs. The dependency's package location and manifest change; its mathematical source, imports and upstream elaboration options are preserved. The five public targets, permitted axioms and 185-target order are unchanged. `SHA256SUMS` is regenerated for the resulting repository contents.
