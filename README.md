# Planar Pólya–Szegő Buckling: Area Inequality and Equality
Authors: Quanyu Tang and Haiqi Zhang

This Lean formalization proves `cor:area` and the two-dimensional `conj:PS` in the supplied manuscript *A sharp comparison between planar buckling and Dirichlet eigenvalues* ([PS_dim2_v3.tex](paper/PS_dim2_v3.tex)). The public statements use the original Sobolev spaces, variational eigenvalues and Bessel constants.

For every open set $\Omega\subset\mathbb R^2$ with $0<|\Omega|<\infty$,

$$|\Omega|\,\Lambda_1(\Omega)\geq\pi j_{1,1}^2,$$

and equality holds if and only if $\Omega=B_R(a)$ for some $a\in\mathbb R^2$ and $R>0$. The equality conclusion is equality of sets with an **open disk**.

If $R>0$ and $\pi R^2=|\Omega|$, the planar Pólya–Szegő result is

$$\Lambda_1(B_R(0))\leq\Lambda_1(\Omega),$$

with equality if and only if $\Omega=B_R(a)$ for some $a$. These public results have only the stated geometric and measure hypotheses; they do not take the initial delivery's `PaperExternals` package.

The two additional public results give $\Lambda_1(B_R(a))=j_{1,1}^2/R^2$ for $R>0$, and $\Lambda_1(\Omega)\geq(j_{1,1}^2/j_{0,1}^2)\lambda_1^D(\Omega)$ for nonempty open $\Omega$.

## Mathematical objects

`Plane` is `EuclideanSpace ℝ (Fin 2)`. A test function is smooth with compact support contained in the open set. `H01` and `H02` are the closures of its actual first- and second-derivative data in the corresponding products of `L²(Ω)`. The Hilbert-space and weak-gradient bridges retain these original data and their values and derivatives.

The Dirichlet eigenvalue is the infimum of $E_1/E_0$ over `H01` data with nonzero mass. The buckling eigenvalue is the infimum of the squared Laplacian norm divided by the squared gradient norm over `H02` data with nonzero gradient energy. The Bessel functions use their defining power series; `j01` and `j11` are the infima of their positive real zeros. `Challenge.lean` contains the full definitions, including the original `toL2` fallback; the test-function bridges prove the required square integrability.

## Public verification targets

`comparator.json` compares these exact declarations from `Solution` with the separately checked `Challenge`:

| Declaration | Result |
| --- | --- |
| `BucklingChallenge.area_inequality` | `cor:area`, inequality |
| `BucklingChallenge.area_equality_iff` | `cor:area`, exact open-disk equality |
| `BucklingChallenge.polya_szego_buckling` | `conj:PS` in dimension two |
| `BucklingChallenge.bucklingEig_ball` | Disk buckling eigenvalue |
| `BucklingChallenge.buckling_ge_dirichlet` | Buckling–Dirichlet comparison |

`Challenge.lean` imports only canonical Mathlib and intentionally omits the five specification proofs. `Solution.lean` supplies proofs in a separate environment without importing `Challenge`. The permitted axioms are exactly `propext`, `Quot.sound` and `Classical.choice`.

The local verification record covers the full source closure and the literal submission statements. `UnconditionalAreaFinalAudit.lean` prints the complete types of 14 internal roots and checks their axiom sets. `SubmissionSolutionAudit.lean` prints the complete types of the five public results and checks their axiom sets. These audits supplement the actual Challenge/Solution comparison.

## Reproduce the checks

| Component | Fixed revision |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc3` |
| Mathlib | `c55e6e786f49471c72fbddbec5415808896aec1e` |
| EllipticPDE | `ec784093f30308ef770ff855ce624725adf6f870` (`subDir = "lean"`) |

On Linux with the fixed toolchain and the prerequisites used by the workflows:

```sh
python3 -m pip install --disable-pip-version-check --require-hashes --no-deps -r requirements-ci.txt
python3 scripts/check-release-inputs.py
python3 scripts/validate-formalization.py
python3 scripts/check-lean-sources.py
sha256sum --check verification/SHA256SUMS
bash scripts/build-serial.sh
lake env lean -j1 -D Elab.async=false UnconditionalAreaFinalAudit.lean
lake env lean -j1 -D Elab.async=false SubmissionSolutionAudit.lean
bash scripts/verify-comparator.sh
sha256sum --check verification/SHA256SUMS
git diff --exit-code
```

`verification/build-targets.txt` builds 185 reviewed targets in dependency order: 104 project modules and 81 pinned EllipticPDE modules. The project sets `-j1` and `Elab.async=false` for its own libraries. The separate EllipticPDE package keeps its pinned compiler settings; ordering its targets does not impose those internal thread settings on it.

The **Lean verification** Action builds the full closure, runs both audits and checks the frozen sources. **Palomar checks** validates the fixed metadata contract, license and sources, then compares all five targets through Lean's kernel and the toolchain's bundled **NanoDa** and **con-ron**. The wrapper supplies the protected external-kernel configuration; the submitted `comparator.json` does not declare external kernels. Both workflows check source checksums again after verification.

Check the Actions result and logs for the **exact commit** being reviewed. A local native check, printed type or axiom guard does not establish a Linux Comparator or independent-kernel result. Source-byte provenance, historical development comments and verification boundaries are explained in [verification/README.md](verification/README.md).

## Provenance and availability

Aristotle produced the initial conditional development. Codex assisted completion of the missing proof obligations, API porting, semantic and axiom review, and local Lean verification. No independent human review of the formalization is recorded. See `formalization.yaml` for the source and automation disclosure. The formalization is licensed under Apache-2.0; retained dependency and vendored-tool notices keep their own attribution and license terms.

Repository name: `polya-szego-planar-unconditional-palomar`. The repository can remain private during preparation, and its Linux CI can run while private. Palomar submission requires public access and is a separate later step. Neither workflow changes repository visibility or submits the project to Palomar; successful CI is not registry acceptance.
