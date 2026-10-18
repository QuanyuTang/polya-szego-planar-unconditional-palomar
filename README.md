# A Formal Proof of the Planar Pólya–Szegő Buckling Conjecture
Authors: Quanyu Tang and Haiqi Zhang

This repository gives a Lean formalization proving the **planar Pólya–Szegő conjecture for the first buckling eigenvalue**. It establishes the sharp area inequality and characterizes equality by exact equality with an open disk, for every open planar set of finite positive area.

The original informal mathematical proof was developed by the human authors, **Quanyu Tang and Haiqi Zhang**, with assistance from **ChatGPT**. **Aristotle and Codex** constructed the Lean formalization based on the authors' original informal proof.

## The conjecture and the formalized theorem

The classical conjecture asks whether a disk minimizes the first clamped buckling eigenvalue among smooth bounded planar domains of prescribed area. For an open set $\Omega\subset\mathbb R^2$, the variational eigenvalue is

$$\Lambda_1(\Omega)=\inf_{\substack{v\in H_0^2(\Omega)\\\int_\Omega|\nabla v|^2>0}}\frac{\int_\Omega(\Delta v)^2}{\int_\Omega|\nabla v|^2},$$

where $H_0^2(\Omega)$ is the closure of $C_c^\infty(\Omega)$ in the Sobolev norm. Let $j_{1,1}$ be the first positive zero of the Bessel function $J_1$.

The formalized theorem applies to **every open set** $\Omega\subset\mathbb R^2$ with $0<|\Omega|<\infty$:

$$|\Omega|\,\Lambda_1(\Omega)\geq\pi j_{1,1}^2,$$

and equality holds if and only if $\Omega=B_R(a)$ for some $a\in\mathbb R^2$ and $R>0$. The equality conclusion is equality of sets with an **open disk**.

If $R>0$ and $\pi R^2=|\Omega|$, the planar Pólya–Szegő result is

$$\Lambda_1(B_R(0))\leq\Lambda_1(\Omega),$$

with equality if and only if $\Omega=B_R(a)$ for some $a$. This includes the classical smooth bounded case. Connectedness, boundedness, boundary regularity and a sign condition on a buckling eigenfunction are not additional hypotheses of the formalized area theorem.

## Content of the formal proof

The proof first establishes the sharp comparison

$$\Lambda_1(\Omega)\geq\frac{j_{1,1}^2}{j_{0,1}^2}\lambda_1^{\mathrm D}(\Omega),$$

where $\lambda_1^{\mathrm D}$ is the first variational Dirichlet eigenvalue and $j_{0,1}$ is the first positive zero of $J_0$. The comparison follows from a functional inequality for smooth compactly supported test functions, using Bessel profiles, divergence identities and matrix positivity; passage to the original Sobolev closures gives the eigenvalue inequality. The construction permits sign-changing test functions.

The [Faber–Krahn development](UnconditionalFaberKrahn.lean) proves the sharp Dirichlet area bound and its almost-everywhere disk rigidity. It constructs the required minimizers and weak PDE data, proves the positivity and polarization/reflection steps, and supplies the analytic result as a theorem rather than a hypothesis. Combining it with the buckling–Dirichlet comparison yields the sharp buckling area inequality.

For equality, [the disk rigidity argument](RequestProject/Core4.lean) proves that a proper nonempty open subset of a disk has strictly larger buckling eigenvalue. This uses the original $H_0^2$ closure and its control of pointwise limits. Consequently, even removal of a measure-zero subset cannot be ignored in the final equality case. The result is exact set equality with an open disk, rather than only equality almost everywhere.

The proof also establishes $\Lambda_1(B_R(a))=j_{1,1}^2/R^2$ for $R>0$. This converts the sharp area statement into the equivalent fixed-area disk minimization statement.

## Mathematical objects

`Plane` is `EuclideanSpace ℝ (Fin 2)`. A test function is smooth with compact support contained in the open set. `H01` and `H02` are the closures of its actual first- and second-derivative data in the corresponding products of `L²(Ω)`. The Hilbert-space and weak-gradient bridges retain these original data and their values and derivatives.

The Dirichlet eigenvalue is the infimum of $E_1/E_0$ over `H01` data with nonzero mass. The buckling eigenvalue is the infimum of the squared Laplacian norm divided by the squared gradient norm over `H02` data with nonzero gradient energy. The Bessel functions use their defining power series; `j01` and `j11` are the infima of their positive real zeros. [The specification](PlanarBucklingChallenge.lean) contains all definitions. [The solution](PlanarBucklingSolution.lean) proves their identification with the objects used in the proof, including square integrability of test functions and their derivatives.

## Public verification targets

The submission roots are `PlanarBucklingChallenge` and `PlanarBucklingSolution`. Their project-specific filenames comply with the [official module-root policy](https://github.com/PalomarRegistry/PalomarSubmission/blob/d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44/README.md#L149-L158) and avoid dependency module collisions.

`comparator.json` compares these exact declarations from `PlanarBucklingSolution` with the separately checked `PlanarBucklingChallenge`:

| Declaration | Result |
| --- | --- |
| `BucklingChallenge.area_inequality` | Sharp area inequality |
| `BucklingChallenge.area_equality_iff` | Exact open-disk equality characterization |
| `BucklingChallenge.polya_szego_buckling` | Planar Pólya–Szegő conjecture, including equality |
| `BucklingChallenge.bucklingEig_ball` | Disk buckling eigenvalue |
| `BucklingChallenge.buckling_ge_dirichlet` | Buckling–Dirichlet comparison |

`PlanarBucklingChallenge.lean` imports only canonical Mathlib and intentionally omits the five specification proofs. `PlanarBucklingSolution.lean` supplies proofs in a separate environment without importing `PlanarBucklingChallenge`. The permitted axioms are exactly `propext`, `Quot.sound` and `Classical.choice`.

`UnconditionalAreaFinalAudit.lean` prints the complete types of 14 internal roots and checks their axiom sets. `SubmissionSolutionAudit.lean` prints the complete types of the five public results and checks their axiom sets. These audits supplement the actual Challenge/Solution comparison.

The [final semantic audit](verification/FINAL-AUDIT.md) records the statement correspondence, unchanged definitions, discharged analytic obligations and exact-set equality argument.

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

`verification/build-targets.txt` builds 185 reviewed targets in dependency order: 104 project modules and 81 pinned EllipticPDE modules.

The **Lean verification** Action builds the full closure, runs both audits and checks the frozen sources. **Palomar checks** validates the fixed metadata contract, license and sources, then compares all five targets through Lean's kernel and the toolchain's bundled **NanoDa** and **con-ron**. The wrapper supplies the protected external-kernel configuration; the submitted `comparator.json` does not declare external kernels. Both workflows check source checksums again after verification.

Check the Actions result and logs for the **exact commit** being reviewed. A local native check, printed type or axiom guard does not establish a Linux Comparator or independent-kernel result. Source-byte provenance, historical development comments and verification boundaries are explained in [verification/README.md](verification/README.md).

## Provenance and availability

Based on the authors' original informal proof, Aristotle produced the initial conditional development, and Codex completed the missing proof obligations, API porting, semantic and axiom review, and local Lean verification. No independent human review of the formalization is recorded. See `formalization.yaml` for the source and automation disclosure. The source manuscript was consulted privately and is not included in the current source tree; earlier Git history is retained. The formalization is licensed under Apache-2.0; retained dependency and vendored-tool notices keep their own attribution and license terms.

Repository name: `polya-szego-planar-unconditional-palomar`. The repository can remain private during preparation, and its Linux CI can run while private. Palomar submission requires public access and is a separate later step. Neither workflow changes repository visibility or submits the project to Palomar; successful CI is not registry acceptance.
