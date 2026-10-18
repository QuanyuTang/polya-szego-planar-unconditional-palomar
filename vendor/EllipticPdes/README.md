# Vendored EllipticPDE source closure

Author: Alejandro Soto Franco. These third-party mathematical sources retain
all original copyright and author notices and the upstream Apache-2.0 license
in `LICENSE`.

The 81 Lean modules were copied byte for byte from
`alejandro-soto-franco/EllipticPDE` at commit
`ec784093f30308ef770ff855ce624725adf6f870`, beneath its `lean/` directory.
The exact upstream paths, Git blob IDs and SHA-256 values are recorded in
`../../verification/elliptic-vendor.json`.

The enclosing package configuration is a submission packaging adaptation:
it keeps the upstream package name and Lean options, pins the same Mathlib
revision as the containing project, and declares only the reviewed source
closure. It omits unrelated upstream audit and submission targets. No
mathematical Lean source is changed.

The containing project uses this directory as an ordinary contained Lake
path dependency. This places its `.lake/build` and `.lake/config` directly
under the dependency package root, as supported by the Palomar verifier's
writable-directory policy, rather than beneath a Git dependency's `lean/`
subdirectory.
