# Accompanying informal manuscript

Authors: Quanyu Tang and Haiqi Zhang

[Read the PDF](PS_dim2_v5.pdf) or [download the TeX source](PS_dim2_v5.tex).

## Status and relationship to the formalization

This is **working draft v5, dated 18 October 2026**. The manuscript is under revision and has not yet been submitted to arXiv. The source and PDF are provided for public reading and feedback. An arXiv link will be added when available.

The authors developed the original informal proof with assistance from ChatGPT. Aristotle and Codex constructed the Lean formalization from that original proof; this v5 manuscript is its current revised presentation. The formal development is not a line-by-line transcription of the manuscript. Palomar version 1 registers the Lean declarations at commit `5311f47821b5da92e81e75b7da5091d176c8deb9`, rather than verifying every step or sentence of this evolving draft.

The repository copy was prepared from the authors' `PS_dim2_v5.tex`. The original file had SHA-256 `90f4416b943f7e4ffeb4ae88594e4b3e96ce6fa36ea4e0c28bf466a5842b3e40`. Apart from normalizing line endings and trailing whitespace, the only changes are a dated version label and a first-page notice that the manuscript is under revision and has not yet been submitted to arXiv. The mathematical text and the existing AI-use disclosure are unchanged.

## Compilation

The manuscript is self-contained and includes its bibliography. With pdfLaTeX and the packages named in the preamble installed, run the following from this directory:

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error PS_dim2_v5.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error PS_dim2_v5.tex
```

For repository updates, keep auxiliary files outside the source tree and copy back only the final PDF. The checked-in PDF was compiled locally with pdfLaTeX from TeX Live 2022. Source and PDF hashes are recorded in `../verification/SHA256SUMS`; PDF bytes can vary with the TeX environment and build time.

## Rights

Copyright (c) 2026 Quanyu Tang and Haiqi Zhang. All rights reserved for the manuscript, including its TeX source and PDF. No additional reuse license is granted for these manuscript files. The repository's Apache-2.0 license applies to the formalization code; it does not extend to the manuscript.
