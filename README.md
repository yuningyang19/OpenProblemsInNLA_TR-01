# Subspace embeddings with the rerandomized SRHT

Yuning Yang

[Read the manuscript (PDF)](manuscript.pdf) · [LaTeX source](manuscript.tex)

This repository contains the manuscript addressing
[TR-01: Optimal dimension for a rerandomized Hadamard embedding](https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/randomized-and-low-rank-approximation/TR-01)
in Alex Townsend's *Open Problems in Numerical Linear Algebra* collection.

Theorem 1 (page 2) gives an affirmative answer at the prescribed width

$$
k=\min\{n,\lceil Cr/\varepsilon^2\rceil\},
$$

with a universal constant $C$, for every power-of-two ambient dimension,
every $1\le r\le n$, and every $0<\varepsilon<1$. The distribution uses exactly
two independent Rademacher diagonals, two normalized real Walsh transforms,
and an independent uniform coordinate subset sampled without replacement.
The success probability is at least $0.99$ on each fixed target subspace.
The range includes TR-01's $0<\varepsilon<1/2$. The explicit universal
constant and completion of the proof are in Section 5.3 (pages 39–40).

The manuscript includes the full proof and supporting references. Its
acknowledgments describe AI assistance. The linked earlier Lean companion
covers the earlier selected-width theorem, not the current prescribed-width
extension.

## Build

Requires a TeX Live or equivalent installation with `latexmk`, `pdflatex`,
and the standard packages used in the source, including TikZ and microtype.
Run from this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build manuscript.tex
cp build/manuscript.pdf manuscript.pdf
```

The only external TeX input is `figures/p7_contraction.tex`; the bibliography
is included in `manuscript.tex`. No private working-repository files are
required. File hashes and the packaging build are recorded in
[`MANIFEST.json`](MANIFEST.json).
