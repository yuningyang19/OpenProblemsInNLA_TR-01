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

## Relation to Simons Problem 5.6

Problem 5.6 in the Simons workshop collection asks whether the rerandomized
SRHT is an oblivious subspace embedding with width $k=O(r/\varepsilon^2)$.
Theorem 1 answers that question as well: it gives the prescribed width
$k=\min\{n,\lceil Cr/\varepsilon^2\rceil\}$, rather than only the existence of
a width of that order. TR-01 also makes the normalization, uniform sampling
without replacement, and $0.99$ success probability explicit. The workshop
assumption $n=\Omega(\log r)$ adds no restriction here, since
$\log r\le r\le n$.

Our separate [Simons Problem 5.6 repository](https://github.com/yuningyang19/rerandSRHT_prob_5_6_simons_workshop)
contains the resolution of the workshop formulation and its Lean companion.

The manuscript includes the full proof and supporting references. Its
acknowledgments describe AI assistance. The [Lean 4 companion](lean/README.md)
now covers the current prescribed-width theorem and its supporting mathematics.
Manuscript-to-statement correspondence was reviewed in an independent agent
context; the formal proofs passed Lean compilation, axiom checks and a fresh
kernel replay. The upstream report remains a solution claim for maintainer review.

## Run the Lean verification

After [installing Lean](https://lean-lang.org/install/) and Python 3:

```sh
git clone https://github.com/yuningyang19/OpenProblemsInNLA_TR-01.git
cd OpenProblemsInNLA_TR-01/lean
lake exe cache get
python3 verify.py
```

See [the full instructions](lean/README.md) for fresh kernel replay,
semantic regression tests, the statement-to-proof map, and the verification
scope. Lean 4.33.0 and the Mathlib revision are pinned in the project.

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
