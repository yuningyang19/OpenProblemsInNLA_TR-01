# Lean 4 companion for the prescribed-width theorem (v7)

This standalone project formalizes the mathematical statements and proofs in
[the manuscript](../manuscript.pdf), including the prescribed width
`min(n, ceil(C*r/epsilon^2))`, the full range `0 < epsilon < 1`, and the
Bernoulli-density and sampling extensions used to prove it.

The statement-to-manuscript correspondence was reviewed in an independent agent
context. Lean's kernel checks the formal proofs of those statements. These are
separate checks: Lean does not parse the English manuscript or certify novelty.
The recorded scope is 12 named results, 50 supporting interfaces and 34
definitions, together with 10 changed/additional interfaces. The 407 declarations
in the dependency audit are implementation targets, not 407 manuscript theorems.

## Install and run

Install Git and Lean using the [official Lean installation guide](https://lean-lang.org/install/).
On macOS or Linux, the official [elan installer](https://github.com/leanprover/elan)
is an alternative:

```sh
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

Open a new terminal after installation. On Windows, use the official Lean setup
instructions or run the following commands inside WSL. Python 3 is needed only
for the verification wrappers. No TeX installation is required for Lean.

```sh
git clone https://github.com/yuningyang19/OpenProblemsInNLA_TR-01.git
cd OpenProblemsInNLA_TR-01/lean
lake exe cache get
python3 verify.py
```

`lean-toolchain` selects Lean **4.33.0** automatically through elan. Mathlib is
pinned to `db584cd6d46c92f209a44c0f1c829460d327499d`; do not run `lake update`
when reproducing this version. `lake exe cache get` downloads the pinned
Mathlib build cache. The first project build can take tens of minutes and
requires several GB of disk space; later builds reuse the local cache.

The default verifier checks the source hashes, builds the proof, executes the
exact public-type checks and axiom audit, and validates the archived dependency
graph. For new graph evidence, all seven semantic regression clients, and a
fresh kernel replay, run:

```sh
python3 verify.py --graph --semantic --fresh-kernel
```

The fresh kernel replay can take around 20 minutes or longer. Logs and the
machine-readable result are written to `build/`; a failed command returns a
nonzero exit status. To rebuild project objects from scratch while keeping the
pinned dependency cache, remove **only** `.lake/build` before running the verifier.

Without Python, the core Lean checks are:

```sh
lake build Problem56.PaperV7.Certification Problem56.PaperV7.BoundaryChecks
lake env lean Problem56/PaperV7/BoundaryChecks.lean
lake env lean Problem56/PaperV7/AxiomAudit.lean
lake env leanchecker --fresh -v Problem56.PaperV7.Certification
```

## Read the statement and proof

- [`Expected.lean`](Problem56/PaperV7/Expected.lean): independently reviewed reference statements.
- [`Certification.lean`](Problem56/PaperV7/Certification.lean): proved public declarations with exactly those types, beginning with `Problem56.PaperV7.certified_main` and `certified_explicit_main`.
- [`BoundaryChecks.lean`](Problem56/PaperV7/BoundaryChecks.lean): definitional equality checks between public theorem types and references.
- [`Main.lean`](Problem56/PaperV7/Main.lean): prescribed-width proof assembly.
- [`final_candidate_correspondence.json`](audit/final_candidate_correspondence.json): manuscript-to-declaration map, including inherited and revised interfaces.

The new modules reuse the earlier v6 Walsh, cumulant, graph-counting and
probability proofs. All 159 inherited certification inputs remain byte-identical.
New proofs cover arbitrary Bernoulli densities, saturated sampling (including
a joint-law theorem with no upper Bernoulli draw), and the prescribed width.

## Verification record and provenance

[`SOURCE_MANIFEST.json`](SOURCE_MANIFEST.json) records all 191 certified source
and build inputs, their import closure, and the immutable mathematical source
commit. They were exported without changing any mathematical bytes.
[`audit/delivery_check.json`](audit/delivery_check.json) records the completed
checks, and [`audit/final_binding_review.json`](audit/final_binding_review.json)
records the independent binding review. Historical path strings in audit reports
refer to the original working layout; no private repository is needed to build.

All checked theorem dependencies use only `propext`, `Classical.choice` and
`Quot.sound`; no `sorry`, `admit` or custom mathematical axioms are admitted.
The project objects were rebuilt separately using pinned dependency caches. An
initial universe annotation error in the checking client was corrected; both the
initial failed receipt and successful recovery are retained. The final integrated
proof objects also passed `leanchecker --fresh` (exit 0; 1072 seconds). These facts
do not assert a fresh compilation of all Mathlib dependencies or binary-identical
object files across filesystem paths.

The frozen manuscript used for the correspondence review is retained in
[`audit/frozen_manuscript.tex`](audit/frozen_manuscript.tex). Later editorial-only
changes to the public manuscript are documented separately. See
[`NOTICE.md`](NOTICE.md) for the inherited companion's license notice.
