# TR-01 upstream resolution PR task

Work from the current published `ajt60gaibb/OpenProblemsInNLA` `main`, not from a stale local snapshot. Before editing, fetch the latest upstream `main` and read the current versions of:

- `CONTRIBUTING.md`
- `RESOLVED.md`
- `.github/PULL_REQUEST_TEMPLATE.md`
- `randomized-and-low-rank-approximation/TR-01/README.md`
- the existing TR-01 report: https://github.com/ajt60gaibb/OpenProblemsInNLA/issues/48

Also inspect the recent resolution workflows, especially PRs #128, #134 and #136 and their linked issues. Follow the repository's current conventions rather than copying an older status scheme.

## Authoritative evidence for TR-01

The public proof repository is:

`https://github.com/yuningyang19/OpenProblemsInNLA_TR-01`

Use the immutable reviewed revision

`ed21181197ac839eac95f549404f94e7e3aa6e10`

for all primary manuscript and Lean links in the upstream submission. Do not replace immutable links by `main` links in the canonical evidence.

At that revision:

- `manuscript.pdf` and `manuscript.tex` contain the full prescribed-width proof.
- Theorem 1 proves
  \[
  k=\min\{n,\lceil Cr/\varepsilon^2\rceil\}
  \]
  with one universal constant, success probability at least `0.99`, the exact two-sign/two-Walsh law, fixed-size uniform sampling without replacement, and every fixed target subspace. It proves the stronger range `0 < epsilon < 1`, hence covers TR-01's `0 < epsilon < 1/2`.
- The Lean project is under `lean/`.
- The main certified declarations are in `lean/Problem56/PaperV7/Certification.lean`, especially `Problem56.PaperV7.certified_main` and `Problem56.PaperV7.certified_explicit_main`.
- The independent target statements are in `lean/Problem56/PaperV7/Expected.lean`.
- Statement correspondence and proof mapping are in `lean/audit/final_candidate_correspondence.json` and `.md`.
- Public verification evidence includes `lean/audit/delivery_check.json`, `lean/audit/fresh_kernel_replay.json`, `lean/audit/cold_rebuild.json`, `lean/audit/semantic_regressions.json`, and the axiom audit sources.
- `lean/README.md` gives the pinned Lean/Mathlib versions and reproduction commands.
- The recorded allowed transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`, `admit`, custom mathematical axioms, or `sorryAx` may support the target.

Do not alter the mathematical manuscript or Lean proof in this task. This task is only to prepare and submit the upstream catalog resolution cleanly.

## Status to propose

The current upstream repository has three complete-resolution evidence levels: `Solution claimed`, `Solved`, and `Lean verified`. Its current `CONTRIBUTING.md` permits `Lean verified` when the exact original target has a kernel-checked Lean proof, reviewed statement correspondence, reproducible verification evidence, pinned toolchain/dependencies, and a transitive axiom report.

Audit the public revision above against those requirements first. If every requirement is genuinely met, propose

`**Status:** Lean verified`

for TR-01. Do not downgrade merely because issue #48 was originally opened before the v7 Lean completion and therefore said `Solution claimed`.

However, do not force the label. If you find a real mismatch between the formal target and TR-01, an unproved premise not present in TR-01, missing transitive axiom evidence, or another failure of the current upstream Lean requirements, stop promotion at the strongest justified status and document the exact blocker. Never claim that the upstream catalog itself reran Lean unless you actually perform such a rerun in this task.

## Upstream editing scope

Create or use a fork of `ajt60gaibb/OpenProblemsInNLA`, fetch `upstream/main`, and create a dedicated branch from the latest upstream head, e.g.

`tr01-prescribed-width-resolution`

Keep the diff minimal and preserve all unrelated current upstream work.

For TR-01:

1. Keep the permanent ID `TR-01`, canonical path, original problem statement, references, difficulty and importance unchanged.
2. Update `randomized-and-low-rank-approximation/TR-01/README.md`, which is the source of truth:
   - change the status only to the strongest evidence level justified by the audit;
   - update `Last checked` to the actual review date;
   - add a prominent resolution notice;
   - explain precisely that the prescribed width itself is proved, not merely the existence of some smaller good width;
   - compare every relevant assumption and quantifier with the original TR-01 statement;
   - state that the manuscript proves the stronger `0 < epsilon < 1` range while TR-01 asks only `0 < epsilon < 1/2`;
   - add a `Lean proof and verification evidence` section modeled on the current IE-01 entry and satisfying the current `CONTRIBUTING.md` checklist;
   - use immutable `ed211811...` links for manuscript, Lean source, statement correspondence, reproduction guide/logs and axiom evidence;
   - distinguish manuscript proof, independent correspondence review, Lean kernel verification, and any upstream-local checks actually run.
3. Update `RESOLVED.md` with a concise TR-01 entry and exact evidence level.
4. Regenerate only the catalog/index/problem artifacts required by the current repository tooling. Expect changes such as `CATALOG.md`, root `README.md`, `randomized-and-low-rank-approximation/README.md`, `TR-01/problem.tex`, and `TR-01/problem.pdf` as generated consequences. Do not hand-edit generated files when the repository scripts own them.
5. Do not add a duplicate full manuscript or Lean tree to the upstream catalog unless current repository conventions explicitly require it. Prefer stable links to `yuningyang19/OpenProblemsInNLA_TR-01@ed211811...`; IE-01 shows that external formal-proof evidence is acceptable.
6. Do not modify repository-wide tooling, status definitions, tests, ID registry, renderer code, or contribution policy unless a current-main bug makes the TR-01 update impossible. If such a bug appears, stop and report it before broadening scope.

## Required validation

Use the latest upstream branch as the historical base. In a fork, do not accidentally validate against a stale `origin/main`; use the remote/ref that actually denotes the current published upstream main.

Run the current repository-prescribed checks, including at least:

```bash
python3 tools/validate_problem_ids.py --base-ref upstream/main
python3 tools/update_catalog.py --base-ref upstream/main
python3 tools/render_problems.py TR-01
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
```

Also run the current status-related tests if present in upstream `main`, and any additional checks required by the PR template or workflow. Compile/inspect the regenerated TR-01 PDF. Confirm that no permanent ID/path mapping or original mathematical target changed.

For the Lean evidence, inspect the immutable public revision directly. At minimum verify that the pinned files and theorem names referenced in the canonical README actually exist and that the public verification record is internally consistent. If practical, clone the immutable revision and run the public default verifier. The expensive fresh replay need not be repeated solely to restate an already public archived record, but if you do rerun it, report the actual command/result. Never fabricate a rerun.

## Pull request

Open a PR against `ajt60gaibb/OpenProblemsInNLA:main` from the fork branch, following the current `.github/PULL_REQUEST_TEMPLATE.md` exactly.

The PR should:

- identify `TR-01` and the exact prescribed-width affirmative resolution;
- link the immutable manuscript and Lean evidence at `ed211811...`;
- explain exact target correspondence and that no cases remain;
- for `Lean verified`, list the pinned Lean version, Mathlib revision, certified theorem declarations, correspondence evidence, reproduction commands, verification record and allowed axiom set required by current policy;
- explicitly distinguish formal Lean verification from informal AI-agent mathematical review and external human peer review;
- list all changed/generated documents and validation results;
- include `Closes #48` so the existing issue is linked to the PR;
- request maintainer review without asserting that upstream has independently rerun the Lean proof unless it actually has.

After opening the PR, add a short comment to issue #48 noting that the v7 Lean companion is now public at the immutable revision and linking the PR. Preserve the historical issue text; do not erase the fact that the original report began as `Solution claimed` before the Lean completion.

## Stop conditions and reporting

Do not merge the PR yourself. Do not close #48 manually; let `Closes #48` act on merge or let the maintainer decide.

At completion report:

- latest upstream base SHA used;
- fork/branch and pushed head SHA;
- exact files changed;
- final proposed status and why it satisfies the current policy;
- validation/test/PDF results;
- PR URL and issue comment URL;
- any remaining maintainer-only decision or CI requirement.

If upstream `main` changes materially during the task, rebase/update from the new upstream head, rerun the validations, and only then push the final PR head.