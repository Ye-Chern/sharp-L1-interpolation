# Lean formalization

This package uses Lean 4.36.0 and Mathlib v4.36.0, pinned to
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842` in `lake-manifest.json` along with
its transitive dependencies. Elan selects the toolchain from `lean-toolchain`.

```sh
python3 scripts/check-lean-sources.py   # from Lean/ (or repo root on Lean/scripts/)
lake exe cache get
lake build Challenge Solution SharpL1
lake env lean Audit.lean
```

- **Palomar Comparator entry point:** `SharpL1.theorem_sharp_L1_interpolation_full`
  in [`Challenge.lean`](Challenge.lean) / [`Solution.lean`](Solution.lean),
  configured in [`comparator.json`](comparator.json) and documented in
  [`formalization.yaml`](formalization.yaml). On Linux with `bubblewrap`
  (`bwrap`), run `./scripts/verify-comparator.sh` to verify the statement/solution
  pair with Lean's kernel and NanoDa.
- **Internal library master theorem & audit:** `Audit.lean` prints the axiom
  dependencies of the internal theorems, including
  `SharpL1.Analysis.theorem_sharp_L1_interpolation_full` in
  `SharpL1/Analysis/MainTheorem.lean`, confirming only the standard axioms
  `[propext, Classical.choice, Quot.sound]`. See the
  [formalization map](../FORMALIZATION.md) for the full module correspondence.

## Parallel work

Use a dedicated worktree and branch per production task. Keep `Lean/.lake/build`
local to each worktree. On Linux or Windows, worktrees can share Mathlib's
compressed archive cache through `MATHLIB_CACHE_DIR`; this is independent of
the project's build output. Prefer a module-specific `lake exe cache get` when
the needed imports are known.

On the current Windows host the first runs reused the prebuilt dependencies
from an existing project whose toolchain and every locked Git revision match.
The checkout uses directory junctions for these packages. If reusing an
unpacked cache across worktrees, check the toolchain and every revision before
linking, designate one writer for cache maintenance, and avoid `lake update`
or cache refresh from linked worker worktrees. Dependency changes use a fresh
package directory. Keep trial outputs out of production PRs.

Start with one or two simultaneous local Lean processes and tune using free
RAM and warm-build timings. The initial Windows host had 16 logical CPUs,
15.7 GiB installed RAM and about 3.3 GiB free. Use `LEAN_NUM_THREADS=2` for
constrained local builds and delegate full clean validation to CI when useful.

## Historical bracket certificate builds

The arithmetic certificates are an optional Lean library, separate from the
usual theorem-development build. Run `lake build SharpL1Data.Order03` from
this directory to check the full order-3 dataset. Subsequent order targets
are named `SharpL1Data.Order04` through `SharpL1Data.Order19`. Build heavy
orders one at a time on the local Windows host. Altering the source CSV
invalidates the Lake input target.
