# Lean formalization

This package uses Lean 4.32.2 and Mathlib v4.32.2, pinned to
`905b95818eb32af7874a58b427f50c1711a5e96c` in the Lake manifest along with its
transitive dependencies. Elan selects the toolchain from `lean-toolchain`.

```sh
cd Lean
lake exe cache get
lake build
lake env lean Audit.lean
```

`Audit.lean` prints the axiom dependencies of the main theorems, including
`SharpL1.Analysis.theorem_sharp_L1_interpolation_full`. The Lean CI job also
audits declarations against the standard axiom allowlist. See the
[formalization map](../FORMALIZATION.md) for the current theorem and its proof modules.

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
