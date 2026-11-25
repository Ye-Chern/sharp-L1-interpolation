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

`Audit.lean` prints the kernel dependencies of the Phase A theorems. The Lean CI
job also audits declarations against the standard axiom allowlist. The separate
certificate CI job runs the Python checkers. See the [Phase A map](../notes/phase-a.md)
for the statement reached by each layer.

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
