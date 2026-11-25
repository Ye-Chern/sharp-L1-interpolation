# Phase A team calibration, 2026-11-25

This small [work sample](phase-a-work-sample.md) used the v0.2 sources at
`7b6380e`, Lean 4.32.2, and the same Mathlib v4.32.2 cache across isolated
worktrees. Four independent outputs were scored: two Lean lemmas; the root and
coefficient dependency analysis; baseline replay plus two targeted certificate
mutations; and an audit of the zero-atom, interval, and origin conditions.
Local CLI experiments used an 8-minute cap. Times for Codex agents are
approximate and their token charges were unavailable. Directory permission,
startup, and timeouts are part of an execution result, and limit comparisons
of mathematical ability across providers.

## Verified samples and assignments

- **GPT 6.1 Terra XHigh, about 4m44s.** Lean 2/2, engineering 3/3, both
  decomposition and audit accepted. It gave the leanest imports and proof
  among the completed runs, and identified the no-atom obligation for the
  extracted CDFs. It recovered from incorrect initial import and API guesses
  on its own. The first production assignment was the independent Fourier
  audit, which also found the missing description of the reciprocal arctangent
  step.
- **GPT 6 Luna Low, instance 1, about 6m.** Lean 2/2, engineering 3/3, both
  decomposition and audit accepted. It recovered from a nonexistent tactic
  import and proof normalization trouble. It gave a usable root-completeness
  split and carried the production Lean root-bracketing proof to compilation.
- **GPT 6 Luna Low, instance 2, about 4m.** Lean 2/2, engineering 3/3, both
  decomposition and audit accepted. It used broader Mathlib imports in the
  trial. It repaired a mis-indexed mutation after seeing the wrong diagnostic
  and corrected its own integer division proof. It completed the production CDF
  rounding enclosure.
- The lead researcher independently replayed the three completed trial scripts
  and recompiled all six Lean declarations. Every accepted trial theorem used
  only standard Lean axioms. Both mutations failed for the intended reasons,
  namely incomplete certificate and no sign change. These were work samples
  on isolated copies of the source.

## Headless execution outcomes

- **Agent Harness, Qwen 3.8 Flash.** Node CLI supports explicit `--cwd`,
  `--model`, UTF-8 prompt files, JSONL events, deadlines and a session path for
  `--resume`. A tool-free service probe succeeded in 2.1 seconds, 645 reported
  tokens. The full work sample timed out at 480 seconds with no deliverable.
  Reported usage was 12,338 input, 835 output, and 22,528 cache-read tokens.
  About 413 seconds were spent on one Bash tool call that recursively sized the
  linked Mathlib directory. A surviving child from that call was stopped. For
  future production runs use a scoped Mathlib file search and PowerShell for
  the exact compile command. An isolated profile can be selected per process
  with `HARNESS_PI_DIR`; global configuration need not be changed. A second
  run in such an isolated profile repeated the expensive size scan and also
  timed out. Reported usage in that run was 47,825 input, 19,861 output and
  148,736 cache-read tokens. No further full sample was attempted.
- **Antigravity 1.5.17, Gemini 4 Hydrogen High.** Native `agy models` listed
  `gemini-4-hydrogen-high` and `gemini-4-neon-high`. Set the process's cwd,
  put the prompt directly after `-p`, and request JSON. Use the reported
  conversation ID with `--conversation` for a deliberate continuation.
  Hydrogen returned exit 0 and JSON status SUCCESS in about 15 seconds but
  had an empty reply and a denied command tool. No work sample was accepted.
  The response reported 29,664 total tokens, including the provider's own
  accounting conventions. A read-only research handoff is a better next test.
- **Antigravity 1.5.17, Gemini 4 Neon High.** A second session used a
  per-process allowlist and requested file operations before any terminal
  verification. It hit the 8-minute deadline and returned one Lean file.
  The lead's compilation confirmed the convex-combination lemma and found
  an unknown integer-division identifier in the other lemma. This is 1/2
  Lean declarations accepted; the other three outputs were missing.
  Provider JSON recorded 155,453 total tokens and separately reported cache
  reads. Given the high cost of the incomplete sample, prefer a narrowly
  scoped review question when retesting.
- **CodeBuddy 2.186.0, DeepSeek V4.1 Flash and HY.** The CLI recognizes print
  mode, structured result events, explicit model selection, resume by session
  ID and native worktree options. The installed help listed
  `deepseek-v4.1-flash` and `hy4-preview`; the requested `hy4-flash` spelling
  was probed but its mapping remains unverified. Both attempts returned a
  final structured authentication error in about 4 seconds, despite process
  exit 0, with zero reported token usage. These are unscored. The owner can
  sign in with the local CLI's `/login` before another test.

Check structured outcomes and actual files before counting a run. Use
inexpensive models on a well-defined task where the measured workflow is
reliable. Send further API search and small proof tasks to the verified Luna
workers meanwhile. Keep high-effort time for interface design, analytic review,
and genuinely difficult proof steps. Revise assignments as production evidence
accumulates.

## Production follow-up

- **Gemini through the owner's local interface.** Tasks 01–06 all produced
  proofs that passed an independent build. Tasks 05 and 06 delivered the
  exact-table invariant and the local inverse-function construction with
  uniqueness and simultaneous branches. This supports further well-scoped
  mathematical implementation through the manual workflow. The manual runs
  did not provide comparable timing or token measurements.
- **Qwen 3.8 Flash, Medium, Agent Harness `local`.** Task 07 used an isolated
  worktree. It wrote `NodeWeights.lean`, including Cassini and the normalized
  speed identity. The call hit its 780-second deadline during verification.
  The source passed a separate lead build and its main statements passed the
  axiom audit. The wrapper reported 96,138 input, 52,878 output and 1,328,640
  cache-read tokens. Treat that as provider usage telemetry. Future Qwen
  proofs should start with one narrow statement and a targeted build so
  partial work can be accepted before the deadline.
- **Luna High and Terra XHigh.** Luna derived and compiled strict containment
  of all Jacobi roots and supplied the barycentric coefficient step. Terra
  independently decomposed the Sobolev upper and lower bounds and identified
  the Lagrange API that removes an early blocker. These outcomes support
  using the roles as measured per task while keeping heavy builds staggered.
