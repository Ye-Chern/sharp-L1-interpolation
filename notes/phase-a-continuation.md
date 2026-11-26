# Phase A continuation, 2026-11-25

## Formal results

- `checkRootRow_sound` certifies root brackets from the executable row check.
- `cdfLower_sound` and `cdfUpper_sound` prove the full triangular rounding enclosure.
  The proof uses one relational invariant for the real and integer traversals.
  The exact real recurrence is a formal arithmetic object. Its identification
  with the law of an exponential sum still requires the probability bridge.
- `checkOrder_sound` produces a checked origin, strictly ordered grid points,
  positive margins, and coverage through the outer grid endpoint.
  `checkOrder_derivative_pos` turns this into strict real-variable derivative
  positivity on the covered region under the componentwise sign enclosures,
  their monotonicity, and the derivative identity. `origin_derivative_pos`
  supplies the mean-value argument given a bound on the variation of H″.
- `jacobi_charpoly` proves paper equation `char`. `JacobiSpectrum.lean`
  proves simple spectrum, real splitting, exact root count and the affine
  formula for the direction matrix with positive diagonal entries.

## Certificate data

`CSV.lean` loads the repository CSV with a Lake input dependency and quotes the
selected integer data into Lean expressions. Each order is partitioned into
small proof chunks. Kernel checks prove Boolean acceptance for the emitted
values, then `checkOrder_of_chunks` joins the consecutive pieces.
`lake build SharpL1Data.Order03` checks the actual first order; larger orders
use the same module names with two decimal digits. The optional
`SharpL1Data` library imports the individual proofs. The dedicated GitHub job
checks the orders serially in each group to avoid excessive concurrent memory.
A separate Python exporter was cross-checked against all 2145 CSV rows.

The compiled kernel data theorem and the real-variable bridge are distinct.
Remaining inputs to the finite center theorem include the probability
interpretation of the recurrence, comparison by coefficients and parameter,
and the analytic identities supplying H′ and its origin variation.

## Worker setup and evidence

- The two Luna follow-ups ran at High. One built the triangular recurrence and
  local arithmetic; the lead completed the common invariant. The other built
  the root-row checker and worked on the exponential product calculation.
  Terra delivered the Jacobi determinant and spectrum proofs.
- CodeBuddy 2.186.0 authenticated in headless mode after local login.
  `hy4flash-free` produced the CSV exporter. `deepseek-v4.1-flash` produced
  an arithmetic sign-bound proof and ran its narrow Lean build. The lead
  streamlined the proof and kept the sign conversion executable on integers.
  HY's command was denied, so the lead ran deterministic export checks locally.
- Antigravity 1.5.17 executed `lean --version` with single-process
  `permissions.allow = ["command(lean --version)"]`. A separate file-only
  Hydrogen run confirmed the Fubini route to the exponential tail law.
- The local Agent Harness added a `local` tool profile with read, search,
  editing, writing and the preferred terminal. It selected PowerShell on
  Windows. Independent workdirs and session IDs can run concurrently; there
  is a lock only for concurrent writes to the same saved session.
  The Medium Qwen exporter verification finished in 173 seconds and found
  a cross-drive path bug, fixed and rerun successfully. A parallel API survey
  timed out at 240 seconds. Pi reported XHigh for that run despite a High
  request. Use explicit Medium for bounded routine tasks and raise effort
  for a well-scoped problem when warranted.
