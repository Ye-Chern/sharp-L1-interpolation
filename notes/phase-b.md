# Analytic bridge progress, 2026-11-25

This branch is based on the certificate PR #5. The proof still follows the
paper's cutoff at 20.

## Compiled modules

- **Jacobi endpoints and reflection.** `JacobiSymmetry.lean` proves the
  three specializations at t=−1,0,1 and the full root-multiset reflection
  under t↦−t. Together with the preceding spectrum commit, the roots are
  all real and simple for every real parameter. Smooth dependence and the
  node-speed identity are separate steps.
- **Probability law.** `ExponentialMix.lean` proves the Fubini calculation
  for the strict tail of B−A. `NoAtom.lean` proves that any nonzero
  independent exponential term gives zero mass to a level set.
  `DifferenceLaw.lean` proves the exact two-component mixture as an equality
  of measures. `ExponentialRecurrence.lean` proves the same mixture after
  convolution with an independent interior law and the resulting identity
  for the closed CDF at zero. `ScaledExponential.lean` identifies the law
  of a positively scaled unit-rate exponential. `SignMean.lean` converts a law's
  CDF at zero to its sign expectation when there is no atom at zero.
  `WeightedExponential.lean` defines the iterated convolution law and proves
  all three branches of its zero-threshold CDF recurrence.
- **Coefficient comparison.** The accepted result of Gemini task 03 is
  `measure_sum_mul_le_antitone_of_expMeasure`. It allows both positive
  and negative coefficients. The two sums use the same random variables.
- **Fourier scalars.** The accepted result of Gemini task 01 includes
  the exact rational estimates behind `traceRatio` and `Gbound`.
  The remaining matrix trace and Fourier arguments are separate dependencies.
- **Exterior region.** `Exterior.lean` proves the speed factor decreases
  on [t,1], the nonnegative exterior weights increase, and their alternating
  sum is nonnegative for ordered nodes. A direct scalar consequence is the
  strict derivative bound on (1/2,1) whenever the paper's derivative formula
  holds. `CenterCriterion.lean` gives the final one-dimensional argument
  from central derivative positivity, exterior monotonicity and reflection.
  `FiniteCenter.lean` assembles the interval and origin proofs into the
  conditional center theorem, with the analytic inputs explicit.

## Resume the proof

1. Show that each row of the triangular integer-knots computation represents
   the zero-threshold CDFs of its corresponding contiguous slices using
   `weightedCdfZero_mixed`, `weightedCdfZero_nonpos` and
   `weightedCdfZero_nonneg_pos`. Use nonempty sorted lists for the final
   identification since `cdfExact []` is a default and the empty sum is zero.
   Reuse coefficient comparison and the no-atom lemma to supply the four real
   sign enclosures.
2. Establish smooth ordered Jacobi root curves, the node-speed formula and
   the error/derivative identities, especially `dS`, `Hderivative` and
   `Hcomp`. The exterior scalar lemmas are ready for those identities.
3. Apply the uniform origin bound, interval positivity and the center
   criterion. The numeric verification and this real-variable theorem
   have separate acceptance conditions.
4. Complete the large-order Fourier comparison and the sharp Sobolev
   reduction, including upper bound, optimizing sequences and the
   one-dimensional Sobolev class.

## Execution checkpoint

At 99d80fb the Lean kernel checked the original CSV for every order from 3
through 19. The run covers 2145 rows, 2128 adjacent intervals and 17 origin
neighborhoods. High orders use two-row proof chunks and the two largest
orders run as independent CI jobs.
[Certificate run](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/runs/45636804324).

Manual Gemini task files for the current round are in isolated worktrees
under `D:/work/sharp-L1-team/manual-gemini`. The main proof integrated
tasks 01 and 03 after recompiling their relevant statements. The remaining
two task cards concern the exact order-1/2 comparison and the implicit
Jacobi node-speed formula. The local Agent Harness uses explicit Medium
for scoped Qwen work. Its latest no-atom trial reached the deadline, and
the accepted proof of that lemma was completed directly.
