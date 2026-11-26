# Analytic bridge progress, 2026-11-25

> Historical checkpoint before PR #7. See the [current proof and verification map](../FORMALIZATION.md) for the all-order theorem.

This branch is based on the certificate PR #5. The proof still follows the
paper's cutoff at 20.

## Compiled modules

- **Jacobi endpoints and reflection.** `JacobiSymmetry.lean` proves the
  three specializations at t=−1,0,1 and the full root-multiset reflection
  under t↦−t. Together with the preceding spectrum commit, the roots are
  all real and simple for every real parameter. See the node-speed item below
  for regularity and the formula along an interior branch.
  `JacobiContainment.lean` (Luna High) bounds every root in `(−1,1)` for
  interior parameters by the Chebyshev recurrence and endpoint reflection.
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
  `WeightedComparison.lean` proves the CDF ordering for entire coefficient
  lists, invariance under a positive common scale and the sign expectation
  formula for any list with a nonzero coefficient.
- **Probability semantics of the exact table.** `CDFSemantics.lean` is the
  accepted result of Gemini task 05. The table's entry at gap `g` and index
  `i` is the zero-threshold CDF of the associated slice. For every nonempty
  nondecreasing integer list, the final `cdfExact` equals the weighted CDF.
  The analytic proof lives in a separate module from the executable checker.
  `CDFBridge.lean` then proves the sign-mean enclosure from ordered coefficient
  lists bracketing the true coefficients at any positive integer scale.
  `RealEndpoints.lean` instantiates this on the actual checked row for the core
  coefficient list. Connecting the root's descending witness to the global
  order and handling the three augmentations remain.
- **Barycentric differences.** `DividedDifference.lean` proves polynomial
  coefficient reproduction and deletion after multiplication by a node's
  linear factor. `DividedCDF.lean` proves the two constant branches and the
  two-endpoint recurrence for truncated-power differences. The induction
  identifying the two families of recurrences remains open.
  `ErrorDividedDifference.lean` proves the single and double endpoint
  deletion formulas and `barycentric_Hcomp`, the algebraic equality of the
  derivative's weighted divided difference with a combination of four
  truncated-power differences. Identifying both sides with the paper's
  derivative and sign laws still requires the surrounding analytic bridges.
- **Coefficient comparison.** The accepted result of Gemini task 03 is
  `measure_sum_mul_le_antitone_of_expMeasure`. It allows both positive
  and negative coefficients. The two sums use the same random variables.
- **Fourier scalars.** The accepted result of Gemini task 01 includes
  the exact rational estimates behind `traceRatio` and `Gbound`.
  The remaining matrix trace and Fourier arguments are separate dependencies.
- **Low orders and node speed.** `LowOrders.lean` (Gemini task 02) proves
  strict center maximality for the explicit order-1 and order-2 functions.
  `LowOrderNodes.lean` (Gemini task 11a) identifies the complete ordered root
  sets and matches the paper's explicit error to these functions on `[0,1]`.
  Both strict center comparisons on the positive half of the interval now
  hold for the canonical ordered nodes. The all-order identification with
  the integral error and its reflection identity are separate steps.
  `NodeSpeed.lean` (task 04) proves the polynomial speed identity, simplicity
  for interior roots, and the exact speed and its bounds along differentiable
  root branches. `RootBranches.lean` (task 06) proves local existence,
  uniqueness, differentiability and the speed on a neighborhood. For an
  ordered interior family of full size, the simultaneous disjoint branches
  exhaust the root multiset locally. `JacobiOrdered.lean` (Luna High) defines
  the canonical root order for every parameter. `OrderedNodeCurves.lean` identifies
  it with the local differentiable branches in `(−1,1)` and proves the nodes
  strictly increase and `t − u_j(t)` is monotone there. Closed-interval endpoint
  continuity and the exact endpoint partition remain open.
  `NodeWeights.lean` (Qwen Medium, task 07) uses Chebyshev's Cassini identity
  to prove the inverse-denominator speed formula for the monic polynomial.
  The Qwen call ended by timeout after writing the source. The module passed
  the independent targeted build in the main worktree.
- **Exterior region.** `Exterior.lean` proves the speed factor decreases
  on [t,1], the nonnegative exterior weights increase, and their alternating
  sum is nonnegative for ordered nodes. A direct scalar consequence is the
  strict derivative bound on (1/2,1) whenever the paper's derivative formula
  holds. `CenterCriterion.lean` gives the final one-dimensional argument
  from central derivative positivity, exterior monotonicity and reflection.
  `FiniteCenter.lean` assembles the interval and origin proofs into the
  conditional center theorem, with the analytic inputs explicit.
  `TruncatedPowerDeriv.lean` proves differentiation of every positive-part
  power with exponent at least two at its knot and away from it.

## Resume the proof

1. Use the exact table's CDF semantics, coefficient comparison and the
   ordered root families to supply the four real sign enclosures. Use
   nonempty sorted lists since `cdfExact []` is a default and the empty
   sum is zero.
2. Prove endpoint continuity of the ordered Jacobi roots and their exact
   endpoint partition. Prove the error and derivative identities, especially `dS`,
   `Hderivative` and `Hcomp`. The exterior scalar lemmas are ready for those
   identities.
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

Gemini tasks 01 through 06 were recompiled and integrated. The remaining
work and the order for delegated tasks are in [the handoff](tasks/START.md).
The [finite algebraic bridge](finite-algebraic-bridge.md) derives `Hcomp` from
the weighted CDF by a common divided-difference recurrence and deletion
identities. This removes the simplex-integral and density-regularity
dependencies from that particular bridge. Its mathematical derivation and
the compiled modules above have separate statuses.
