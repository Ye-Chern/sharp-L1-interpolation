# Phase A proof dependencies and status

Baseline: paper v0.2, commit `7b6380e`. The target remains the all-order computer-assisted proof with the analytic cutoff at 20. [Issue #4](https://github.com/Ye-Chern/sharp-L1-interpolation/issues/4) remains deferred.

## Next dependencies

1. **A1, integer polynomial evaluation.** Match `certificates/check.py:polynomial` to the real polynomial in paper.tex, equation `char`. Use Mathlib's `Polynomial.Chebyshev.U` throughout. The integer loop is independent of the later Jacobi matrix identification.
2. **A2, certified roots.** Prove degree and nonzero; use the intermediate value theorem on each open bracket, strict descending order to separate roots, and the degree bound to exhaust the roots with multiplicities. Keep the result at the polynomial level. The characteristic polynomial identity in M1 will identify these with eigenvalues.
3. **A3, directed CDF recursion.** Positive denominator and nonnegative coefficients give a one-step enclosure, including incoming rounding error. Lift to each subarray with exact constant branches for all nonpositive and nonnegative-with-a-positive-entry data. Preserve the `≤ 0` convention at zero.
4. **A4, finite computation.** A1 and A3 feed executable row, interval and coverage checks. Prove kernel acceptance against the actual data, in chunks if needed. First run a small order and measure the kernel reduction before choosing the representation of all 2145 rows. A Python PASS is a baseline for this step.
5. **B1, finite real-variable bridge.** A2 and M1 yield true coefficient enclosures. Couple all coefficient vectors with the same independent exponentials. B2 supplies the analytic recurrence and no-atom criterion. B3 supplies the derivative identity and monotonicity. Then A4 gives strict positivity over each covered interval; independently prove the origin and exterior estimates. This yields center maximality for the finite orders.
6. **B2, CDF semantics.** Use the exponential difference mixture in [the audit note](audit-v0.2-phase-a.md). Use Hermite–Genocchi separately to connect the divided differences to the density of the augmented simplex combination.
7. **M1 / B3, Jacobi and error identities.** `char`, node speed, reflection and endpoints precede the operator and explicit error formula. `dS` and Hermite–Genocchi precede `Hvalue` and `Hderivative`. Exponential convolution gives `Hcomp`. Preserve separate derivatives in the parameter and in the density argument.
8. **C1, analytic orders.** Independently audit and formalize the existing trace identities, characteristic-function bounds, dominated inversions and integration by parts for `n ≥ 20`. Combine with B1 and the direct low-order cases to get center maximality at all orders.
9. **D1, sharp Sobolev constants.** In parallel with the center question, M1 feeds the operator norm and polynomial reproduction. The Peano kernel provides the upper bound, while interpolation of the truncated power and mollification provide sharpness. Combine with the all-order center theorem and evaluate the exact center value to obtain the stated constants.

## How to resume

- [Issue #2](https://github.com/Ye-Chern/sharp-L1-interpolation/issues/2) tracks A1–A4. Start with the first unfinished dependency in the list above and check the declarations and build output.
- [Issue #1](https://github.com/Ye-Chern/sharp-L1-interpolation/issues/1) tracks independent audit of the analytic bridges and sharpness. Cite the equation label, proof hypotheses and effect on the main theorem for each correction.
- [Issue #3](https://github.com/Ye-Chern/sharp-L1-interpolation/issues/3) tracks [literature leads](literature.md). Match the exact interval, derivative orders and three norms before comparing constants.
- Read [Lean/README.md](../Lean/README.md) for the pinned build and cache procedure. Keep worker outputs on separate branches or worktrees and use small PRs for accepted research. Record independently reproduced evidence and unfinished assumptions here or in the linked note.

Acceptance layers are build and axiom audit → isolated mathematical lemma → finite data accepted by Lean → finite/all-order real-variable center theorem → optimal Sobolev constants. The Python replay has verified the arithmetic checks and their reported counts. The later analytic results are research-draft claims at this stage.
