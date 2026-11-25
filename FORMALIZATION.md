# Lean formalization plan (proposed; no Lean code has been compiled)

Start with the finite theorem, not the whole Sobolev statement. Pin a Lean and mathlib version; keep definitions stable, use small independently checkable modules, and explicitly track gaps. The suggested file names below are architecture, not claims about existing mathlib APIs.

## Milestone A — algebraic and finite certificate layer

1. `Chebyshev.lean`: define `U`, prove the recurrence, degree, parity, and scaled integer evaluation identity. Prove the `n+1` disjoint sign-change brackets certify the complete root list, using continuity and polynomial degree. Define the Jacobi matrix and prove the characteristic polynomial identity independently.
2. `Certificate/CDF.lean`: implement the two directed integer recurrences on a sorted coefficient list. Prove arithmetic bounds by induction, for a real-valued recursion defined with nonnegative convex weights. At this stage no probability theory is necessary. Address zero coefficients explicitly.
3. `Certificate/Check.lean`: parse/generate structured data, check all signs and interval coverage. Prove a soundness theorem `check cert = true → ValidCertificate cert`. Check data by kernel-supported computation (`decide` on manageable chunks or proved reflection with a small checker); split by order if necessary. If using `native_decide`, document its trust assumptions. Do not treat a Python/C++ PASS as a theorem. Import data from the CSV through a deterministic converter or encode as Lean data; validate what the kernel actually reads.
4. `Certificate/Data.lean`: one certificate per n, 3 through 19. Prove all finite checks. `check_constants.py` gives similarly small arithmetic/integral certificates if needed.

## Milestone B — bridge finite data to analysis

5. `DividedDifference.lean`: Lagrange leading coefficient, divided differences of truncated powers, simplex-integral representation. Establish the CDF recurrence and monotonicity with respect to coefficients. One could define the B-spline CDF by recursion first and prove its equality to a simplex integral later.
6. `Error.lean`: define E_n via explicit roots or the difference-operator kernel, prove the identities for H and H'. Establish evenness, exterior monotonicity, and the origin derivative bound. Then combine with the verified finite certificates to derive center maximality for n < 20. This milestone is separate from proving the best-constant theorem.

## Milestone C — uniform analytic estimate

7. `QuadraticForm.lean`: exponential variables, diagonalization, characteristic function, Gamma scaling, sign expectations, derivative formulas. Use the same symbols and normalizations as Section 5 of the paper. Avoid introducing an unjustified probability axiom.
8. `FourierBounds.lean`: trace identities, weighted Jensen amplitude bound, single-sided phase estimate, Fourier inversion and integration by parts. Prove the explicit rational bounds and the theorem for n >= 20. Audit domination and endpoint regularity.
9. `CenterMaximum.lean`: combine all orders. The exact center formula can be handled at this stage.

## Milestone D — sharp Sobolev inequality

10. `MovingNodes.lean`: eigenvalue monotonicity and simplicity, endpoint interpolation, cofactor identity for node speed.
11. `SharpInterpolation.lean`: difference operator norm, Hermite–Genocchi, integral Taylor remainder and Peano kernel bound, sharpness via interpolation of the truncated power and mollification. A first intermediate theorem for smooth functions is useful, followed by density or Sobolev extension to the stated space.

## Audit rules and publication status

- Track `sorry`/axioms explicitly. Final target: no unacknowledged holes; check `#print axioms` on principal theorems. Avoid custom axioms for the intended analytic lemmas.
- Report which theorem is proved (finite certificate validity, real-variable center maximum, smooth-function inequality, or full Sobolev sharpness). These are not interchangeable.
- Prefer conventional mathlib abstractions once discovered; names above are placeholders. Keep the prose proof versioned alongside the formal one, and record any changes in statements and proof dependencies.
- The project is an opportunity to learn Lean: the certificate arithmetic and Chebyshev recurrence are suitable first exercises, before probability and functional analysis.
