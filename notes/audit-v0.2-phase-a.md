# v0.2 independent audit, initial certificate bridge

Scope: paper.tex equations `char`, `cdfrec`, `intervalLower`, `Hcomp`, and the origin test, with the Python checker at `7b6380e`. This note verifies the steps listed below and identifies the analytic inputs still needed.

## Roots and index order

For order n ≥ 1, set V_k(S,Y)=S^k U_k(Y/S) for S>0. The integer recurrence has coefficients 2Y and −S². Substituting t=T/S shows that V_(n+1)−2T V_n+T² V_(n−1) is S^(n+1) times the unnormalized polynomial in equation `char` at Y/S. Both that power and the leading normalization 2^(−n−1) are positive. With n+1 ordered, disjoint strict brackets, continuity gives n+1 distinct real roots. The degrees of U_(n+1), U_n, U_(n−1) are respectively n+1, n, n−1, with nonzero leading coefficient for the first term. The degree bound counts multiplicities, which also proves simplicity.

For descending root brackets (l_i/S, h_i/S), the core coefficients are ascending and lie between (T−h_i)/S and (T−l_i)/S. Include the exact extremes (T−S)/S and (T+S)/S to get the augmented arrays. The CDF is antitone in coefficients by the common-exponential coupling. An upper CDF at the lower coefficients gives a lower G, and a lower CDF at the upper coefficients gives an upper G, under the no-atom hypothesis below.

## CDF recurrence via two independent exponentials

Let Y be the sum of the interior terms, and let A and B be independent exponentials of means a and b, independent of Y. For the mixed-sign row use a=−l>0 and b=h>0. Normalizing independent rate-one exponentials by their almost surely positive sum relates the sign event for the exponential sum to the uniform-simplex sign event. For x≥0 the two tails are

```text
P(B−A > x) = ∫ exp(−(A+x)/b) dP_A = b/(a+b) exp(−x/b)
P(A−B > x) = ∫ exp(−(B+x)/a) dP_B = a/(a+b) exp(−x/a).
```

The continuous law of B−A is therefore the mixture of −A (weight a/(a+b)) and B (weight b/(a+b)). Adding the independent Y and evaluating the CDF at zero gives the exact recursion, where dropping the high endpoint retains −A. The proof allows equal and zero interior coefficients. This offers a shorter route for `cdfrec` if the exponential sum is the formal semantic object. Hermite–Genocchi remains needed elsewhere in the paper.

If the entire vector is nonpositive, the CDF at zero is 1, including the all-zero case. If all coefficients are nonnegative and one is positive, the CDF is 0 because the corresponding exponential is strictly positive almost surely. In general G=1−2F+P(X=0). Any nonzero coefficient makes the sum atomless by conditioning on the other exponentials, so the four output CDFs on the exact coefficients use G=1−2F. A zero singleton in the dynamic program still has CDF 1. Distinct roots give at most one zero among the core coefficients and the added endpoint coefficients are nonzero for these parameter rows. Strict separation of the certified brackets also makes the lower and upper arrays individually strictly ordered. A generic CDF lemma must allow all-zero input even though the four extracted CDFs here have no atom.

## Intervals, origin, and derivative normalization

Writing the stored integer margin as L, the certificate gives 2H'(t)≥L/S by monotonicity of each G in the parameter. The minus sign in front of the core G uses its upper bound at the right endpoint. The underlying monotonicity follows by evaluating each quadratic form on the same Gaussian vector for both parameter choices and using the positive parameter matrix.

At a=T/S=2^−24, L S>4M T² is equivalent to L/(2Sa)>2Ma. Hence H'(a)/a>2Ma. Evenness gives H'(0)=0 when H is differentiable at zero. Apply the mean value theorem to H' to find c∈(0,a) with H''(c)=H'(a)/a. The bound |H'''|≤M then gives H''(t)≥H''(c)−Ma>0 on [0,a]. This reproduces the sufficient arithmetic test without altering its constants.

As a check on `Hcomp`, with a=t+1 and b=t−1 the removal of one exponential of coefficient a applies 1+a∂_x to the density. Thus G_0=G_Q−2(a+b)ρ_Q(0)−2abρ'_Q(0), and the average of the single-endpoint signs is G_Q−(a+b)ρ_Q(0). Using a+b=2t and ab=−(1−t²) yields the stated coefficients in `Hgauss`. The argument requires the density regularity and boundary decay for the integrations by parts. The uniform Fourier domination in the origin neighborhood still needs a dedicated review before accepting that analytic input.

## Reproduction

The two existing Python checks passed locally. The finite checker traversed 2128 adjacent intervals and 17 origin neighborhoods. Its exact integer comparisons do not depend on the displayed decimal margins. These results leave the Jacobi characteristic identity, the density/error identities with their regularity, the full analytic estimate and Sobolev sharpness as separate review targets.
