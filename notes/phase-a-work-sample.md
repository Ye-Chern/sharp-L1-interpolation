Independent Phase A work sample. The source is paper.tex and certificates/check.py. Work only within this checkout. You may search Mathlib API, run commands and correct your artifacts. Use the supplied Lean project and cache; do not run lake update, change the manifest, write to shared dependencies, change project code, or contact GitHub. Same work sample for each candidate. Aim for 8 minutes from receipt, submit useful partial results if needed. No subdelegation. Report commands actually run, results and limitations. Complete four independent parts, with the Lean proof first:

1. Lean: create Lean/Trial.lean with proofs of BOTH statements below. You may add imports or helper lemmas. Statements must remain equivalent. No sorry, custom assumptions, native_decide, or new axioms. Use narrow imports and run lake env lean Trial.lean from Lean. Include #print axioms for both.
theorem convex_step (a b x y X Y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : x ≤ X) (hy : y ≤ Y) :
    a*x + b*y ≤ a*X + b*Y
theorem directed_step (v d : ℤ) (hd : 0 < d) :
    (v / d) * d ≤ v ∧ v ≤ ((v + d - 1) / d) * d

2. Decomposition: write Trial.md with a short proof plan from the scaled integer Chebyshev endpoint signs to a complete, ordered list of real roots and then the proper lower and upper coefficient arrays for the CDF. Give exact preconditions (including the sign of the scale), avoid assuming the desired eigenvalue theorem, and identify the interface for using the roots later.

3. Engineering: write trial_check.py, runnable from checkout root with stdlib Python. Check the unchanged CSV baseline, then create temporary mutated copies for a whole missing final order and an invalid in-range root sign bracket. Assert each rejection at the intended diagnostic. Run it. Do not alter tracked sources. No dependence on the output's floating-point numbers.

4. Audit (also in Trial.md): Starting from the CDF convention F=P(X<=0), decide which subarrays can be all zero and when G=1-2F is valid. Check signs and factors of two for the paper's intervalLower and origin test L*S>4*M*T^2. Either find a genuine problem or supply the missing local argument, with the exact hypotheses. Distinguish observations that affect the v0.2 data from general interface risks.

Allowed output files: Lean/Trial.lean, Trial.md, trial_check.py plus temporary scratch removed at end. Summarize the completed deliverables and any errors encountered.
