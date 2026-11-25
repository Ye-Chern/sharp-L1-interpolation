# Sharp higher-order L1 interpolation on an interval

**Research draft v0.2 — 2026-11-25.** This is a proposed computer-assisted proof, not yet independently peer-reviewed or Lean-verified. Priority in the literature and author attribution remain to be confirmed. The PDF is in Chinese; the certificate scripts are in English.

For positive integer n, the goal is to find the lexicographically best pair (A_n, B_n) in

```
||F^(n)||_1 <= A_n ||F||_1 + B_n ||F^(n+1)||_1,  F in W^(n+1,1)([-1,1]).
```

The draft proves the reduction to a single-variable maximum E_n, a uniform analytic estimate for n >= 20, and a finite interval certificate for n = 3,...,19. The cases n=1,2 are elementary; n=3 also admits an elementary calculation. The remaining open objectives of this project are a uniform purely analytic proof, independent proof review, literature verification, and Lean formalization. No claim of novelty or publication priority is made.

## Contents

- `paper.pdf`, `paper.tex`: self-contained article. Build with XeLaTeX twice (CTeX + Fandol fonts).
- `certificates/brackets.csv`: exact integer endpoint and root-bracket data, denominator 2^55.
- `certificates/check.py`: independent verifier using Python arbitrary-precision integers, not the C++ generator.
- `certificates/check_constants.py`: rational checks of the explicit analytic constants.
- `certificates/verify.cpp`: fast certificate generator, using floating point only to propose root brackets; not trusted by the independent verifier.
- `certificates/check.log`, `constants.log`, `generation.log`: actual run output.
- `FORMALIZATION.md`: suggested Lean architecture and trusted-base audit.

## Reproduce

Run from the repository root:

```sh
python certificates/check.py
python certificates/check_constants.py
```

Expected: `PASS n=3..19: 2128 intervals, 17 origin neighborhoods`, and `PASS: all numerical bounds in Section 6`.

Regenerate the certificate if desired (GCC/Clang with `__int128` support):

```sh
g++ -O3 -std=c++17 certificates/verify.cpp -o verify
./verify 3 19 certificates/brackets.csv
python certificates/check.py
```

Certificate rows have no header: `n,T,l1,h1,...,l_(n+1),h_(n+1)`. All values after n are signed integers in units of 2^-55. The root brackets are in descending root order. The verifier checks the exact polynomial sign changes, disjointness, root count via degree, directed CDF recursion, all consecutive parameter intervals, origin neighborhoods, and exact coverage. Its logical bridge to the real-variable theorem is Section 7 of the paper. The constants script uses a decreasing-function Riemann upper sum for two simple integrals; the article also gives an elementary antiderivative recurrence, so this script is optional for the analytic proof.

A PASS message is not a Lean theorem. In particular the probability, Fourier, Sobolev and interpolation lemmas in the paper require independent proof review and eventual formalization.
