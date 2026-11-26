# Supplementary Structural Observations and Open Problems

> **Scope and verification notice.** This note records supplementary mathematical observations surrounding the moving-node operator $T_n$, the Jacobi matrix family $J_n(x)$, and the error profile $E_n(t)$ from [`paper.tex`](../paper.tex). **None of the results in this note are required for the proof of Theorem 1 in `paper.tex`, and none of them are formalized in `Lean/SharpL1/`.** Each section explicitly states its proof status.

---

## 1. Cross-Order Interlacing and Generalized Gauss Quadrature

*Proof status: Expository analytic derivation (not Lean-verified).*

Let $u_{n,0}(x) < u_{n,1}(x) < \dots < u_{n,n}(x)$ denote the eigenvalues of the $(n+1)\times(n+1)$ symmetric tridiagonal Jacobi matrix $J_n(x)$, whose monic characteristic polynomial is
$$
p_x(y) = 2^{-n-1}\bigl(U_{n+1}(y) - 2x U_n(y) + x^2 U_{n-1}(y)\bigr).
$$

### 1.1 Cross-order interlacing

For $|x| < 1$, set $y = \cos\theta$ ($\theta \in (0, \pi)$) and let $\phi_x(\theta) := \arg\frac{e^{i\theta} - x}{1 - x e^{i\theta}}$ be the Blaschke phase, which increases strictly from $0$ to $\pi$ on $[0, \pi]$. Expressing $U_m(\cos\theta) = \sin((m+1)\theta)/\sin\theta$ shows that the angles $\theta_{n,j}(x) \in (0, \pi)$ corresponding to $u_{n,j}(x) = \cos\theta_{n,j}(x)$ (listed in decreasing order of $\theta$) solve the phase equation
$$
(n + 1)\theta + \phi_x(\theta) = k\pi \qquad (k = 1, \dots, n + 1).
$$
Increasing $n$ by $1$ adds $\theta \in (0, \pi)$ to the left-hand side. Since the left-hand side is strictly increasing in $\theta$, the solutions for orders $n$ and $n+1$ strictly interlace:
$$
u_{n+1,j}(x) < u_{n,j}(x) < u_{n+1,j+1}(x) \qquad (j = 0, \dots, n).
$$

### 1.2 Generalized Gauss quadrature and walk counting

Recall that for $|x| < 1$, the first component $v_{j,0}$ of a unit eigenvector $v_j$ of $J_n(x)$ satisfies $u_j'(x) = v_{j,0}^2$ (by centrosymmetry and Hellmann--Feynman perturbation). Thus the discrete measure $\mu_{n,x} := \sum_{j=0}^n u_j'(x)\,\delta_{u_j(x)}$ is precisely the spectral measure of $J_n(x)$ at the first basis vector $e_0$, so its $m$-th moment is $\langle e_0, J_n(x)^m e_0 \rangle$.

Now embed $J_n(x)$ into the semi-infinite tridiagonal Jacobi operator $J_\infty(x)$ on $\ell^2(\mathbb{N})$ whose $(0,0)$-entry is $x/2$, whose remaining diagonal entries are all $0$, and whose sub- and super-diagonal entries are all $1/2$. Comparing $J_n(x)$ with $J_\infty(x)$ reveals two differences at the far end of the chain:
1. $J_n(x)$ has a nonzero far-endpoint diagonal entry $(J_n(x))_{n,n} = x/2$ (a weighted self-loop at vertex $n$);
2. $J_n(x)$ is truncated beyond index $n$ (no edge from $n$ to $n+1$).

Consider a weighted closed walk of length $m$ on $\mathbb{N}$ starting and ending at index $0$:
- A walk of length $m = 2n$ **can** reach vertex $n$ and return to $0$ (via the unique path $0 \to 1 \to \dots \to n \to n-1 \to \dots \to 0$).
- However, to use the perturbed far-endpoint diagonal entry $(J_n(x))_{n,n} = x/2$, a closed walk must take $n$ steps from $0$ to $n$, traverse the self-loop at $n$ ($1$ step), and take $n$ steps back to $0$, requiring **at least $2n + 1$ steps**.
- Stepping past the truncation boundary from $n$ to $n+1$ and returning to $0$ requires **at least $2n + 2$ steps**.

Consequently, for every $0 \le m \le 2n$, every closed walk of length $m$ from $0$ to $0$ has identical weight in $J_n(x)$ and in $J_\infty(x)$, so
$$
\langle e_0, J_n(x)^m e_0 \rangle = \langle e_0, J_\infty(x)^m e_0 \rangle \qquad (0 \le m \le 2n).
$$
Computing the Stieltjes transform of the rank-one perturbation $J_\infty(x)$ of the free Chebyshev Jacobi operator $J_\infty(0)$ yields the absolutely continuous spectral measure $\frac{2\sqrt{1 - y^2}}{\pi(1 - 2xy + x^2)}\,dy$ on $[-1,1]$ (for $|x| < 1$), giving the **generalized Gauss quadrature rule**:
$$
\sum_{j=0}^{n} u_j'(x)\,P\bigl(u_j(x)\bigr)
= \int_{-1}^{1} P(y)\,\frac{2\sqrt{1 - y^2}}{\pi(1 - 2xy + x^2)}\,dy
\qquad (\deg P \le 2n).
$$
At $x = 0$, the far-endpoint self-loop weight $x/2$ vanishes, so the first discrepancy occurs only at length $2n + 2$ (stepping to vertex $n+1$ and back). Exactness therefore increases by one degree to $\deg P \le 2n + 1$, recovering classical Chebyshev--Gauss quadrature.

---

## 2. Asymptotics and Extended Numerical Table for $B_n = E_n(0)$

*Proof status: The cancellation-free integral representation and strict monotonicity $B_{n+1} > B_n$ are proved rigorously in prose in Corollary 3 of [`paper.tex`](../paper.tex) (not separately formalized in Lean~4; the closed-form cosine sum `centerBestConstant` is formalized in `Lean/SharpL1/Analysis/MovingOperator.lean`). The asymptotic expansion and extended numerical table below are expository complements (not Lean-verified).*

By Corollary 3 of [`paper.tex`](../paper.tex), the exact center constant satisfies the cancellation-free integral representation
$$
1 - B_n
= \frac{n + 2}{\pi(n + 1)}\int_0^1 \frac{s^{-1/2}(1 - s)^{n+1}}{1 - (-s)^{n+2}}\,ds
\qquad (n \ge 1),
$$
from which strict monotonicity $\frac12 = B_1 < B_2 < B_3 < \dots < 1$ follows directly. Unlike the alternating cosine sum (whose $2^{n+1}$ prefactor causes catastrophic floating-point cancellation at large $n$), the integral above has a strictly positive integrand on $(0, 1)$.

Because $s(1 - s) \le \frac14$ on $[0, 1]$, replacing the denominator $1 - (-s)^{n+2}$ by $1$ commits an error of order $O(4^{-n})$—the $t = 0$ specialization of the $4^{-n}$ reflection tail in the vertical-chord analysis of `paper.tex`. Evaluating the resulting Beta integral $B(\frac12, n+2)$ gives the asymptotic expansion
$$
1 - B_n
= \frac{4^{n+2}}{\pi(n + 1)\binom{2n+4}{n+2}} + O(4^{-n})
= \frac{1}{\sqrt{\pi n}}\left(1 + \frac{1}{8n} + O(n^{-2})\right).
$$

### Numerical table of $B_n$

The table below lists $B_n = E_n(0)$ on the reference interval $[-1, 1]$ together with the corresponding rescaled second constant $B_n([0,1]) = B_n / 2$ on $[0, 1]$ (all values are unconditionally proved to be the sharp second constants by Theorem 1 of `paper.tex`):

| $n$ | Exact $B_n$ on $[-1, 1]$ | Numerical $B_n$ on $[-1, 1]$ | Numerical $B_n / 2$ on $[0, 1]$ |
|---:|:---|---:|---:|
| $1$ | $1/2$ | $0.500000000$ | $0.250000000$ |
| $2$ | $(2\sqrt{2} - 1)/3$ | $0.609475708$ | $0.304737854$ |
| $3$ | $3\sqrt{5}/4 - 1$ | $0.677050983$ | $0.338525492$ |
| $4$ | $(9\sqrt{3} - 12)/5$ | $0.717691454$ | $0.358845727$ |
| $5$ | — | $0.746758277$ | $0.373379139$ |
| $10$ | — | $0.820466444$ | $0.410233222$ |
| $20$ | — | $0.873268528$ | $0.436634264$ |
| $100$ | — | $0.943514627$ | $0.471757314$ |

---

## 3. Local Concavity at $t = 0$ and the Gaussian Scaling Profile

*Proof status: Expository / partially heuristic (not Lean-verified). See the explicit caveat below regarding convergence of derivatives.*

Set $H_n(t) := 1 - E_n(t)$. A Poisson-summation representation analogous to Section 2 yields $E_n''(0) < 0$ (equivalently $H_n''(0) > 0$) for every $n \ge 1$, confirming that the origin $t = 0$ is always a strict local maximum with negative curvature.

In the diffusive window $t = r / \sqrt{n}$ ($r \in \R$ fixed as $n \to \infty$), the normalized complex Gaussian quadratic form $Q_{r/\sqrt{n}} / \sqrt{n}$ converges in distribution to $N(r, \frac12)$. This motivates the universal Gaussian scaling profile on compact subsets of $r \in \R$:
$$
\begin{aligned}
\sqrt{n}\,H_n(r/\sqrt{n}) &\longrightarrow r\operatorname{erf}(r) + \pi^{-1/2}e^{-r^2} = \mathbb{E}|r - Z|, \\
H_n'(r/\sqrt{n}) &\longrightarrow \operatorname{erf}(r), \\
n^{-1/2}H_n''(r/\sqrt{n}) &\longrightarrow 2\pi^{-1/2}e^{-r^2},
\end{aligned}
$$
where $Z \sim N(0, \frac12)$.

> **Proof-status caveat.** While the weak central limit theorem $Q_{r/\sqrt{n}} / \sqrt{n} \Rightarrow N(r, \frac12)$ (together with uniform integrability) accounts for the pointwise limit of $\sqrt{n}\,H_n(r/\sqrt{n})$, **local uniform convergence of the derivatives $H_n'(r/\sqrt{n})$ and $n^{-1/2}H_n''(r/\sqrt{n})$ does not follow from the standard central limit theorem alone**. Proving those derivative limits rigorously requires local-limit or characteristic-function / Fourier-inversion estimates (for instance via the exact rational characteristic function $\Phi_{n,t}$ derived in `paper.tex`). Because none of these scaling limits are needed for Theorem 1, we record them here as an unformalized structural observation rather than a proved theorem.

---

## 4. Open Problems

Several natural questions surrounding $E_n(t)$, $B_n$, and finite-interval Landau--Kolmogorov inequalities remain open (note that strict monotonicity $B_{n+1} > B_n$ for all $n \ge 1$, listed as open in earlier drafts, is now proved unconditionally in Corollary 3 of [`paper.tex`](../paper.tex)):

1. **Global strict concavity of $E_n$.** Is $E_n''(t) < 0$ on the entire open interval $(-1, 1)$ for every $n \ge 1$? Currently we only have local concavity at $t = 0$ and the diffusive-scale Gaussian heuristic above.
2. **Global positivity of $\Delta_n(t)$.** The vertical-chord quantity $\Delta_n(t) = 4t\rho_t(0) - 2(1 - t^2)\rho_t'(0)$ (equivalently $\rho_t'(0)/\rho_t(0) < \frac{2t}{1-t^2}$ for the density $\rho_t$ of $Q_t$, or $-f_t'(t)/f_t(t) < \frac{2(n+1)t}{1-t^2}$ for the density $f_t$ of the uniform simplex convex combination of the $n+3$ extended nodes $\mathbf{z}_t$) is proved strictly positive for all $n \ge 3$ and $t \in (0, 1/2]$ in `paper.tex` and `Lean/SharpL1/`. Does $\Delta_n(t) > 0$ also hold on the exterior $t \in (1/2, 1)$ and for $n = 1, 2$?
3. **Full optimal trade-off curve and Stechkin problem for $N > A_n$.** Theorem 1 and its Stechkin corollary determine the sharp constant $B_n = \mathcal{E}_{A_n}$ at the minimal admissible first constant $A = A_n$. Determining the exact trade-off curve $B_n(A)$ (and $\mathcal{E}_N$) for all $A > A_n$ on a finite interval in the all-$L^1$ setting remains open.
4. **Burenkov's $L^2$ open problem.** In Burenkov (1980), alongside the all-$L^1$ inequality (eq. (24)) whose sharp second constant is resolved by our $n = 1$ theorem, the analogous all-$L^2$ inequality on $[0, 1]$ (eq. (25)) was also left open and is not addressed by the present work.
