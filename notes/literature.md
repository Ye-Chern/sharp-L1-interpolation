# Literature Review and Mathematical-Equivalence Audit

**Status:** Final primary-source-verified literature review for PR #8 (branch `docs/english-paper`).
**Target problem:** On a compact interval $I = [-1, 1]$ (and by affine scaling on any $[a, b]$ of length $L = b - a > 0$), determine the lexicographically sharp pair of constants $(A_n, B_n)$ in the additive all-$L^1$ Landau–Kolmogorov inequality
$$
\|f^{(n)}\|_{L^1(I)} \le A_n \|f\|_{L^1(I)} + B_n \|f^{(n+1)}\|_{L^1(I)}, \qquad f \in W^{n+1,1}(I),
$$
where $A_n = 2^n n!$ (equivalently $4^n n! L^{-n}$ on $[a,b]$) is minimal over all valid additive inequalities and
$$
B_n = E_n(0) = 1 - \frac{2^n}{n+1} + \frac{2^{n+1}}{n+1}\sum_{k=1}^{\lfloor(n+1)/2\rfloor} (-1)^{k-1}\cos^{n+1}\frac{k\pi}{n+2}
$$
(equivalently $\frac{L}{2}B_n$ on $[a,b]$) is minimal once $A = A_n$ is fixed.

**Normalization table (critical when comparing with Russian/Ukrainian sources using $[0,1]$ and highest order $n_{\mathrm{Bur}} = n + 1$):**

| Interval | $n = 1$ ($n_{\mathrm{Bur}} = 2$) first constant | $n = 1$ second constant | General $n$ first constant | General $n$ second constant |
| --- | ---: | ---: | --- | --- |
| $[0, 1]$ | $4$ | $1/4$ | $4^n n!$ | $\frac{1}{2} B_n$ |
| $[-1, 1]$ | $2$ | $1/2$ | $2^n n!$ | $B_n$ |

---

## 1. Executive Verdict and Contribution Boundary

To the best of our knowledge, based on direct inspection of the primary sources listed in Sections 2–4 and the citation-chain checks summarized in Section 5, **no prior work determines the exact all-$L^1$ lexicographically optimal second constant $B_n$** (even for $n = 1$, where $B_1([0,1]) = 1/4$ resolves the $L^1$ half of Burenkov's 1980 explicit open problem).

### Clear Separation of Known vs. New Results

- **Established prior results (must be credited, never claimed as new):**
  1. **First optimal constant $A_n([0,1]) = 4^n n!$** for all-$L^1$ adjacent orders ($p = q = r = 1$): proved by Burenkov (1980, Theorem, p. 23, and §4°, p. 26) via the monic second-kind Chebyshev polynomial $Q_n = 2^{-n} U_n$; extended to general $(p, q, r)$ in Burenkov (1986, Theorem 1, p. 40).
  2. **General equivalence of the minimal first constant with the polynomial Markov–Nikolskii constant and finiteness of the second constant $B^*(A^*)$:** established in full generality by Babenko–Kofanov–Pichugov (1997; 1998), Kofanov (2002, §4.3, Theorem 4.3.2), and the monograph Babenko–Korneichuk–Kofanov–Pichugov (2003, Theorem 4.6.2).
  3. **General non-sharp bounds on $B^*(n+1, 1)$ on $[0,1]$:** $1/12 \le B(n+1, 1) \le 1/2$ and lower asymptotic bound $1/4$ in Burenkov (1980, p. 29 note added in proof; 1986, Theorem 2(4)–(5)).
  4. **Best $L^1$ polynomial approximation of $W_1^{n+1}([-1,1])$ and the Chebyshev perfect spline $s_{n,n+1}$:** Boyanov (1975, §3) for $n = r - 1$ and Kofanov (1983/1984, Theorems 3 and 5) for all $n \ge r - 1$, yielding $E_n(W_1^{n+1})_1 = \|s_{n,n+1}\|_\infty = |s_{n,n+1}(0)|$.
  5. **Classical tools:** Bernstein/Markov $L^1$ sign-orthogonality of $U_n$, Curry–Schoenberg / Hermite–Genocchi divided-difference identities, Peano kernels, and Stechkin's lower-bound principle connecting additive derivative inequalities to best bounded-operator approximation (Stechkin 1967; Skorokhodov 2019, Proposition 2).

- **Our contributions (cautious "to the best of our knowledge" framing for originality):**
  1. The **moving-node divided-difference operator $T_n$** realized globally via the eigenvalues of the symmetric tridiagonal Jacobi matrix $J_n(x)$, which disintegrates Burenkov's rank-one functional while preserving $\|T_n\|_{L^1\to L^1} = A_n$.
  2. Exact reduction of the sharp second constant $B_n$ to $\max_{t \in [-1,1]} E_n(t)$ for the explicit moving-node error profile $E_n(t)$, together with the sign-aligned spline sharpness construction.
  3. Unconditional proof for all $n \ge 1$ that $E_n$ is strictly decreasing on $[0, 1]$, attaining its **unique global maximum at the center $t = 0$**, via the complex-analytic vertical-chord contour integral ($n \ge 4$), elementary algebra ($n = 1, 2$), and a five-subinterval rigorous bound ($n = 3$).
  4. Explicit all-$n$ formula for $B_n = E_n(0)$ (together with the exact approximation-theoretic identity $B_n = 1 - A_n E_n(W_1^{n+1})_1$ linking the center value to Boyanov 1975 / Kofanov 1984), solving—to the best of our knowledge—the $L^1$ part of Burenkov's 1980 open problem (improving eq. (24) on $[0,1]$ from $1/2$ to the sharp $1/4$, while the $L^2$ eq. (25) remains open).
  5. Exact $C^{n+1}$ equality characterization (scalar multiples of rescaled $U_n$), the direct Stechkin-problem corollary $\mathcal{E}_{A_n}(D^n; \mathcal{W}_n) = B_n$ attained by $T_n$, and a complete Lean 4 / Mathlib formalization of the main theorem.

---

## 2. Primary-Source Deep Audits and Mathematical-Equivalence Verdicts

All four critical primary papers below were inspected directly page-by-page from the original PDFs/scans.

### 2.1 Burenkov (1980) — Exact Open Problem and Note Added in Proof

- **Source:** V. I. Burenkov, *Exact constants in inequalities for norms of intermediate derivatives on a finite interval* (Russian: *О точных постоянных в неравенствах для норм промежуточных производных на конечном интервале*), Trudy Mat. Inst. Steklov. **156** (1980), 22–29. URL: `https://www.mathnet.ru/eng/tm2408`. (Inspected directly from original Russian scan.)
- **Notation:** Interval $(0,1)$, derivative orders $(0, n_{\mathrm{Bur}}-1, n_{\mathrm{Bur}})$ with $n_{\mathrm{Bur}} \ge 2$, all in $L_p(0,1)$ ($1 \le p \le \infty$). Thus $n_{\mathrm{Bur}} = n + 1$ in our indexing.
- **Verified contents:**
  - **Theorem (p. 23, eq. (6)):** $\|f^{(n_{\mathrm{Bur}}-1)}\|_{L_p(0,1)} \le \frac{(n_{\mathrm{Bur}}-1)!}{\|Q_{n_{\mathrm{Bur}}-1}\|_{L_p(0,1)}}\|f\|_{L_p(0,1)} + \|f^{(n_{\mathrm{Bur}})}\|_{L_p(0,1)}$, with sharp first constant attained by the monic $L_p$-minimal polynomial $Q_{n_{\mathrm{Bur}}-1}$.
  - **§4° (p. 26):** Evaluates $p = 1$ using the monic second-kind Chebyshev polynomial $Q_m(x) = 2^{-m} S_m(2x-1)$ ($S_m = 2^{-m} U_m$, $\|Q_m\|_{L_1(0,1)} = 2^{-2m}$), yielding $A_n([0,1]) = 4^n n!$.
  - **§10° (pp. 26–27), eqs. (24)–(25):** For $n_{\mathrm{Bur}} = 2$ (our $n = 1$) and $p = 1, 2$, evaluates $B(\omega)$ explicitly from eq. (14) using $\omega(\xi)$ from eq. (23):
    $$
    \|f'\|_{L_1(0,1)} \le 4\|f\|_{L_1(0,1)} + \frac{1}{2}\|f''\|_{L_1(0,1)} \qquad \text{(eq. 24)},
    $$
    $$
    \|f'\|_{L_2(0,1)} \le 2\sqrt{3}\|f\|_{L_2(0,1)} + \sqrt{\frac{6}{35}}\|f''\|_{L_2(0,1)} \qquad \text{(eq. 25; note a print typo `L_1` for `L_2` on the first RHS norm in the scan)}.
    $$
    Immediately below eq. (25) on p. 27, Burenkov explicitly states:
    > «Вопрос о точности постоянных при норме $f''$ в неравенствах (24) и (25) остается открытым.»
    > (*"The question of the sharpness of the constants in front of the norm of $f''$ in inequalities (24) and (25) remains open."*)
    He contrasts this with $p = \infty$ (eq. (5), Landau's inequality), where $1/2$ is sharp, and does **not** conjecture the value $1/4$ for eq. (24).
  - **Примечание при корректуре (Note added in proof, p. 29 — verified at 300 dpi from the original scan):**
    > *Примечание при корректуре.* Если $B(n, p)$ — точная постоянная при $\|f^{(n)}\|_{L_p(0,1)}$ в (6), то $1/12 \le B(n, p) \le 1/2$ (в тексте $B(n, p) \le 1$), $7/16 \le B(n, \infty) \le 1/2$, $\lim_{n \to \infty} B(n, p) \ge 1/4$, $\lim_{n \to \infty} B(n, \infty) = 1/2$.
    - **Typography & mathematical precision:** The scan prints plain `lim` (without an underline bar) in $\lim_{n\to\infty} B(n,p) \ge 1/4$—clearly intending $\varliminf_{n\to\infty}$, as subsequently formalized with $\varliminf$ in Burenkov (1986, Theorem 2(5), eq. (17), p. 41).
    - **Comparison with our result:** Our theorem determines $B(n+1, 1) = \frac{1}{2} B_n$ exactly for every $n \ge 1$. For $n = 1$ ($n_{\mathrm{Bur}} = 2$), $B(2, 1) = 1/4$, strictly improving eq. (24) from $1/2$ to the sharp $1/4$. For all $n \ge 1$, $\frac{1}{2} B_n$ lies inside $[1/4, 1/2) \subset [1/12, 1/2]$, and (as recorded in `notes/structural-observations.md`, outside the Lean-verified scope) approaches the upper endpoint $1/2$ at rate $\frac{1}{2} - \frac{1}{2\sqrt{\pi n}} + o(n^{-1/2})$ as $n \to \infty$.

### 2.2 Burenkov (1986) — Mathematical Comparison of Theorem 2(1) Operator vs. $T_n$

- **Source:** V. I. Burenkov, *Exact constants in inequalities for norms of intermediate derivatives on a finite interval. II* (Russian: *О точных постоянных в неравенствах для норм промежуточных производных на конечном интервале. II*), Trudy Mat. Inst. Steklov. **173** (1986), 38–49. URL: `https://www.mathnet.ru/eng/tm2147`. (Inspected directly from original Russian scan.)
- **Verified contents:**
  - Generalizes the lexicographic problem $A^*_{n, n-1}(p, q, r)$ and $B^*_{n, n-1}(p, q, r)$ to distinct exponents $1 \le p, q, r \le \infty$ on $(0, 1)$ (again $n_{\mathrm{Bur}} = n + 1$).
  - **Theorem 1 (p. 40, eq. (13)):** $A^*_{n_{\mathrm{Bur}}, n_{\mathrm{Bur}}-1}(p, q, r) = (n_{\mathrm{Bur}}-1)! / \|Q_{n_{\mathrm{Bur}}-1; p}\|_{L_p(0,1)}$.
  - **Theorem 2 (p. 41):**
    - Part 1: For $p < \infty$, $B^*_{n, n-1} \le \|\mathcal{B}\|_{L_r(0,1) \to L_q(0,1)}$, where $(\mathcal{B}\varphi)(x) = \int_0^1 \beta(x, \xi)\varphi(\xi)\,d\xi$ with $\beta(x,\xi) = \gamma(\xi)$ for $0 \le \xi \le x$ and $\gamma(\xi) - 1$ for $x < \xi \le 1$, where $\gamma(\xi) = \int_0^\xi \omega(\eta)\,d\eta$.
    - Parts 2–6 (eqs. (14)–(18)): Global bounds $B^*_{n,n-1} \in [0, 1]$ ($n \ge 1$), $\inf B^*_{n,n-1} > 0.03$ ($n \ge 2$), $\frac{1}{2}((1+q)^{-1/q} - 1/n) \le B^*_{n,n-1} \le 2^{(1/r - 1/q)_+ - 1}$, $\frac{1}{4} \le \inf_{p,q,r}\varliminf_{n\to\infty} B^*_{n,n-1} \le \frac{1}{2}$, and $\lim_{n\to\infty} B^*_{n,n-1}(p,\infty,\infty) = 1/2$.
    - Part 7 (eq. (19)): Exact value $B^*_{n, n-1}(p, \infty, 1) = 1$ (and Theorem 3, p. 45, solves the three-number Kolmogorov problem for $q = \infty, r = 1$; Theorem 4, pp. 47–48, solves the corresponding Stechkin problem for $L_p \to L_\infty$ on $W_1^{n+1}$).
- **RIGOROUS MATHEMATICAL VERDICT (Burenkov 1986 Thm 2(1) vs. our $T_n$):**
  - **Genuinely distinct constructions; neither is a special case of the other.**
  - In Burenkov's decomposition $f^{(n-1)} = A_\omega f + B_\omega f^{(n)}$ (p. 42, eqs. (24)–(26), where $\mathcal{B} = B_\omega$), the approximating operator $A_\omega$ (also denoted $T_n$ in Theorem 4, p. 48, eq. (41)) is a **rank-one, constant-valued functional** independent of $x$: on $[-1, 1]$ at $p = 1$ (with our index $n$),
    $$
    (A_\omega F)(x) \equiv 2^{n-1} n! \int_{-1}^{1} s_n(y) F(y)\,dy.
    $$
    Consequently, its remainder kernel $\Lambda(x, \xi) = \mathbf{1}_{\{x > \xi\}} - (1 - \gamma(\xi))$ approximates the Heaviside step $\mathbf{1}_{\{x > \xi\}}$ by a function independent of $x$.
  - **Exact relation between the two operators at $p = 1$:** Integrating our moving-node operator $T_n F(x) = 2^n n! \sum_{j=0}^n \varepsilon_j u_j'(x) F(u_j(x))$ over $x \in [-1,1]$ and substituting $y = u_j(x)$ on each subinterval $[r_j, r_{j+1}]$ gives
    $$
    \frac{1}{2}\int_{-1}^{1} (T_n F)(x)\,dx = 2^{n-1} n! \sum_{j=0}^{n} \varepsilon_j \int_{r_j}^{r_{j+1}} F(y)\,dy = 2^{n-1} n! \int_{-1}^{1} s_n(y) F(y)\,dy = (A_\omega F)(x).
    $$
    Thus Burenkov's $A_\omega$ is the **spatial average** (rank-one collapse) of our infinite-rank operator $T_n$.
  - **Why Burenkov's operator cannot give our sharp constant:** On p. 43, Burenkov explicitly computes $\|\mathcal{B}\|_{L_1(0,1)\to L_1(0,1)} = \max_{0 \le \xi \le 1} \int_0^1 |\Lambda(x, \xi)|\,dx = \frac{1}{2}$ for every order $n$ (equivalently $1$ on $[-1, 1]$). In fact, for **any** constant-valued (rank-one) operator $S$ exact on $\pi_n$, $S h_0(x) \equiv c \in [0, 1]$ forces $\|D^n h_0 - S h_0\|_{L^1([-1,1])} = |c| + |1 - c| = 1$ ($1/2$ on $[0, 1]$). Disintegrating $A_\omega$ into the $x$-dependent moving-node divided difference $T_n F(x) = n! F[u_0(x), \dots, u_n(x)]$ is essential to break below $1$ (on $[-1,1]$, i.e. $1/2$ on $[0,1]$) and reach the sharp constant $B_n < 1$ while keeping $\|T_n\|_{L^1\to L^1} = A_n$.

### 2.3 Kofanov (1983/1984) — Formula-by-Formula Equivalence Check vs. $E_n(t)$ and $B_n$

- **Source:** V. A. Kofanov, *Approximation in the mean of classes of differentiable functions by algebraic polynomials*, Izv. Akad. Nauk SSSR Ser. Mat. **47** (1983), no. 5; English transl. in Math. USSR Izv. **23** (1984), no. 2, 353–365. DOI: `10.1070/im1984v023n02abeh001774`. (Inspected directly page-by-page from the English translation PDF.)
- **Setting and verified formulas:** On $[-1,1]$ with $L = L^1[-1,1]$ and $M = L^\infty[-1,1]$, Kofanov determines the best $L^1$ polynomial approximation error $E_n(W_L^r)_L := \sup_{\|f^{(r)}\|_1 \le 1} \inf_{P \in \pi_n} \|f - P\|_1$ for all integers $r \ge 2$ and $n \ge r - 1$.
  - Let $x_i = -\cos\frac{i\pi}{n+2}$ ($i = 1, \dots, n+1$) be the sign-change nodes of $s_n(t) = \operatorname{sgn}\sin((n+2)\arccos t) = \operatorname{sgn} U_{n+1}(t) \perp \pi_n$, and let $s_{n,r}$ be its $r$-th integral (p. 353):
    $$
    s_{n,r}(x) = \pm \frac{1}{r!}\left[(x+1)^r + 2\sum_{i=1}^{n+1} (-1)^i (x - x_i)_+^r\right].
    $$
  - Let $e_{n,r}(x) := \frac{1}{(r-1)!} E_n((x - \cdot)_+^{r-1})_L$. By duality (eq. (17), p. 357), $E_n(W_L^r)_L = \sup_{x \in [-1,1]} e_{n,r}(x)$.
  - **Theorem 3 (p. 356, eq. (13)) & Theorem 5 (p. 363, eq. (47)):** $E_n(W_L^r)_L = \|s_{n,r}\|_M$. In the boundary case **$n = r - 1$** (where $r = n + 1$, matching our Sobolev class $W^{n+1,1}$ and polynomial kernel $\pi_n$), Kofanov explicitly notes (p. 357) that $e_{n, n+1}(x) = |s_{n, n+1}(x)|$ for all $x \in [-1, 1]$ was already obtained earlier by **B. D. Boyanov** (*Mat. Zametki* **17** (1975), 511–524, §3); here $n + 2 - r = 1$, $s_{n,n+1}$ has a single interior extremum $x_{1, n+1} = 0$, and $G_{n, n+1} = \varnothing$.
  - **Theorem 6 (p. 364, eq. (50)):** Sharp Jackson-type inequality $E_n(f)_L \le \|s_{n,r}\|_M E_{n-r}(f^{(r)})_L$ for $n > r - 1$ (does not cover $n = r - 1$ and does not involve derivative norms on the LHS).

- **RIGOROUS FORMULA-BY-FORMULA MATHEMATICAL VERDICT (Kofanov 1984 vs. our $E_n(t)$ and $B_n$):**
  1. **Exact algebraic identity at the center $t = 0$ (genuine hidden connection!):**
     At $r = n + 1$ and $x = 0$, since $-x_i = \cos\frac{i\pi}{n+2} > 0$ precisely for $i = 1, \dots, \lfloor(n+1)/2\rfloor$,
     $$
     |s_{n, n+1}(0)| = \frac{1}{(n+1)!}\left[1 - 2\sum_{k=1}^{\lfloor(n+1)/2\rfloor} (-1)^{k-1}\cos^{n+1}\frac{k\pi}{n+2}\right] = E_n(W_L^{n+1})_L.
     $$
     Comparing term-by-term with our exact center constant $B_n = E_n(0)$ (eq. (3.6) of `paper.tex`) yields the **exact identity** for every $n \ge 1$:
     $$
     \boxed{B_n = E_n(0) = 1 - 2^n n!\,|s_{n, n+1}(0)| = 1 - A_n \, E_n(W_L^{n+1})_L.}
     $$
     **Structural explanation:** At $t = 0$, our moving nodes $u_j(0) = -\cos\frac{(j+1)\pi}{n+2}$ ($j = 0, \dots, n$) coincide with Kofanov's Chebyshev nodes $x_1, \dots, x_{n+1}$. Therefore, our interpolating polynomial $P_0 \in \pi_n$ for $h_0(y) = \frac{1}{n!} y_+^n$ IS the unique best $L^1$-approximating polynomial of $h_0$ from $\pi_n$, so $\|G_0\|_1 = \|h_0 - P_0\|_1 = e_{n, n+1}(0) = |s_{n, n+1}(0)| = E_n(W_L^{n+1})_L$. Meanwhile, symmetry gives $P_0^{(n)} = T_n h_0(0) = \frac{1}{2}$, hence $\|G_0^{(n)}\|_1 = \|\mathbf{1}_{\{y>0\}} - \frac{1}{2}\|_1 = 1$, and our sharpness identity $E_n(0) = \|G_0^{(n)}\|_1 - A_n\|G_0\|_1$ becomes $1 - A_n E_n(W_L^{n+1})_L$.
  2. **Complete non-equivalence away from $t = 0$ ($E_n(t)$ vs. $e_{n, n+1}(t)$):**
     For $t \neq 0$, our error profile $E_n(t)$ is **strictly different** from $1 - A_n e_{n, n+1}(t) = 1 - A_n |s_{n, n+1}(t)|$ (and is not obtained from $e_{n, n+1}(t)$ by any simple substitution):
     - For $t \neq 0$, the moving Jacobi nodes $u_0(t) < \dots < u_n(t)$ are distinct from the fixed Chebyshev nodes $x_1 < \dots < x_{n+1}$; the sign function $\operatorname{sgn}(G_t)$ is orthogonal to $\pi_{n-1}$ but **not** to $\pi_n$ (its $n$-th moment is $-t \cdot 2^{1-n} \neq 0$). Thus $P_t$ is not the best $L^1$-approximant of $h_t$ from $\pi_n$, and $\|G_t^{(n)}\|_1 = 1 - t + 2t\,T_n h_t(t) \neq 1$.
     - Even the **direction of monotonicity is opposite**: $e_{n, n+1}(t) = |s_{n, n+1}(t)|$ attains its maximum at $t = 0$ and vanishes at $t = \pm 1$, so $1 - A_n e_{n, n+1}(t)$ is **minimized** at $t = 0$ (rising from $B_n$ to $1$), whereas our $E_n(t)$ is **maximized** at $t = 0$ (strictly decreasing from $B_n$ down to $0$).
     - Numerical check for $n = 2, t = 0.5$: $E_2(0.5) \approx 0.441009$, whereas $1 - A_2 |s_{2,3}(0.5)| \approx 0.857023$.
  3. **Does Kofanov 1984 (or Boyanov 1975) imply our theorem $B_n^* = E_n(0)$?**
     - **No.** Neither Boyanov (1975) nor Kofanov (1984) considers Landau–Kolmogorov derivative inequalities or computes $\|G_0^{(n)}\|_1 - A_n\|G_0\|_1$.
     - At most, combining their value $\|G_0\|_1 = |s_{n, n+1}(0)|$ with $\|G_0^{(n)}\|_1 = 1$ (and mollifying $G_0$) yields the **lower bound** $B_n^* \ge 1 - A_n E_n(W_L^{n+1})_L$.
     - Crucially, their theory gives **no path to the upper bound** $B_n^* \le 1 - A_n E_n(W_L^{n+1})_L$: inserting a best polynomial approximant $P \in \pi_n$ into $\|f^{(n)}\|_1 \le \|P^{(n)}\|_1 + \|f^{(n)} - P^{(n)}\|_1 \le A_n \|f\|_1 + A_n \|f - P\|_1 + \|f^{(n)} - P^{(n)}\|_1$ enters with the **wrong sign** ($+A_n E_n(W_L^{n+1})_L > 0$, producing $B > 1$ instead of $B < 1$). Achieving the **negative sign** $-A_n E_n(W_L^{n+1})_L$ as an upper bound requires both our moving-node operator $T_n$ and the global center-maximum theorem $E_n(t) \le E_n(0)$ for all $t \in [-1, 1]$.
  4. **Recommendation for `paper.tex`:** Explicitly remark on the exact identity $B_n = 1 - A_n E_n(W_1^{n+1})_1$ citing Boyanov (1975) and Kofanov (1984), while making clear that their polynomial-approximation results give only the center value (hence at most the lower bound) and neither produce the moving-node operator $T_n$ nor the off-center profile $E_n(t)$ or upper bound.

### 2.4 Rafalson (2004) — Full-Theorem Audit and Method Comparison

- **Source:** S. Rafalson, *On constants in some inequalities for intermediate derivatives on a finite interval*, J. Approx. Theory **127** (2004), no. 2, 207–222. DOI: `10.1016/j.jat.2004.03.003`. (Inspected directly page-by-page, all 16 pages.)
- **Verified contents:**
  - Introduces the exact same lexicographic constants $A_{m+k+1,m}(p,q,r)$ and $B_{m+k+1,m}(p,q,r)$ on $I = [-1,1]$ (p. 208) and quotes Burenkov (1986) for $k = 0$ (eq. (2), p. 208).
  - **Main tools (§2, Lemmas 1–2, pp. 208–211):** Peano-kernel integral representation for $f - S_{r-1; p(\cdot)}(f)$ using orthogonal-polynomial partial sums $S_{k; p_m}(f^{(m)}; x)$ with Jacobi weight $p_m(u) = (1 - u^2)^m$, integrated by parts $m$ times into Legendre polynomials $X_{i+m}(u)$ and Jacobi polynomials $J_i^{(m,m)}(x)$.
  - **All main theorems:**
    - **Theorem 1 (p. 211, eq. (14)):** Exact formula for the **first constant** $A_{m+k+1,m}(2, \infty, r)$ for all $m \ge 1, k \ge 0, 1 \le r \le \infty$.
    - **Remark 1 (p. 213, eq. (22)):** Weighted $L^2_\alpha$ generalization for the **first constant** $A_{m+k+1,m}(2, \alpha; \infty, r)$.
    - **Theorem 2 (p. 213, eq. (23)):** Upper bound for the **first constant** $A_{m+k+1,m}(2, q, r)$ (exact for $k = 0$, Remark 2).
    - **Theorem 3 (pp. 221–222, parts (1)–(4)):** Upper bounds for the **first constant** $A_{m+k+1,m}(p, q, r)$ in four regimes of $(p, q)$—none of which even includes $p = q = 1$.
- **RIGOROUS MATHEMATICAL VERDICT:** **Zero overlap on our all-$L^1$ second constant.** Despite defining $B_{m+k+1,m}(p,q,r)$ on p. 208, Rafalson never computes, optimizes, or estimates any second constant $B$; his Peano kernel $N_{k+1; p_m}(x, t)$ serves only to guarantee finiteness of $B$. Methodologically, his fixed $L^2$-orthogonal Jacobi–Legendre projections (which reduce to rank-one constants when $k = 0$) are entirely distinct from our $L^1$-adapted moving-node divided-difference operator $T_n$.

---

## 3. Secondary Sources Verified from Primary Files

All bibliographic metadata, theorem numbers, and mathematical scopes below were verified directly against the local files in `D:\gemini\math\Ref`.

1. **Babenko–Kofanov–Pichugov (1997):** V. F. Babenko, V. A. Kofanov, and S. A. Pichugov, *On additive inequalities for intermediate derivatives of functions given on a finite interval*, Ukrainian Math. J. **49** (1997), no. 5, 685–696 (transl. from Ukr. Mat. Zh. **49** (1997), no. 5).
   - *Scope:* Establishes the abstract Banach-space / polynomial-approximation scheme proving $A^*_{n,k}(p,q,r) = M^*_{n,k}(p,q)$ (Markov–Nikolskii constant) and existence of a finite second constant $B^*$. Does not determine our exact all-$L^1$ second constant $B_n$.
2. **Babenko–Korneichuk–Kofanov–Pichugov (2003):** V. F. Babenko, N. P. Korneichuk, V. A. Kofanov, and S. A. Pichugov, *Inequalities for Derivatives and Their Applications* (Russian: *Неравенства для производных и их приложения*), Naukova Dumka, Kiev, 2003, 590 pp.
   - *Verified locations:* **§4.6** (pp. 205–215), **Theorem 4.6.1** (pp. 207–209, abstract scheme) and **Theorem 4.6.2** (p. 210, eq. (4.6.14), proving $A^*_{r,k}(q,p,s) = M^*_{r,k}(q,p)$ and a Taylor-remainder upper bound on $B^*_{r,k}$); **§9.5** (pp. 543–549, overview of additional finite-interval additive inequalities). Does not contain our exact all-$L^1$ second constant.
3. **Kofanov (2002, doctoral thesis):** V. A. Kofanov, *Inequalities of Kolmogorov Type and Extremal Problems of Analysis* (Ukrainian: *Нерівності типу Колмогорова та екстремальні задачі аналізу*), Doctoral Dissertation, Dnepropetrovsk, 2002.
   - *Verified locations:* **§4.3**, p. 149 (PDF p. 151, eqs. (4.3.4)–(4.3.5), lexicographic definitions of $A^*, B^*$); **Theorem 4.3.1** (p. 149); **Theorem 4.3.2** (p. 152, PDF p. 154, eq. (4.3.11)): proves $A^*_{r,k}(p,q,s) = M^*_{r,k}(p,q)$ and the coarse upper bound $B^*_{r,k} \le \frac{2^{r+1} M^*_{r,k}}{(r-1)!} + \frac{2^{r-k+1}}{(r-k-1)!}$ via Taylor's remainder. No exact all-$L^1$ second constant.
4. **Skorokhodov (2018, doctoral thesis):** D. S. Skorokhodov, *Optimal Recovery of Operators and Functionals and Related Extremal Problems of Approximation Theory* (Ukrainian: *Оптимальне відновлення операторів та функціоналів і суміжні екстремальні задачі теорії наближення*), Doctoral Dissertation, Oles Honchar Dnipro National University / Institute of Mathematics NAS of Ukraine, Dnipro–Kyiv, 2018.
   - *Verified locations:* **§5.1.2** (pp. 224–226, finite-interval Landau–Kolmogorov framework); **Theorem 5.6.6** (p. 293), covering $p, q \in \{1, \infty\}$ and ideal-lattice norm $E$ (including $E = L_1$) on the **strictly restricted cone $MM_r$ of $r$-multiply monotone/nonnegative functions** on $[0, 1]$!
   - *Critical distinction (false-positive trap):* For $r = 2, k = 1, p = q = 1, E = L_1$ on $MM_2([0,1])$, Theorem 5.6.6 yields $A_{\min} = 2$ with $B(2) = 1/4$, and at $A = 4$ yields $B(4) = 1/8$. On the full unconstrained Sobolev space $W^{2,1}([0,1])$, $A_{\min} = 4$ and $B(4) = 1/4$. Completely distinct problem from the free Sobolev class.
5. **Skorokhodov (2019):** D. Skorokhodov, *On the Landau–Kolmogorov inequality between $\|f'\|_\infty$, $\|f\|_\infty$ and $\|f'''\|_1$*, Researches in Mathematics **27** (2019), no. 1, 55–66. DOI: `10.15421/241906`.
   - *Verified locations:* pp. 56–57 survey of completely solved finite-interval Landau–Kolmogorov cases (none is all-$L^1$); **Proposition 1** (p. 57, citing [BKKP 2003, Thm 4.6.2] for $A^* = M^{p,q}_{k,r-1}$); **Proposition 2** (p. 58, citing Stechkin 1967 [29, §2]): for every $(A, B) \in \Gamma(D^k; L_s^r)$, $B \le E_N(D^k; W_s^r)$ (at $N = A$). Direct reference for our Stechkin corollary $\mathcal{E}_{A_n}(D^n; \mathcal{W}_n) = B_n$.
6. **Skorokhodov (2022):** D. Skorokhodov, *The Landau–Kolmogorov problem on a finite interval in the Taikov case*, J. Approx. Theory **280** (2022), 105771 (arXiv:2107.01698; local PDF is the Nov. 2020 preprint).
   - *Scope:* Solves the pointwise and uniform finite-interval problem in the Taikov setting $p = s = 2, q = \infty$, including lexicographically optimal pairs $(A^*, B(A^*))$ for $k \in \{r-2, r-1\}$. Modern benchmark paper in JAT; its survey likewise lists no all-$L^1$ second constant.
7. **Guo–Liu–Xu (2024):** D. Guo, Y. Liu, and G. Xu, *An optimal interpolation problem with Hermite information in the Sobolev class $W_1^n([-1,1])$*, Trudy Inst. Mat. Mekh. UrO RAN **30** (2024), no. 1, 270–279. DOI: `10.21538/0134-4889-2024-30-1-270-279`.
   - *Verified locations:* **Theorem 2.1** (p. 274) proves Lagrange interpolation at the interior extrema $\Theta_n = \{\cos\frac{k\pi}{n+1}\}$ of $T_{n+1}$ (zeros of $U_n$) is optimal in $L^1$ for $W_1^n([-1,1])$; **eq. (2.1)** (p. 275) states the $L^1 \to L^1$ integral-operator norm formula; **Lemma 2.1** (p. 275) gives the truncated-power interpolation remainder; p. 274 cites Kofanov (1984) for $n = r - 1$. Relevant methodological neighbor (function recovery rather than derivative-inequality second constants).
8. **Rafalson (1983):** S. Z. Rafalson, *An inequality between the norms of a function and its derivatives in integral metrics* (Russian: *Одно неравенство между нормами функции и ее производных в интегральных метриках*), Mat. Zametki **33** (1983), no. 1, 77–82.
   - *Verified contents:* Cites Burenkov (1980) on p. 78; main Theorem (p. 79, eq. (4)) proves a sharp **multiplicative weighted $L^2$** inequality under Fourier–Legendre orthogonality conditions $c_k(f) = 0$ ($k = s, \dots, r-1$). Excluded from overlap.
9. **Berdnikova–Rafalson (1985):** I. V. Berdnikova and S. Z. Rafalson, *Some inequalities between norms of a function and its derivatives in integral metrics* (Russian: *Некоторые неравенства между нормами функции и ее производных в интегральных метриках*), Izv. Vyssh. Uchebn. Zaved. Mat. **1985**, no. 12 (283), 3–6.
   - *Verified contents:* Theorems 1–3 (pp. 4–6) extend Rafalson (1983) to weighted $L^2$ multiplicative inequalities with Jacobi, Hermite, and Laguerre orthogonality conditions. Excluded from overlap.
10. **Babenko–Skorokhodov (2012):** Yu. V. Babenko and D. S. Skorokhodov, *The Kolmogorov and Stechkin problems for classes of functions whose second derivative belongs to the Orlicz space* (Russian: *Задачи Колмогорова и Стечкина для классов функций, вторая производная которых принадлежит пространству Орлича*), Mat. Zametki **91** (2012), no. 2, 172–183; English transl. in Math. Notes **91** (2012), no. 2, 161–171.
    - *Verified contents:* Theorems 1–7 concern $\|x'\|_\infty$ or $|x'(t)|$ vs. $\|x\|_\infty$ and $\|x''\|_{(N)}$ on $[0, 1]$ (uniform norms on $x$ and $x'$). Excluded from overlap.

---

## 4. Peripheral / Excluded References Inspected

- **Motornyi–Motornaya (1999):** V. P. Motornyi and O. V. Motornaya, *On the best $L_1$-approximation by algebraic polynomials to truncated powers and to classes of functions with $L_1$-bounded derivative*, Izv. Math. **63** (1999), no. 3, 561–582 (transl. from Izv. RAN Ser. Mat. **63** (1999), no. 3, 147–168). Studies fixed-$r$, $n \to \infty$ asymptotics of polynomial $L^1$-approximation of $(x-a)_+^{r-1}$ and $W_1^r$; peripheral (not needed in `paper.tex`).
- **Gaidabura–Kofanov (2016):** A. Ye. Gaidabura and V. O. Kofanov, *An equivalence theorem for additive inequalities of Kolmogorov type* (Ukrainian: *Теорема еквівалентності для адитивних нерівностей типу Колмогорова*), Visnyk Dnipropetrovskoho Universytetu, Ser. Mat. **21** (2016), 17–22. Proves an abstract equivalence between additive best-approximation inequalities and approximation of Sobolev classes by scaled Sobolev classes, yielding a duality lower bound $B \ge E(W_{q',0}^{r-k}, A W_{p',0}^r)_{s'}$ (Corollary 2, p. 22) without evaluating any explicit sharp all-$L^1$ second constant; peripheral (not needed in `paper.tex`).
- **Background references from the earlier literature map (retained for context):**
  - A. Pinkus, *On $L^1$-Approximation*, Cambridge Tracts in Mathematics **93**, Cambridge Univ. Press, 1989, DOI: `10.1017/CBO9780511526497` (canonical sets, $T$- and $WT$-systems, $L^1$ minimality of $U_n$).
  - H. B. Curry and I. J. Schoenberg, *On Pólya frequency functions IV: The fundamental spline functions and their limits*, J. Analyse Math. **17** (1966), 71–107, DOI: `10.1007/BF02788653` (B-splines / Peano kernel for divided differences).
  - A. Shadrin, *The Landau–Kolmogorov inequality revisited*, Discrete Contin. Dyn. Syst. **34** (2014), no. 3, 1183–1210, arXiv:1210.7708 (finite-interval $L^\infty$ background).
  - S. K. Bagdasarov, *Kolmogorov inequalities for functions in classes $W^r H^\omega$*, Izv. Math. **74** (2010), no. 2, DOI: `10.1070/IM2010v074n02ABEH002486` ($L^\infty$ intermediate norm with modulus-of-continuity constraint; excluded from overlap).
  - Classical foundational references verified via bibliographies of Burenkov (1980, 1986) and Skorokhodov (2019): E. Landau, *Proc. London Math. Soc.* (2) **13** (1913), 43–49; A. N. Kolmogorov, *Uchen. Zap. Moskov. Gos. Univ. Matematika* **30** (1939), 3–16; S. B. Stechkin, *Mat. Zametki* **1** (1967), no. 2, 137–148 (English transl. *Math. Notes* **1** (1967), no. 2, 91–99); B. D. Boyanov, *Mat. Zametki* **17** (1975), 511–524 (English transl. *Math. Notes* **17** (1975)).

---

## 5. Search-Coverage Caveats

Prior citation-chain sweeps covered:
- Google Scholar citing records for Kofanov (1984) and the Russian version of Burenkov (1980);
- All 15 Math-Net.Ru citing records for Burenkov (1980);
- Partial citing records for Burenkov (1986);
- Targeted Russian/Ukrainian and international approximation-theory literature from 2015–2026.

**Remaining blind spots:** Some incremental citing records of the English translations of Burenkov (1980, 1986), regional Ukrainian/Russian conference proceedings, and unindexed monographs were not exhaustively audited. Accordingly, originality statements in `paper.tex` and `README.md` should use cautious language (*"to the best of our knowledge"*) rather than an unconditional claim that the problem has never been solved anywhere since 1980.
