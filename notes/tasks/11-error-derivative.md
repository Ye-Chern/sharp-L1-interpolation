# 任务 11 · 误差函数、外部单调和 Hcomp

读论文 `E`、`Eexplicit`、`dS`、`Hcomp` 和 [`finite-algebraic-bridge.md`](../finite-algebraic-bridge.md) 第二部分。使用 07 的归一化权重、08 的概率等式、09 的节点。推荐把独立可编译步骤放在 `Analysis/Error.lean` 与 `Analysis/ErrorDerivative.lean`。

1. 先定义 `Eexplicit` 右侧和 `H=1−E`。在节点有界连续时证明 `E` 连续。写出对 `t` 的完整导数，其中每一项用 `u_j′−1`。截断幂指数 `n+1≥2`，含 `u_j(t)=t` 的点也可微。用 `Exterior.lean` 接上 `t>1/2` 的单调性。
2. 在增广节点上证明 `dS` 的有限求和式。先证内部权重，端点用 `2^(n+1)*p_t(1)=L_t(1)` 和反射。将导数写为 `1−D_Z((L_t(y)−2(1−y²)) f_(n,t)(y))`。
3. `ErrorDividedDifference.lean` 已证明 `barycentric_Hcomp` 的差商代数式。用 08 把四组差商接到 CDF，再由存在非零系数得到 `G=1−2S`。该路线还给出 `H=t(1−2S)+(n+2)(1−t²)A₁/(n+1)`，可另行记录。
4. 补齐误差反射、`E(±1)=0` 和积分定义 `E` 与显式式子的等价。`LowOrderNodes.lean` 已将一、二阶显式式子接到 `e₁`、`e₂`，证明了 `0<t≤1` 的严格比较。应用统一反射后覆盖负半区。

分派时先做一个小步。禁止把 `|t|<1` 的假设误用于端点，或把只对自变量求导的密度公式当成总导数。

收尾时保存了显式误差求导的本机草稿 `D:/work/sharp-L1-team/results/ExplicitError.lean`。最近一次 Lean 检查只报告 `hpow` 的指数 `n + 1 - 1` 尚未化简为 `n`，可从这个报错继续。草稿未进入主库构建。`hasDerivAt_truncatedPower_zero` 已独立编译。
