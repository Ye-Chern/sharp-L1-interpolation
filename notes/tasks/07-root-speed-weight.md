# 任务 07 · 从 Chebyshev 恒等式得到节点的差商权重

交付模块 `Lean/SharpL1/Analysis/NodeWeights.lean`，导入 `NodeSpeed.lean`。证明论文 `ode` 中的速度与差商分母关系所需的局部代数恒等式。这里 `k + 1 = n`，`nodePolynomial k t` 是未归一化的 (p)。

1. 利用 (U_{m+1}U_{m-1}=U_m^2-1)（Mathlib 搜索 Cassini 型式，或用 `U_add_two` 归纳），在 `(nodePolynomial k t).eval y = 0` 下证明

   `((U ℝ ((k : ℤ) + 1)).eval y - t * (U ℝ k).eval y)^2 = 1`。

   具体地，在 (U_{k+2}=2tU_{k+1}-t^2U_k) 中消去 (U_{k+2})。这一步不需要根的排序、区间假设或除法。
2. 推出 `|nodePolynomialDerivT k t y| = 2`。结合 `implicit_deriv_nodePolynomial_eq_zero` 和 `node_speed_bounds`，证明对内点可微根分支 `|((nodePolynomial k t).derivative.eval (u t))| * u' = 2`。除以首项系数 (2^{k+2}) 就是 (|p_t'(u)|u'=2^{-(k+1)})（(p_t) 首一）。

这比直接形式化伴随矩阵余子式短。保留 `NodeSpeed` 的现有命名和索引。只修改自己的模块。存在不同的数学路径时可自行选择。按任务环境选一个编译进程，从 `Lean` 运行 `lake build SharpL1.Analysis.NodeWeights`；交付定理名、退出码、`#print axioms`，有部分结果也保存已编译引理。
