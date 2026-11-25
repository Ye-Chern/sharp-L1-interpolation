# 任务 09 · 从局部根分支得到全局有序节点

读论文 §3 和现有 `JacobiSymmetry.lean`、`JacobiSpectrum.lean`、`Analysis/NodeSpeed.lean`。任务 06 提供局部可微根。工作目标是从多重集排序定义 `u : ℝ → Fin (k+2) → ℝ`，保持与检查器的下降根序或论文的上升节点序之间精确的反转映射。

1. 先交付已验证的根数组定义、严格排序和多重集等式。`Splits`、`Nodup` 和基数都已有。证明参数在内部时所有根在 `(−1,1)`；若 `JacobiContainment.lean` 已验收直接复用。
2. 局部取每个根的可微分支，利用有限多个不交区间和分支连续性使索引不换位，所有根由基数穷尽。应用 `hasDerivAt_node_speed` 和 `node_speed_bounds`。闭区间端点需连续性，切勿仅由内部可微声称端点连续。
3. 用 `nodePolynomial_one`、`nodePolynomial_neg_one` 和第二类 Chebyshev 的余弦根获得端点，其中 `n=1` 仍要覆盖。导出 `u_j` 到相邻区间的递增双射、反射、`t−u_j(t)` 的单调性和任务 07 所需权重产品。图省事可先完成从速度上界到 `t−u_j` 单调的独立 lemma。

小步输出推荐拆进 `Analysis/OrderedNodes.lean`。报告 `HasDerivAt` 的确切参数域、闭区间连续性和有无完整端点结论。
