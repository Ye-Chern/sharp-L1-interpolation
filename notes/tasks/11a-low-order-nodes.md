# 任务 11a · 将一、二阶显式误差接到 Jacobi 节点

这是任务 11 的独立小步。打开 `D:/work/sharp-L1-team/manual-gemini/11a-low-order-nodes`。读 `paper.tex` 的 `char`、`Eexplicit` 和第 7 节，以及 `Lean/SharpL1/Chebyshev.lean`、`Analysis/LowOrders.lean`。只新建 `Lean/SharpL1/Analysis/LowOrderNodes.lean`。

对 `0 ≤ t ≤ 1`，`n=1` 的两个根递增为 `(t−1)/2`、`(t+1)/2`。`n=2` 的三个根递增为 `(t−sqrt(8+t²))/4`、`t/2`、`(t+sqrt(8+t²))/4`。两阶分别是 `nodePolynomial 0 t` 和 `nodePolynomial 1 t`。

1. 给出这些实根按 `Fin 2`、`Fin 3` 索引的声明，证明递增且穷尽相应 `nodePolynomial.roots`。可复用 `roots_eq_of_natDegree_le_card_of_ne_zero`，或者直接因式分解并计算根。`Real.sq_sqrt` 提供平方消元。
2. 将明确的根代入 `Eexplicit` 右侧，证明它分别等于 `e₁`、`e₂`。对于 `n=2`，前两根不超过 `t`，最后一根至少为 `t`，由 `sqrt(8+t²) ≥ 3t`（平方后等价于 `t²≤1`）推出。对于 `n=1` 也只有最大根有贡献。处理端点相等的情况。

若全局有序根的接口已出现，可以补一个直接连接。主要交付为上述两组根和显式误差等式，之后可用唯一排序统一。不要重做任务 02 已证明的严格中心比较。用 `lake build SharpL1.Analysis.LowOrderNodes`，报告退出码、定理名和公理审计。
