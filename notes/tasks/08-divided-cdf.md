# 任务 08 · 截断幂差商的指数 CDF 语义

读 [`finite-algebraic-bridge.md`](../finite-algebraic-bridge.md) 第一部分，复用 `Analysis/DividedDifference.lean` 和 `Probability/WeightedExponential.lean`。拟新建 `Analysis/DividedCDF.lean`。在按降序排列的非空互异节点 `Z` 上，以 `t−z` 为系数，目标是 `weightedCdfZero (Z.map (fun z => t-z)) = D_Z f_(|Z|-1,t)`。

1. 定义截断幂为 `if t ≤ y then (y-t)^m else 0`，所以 `m=0` 对应闭事件。先证乘 `y−t` 把阶数提高一，以及同号分支。用已有 Lagrange 系数定理证明全部节点不小于 `t` 时差商等于 1，全部节点不大于 `t` 时对 `m≥1` 等于 0。
2. 若需要从 `Finset` 转到 `List`，优先使用 `Z.toFinset`、`Nodup`、`List.toFinset_card_of_nodup`，让删端点与 `Finset.erase` 一致。将 `y−t` 表成 `(y−a)`、`(y−b)` 的仿射组合，调用单删点引理。中间结果可只交上述两个删点递推的相等式。
3. 对列表长度强归纳。两端异号用 `weightedCdfZero_mixed`。单节点含等号，禁止第一步直接使用 `max⋅0` 代替零阶指示函数。

从 `Lean` 构建新模块。报告每条结果是单点、矩恒等式、递推还是最终概率等式。

## 当前接续点

`DividedCDF.lean` 的三个递推分支已编译。本机工作区 `D:/work/sharp-L1-team/luna-divided-cdf` 的 `Lean/SharpL1/Analysis/DividedCDFLaw.lean` 是 Luna 的持续草稿。该文件前两条公开引理，即 `toFinset_erase_head_of_nodup` 与 `toFinset_erase_last_of_nodup`，已在只有辅助引理时独立编译。下半段的总定理尚未通过。先明确使用长度强归纳的局部递归结构，再修复 `dropLast`、`tail = middle ++ [a]` 的重写和同号分支的等式方向。可将草稿缩回两个引理后重新增补，原文件仍留作比对。
