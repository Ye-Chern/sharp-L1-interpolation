# Gemini 任务 06 · 从简单根构造局部可微节点

打开独立工作目录 `D:/work/sharp-L1-team/manual-gemini/06-root-branches`。
读 `Lean/SharpL1/Analysis/NodeSpeed.lean`、`Lean/SharpL1/JacobiSpectrum.lean`
及论文第 3 节。把新证明放到 `Lean/SharpL1/Analysis/RootBranches.lean`。

给定 `k : ℕ`、`t y : ℝ`，满足 `|t| < 1`、`|y| < 1` 和
`(nodePolynomial k t).eval y = 0`，构造 `u : ℝ → ℝ`，证明 `u t = y`、
`DifferentiableAt ℝ u t`、`∀ᶠ s in nhds t, (nodePolynomial k s).eval (u s) = 0`。
再用任务 04 已有的 `hasDerivAt_node_speed` 得到 `HasDerivAt` 形式的确切速度。

可以对 `F (s, x) = (s, (nodePolynomial k s).eval x)` 应用 Mathlib 逆函数定理。
其导数为下三角矩阵，右下角由 `derivative_nodePolynomial_ne_zero_of_root`
给出非零性。取局部逆在 `(s, 0)` 处的第二坐标。如果找到更直接的隐函数 API，也可以使用。

优先交付单个简单根的局部存在性。若有余力，证明附近的唯一性，或证明在有限个
互不相交的小区间内同时得到这些分支，使下一步可以把局部分支与排序后的根逐一对应。
全局按序分支、端点及误差导数属于后续步骤。

从 `Lean` 运行 `lake build SharpL1.Analysis.RootBranches`，记录实际退出码、
定理名和 `#print axioms`。保留现有工作区与依赖版本。若未做完，交付已编译的中间引理和确切卡点。
