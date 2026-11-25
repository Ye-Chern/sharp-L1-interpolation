# Gemini 任务 05 · 把证书三角表接到概率分布

打开独立工作目录 `D:/work/sharp-L1-team/manual-gemini/05-cdf-table`。
读 `Lean/SharpL1/Certificate/CDF.lean` 和 `Lean/SharpL1/Probability/WeightedExponential.lean`。
需要访问现有私有表函数时，直接在 `CDF.lean` 追加证明并添加相应 import。

目标是证明 `cdfExact knots = weightedCdfZero (knots.map (fun x : ℤ => (x : ℝ)))`，
其中整数列表 `knots` 非空且按非降序排列。左边是原检查器实际调用的 `cdfExact`，
右边是独立单位速率指数变量加权和在 0 处的闭 CDF。

- 间距 `g` 的表项 `i` 对应 `((knots.drop i).take (g + 1))`。可用 `getElem?`
  表示包含越界情况的不变量。更新取上一行相邻项，分别删去右端和左端。
- 右端非正时用 `weightedCdfZero_nonpos`。左端非负且右端正时用
  `weightedCdfZero_nonneg_pos`。其余情况直接用 `weightedCdfZero_mixed`。
- 单独处理单点和重复端点。`cdfExact [] = 0` 是检查器的默认值，
  概率层的空和闭 CDF 等于 1，故最终等式要求非空。

如果总证明太长，优先交付已编译的行更新不变量和准确的剩余命题。可自主选择列表证明写法，
保留整数检查器及现有输入格式。从 `Lean` 运行 `lake build SharpL1.Certificate.CDF`，
记录定理名、编译退出码和 `#print axioms`。只使用本工作目录，保留现有工具链和依赖缓存。
