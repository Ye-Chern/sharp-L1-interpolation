# Lean 形式化接续入口

目标是 `paper.tex` v0.2 的字典序锐常数定理，沿用统一解析门槛 `n ≥ 20`。先看当前分支的 [阶段记录](../phase-b.md)、[形式化总览](../../FORMALIZATION.md)和 [差商推导](../finite-algebraic-bridge.md)。正式结果以实际编译和公理审计为准。

## 接手时先核对

1. 主仓库在 `D:/work/sharp-L1-interpolation`。整理结果的分支是 `research/analysis-bridges`，GitHub [草稿 PR #6](https://github.com/Ye-Chern/sharp-L1-interpolation/pull/6)。先核对分支的最新提交和工作区状态。工作区中可能有尚未提交的产物。
2. 05、06、07 已在主工作区独立编译。继续使用它们的实际结论。06 覆盖局部唯一性和全体有序根的局部延拓，闭区间端点连续性仍待证明。07 已证明首一多项式的导数绝对值乘节点速度等于 `2^(−n)`。
3. 原始 CSV 的 `n=3,…,19` 全部已由 Lean 内核验收。日常验证只需构建修改过的模块和审计。完整证书的重跑可交 GitHub Actions，已有验收记录。[证书运行](https://github.com/Ye-Chern/sharp-L1-interpolation/actions/runs/45636804324)

## 派发顺序

下列是默认顺序，可并行的条目仍需按本机资源安排。每次只派发卡中一个有明确退出条件的小步，验收后再继续。

1. [08 差商和指数 CDF](08-divided-cdf.md) 与 [09 全局节点](09-ordered-nodes.md) 可以并行。08 的三种差商递推已编译，剩下列表归纳。09 可直接使用任务 06 的全体局部分支定理，并通过 07 接到算子权重。
2. [10 有限证书端点](10-real-endpoints.md) 需要 09 的统一排序。此步可与 [11 误差与导数](11-error-derivative.md) 并行，后者用 07、08 和 09。其中 [11a 低阶根与误差公式](11a-low-order-nodes.md) 可以独立派发，先检查 Gemini 工作区的产物。
3. [12 特征函数与原点](12-fourier-origin.md) 的单项特征函数及四根下界可提前开始。其联合原点估计使用 11。收齐 10、11、12 后，把条件定理 `center_min_of_checked_order` 的诸条件全部消去。
4. [13 大阶估计](13-uniform-orders.md) 用 08、09、11、12 的定义和恒等式。先派迹常数，振幅、反演和数值余量逐个推进。合并低阶、有限阶和大阶后，证明全阶中心最大值和中心的余弦和。
5. [14 锐 Sobolev 不等式](14-sharp-sobolev.md) 的低层积分类引理可提前做。完整不等式及锐性最后接到全阶中心定理。

## 运行与验收

用最新的已验收提交建立任务分支和独立 worktree。共享已固定版本的 Mathlib `Lean/.lake/packages`，每个工作树保留独立 `Lean/.lake/build`。在 [`Lean/README.md`](../../Lean/README.md) 有当前缓存说明。从一个 Lean 进程开始，根据空闲内存和耗时增加并行。不要让执行者覆盖 Gemini 工作区、改共享缓存或者发布到 GitHub。需要上下游变更时先验收并接收上游提交，再从新提交分派。

WorkBuddy 可以通过界面打开独立 worktree，交给它对应 Markdown 的内容。Qwen Harness 可直接传任务路径。示例中把两个路径换成所派任务的工作目录和卡片绝对路径。

```powershell
$env:LEAN_NUM_THREADS = '1'
& 'D:/work/agent-harness/harness.cmd' run --cwd $taskWorktree `
  --model 'qwen-token-plan-individual-cn/qwen3.8-flash' --thinking medium `
  --tools local --format json --prompt-file $taskCard
```

每个结果留下具体改动、目标模块的实际编译退出码和主定理的 `#print axioms`。接手 Agent 要独立复跑；接受已有声明实际覆盖的内容。若超时或只完成一半，先保存可编译部分，再记下第一条缺失声明及所需假设。阶段记录区分 CDF 语义、整数证书、中心定理和原始锐 Sobolev 定理。
