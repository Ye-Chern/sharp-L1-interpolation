# 任务 10 · 把有限证书接到真实符号期望

等任务 05 的 `cdfExact` 等式和任务 09 的有序根接口。先可做列表机械辅助引理。读 `Certificate/Checker.lean`、`Certificate/RootRow.lean`、`Certificate/CDFBridge.lean`、`Analysis/FiniteCenter.lean`。

1. 从 `checkRootRow_sound` 和真实根的多重集与顺序等式，证明每个网格行的整系数列表，经 `/gridScale` 后夹住真实 `t−u_j(t)`。有效括区严格分离，因此上下界列表各自有序。检查 `n+1` 个节点、`n−1 = k`、正尺度和左右根序。
2. 对 `core/plus/minus/both` 四个列表同时维护 `List.Forall₂`。原始可执行检查器在左边插入 `t−s`，在右边追加 `t+s`。`checkRootRow_sound` 的根严格在 `(−1,1)`，故这两个端点也保持有序。点列非空，真实系数不全部为零。
3. 调用 `cdfSign_encloses_weightedLaw` 和 05，给出 `FiniteCenter` 所要求的三项下界和 `core` 上界。单调性在证书参数区间上成立即可。若当前装配定理需要全实线 `Monotone`，可使用夹到区间的延拓，或把上游假设改成证书真正使用的 `MonotoneOn` 并重新验证。

目标为从 `checkOrder n rows = true` 产生实符号端点不等式。无需重算 CSV。推荐新增 `Certificate/RealEndpoints.lean`。
