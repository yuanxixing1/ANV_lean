# 形式化兼容索引

本页替代旧包的完成度叙述，只解释保留的辅助层和当前实际论文入口。权威状态为 [STATUS.md](STATUS.md)，完整论文映射为 [PAPER_LEAN_MAP.md](PAPER_LEAN_MAP.md)，不是本页历史文件名或同名定理。

当前理论各主链已分别验证；14:43 UTC 冻结源码的独立语义审查已通过；全工程干净构建已于 16:00:44 UTC 通过；全声明公理/签名审计已于 16:12:01 UTC 通过；发布包一致性检查亦已通过；理论范围内无已知未关闭事项。

## 新旧入口如何区分

| 保留的历史接口 | 合法用途 / 不应作出的推论 | 实际入口 |
|---|---|---|
| `Prob.lean` 的独立奖励流浓缩 | 独立流特例，不是公共疲劳下历史依赖运行的完整 A.1 | `ObservedPrefix.measure_good_compl_le_finite` → `ExecutionLaw.actual_good_compl_le` |
| `Adaptive.lean` 的条件 Azuma | 按其实际条件成立的逐轮辅助界，不是稀疏前 m 次实际观察界 | `GoodEvent.lean` 的观察计数补偿指数过程 |
| `GoodRun`、`RunModel` | 抽象计数/包含归纳接口；字段并不自动由算法满足 | `Execution.run`、有限 `GoodRunOn` 适配、`ActualPropagation` |
| `Statements.lean` 的 `AnvBandit.theorem_4_1` | 接收 htriv/hcrude/hglob/hnode/hpot 的最小值组合器 | `AnvBandit.Main.theorem_4_1_canonical` |
| `Statements.lean` 的 `AnvBandit.theorem_C_4` | 接收派生成本界的代数组合器 | `AnvBandit.Main.theorem_C_4` |
| `Explicit.lean` 的 `DecayModel.theorem_4_1_explicit` | 以 hE/hR 为输入的系数组合层 | `ActualExplicitRegret.actual_explicit_canonical` |
| `Statements.lean` 的 `combine_timeorder_bounds`、`TimeOrder` | 合法域已修正，但仍是自由函数的算术层 | `ActualExplicitRegret.actual_time_order`、`actual_Hxi_order` |
| `Exponential.lean` 的 `expBench`、`proposition_A_4` | 受限同步最大值等于最大边际和；不独自给出真实 Vstar1 | `ExponentialDP.proposition_A_4_full`、`greedy_policy_attains` |
| `Statements.lean` 的 `proposition_B_1`、`lemma_B_2` | 更新容量与剩余次数等局部引理，不代表算法全部性质 | `Execution.lean`、`ExecutionPhases.lean`、`ExecutionBounds.lean` |
| `NodeCost.lean` 的条件到达/淘汰及积分组合 | 不把 harr/helim/hbd/hlin 输入当作已证明 | `ActualNodeExpectation.goodLoss_node` |
| `Potential.lean` 的 `lemma_C_3`、抽象 `Kbeta_summable` | Abel/级数工具；hpcost/hpot 和包络需实际实例化 | `Absorbing.weighted_loss_potential_branch`、`concreteKbeta_summable` |
| `Statements.lean` 的 `proposition_C_5`、`corollary_4_2` | 纯上界组合及数值充分条件，不独自构造基线 | `BaselineRealizedReward.original_realized_regret_bound`、`BaselineComparison.corollary_4_2` |

上表声明名默认省略根 `AnvBandit`；不使用虚构的 `AnvBandit.Statements` 命名空间。文件名不必等于声明命名空间。

## 当前主链

```text
原始曲线 + 合法公开参数 + 原始矩阵/条件联合律
  → 真实递归执行与个人观测统计
  → 有限已观测前缀浓缩与阈值预算
  → 可靠推荐、实际传播与稳定
  → 全局等待 / 逐节点到达 / 势函数三个同一损失界
  → C.4 + A.5 实际轨迹转换 → 完整定理 4.1
  → 显式系数、全部合法日程时间阶、指定尺度和次线性
```

独立且已接通的目标分支：一般基准/公共整数 DP/指数真实联合基准；全 K 臂无通信真实运行及显示界比较。`ObservedRegret.original_theorem_4_1` 将主结论覆盖到原始有限观测律，`RealizedReward` 说明实际收到奖励的期望含义。

## 文档与证据版本

- 最新 PDF 覆盖旧 `reference/full_text.txt`、旧 Markdown 摘录及旧说明中的冲突。
- `evidence/original_*` 保留原始历史，不充当本次成功证明。
- 阶段专项记录中的“尚需”只陈述其当时的集成状态；当前闭合情况须看最终入口及新日志。
- `Numerics.lean` 的算术结论不认证论文实验；本任务只验收理论范围。
