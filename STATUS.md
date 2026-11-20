# 当前验证状态

更新时间：2026-10-27。目标版本及哈希见 [SPEC_VERSION.md](SPEC_VERSION.md)。

## 验收结论

**理论范围最终验收通过。** 2026-10-27 14:43 UTC 冻结源码的独立语义审查通过；全源码干净构建于 16:00:44 UTC 通过，全量依赖/签名审计于 16:12:01 UTC 通过。发布包的冻结哈希、证据副本、文件清单、交叉引用及归档完整性均已核对。

这里严格区分：定义对齐、辅助定理已证、连接实际运行、论文入口闭合、全工程最终复验。下表保留专项证据索引；所有所列源模块又在同一冻结源码上通过全量干净构建与最终公理/签名审计。专项日志不替代最后的全量记录。

| 范围 | 当前层次及主要入口 | 实际证据 |
|---|---|---|
| 规格、参数、正整数曲线、精确预算与矩阵常数 | 定义对齐；`DecayModel.ofPositiveCurves`、`HKappa`、`ContactMatrix.ofStochasticIrreducible` | `SPEC_VERSION.md`；`evidence/current/P1_CORE_AXIOMS.txt` |
| 算法 1、条件联合运行律与有限浓缩 | 实际运行已连接；`Execution.run`、`ExecutionLaw.actual_good_compl_le`、`actualGoodRun` | `evidence/P4_actual_build.log`、`evidence/P4_axioms_signatures.log`；`evidence/current/P3_OBSERVED_AXIOMS_SIGNATURES.log` |
| 字面 +∞ UCB 与最小编号打破平局 | 合作与全臂基线均与 `WithTop ℝ` 的最小 argmax 等价，专项通过 | `evidence/current/EXECUTION_UCB_AXIOMS_SIGNATURES.log` |
| B.5、C.1 与两机制全局等待界 | 实际传播、集合稳定及公共预算已接通；`GlobalRegret.goodLoss_global_paper` | `evidence/current/GLOBAL_REGRET_PROFILE_03_AUDIT.log`、`GLOBAL_THEOREM_AUDIT_OBSERVED_TRAJECTORY01.log` |
| C.2 逐节点分支 | 论文入口专项通过；`ActualNodeExpectation.goodLoss_node` | `evidence/current/LANE2_NODE_EXPECTATION_02.log`、`LANE2_NODE_EXPECTATION_AXIOMS.log` |
| C.3 势函数分支 | 论文入口专项通过；`Absorbing.weighted_loss_potential_branch` | `evidence/current/LANE2_ABSORBING_FINAL_01.log`、`LANE2_ABSORBING_FINAL_AXIOMS.log` |
| C.4 与定理 4.1 完整三分支有限界 | 论文入口专项通过；`Main.theorem_C_4`、`Main.theorem_4_1_canonical` | `evidence/current/LANE2_MAIN_THEOREMS_01.log`、`LANE2_MAIN_AXIOMS_SIGNATURES.log` |
| 任意原始有限观测律与实际奖励期望 | 原始律入口专项通过；`ObservedRegret.original_theorem_4_1`、`RealizedReward.expected_realized_eq_pathReward_original` | `evidence/current/ORIGINAL_MAIN01.log`、`ORIGINAL_MAIN_AUDIT_BASELINE_REALIZED01.log`；相关检查模块 |
| A.3 一般基准与 A.4 真正联合全知基准 | 完整优化域入口专项通过；`PublicDP.W_eq_Vstar1`、`ExponentialDP.proposition_A_4_full` | `evidence/p10/axiom_signature.log`、`public_dp_axiom_signature.log` |
| 显式系数、一般/指定尺度时间阶、次线性 | 真实遗憾入口专项通过；`ActualExplicitRegret.actual_explicit_canonical`、`actual_time_order`、`actual_sublinear` | `evidence/current/P11_EXPLICIT_REGRET02_CHAIN.log`、`P11_AUDIT_BASELINE_CHAIN02.log` |
| C.5 全 K 臂无通信基线 | 真实运行、共享公共状态、原始律与实际奖励入口专项通过 | `evidence/current/BASELINE_OBSERVED02_AUDIT_COMPARISON01.log`、`ORIGINAL_MAIN_AUDIT_BASELINE_REALIZED01.log` |
| 推论 4.2 | 两条实际算法上界及显示界比较专项通过；`BaselineComparison.corollary_4_2` | `evidence/current/BASELINE_COMPARISON_AUDIT_ENCODING01.log` |
| P12 独立语义审查 | **通过**：冻结源码的原始假设、算法、概率律、三分支、完整基准、时间阶及基线未发现残留数学语义缺口 | `evidence/current/FINAL_SEMANTIC_REVIEW.md`，含关键源码指纹 |
| P12 全源码干净构建 | **通过**：删除项目自身构建产物后，全部源文件及检查模块编译成功；退出码 0；冻结源码/配置身份一致 | `verification/CLEAN_BUILD_LOG.txt`、`BUILT_MODULES.txt`、`SOURCE_SHA256.txt`；结束时间 16:00:44 UTC |
| P12 全量依赖/签名审计 | **通过**：全部导入项目声明公理闭包合规；编译器运行时伴随实现严格分类；安全逻辑引用及完整签名检查成功，源码前后哈希一致 | `verification/CLEAN_AXIOMS.txt`、`CLEAN_SIGNATURES.txt`、`SOURCE_SHA256_AFTER.txt`、`RESULT.txt`；完成时间 16:12:01 UTC |
| P12 发布一致性 | **通过**：包内源码/配置及验证器匹配验证快照，实际日志副本一致；文件哈希、交叉引用、安全路径及归档完整性检查通过 | `RELEASE_SHA256.txt`；范围见 [OPEN_ISSUES.md](OPEN_ISSUES.md) |

## 读证据的规则

1. 同一日志可能包含多个 TARGET，某一 TARGET 成功不覆盖其他失败。早期失败记录保留；应查修复后的成功记录及对应源码哈希。
2. 阶段笔记是历史检查点，里面的“尚需集成”不能自动覆盖后续成功结果；也不能用其自述替代当前签名。
3. `evidence/original_*` 是原包历史记录，不是本次独立构建。根目录 `BUILD_LOG.txt` / `AXIOMS.txt` 是本次 `verification/` 最终日志的副本；不是原包记录。
4. 完整逐条目标、文件和声明见 [PAPER_LEAN_MAP.md](PAPER_LEAN_MAP.md)。不使用源码行数、百分比或定理数量作为完成证据。
5. 实验数据真实性不在理论验收范围内；未因理论专项通过而认证实验。
