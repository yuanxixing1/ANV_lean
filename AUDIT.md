# F01–F12 修复审计

依据：最新目标 PDF 与 `reference/ANV_Lean形式化_源码审计与Dot执行规划.md`。以下是当前源码及专项成功检查的分项结论；14:43 UTC 冻结源码的独立语义审查已通过（`evidence/current/FINAL_SEMANTIC_REVIEW.md`）；全源码干净构建已于 16:00:44 UTC 通过，全声明公理/签名审计已于 16:12:01 UTC 通过，发布包一致性检查亦已通过，详见 [STATUS.md](STATUS.md)。名称默认以 `AnvBandit` 为根。

| 编号 / 原问题 | 当前解决方式与可核对入口 | 尚需注意的边界 |
|---|---|---|
| **F01 自适应浓缩参数、随机均值、抽样时刻不对齐** | `GoodEvent.lean` 的 `ObservedPrefix.measure_good_compl_le_finite` 处理历史依赖均值和前 m 次实际观察，按观察数补偿 θ²/8；Bernoulli 条件指数界在内部证明。`ExecutionLaw.actual_good_compl_le` 将其接到真实运行。 | 不用逐轮 Azuma 冒充稀疏观察界；不输入错误的 1/8 次高斯参数。`Adaptive.lean`、`Prob.lean` 保留各自明示前提下的辅助结果。 |
| **F02 GoodRun 不是实际运行、无限浓缩错误** | `Execution.run` 是奖励/联系人驱动的真实递归；`N_eq_sum`、`Y_eq_sum`、`empiricalPrefix_at_count` 连接观测统计。`ExecutionBounds.goodRunOnPrefix`、`ExecutionLaw.actualGoodRun` 构造有限 `GoodRunOn`。 | 最终事件只量化 1≤m≤N(T)；旧无限 `GoodRun` 不作为实际算法定义。 |
| **F03 推荐可靠性与稳定性是字段假设** | `ExecutionBounds.reliable_cache_prefix_residual` 从阶段计数和有限前缀推导；`ActualPropagation.informed_subset_actual` 使用同一联系人序列；`stable_after_ideal_completion` 推导整个活跃集合稳定。 | S<T 时是第 S+1 轮开始持有最优臂；不宣称 S 时刻所有旧缓存已经正确；S≥T 只算截断等待。 |
| **F04 B.1/B.2 只证明局部结论** | `Execution.lean` 的初始化、状态构造、`cache_retained`、`run_frozen`、`no_terminal_communication`、`team_total`；`ExecutionPhases.lean` 的阶段计数守恒；`ExecutionBounds.phase_residual_count_prefix` 和可靠缓存结论。字面 UCB 由 `ExecutionUCB.cooperative_choose_eq_min_argmax` 证明。 | 初始化覆盖 K<n；保留累计统计；在收到消息前使用所有节点同轮缓存；不能将旧 `proposition_B_1` 单独称为完整算法证明。 |
| **F05 指数全知基准缩小为同步策略** | `ExponentialDP.value_convex`、`first_round_vertex`、`exists_synchronous_dominates` 对任意联合续程做凸性/Jensen 归约；`Vstar1_eq_expBench`、`proposition_A_4_full`、`greedy_policy_attains` 完成原域结论。一般基准见 `Benchmark.lean`、`PublicDP.W_eq_Vstar1`。 | `expBench` 仍是受限同步辅助基准；真正原域是全部 `Fin n → Fin T → Fin K`。直接路径凸性证明不冒称另有未实现的实数 Bellman 凸性声明。 |
| **F06 一般时间阶错误限制 T≤H** | `ActualExplicitRegret.actual_time_order`：固定实例后 `∃ A≥0, ∀ T h H, ...`；仅要求正整数及 h∣H。`actual_Hxi_order`、`actual_fixed_h_log_order`、`actual_sublinear` 连接真实遗憾。 | 覆盖 H<T、H=T、H>T；β 是实数。整数 `ceil β` 仅用于证明收敛的包络，未改变日程定义。 |
| **F07 精确学习预算被粗界替代** | `DecayModel.HKappa` 是恰 κ 个次优臂的最大阈值和；`sum_mk_le_hkappa` 通过补齐集合覆盖 ≤κ。`Bschedule=HKappa+mMax`。`HKappaUpper`、`hkappa_exact_le_coarse` 单独保留粗界。`ActualPropagation.preparation` 使用精确 Bschedule。 | 粗预算只在后续估计中使用，不更改原始可靠准备阶段；不假设取整后阶段长度单调。 |
| **F08 实数/扩展非负势函数未桥接** | `PotentialBridge.lean`：`finite_arrival_ae`、`VpotE_ne_top`、`Vpot_eq_toReal_VpotE`、`Vpot_recursion_of_irreducible`。 | 先证明几乎必然完成、积分有限和截断一致，再取 `toReal`，不利用 `ENNReal.toReal ⊤=0`。 |
| **F09 C.3 的主要概率/计数工作藏在前提里** | `Absorbing*` 模块证明首次失败/终端吸收、通信前可测性、`conditional_absorbed_drift`、`actual_error_budget_series`、`expected_missing_budget`；`RemainingWaitReal.lean` 的 C.11 和 `ConcreteKbeta.lean` 的具体级数收敛。最终 `Absorbing.weighted_loss_potential_branch` 不含 hpcost/hpot。 | 不在全局良好事件上重新条件化联系人；终端吸收只改变分析过程；具体 Kβ 保留原定义，粗几何/多项式包络仅证明收敛。 |
| **F10 C.1/C.2 与公共分支未闭合** | `GlobalRegret.goodLoss_global_paper` 与 `ActualNodeExpectation.goodLoss_node`；实际到达、淘汰、可测可积及 DP/Abeta 恒等式由 `ActualNode*` 证明。`ActualPublicBudget.terminal_lost_public_selected_cost` 对节点臂对并集只收一次 Bpub。 | 先分别积分候选再取最小，不用 E[min]=min(E)。T 前未到达节点由等待项覆盖；重新插入不重置预算，终端不增加淘汰。 |
| **F11 主定理、显式界与基线仍为条件组合器** | `Main.theorem_C_4`、`Main.theorem_4_1_canonical`；`ObservedRegret.original_theorem_4_1`；`ActualExplicitRegret.actual_explicit_canonical`；`BaselineRealizedReward.original_realized_regret_bound` 与 `BaselineComparison.corollary_4_2`。 | 左侧为实际执行遗憾，不是自由 R；无浓缩/预算/可靠性/稳定性/传播/损失上界自由前提。`Statements.lean`、`Explicit.lean` 仍是辅助组合层。 |
| **F12 边界与常数** | 正索引曲线扩展见 `DecayModel.ofPositiveCurves`；指数式显式 `(s:ℝ)-1` 且 s≥1；canonical pmin 达到最小正元；ReachData 来自不可约性；完成事件先证 a.s.；子集补齐见 F07；实际轨迹积分见 `TrajectoryExpectation.teamRegret_conversion`、`RealizedReward.expected_realized_eq_pathReward_original`。 | 通用 pmin 下界版与精确版分开。原始律的 Bool/哑元/缺席是编码；只要求实际时域的原始条件联合律。 |

## 边界回归重点

- 最终请求条件为非终端阶段边界 `<T`，包括恰在 T 的完整阶段也不通信；T 后状态冻结。
- 所有节点先行动，再产生本轮奖励、更新累计统计；公共状态按整轮同步更新。
- 选择没有观测的臂等价于 `WithTop ℝ` 中 +∞ 的最小 argmax；合作与基线均有完整等价声明。
- 三分支控制同一个原测度下的有限良好事件损失；C.4 只增加一次 δ 失败成本，4.1 保留内外双截断。
- 无通信全 K 臂基线没有推荐或接收，仍由共享团队计数确定公共疲劳；不能改为 n 个独立物理环境。
- 推论 4.2 的严格关系只发生在两条完整显示上界之间。

## 证据与信任

逐条目标和证据入口见 [PAPER_LEAN_MAP.md](PAPER_LEAN_MAP.md)、[STATUS.md](STATUS.md)。全源码干净构建已通过；最终全量证据包括 `verification/CLEAN_BUILD_LOG.txt`、`CLEAN_CHECK_LOG.txt`、`CLEAN_SIGNATURES.txt`、`CLEAN_AXIOMS.txt` 与源码哈希；最终 `verification/RESULT.txt` 记录 `FULL_CLEAN_VERIFICATION_PASS`。完整公理/签名检查已通过；发布包一致性也已独立检查，包括冻结哈希、证据副本、归档字节一致性及安全路径；不能仅用构建成功替代这些检查。

专项及最终全声明公理检查仅出现标准 `propext`、`Classical.choice`、`Quot.sound`。全声明检查区分源码级绕过与编译器自动生成的递归运行时伴随实现：后者只有在安全递归父定义、同模块及类型/宇宙参数一致等严格条件下分类接受，仍检查全部公理闭包；非 partial 逻辑声明的类型与证明/定义体不得引用 unsafe/partial 常量。详见 [VERIFY.md](VERIFY.md)。这不免除普通参数/结构字段审计，也不认证论文实验数据。没有以增加速率、求和性、全正矩阵、无限良好事件或缩小全知策略域来替代目标。
