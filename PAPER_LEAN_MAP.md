# 论文—Lean 对照表

目标 PDF 的实际页号、版本差异及哈希见 [SPEC_VERSION.md](SPEC_VERSION.md)。下面按数学目标列出当前源码中可定位的声明；均以 `AnvBandit` 为根命名空间，文件路径均相对项目根目录。多声明一行表示共同覆盖该条目，不表示某一局部引理独自涵盖全文。同一格中省略命名空间的后续声明继承该格先前注明的命名空间。

**状态约定：** 以下主链有专项构建与审计证据；14:43 UTC 冻结源码的独立语义审查已通过；全源码干净构建已于 16:00:44 UTC 通过；全声明公理/签名审计已于 16:12:01 UTC 通过；发布一致性检查亦已通过。证据索引见 [STATUS.md](STATUS.md)。普通参数及编码解释见 [ASSUMPTIONS.md](ASSUMPTIONS.md)。

## 模型、算法与随机运行

| 目标 | 文件 / 实际声明 | 对应范围 |
|---|---|---|
| 假设 2.1–2.2 | `AnvBandit/Model.lean`：`DecayModel`、`DecayModel.ofPositiveCurves` | 原始曲线、均值范围、唯一底值最优臂；合法零点扩展 |
| 假设 2.3 | `ExecutionLaw.lean` / `ExecutionKernel.lean`：`stateMean`、`rewardDistribution`、`conditional_reward_law`、`conditional_reward_mean`（命名空间 `ExecutionLaw`） | 历史依赖的轮前状态、当轮 Bernoulli 联合律；个人与公共机制 |
| 假设 2.4 | `Contact.lean`：`ContactMatrix.ofStochasticIrreducible`；`ExecutionKernel.lean`：`ExecutionLaw.history_contact_joint`；`ExecutionContacts.lean`：`ExecutionLaw.actual_contact_stream_law` | 每次实际请求的联合条件律与新鲜性；不可约矩阵允许零元素 |
| 算法 1、(3.1)–(3.3) | `Execution.lean`：`Execution.initialD`、`Execution.LocalState.choose`、`Execution.LocalState.cache`、`Execution.LocalState.receive`、`communicate`、`step`、`run` | 最小编号初始化、个人累计统计、先缓存后同步接收、实际更新和停止 |
| +∞ 与最小编号 argmax | `ExecutionUCB.lean`：`ExecutionUCB.cooperative_choose_eq_min_argmax`、`baseline_choose_eq_min_argmax` | 零观测优先规则与 `WithTop ℝ` 的字面 argmax 等价 |
| (3.4)–(3.6) 日程及合法性 | `Execution.lean`：`Execution.Params.phaseEnd`、`phaseEnd_multiple`；`ExplicitParameters.lean`：`Execution.confidenceParams`、`explicitParams` | h∣H、任意实数 β>1；Hξ 的合法运行参数 |
| 任意原始有限观测律 | `ExecutionObserved.lean`：`ExecutionLaw.observed_transition_of_original`、`finite_observed_law_unique`；`ObservedRegret.lean`：`ObservedRegret.original_integral_eq` | Bool、初始哑元及缺席请求编码；不要求 T 后请求律 |

## 附录 A

| 条目 | 文件 / 实际声明 | 已连接内容及边界 |
|---|---|---|
| **A.1** 有限已观测前缀浓缩与均值夹逼 | `GoodEvent.lean`：`ObservedPrefix.measure_good_compl_le_finite`、`observed_mean_bounds`、`good_prefix`；`ExecutionProbability.lean`：`ExecutionLaw.actual_good_compl_le`；`ExecutionBounds.lean`：`ExecutionBounds.goodRunOnPrefix` | m 是真实观察次数，不是经过轮数；只检验 m≤N(T)；条件均值依赖历史；Bernoulli Hoeffding 与补偿过程内证 |
| **A.2** 选择阈值 | `AlgCount.lean`：`GoodRunOn.selection_gap`、`N_lt_mk`、`pair_budget`；`ExecutionBounds.lean` 的真实有限事件适配 | 持有最优臂时阈值后不能再选次优臂；严格 UCB 矛盾；累计计数不随重插入重置 |
| **A.3** 一般串行/个人/公共基准 | `Benchmark.lean`：`Vser_eq_greedy_policy`、`Vser_eq_dp`、`Vstar0_eq_n_Vser`、`benchmark_public_sandwich`；`PublicDP.lean`：`PublicDP.W_batch`、`W_eq_Vstar1` | 串行贪心实现、个人等式、公共双侧夹逼、全部总量 n 的整数批量 Bellman 递推；轮内状态冻结 |
| **A.4** 指数真实公共全知基准 | `ExponentialDP.lean`：`ExponentialDP.Vstar1_eq_expBench`、`proposition_A_4_full`、`greedy_policy_attains` | 全部联合轨迹经凸性归约；前 T 大边际公式及实际逐轮贪心实现；不是只证明受限 `expBench` |
| **A.5** 轨迹遗憾转换 | `Statements.lean`：`proposition_A_5_traj0`、`proposition_A_5_traj1`；`TrajectoryExpectation.lean`：`TrajectoryExpectation.teamRegret_conversion`；`RealizedReward.lean`：`RealizedReward.expected_realized_eq_pathReward_original` | 保留 Γ₀/Γ₁ 和 ρ(T)；实际可测轨迹积分；真实奖励期望与轨迹值的桥接 |
| **A.6** 公共偏差与选择计费 | `ActualPublicBudget.lean`：`ActualPublicBudget.team_area_le`、`public_selection_core`、`selected_times_bound`、`weighted_selected_pairs_bound`；`AbsorbingCharge.lean` / `AbsorbingPublicCharge.lean` 的错误阶段计费 | 正部面积按全团队共享一次；实际 q/N/条件均值对齐；在局部良好前缀及首次失败前应用，不假设无限好事件 |

## 附录 B

| 条目 | 文件 / 实际声明 | 对应范围 |
|---|---|---|
| **B.1** 算法良定义与信息/预算约束 | `Execution.lean`：`Execution.firstTwo_card`、`Execution.LocalState.active_card_le`、`Execution.LocalState.cache_retained`、`N_eq_sum`、`Y_eq_sum`、`team_total`、`run_frozen`、`no_terminal_communication`；`ExecutionKernel.lean`：`ExecutionLaw.action_predictable` | K<n、永久集合覆盖、个人信息、缓存保留、恰 T 轮/nT 次拉取、终端禁止通信；选臂函数无 M 输入 |
| **B.2** 剩余阶段预算与唯一最多推荐 | `AlgCount.lean`：`GoodRunOn.phase_residual_budget`；`ExecutionPhases.lean`：`Execution.preBoundary_count_conservation`；`ExecutionBounds.lean`：`ExecutionBounds.phase_residual_count_prefix`、`reliable_cache_prefix_residual` | 从实际阶段次数和累计统计推导，不把可靠推荐作为字段假设 |
| **B.3** 精确准备阶段 | `Constants.lean`：`DecayModel.HKappa`、`Bschedule`；`ScheduleLower.lean`：`lemma_B_3`、`rH_eq_last_short_phase`、`reliable_phase_exact_budget`；`ActualPropagation.lean`：`ActualPropagation.length_after_preparation` | 恰 κ 子集最大预算、真正最后短阶段、实数幂取整；无长度单调假设 |
| **B.4** 理想传播尾界与矩 | `Propagation.lean`：`measure_complete_gt_le`、`measure_tau_gt_le`、`measure_tau_gt_real_le`；`Moments.lean`：`EtauPow_le`、`M1_le`、`DP_bounds`、`Pbeta_le`；`Contact.lean`：`ofStochasticIrreducible_pmin_attained` | 不可约性构造传播见证，先证几乎必然完成；精确 pmin、εP=1 边界和 Gamma 矩估计 |
| **B.5** 实际传播、稳定与等待 | `ActualPropagation.lean`：`informed_subset_actual`、`stable_after_ideal_completion`；`ActualWaiting.lean`：`expectedWaiting_eq_EminTS`、`expectedWaiting_le_truncated_Pbeta`；`ActualNodeMoments.lean`：`integral_arrivalSum`、`integral_residualSum` | 真正源节点及准备偏移、S+1 稳定、原测度期望；S≥T 只计等待，不虚构已完成传播 |

## 附录 C 与主定理

| 条目 | 文件 / 实际声明 | 对应范围 |
|---|---|---|
| **C.1** 全局稳定尾部探索 | `ActualPublicBudget.lean`：`ActualPublicBudget.stable_tail_public_cost`；`ActualPropagation.lean`：`path_global_personal_candidate`；`GlobalRegret.lean`：`GlobalRegret.goodLoss_global_paper` | 实际稳定集合、个人/公共候选和最小值；公共 Bpub 一次；加上截断等待得到全局分支 |
| **C.2** 逐节点到达与淘汰 | `ActualNodeArrival.lean`：`ActualPropagation.actual_elimination_budget`；`ActualNodePublic.lean`：路径公共候选；`ActualNodeExpectation.lean`：`ActualNodeExpectation.goodLoss_node` | 到达后计费、不同失去臂并集、不重复预算、终端无额外淘汰；真正 Abeta 与 DP；分别取期望再取最小 |
| **C.3 / C.6–C.7** 理想势函数 | `PotentialBridge.lean`：`Vpot_eq_toReal_VpotE`、`Vpot_recursion_of_irreducible` | 未截断扩展势函数与实数截断势函数在有限性证明后统一 |
| **C.3 / C.8–C.9** 实际漂移及错误推荐预算 | `AbsorbingDrift.lean`：`Absorbing.conditional_absorbed_drift`；`AbsorbingErrorSeries.lean`：`actual_error_budget_series`；相关 `AbsorbingCharge.lean`、`AbsorbingPublicCharge.lean` | 首次失败及终端吸收、通信前信息不含当前联系人、实际错误推荐定位、同一累计预算 |
| **C.3 / C.10–C.12** 望远镜与剩余传播 | `AbsorbingExpectation.lean` / `AbsorbingError.lean`：`Absorbing.finite_telescope`、`finite_telescope_with_budget`；`RemainingWaitReal.lean`：`integral_Vpot_inform_eq_remainingV`；`AbsorbingCoupling.lean`：`ideal_subset_state`；`AbsorbingSeries.lean`：`expectedPotential_le_remaining` | 原测度可积性；正部阶段长度增量；理想过程与实际吸收过程耦合 |
| **C.3 / C.4 级数、C.13** 具体 Kβ 与最终分支 | `ConcreteKbeta.lean`：`concreteKbeta_summable`；`AbsorbingBound.lean`：`Absorbing.expected_missing_budget`；`AbsorbingFinal.lean`：`weighted_loss_potential_branch` | 真实 scheduleOmega、remainingV、准备偏移；任意实数 β>1；无 hpcost/hpot 自由假设 |
| **C.4** 一般权重完整界 | `MainTheorems.lean`：`Main.goodLoss_three_branches`、`Main.theorem_C_4`；`OriginalMain.lean`：`ObservedRegret.original_theorem_C_4` | 同一实际损失三分支最小值、平凡截断、失败成本一次 |
| **C.5** 独立全臂基线 | `BaselineRegret.lean`：`BaselineRegret.weightedLoss_bound`；`BaselineTrajectory.lean`：`teamRegret_bound`；`BaselineRealizedReward.lean`：`original_realized_regret_bound` | 真正全 K 臂无通信 UCB；个人统计、同团队公共疲劳；完整公共 min、Γ、ρ(T)、双截断与失败项 |
| **4.1 / (4.3)** 合作完整遗憾 | `MainTheorems.lean`：`Main.theorem_4_1_canonical`；`OriginalMain.lean`：`ObservedRegret.original_theorem_4_1` | 原始矩阵精确常数入口；任意原始有限观测律入口；真实联合全知基准，不是自由 R |
| **4.2 / (4.9)** 显示界改善条件 | `BaselineComparison.lean`：`BaselineComparison.corollary_4_2` | 实际合作/基线分别有上界，两个显示界严格比较；不比较实际遗憾次序 |

## 显式常数、时间阶与底值损失

| 目标 | 主要声明 / 文件 | 量词及连接 |
|---|---|---|
| C.16–C.22：阈值及系数 | `Constants.lean` 的 `thetaN`、`DecayModel.thetaM`、`Bcoef`、`rhoConst`、`Jlam`、`Dlam`；`ActualExplicit.lean` 的 `nk_le_thetaN_mul`、`DecayModel.mkAll_le_thetaM_mul`、`Bschedule_le_Bcoef_mul` | 定义与实际阈值估计分开；精确 Bschedule 后续可用粗界估计 |
| C.23–C.24：准备与传播系数 | `ActualExplicit.lean`：`DecayModel.lastShortPhase_Hxi_le_rcoef`；`TimeBounds.lean`：`DecayModel.Pbeta_Hxi_le` | 从原始不可约矩阵已证传播矩导出；不是外部传播矩假设 |
| C.25–C.26：权重与探索系数 | `ActualExplicit.lean`：`DecayModel.rho_le_rhoConst`；`ActualCostCoefficients.lean`：`DecayModel.Clam_rhoConst_le` | 精确子集容量伸缩，公共 Bpub 只加一份 |
| (4.4)–(4.5) 显式界 | `ActualExplicitCanonical.lean`：`ActualExplicitRegret.actual_explicit_canonical` | 原始矩阵最小正元；δ=(T+1)^(-2)、Hξ；C0、Ch、Clog 不依赖 T,h |
| C.27 / (4.6) 一般尺度 | `GeneralTimeBounds.lean`：`DecayModel.Pbeta_general_horizon`；`ActualExplicitRegret.lean`：`ActualExplicitRegret.actual_time_order` | 对所有 T,h,H≥1、h∣H 统一；不含 T≤H；先选 A 后量化尺度 |
| C.28 / (4.7) 指定尺度 | `ActualAsymptotics.lean`：`ActualExplicitRegret.actual_Hxi_order`、`actual_fixed_h_log_order` | 先固定实例/β/ξ，得 O(h+log(T+1))；固定 h 得 O(log(T+1)) |
| 平均遗憾次线性 | `ActualSublinear.lean`：`ActualExplicitRegret.actual_sublinear` | 合法 h(T)=o(T)；实际遗憾/(nT)→0 |
| 底值损失 | `MainTheorems.lean`：`Main.bottom_loss` | 权重取真实 gap，使用同一 C.4，不添加轨迹转换 Γ |

显式/时间阶入口以规范律表述；`ObservedRegret.original_teamRegret_eq` 可转移至任意满足原始有限观测律的运行，无需增加新上界假设。

## 非目标与历史接口

`Numerics.lean` 的有限算术声明保留，但论文实验和附录 D 的统计真实性未在本任务认证。`Statements.lean`、`Explicit.lean`、`NodeCost.lean`、`Potential.lean` 的同名历史声明可能仍要求关键上界；其正确角色是组合/计数工具，不能替代本表实际最终入口。兼容索引见 [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md)。
