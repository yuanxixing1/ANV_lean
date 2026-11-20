# 原始假设、编码约定与派生条件

本登记以实际声明签名和结构字段为准。已通过冻结源码的独立语义审查、全源码干净构建与最终全声明公理/签名审计；发布验收状态见 [STATUS.md](STATUS.md)。所有省略命名空间的声明均以 `AnvBandit` 为根。

## 1. 原始模型与公开参数

| 项目 | Lean 表示 | 来源及边界 |
|---|---|---|
| n,K≥2；同质未知衰减、合法 Bernoulli 均值、唯一底值最优臂 | `DecayModel`，`AnvBandit/Model.lean` | 假设 2.1–2.2。正底值、非负非增趋零、`b+f≤1`、唯一最优臂；未增加衰减速率或 `∑ f<∞` |
| 曲线只在正使用次数受约束 | `extendPositiveCurve`、`DecayModel.ofPositiveCurves` | 证明 f(0)=f(1) 的扩展保持原性质，并与全部正索引值一致；不要求原先给定的无效 f(0) 满足新约束 |
| T,h,H 为正整数，h∣H，0<δ<1，实数 β>1 | `Execution.Params` | 原算法公开参数域；无 T≤H，无阶段长度单调假设，无整数 β 限制 |
| 原始联系矩阵 | `ContactMatrix` / `Main.canonicalContact` | 非负、每行和为 1、不可约；不要求每个元素严格正。信息流使用反向边 P(y,x)>0；`canonicalContact` 从常规 P(x,y)>0 不可约性转换 |
| pmin 与传播树 | `ContactMatrix.ofStochasticIrreducible`、`ofStochasticIrreducible_pmin_attained`；`ReachData` 的不可约构造 | pmin 正且达到最小正元，ReachData 为派生构造，不是额外图假设。任意 `ContactMatrix.pmin` 只需为正下界，故精确入口使用 canonical 版本 |

`Execution.Params` 不含模型 M；选臂函数只使用公开参数与节点自身状态。分析可使用 M、最优臂和间隙，不代表算法读取它们。

## 2. 两种概率入口

### 规范执行律

`ExecutionLaw.executionMeasure M p C lam` 由实际递归核构造。原始条件奖励联合分布、实际均值、可预测性和联系人分布由构造证明；主入口 `Main.theorem_4_1_canonical` 无自由概率上界或外部运行良好性前提。

### 任意原始有限观测律

`ObservedRegret.original_theorem_4_1` 的额外输入是概率测度 ν 及以下四类条件；完整类型见 `AnvBandit/OriginalMain.lean`。

| 参数 | 精确含义 | 分类 |
|---|---|---|
| `[IsProbabilityMeasure ν]` | ν 是运行的概率律 | 概率模型 |
| `hx`，仅 t<T | 给定此前有限历史，本轮 Bool 奖励向量的条件分布为实际状态决定的 Bernoulli 乘积核 | 原始假设 2.3，不是跨轮独立奖励流 |
| `hj`，仅 t<T 且确有请求 | 给定此前完整历史和本轮奖励向量，联合联系人条件律为各行分布的乘积；当前请求使用新鲜随机性 | 原始假设 2.4，不是只约束边缘分布，也不是对整条未来良好事件条件化 |
| `hzero` | 第 0 个坐标为固定初始哑元 | 空历史编码 |
| `habsent`，仅 t<T 且无请求 | 无联系人槽用恒等映射 `id` 编码 | 缺席编码，不要求发生一次“恒等联系” |

`Path n` 用 Bool 表示 0/1 奖励，用坐标 t+1 表示论文第 t+1 轮观测，坐标 0 是初始哑元。`observedPath_run` 证明抹去未使用联系人不改变执行。`finite_observed_law_unique`、`original_integral_eq` 和 `original_teamRegret_eq` 证明有限统计及真实联合轨迹期望转移；不要求 T 之后满足奖励或请求法则。规范构造中的辅助延拓不是新的实际动作。

`RealizedReward.expected_realized_eq_pathReward_original` 通过轮前条件期望证明实际收到的奖励总和与轨迹价值期望相等，绝不以未来整条动作轨迹为条件替换均值。

## 3. 已在上游证明的条件

以下条件允许出现在局部辅助定理中，但**不作为主论文入口的额外输入**。

| 派生条件 | 消解位置 |
|---|---|
| Bernoulli Hoeffding 界、正确 θ²/8 补偿、有限前缀失败概率≤δ | `ObservedPrefix.bernoulli_hoeffding`、`integral_exponential_le_one`、`measure_good_compl_le_finite`；`ExecutionLaw.actual_good_compl_le` |
| 实际均值的个人前缀包络、真实经验均值与累计计数 | `ExecutionLaw.actualMean_le_personal_envelope`；`Execution.N_eq_sum`、`Y_eq_sum`、`empiricalPrefix_at_count`；`ExecutionBounds.goodRunOnPrefix` |
| 有限事件上的选择阈值、累计个人预算 | `GoodRunOn.N_lt_mk`、`pair_budget`；`ExecutionLaw.actualGoodRun` |
| 阶段可靠缓存、剩余预算 | `ExecutionBounds.reliable_cache_prefix_residual`、`phase_residual_count_prefix` |
| 精确准备阶段、实际传播包含、完整集合稳定 | `ActualPropagation.preparation`、`informed_subset_actual`、`stable_after_ideal_completion` |
| 传播矩、几乎必然完成、到达与残余等待可积 | `Propagation.lean`、`Moments.lean`、`ActualNodeMoments.lean`；均来自不可约联系人律 |
| 全局、节点、势函数三条同一良好事件损失界 | `GlobalRegret.goodLoss_global_paper`、`ActualNodeExpectation.goodLoss_node`、`Absorbing.weighted_loss_potential_branch` |
| 公共正部面积、终端/淘汰/错误推荐共享预算 | `ActualPublicBudget.team_area_le`、`terminal_lost_public_selected_cost`；`Absorbing.actual_error_budget_series` |
| 势函数有限性、实数桥接、通信前漂移、C.11/C.12、具体 Kβ 收敛 | `VpotE_ne_top`、`Vpot_eq_toReal_VpotE`、`Vpot_recursion_of_irreducible`；`Absorbing.conditional_absorbed_drift`；`integral_Vpot_inform_eq_remainingV`、`concreteKbeta_summable` |
| 轨迹遗憾转换及期望可积性 | `TrajectoryExpectation.trajectory_conversion`、`teamRegret_conversion`、`RealizedReward.expected_realized_eq_pathReward_original` |

最终一般权重入口只额外要求确定权重 c≥0 且 c(star)=0；定理 4.1 取已证明合法的 ρ(T)。旧 `GoodRun`、`RunModel` 及组合器的字段/前提不是自动成立；只有已构造的真实运行适配才消解这些前提。

## 4. 各最终分支专属条件

- **A.4 指数实例：** `IsExponential M a eta` 要求 a≥0、eta>0，并仅在自然数 s≥1 上声明 `f k s = a k * exp (-eta k * ((s : ℝ)-1))`。这是指数命题本身的原始条件，不施加于一般曲线主定理。`Vstar1` 仍优化全部联合动作。
- **显式常数和 Hξ：** ξ>0，δ=(T+1)^(-2)，Hξ 合法性已证明。一般时间阶先固定 M,C,λ,β，再选择统一 A，之后量化所有合法 T,h,H；A 不依赖 T,h,H。
- **次线性：** `actual_sublinear` 另要求合法 h(T)≥1 和 h(T)=o(T)，与论文相应结论一致；用 T+1 避免零时域非法参数。
- **无通信基线：** 从首轮全 K 臂，自己的累计 N,Y、相同 UCB，恰 T 轮；`contacts_ignored`。公共均值仍由全体节点此前计数决定。原始律基线只有奖励条件律、初始哑元及无通信编码，不要求联系人独立性；`BaselineLaw.canonical_original_law` 证明该接口有规范实例。
- **推论 4.2：** `hcost` 和 `hcut` 正是论文 (4.9) 的两个数值充分条件，不是未消解的遗憾假设。结论是两个实际遗憾各自有界、且合作显示界严格较小；没有实际遗憾排序结论。

## 5. 信任边界

已查专项入口及最终全声明审计依赖标准 `propext`、`Classical.choice`、`Quot.sound`。它们属于 Lean/Mathlib 的逻辑基础，不是额外 bandit 事实。最终全量审计已确认没有 `sorryAx`、自设数学公理及源码级验证绕过；证据见 `verification/CLEAN_AXIOMS.txt`、`SOURCE_SCAN.txt` 与 `RESULT.txt`。

安全结构递归定义可有由 Lean 编译器生成、标记为 `.partial` 的运行时伴随实现；这与源码级 `partial def` 或 `unsafe def` 不同。全声明审计须用官方识别函数、父声明为安全递归定义、同模块及类型/宇宙参数一致等条件严格分类，不能仅按后缀放行；包括伴随实现在内的所有声明仍检查公理闭包，非 partial 的逻辑声明不得在类型、定义体或证明体中引用 unsafe/partial 常量。源码级绕过仍被禁止；详见 [VERIFY.md](VERIFY.md)。

公理检查不显示普通定理参数，所以必须同时检查完整签名、结构字段、定义与论文对应。编译通过本身也不认证 PDF 解释正确、外部仿真实现正确或实验数据真实。
