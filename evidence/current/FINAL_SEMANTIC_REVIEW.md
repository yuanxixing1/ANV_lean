# ANV Lean 最终数学语义审查

## 结论与验收边界

**本轮审查未在下列最终入口及其实际证明链中发现尚未消解的数学语义错误，或把论文应证明的浓缩、预算、推荐可靠性、传播、成本结论移为最终假设的情形。** 审查包含结构字段展开、定义域和量词、算法时序、原始有限观测律、三个成本分支、完整策略基准及实际遗憾，而不只检查定理名称或公理列表。

这是一份源码与内核检查记录的语义审查，不代替构建及公理审计证据。初次语义审查时，各关键链已有成功检查记录，P12 干净重构建尚未完成；其后全量干净构建、全声明审计和最终验证均已通过，详见文末补充。本报告未启动另一个编译进程，也未修改证明源码。

本报告不验证论文实验数据、仿真程序或数值结果的真实性。`Numerics.lean` 的局部算术结果不作为主定理闭合的证据。

## 规格与方法

- 规格为输入目录中的 35 页《具有个人疲劳与公共疲劳的去中心化合作 ANV 多臂老虎机(1).pdf》，SHA-256 为 `92238f55409a4bbdcffd5374e9b56722e6c0b5fed509f057e33ba5255cd2227d`。
- 验收要求来自同目录 `ANV_Lean形式化_源码审计与Dot执行规划.md` 的 P0–P12、F01–F12 及强制回归清单。
- `lean-toolchain` 固定为 `leanprover/lean4:v4.32.2`；`lakefile.toml` 与 `lake-manifest.json` 的 Mathlib revision 均为 `905b95818eb32af7874a58b427f50c1711a5e96c`。
- 对照阅读了论文模型、算法、附录 A/B/C 的相关陈述和证明，尤其是原始联合条件律、A.4 优化域、C.3 吸收过程、C.4 三分支、基线以及第 33 页次线性结论；检查了对应 Lean 定义、最终声明及被调用的上游结果。已有阶段报告仅作证据索引，不替代源码检查。

## 最终入口及实际假设

| 入口 | 审查结果 |
|---|---|
| `Main.theorem_C_4`，`MainTheorems.lean:46` | 左侧为实际执行的 `weightedLoss`。参数只有 `DecayModel`、合法 `Params`、`ContactMatrix`、疲劳模式及非负且最优臂权重为零的 `c`。没有自由损失函数或派生预算假设。 |
| `Main.theorem_4_1`，同文件第 58 行 | 左侧为完整轨迹基准减实际策略期望收益的 `teamRegret`。C.4、A.5 转换与平凡上界在证明中调用，双重截断保留。 |
| `Main.theorem_4_1_canonical`，同文件第 85 行 | 只要求原始矩阵非负、行和为一、不可约；内部构造达到的最小正元素，恢复论文精确网络常数。 |
| `ObservedRegret.original_theorem_4_1` / `original_theorem_C_4`，`OriginalMain.lean:27,36` | 对任意原始观测路径概率测度成立。只在 `t<T` 要求原文奖励联合条件律、真实请求的联系人联合条件律以及初始/缺席坐标的确定编码；不要求无限未来条件律。 |
| `ActualExplicitRegret.actual_explicit` / `actual_explicit_canonical` | 实际 `teamRegret` 的显式界；旧代数组合接口中的遗憾、传播和成本前提在内部从实际运行证明消解。canonical 版本使用原始矩阵的精确 `pmin`。 |
| `actual_time_order`，`ActualExplicitRegret.lean:142` | `∃ A ≥ 0, ∀ T h H ...`，常数先于全部时域和日程参数选定；只要求正性与 `h∣H`，没有 `T≤H`。 |
| `actual_Hxi_order` / `actual_fixed_h_log_order` / `actual_sublinear` | 分别给出规定的 `Hξ` 下统一阶、固定通信粒度的对数阶，以及 `h(T)=o(T)` 时实际团队遗憾除以 `nT` 趋零。 |
| `BaselineTrajectory.teamRegret_bound` / `BaselineObserved.original_teamRegret_bound` | 真实全臂无通信基线的规范构造与任意原始观测律版本，不是把基线预算作为假设。 |
| `BaselineComparison.corollary_4_2` | 同时给出两个实际算法各自上界及显示上界间严格比较。剩余 `hcost`、`hcut` 是论文自身的充分比较条件，不是被隐藏的算法界；不声称实际遗憾严格排序。 |
| `Benchmark` / `PublicDP` / `ExponentialDP` | 包含串行/个人基准关系、公共上下夹逼和完整批量 DP；A.4 从全体联合动作轨迹的 `Vstar1` 出发，并给出递归贪心策略达到基准。 |

`DecayModel` 的字段只有原始曲线/底值/最优臂条件及 `n,K≥2`。`Params` 的字段只有算法合法参数，包括任意实数 `β>1`。`ContactMatrix` 中一般的正下界参数应与精确版本区分：一般版本允许较保守常数，canonical 构造则取所有正矩阵元素的有限最小值，并证明该值达到。最终 `actualCaps` 是用具体传播过程定义的 `Pβ,Aβ,M1,DP,Kβ`，不是调用者提供的统计界。

## 原始概率模型与算法信息约束

### 有限观测前缀而非额外独立流

`ExecutionKernel` 用当时完整执行状态生成奖励联合 Bernoulli 律。条件均值随历史和实际动作变化；没有把自适应奖励改成跨轮独立同分布序列。公共模式的有效使用次数是 **一加此前全团队使用数**，同轮所有选中同一臂的节点读取同一轮前公共状态，不在轮内人为串行增加疲劳。

`ExecutionObserved` 抹除未发生请求的联系人坐标，并证明 `observedPath_run`：投影不改变任何执行状态。`retainedContact_iff_communicates` 将保留坐标与实际非终端通信精确对应。`observedPrefix_replay`、有限观测律唯一性和 `finite_observed_statistic_transfer` 把规范构造转到任意满足原始有限条件律的测度。

`OriginalMain` 的 `hj` 条件化对象显式是 `(frestrictLe t ω, (ω (t+1)).1)`，即旧历史加本轮已实现奖励，符合联系人在本轮奖励之后生成的时序。没有把它弱化为仅给定旧历史的联系人边际分布。只对真实请求要求联系人乘积律；无请求位置的 `id` 只是缺席编码，不是虚构独立联系人假设。路径空间虽含无限坐标，最终前提仅约束有限时域，时域外坐标不参与结论。

`ObservedTrajectory.original_pathReward_integral` 转移完整联合动作轨迹的收益，而不只是各臂边际计数。因此公共疲劳下的轨迹基准也被保留。`originalTeamRegret` 是同一完整 oracle 减原始测度下实际轨迹收益积分。

### 执行器与有限浓缩

`Execution` 直接递归实现初始化、拉臂、奖励更新、推荐缓存、联系人读取和活动集合更新。动作只读取节点自己的经验统计与公共算法参数；环境均值计算另在 `ExecutionLaw` 中，不被决策器读取。通信读取同一通信前状态，重插入不清除历史统计。

`ExecutionUCB.priorityChoice_eq_min_argmax` 将实现严格识别为 `WithTop ℝ` 上的最小索引最大化：零观测臂指标为 `⊤`。合作版和基线版均有直接实例定理，因此“先最小未见臂，否则有限 UCB 最小 argmax”不是未经证明的替换规则。

`GoodEvent.lean` 的 `ObservedPrefix` 以实际已观测次数为统一范围，随机可预测均值进入中心化项；指数过程的方差项使用截断抽样次数而不是总轮数。`measure_good_compl_le_finite` 只需要 `t<T` 的局部条件，并对节点、臂及合法已观察前缀统一。`ExecutionProbability` 将它实例化到实际运行。`ExecutionBounds.goodRunOn` 与 `goodRunOnPrefix` 从原始模型及该有限好事件构造预算接口，未将无限好事件或 `GoodRunOn` 字段作为最终原始假设。

## F01 至 F12 闭合核对

| 问题 | 当前证明链与语义核对 |
|---|---|
| F01 自适应浓缩 | `GoodEvent` 的有限稀疏观测前缀、随机条件均值、正确 Hoeffding 系数及实际计数指数过程；`ExecutionProbability` 提供实际实例。旧 `Adaptive` 辅助接口不是最终 A.1 的替代品。 |
| F02 抽象 GoodRun | `Execution` 和 `BaselineExecution` 是递归运行；`ExecutionBounds`、`BaselineBounds` 从实际路径构造有限接口。结构中的表示不变量由构造器证明。 |
| F03 可靠性被假设 | `ExecutionPhases` / `ExecutionBounds` 从实际累计计数和有限好前缀推出可靠推荐；`ActualPropagation` 自行完成传播耦合与永久稳定证明。 |
| F04 B.1/B.2 不完整 | 初始化、局部信息、缓存与动态集合、统计保留、通信计数和终端规则均有对应执行证明。`reliable_cache_prefix_residual` 保留 B.2 的 `∑z+max z` 剩余预算条件。 |
| F05 A.4 域缩小 | `ExponentialDP.Vstar1_eq_expBench` 先从完整联合轨迹证明同步归约；`proposition_A_4_full` 的左侧是原始 `Vstar1`。后续递归 `Greedy.policy` 确实按当前均值贪心，并证明达到基准。 |
| F06 时间阶量词 | `actual_time_order` 对所有合法 `T,h,H` 成立，无 `T≤H`；系数独立于 `T,h,H`。`Hξ` 是后续明确实例，不冒充一般结论。 |
| F07 精确学习预算 | `Constants.lean` 中的 `DecayModel.HKappa` 是恰好 `κ` 个不同次优臂预算之和的最大值，`Bschedule=HKappa+mMax`。粗界 `HKappaUpper` 另行命名并只用于显式化；主传播准备期使用精确 `lastShortPhase`。 |
| F08 两种势函数 | `PotentialBridge` 先证明扩展值传播时间几乎处处有限与积分有限，再证明扩展值积分势函数和实值 `Vpot` 一致及递推；没有利用 `toReal ∞=0` 绕过完成性。 |
| F09 C.3 概率计数输入 | `Absorbing` 至 `AbsorbingFinal` 从实际执行构造首次失败/终端吸收、条件漂移、错误推荐预算、正增量求和、剩余等待恒等式及具体 `Kβ` 可和性；最终势函数分支无 `hpcost`、`hpot` 等外部输入。 |
| F10 C.1/C.2 与公共预算 | `GlobalRegret`、`ActualNodeExpectation` 由实际到达、淘汰、可测可积和有限成本推出两种机制预算。公共选择对先合并再用团队面积界，`Bpub` 只计一次。 |
| F11 最终只是条件组合 | `Main.goodLoss_three_branches` 对同一个原始测度下 `goodLoss` 取三界最小值，再由 C.4 统一加入一次失败项；4.1 左侧为真实轨迹遗憾。显式版本同样不含自由 `R`。 |
| F12 边界与常数 | 正指标曲线扩展、`K<n`、精确活动集合容量 `smax=min(K,⌈K/n⌉+2)`、任意实数 `β>1`、所有合法 `H`、无终端通信、精确 canonical `pmin`、同时公共计数及双重截断均在对应定义/证明中保留。 |

## 三分支与常数的特别检查

1. `Main.goodLoss_three_branches` 中全局、逐节点、势函数分支的左侧是同一个 `goodLoss M p C lam c`，没有各自重定义或重新条件化概率空间。`theorem_C_4` 只加一次 `δ n cmax T`，并与 `n cmax T` 取最小；4.1 再保留外层 `nT` 截断与 A.5 的 `Γλ`。
2. 全局等待采用 `min(T,Pβ)`；逐节点分支保留 `Aβ` 和残余等待和的 `DP`。实际到达时间的定义、完成性及积分恒等式在 `ActualNodeMoments` 中证明，不把 `E[toReal ∞]` 当成有限等待时间。
3. 个人与公共预算候选都存在。公共模式中 `F1=min(nW,nWN+Bpub)`，`C1=min(C+d wmax,CN+d wNmax+Bpub)` 的一次性公共项不被按节点、阶段或终端/淘汰拆分重复支付。`ActualPublicBudget.weighted_selected_pairs_bound` 对实际所选集合计费，允许失败前局部好前缀；不要求选择集合与奖励独立。
4. C.3 的吸收状态在首次有限好前缀失效或阶段边界达到终端时变为全体已持有。漂移的条件律位于奖励后、联系人前；期望仍对原始测度积分，未对全局好事件条件化。
5. 日程成本用 `posPart(dℓ-dℓ−1)`，未假设取整后的阶段长度单调。具体 `Kβ` 的剩余等待索引和准备期偏移与论文一致；实数 `β>1` 的级数收敛由上包络证明，没有把 β 改成整数。

## 策略域与边界核对

- **完整公共基准**：`Regret.Vstar1` 优化全部节点和全部轮次的联合动作；每条候选轨迹用自己的公共使用计数。`PublicDP` 证明它等于完整批量动态规划；同步策略只是指数曲线下经证明可取的最优子类。
- **一般曲线**：`DecayModel.ofPositiveCurves` 以 `f(0)=f(1)` 扩展仅在正指标规定的曲线，并证明正指标值不变；没有额外指数衰减、正速率或可和性假设。A.4 的指数等式也只要求 `s≥1`。
- **小 K 与空 sticky 集合**：分配按模运算；不假设 `K≥n`。`firstTwo` 从补集中取至多两个最小臂，动态集合大小和非空活动集合由证明保证。活动集合容量是 `smax=min(K,⌈K/n⌉+2)`（`Constants.lean:79`），实际活动集合满足该界（`Execution.lean:223`）；公共疲劳中单臂每轮批量上界仍为 `n`（`Batch.lean` 的 `syncVal_sub_serialVal_le`），与活动集合容量是不同的概念。
- **时域边界**：`Params` 只要求 `T,h,H≥1`、`h∣H`。通信条件为实际阶段结束且严格早于 `T`，完整末阶段与截断末阶段都不通信；`h>T`、`H<T` 均不被排除。
- **基线**：`BaselineExecution.active=univ`，联系人参数被忽略，策略不读取 `h,H,β` 等通信参数；`BaselineSemantics` 明确在 `T,L` 固定时的参数不变性。公共基线仍由 `BaselineLaw` 的全团队历史计数驱动物理疲劳，绝非 n 个独立公共环境。
- **第 33 页次线性**：`actual_sublinear` 使用合法时域 `T+1` 避免零时域，假设 `h(T)=o(T)`，以 `actual_Hxi_order` 和真实遗憾非负性夹逼 `Rteam/(nT)→0`。这是 `Hξ` 日程族的结论，没有把它推广为任意可能线性增长的 H。

## 公理和构建证据

源码扫描 `AnvBandit/*.lean` 及聚合入口，未发现 `sorry`、`admit`、自设数学 `axiom`、`unsafe`、`native_decide`、`ofReduceBool`、`implemented_by` 或 `extern` 实现绕过；字符串命中仅来自说明性注释。已阅读的最终入口 `#print axioms` 输出只含允许的 `propext`、`Classical.choice`、`Quot.sound`。

可复查的现有成功记录包括：

- `evidence/current/LANE2_MAIN_AXIOMS_SIGNATURES.log`：主入口完整签名、展开结构及公理。
- `evidence/current/LANE2_ABSORBING_FINAL_AXIOMS.log`：实际势函数最终分支。
- `evidence/current/ORIGINAL_MAIN_AUDIT_BASELINE_REALIZED01.log`：任意原始律最终入口及基线实际奖励联系。
- `evidence/current/P11_AUDIT_BASELINE_CHAIN02.log`：显式、一般时间阶、canonical、固定 h 及次线性入口的公理输出；其中 `P11_AUDIT_EXIT_CODE=0`。
- `evidence/current/P11_EXPLICIT_REGRET02_CHAIN.log`：显式及次线性源码检查，包含 `ActualSublinear` 成功退出与源码哈希。
- `evidence/current/BASELINE_COMPARISON_AUDIT_ENCODING01.log`：基线比较及原始编码链。
- `evidence/current/EXECUTION_UCB_AXIOMS_SIGNATURES.log`：合作及基线的字面扩展实数 UCB 最小 argmax 等价，成功退出且仅标准公理。

审查中曾发现聚合入口尚未导入新主结果的集成缺口；复查时 `MainTheorems`、`OriginalMain`、实际显式/渐近/次线性和基线比较均已加入。源码于 2026-10-27 14:43 UTC 冻结后复查，最新 `ExecutionUCB` 也已加入聚合入口；独立检查模块列为显式构建目标。因此先前集成缺口已消解。初次语义审查时，干净副本的全量构建仍待完成；其后的构建结果和全声明审计分类见文末补充。

**最终判定范围**：所审查的最终数学入口没有残留的派生假设、缩小策略域、额外曲线正则性、强化随机独立性或错误时域量词。相同冻结源码的干净全量重构建、最终统一公理清单与源码不变校验现已通过，详见文末；这些实际验证记录而非本语义报告或旧 `.olean` 构成构建验收证据。

## 本轮审查的关键源码指纹

```text
787931a93f1b8741bd1b3c7cdbde090d4d4cff88472d5f3c46817e454d84a647  AnvBandit/MainTheorems.lean
8553affc4b0477d224362213322aa185c97b86fea33a8fe1248f6bb8d2d9af22  AnvBandit/OriginalMain.lean
46cbeaddc5154570005fc9397614fb7bc3914864350860c5ff6bf25262e7222f  AnvBandit/ActualExplicitCanonical.lean
f4084924c21e2353e2c6801cbe113805c894e0bb903c9f524d2347699086053a  AnvBandit/ActualExplicitRegret.lean
efa7a6011149d622abc23fc092910b446e8f809f63d2096ad3018077e0d4cf99  AnvBandit/ActualAsymptotics.lean
8d7ab40ff3f3c6ce970b3af62f65435ed2c3084fb74a75773c1958ba7490f3da  AnvBandit/ActualSublinear.lean
2b6dbf35596da8e32424098c31403557037bd9ad611a93d72b5486b2863d6c16  AnvBandit/BaselineTrajectory.lean
1c8ee32467ee4c18369ed10835cce620b80b4526d008e036ce2e398aac5c64a8  AnvBandit/BaselineObserved.lean
cfa4ea9eb830ec5bf023a7938d26248d063187aeeb42d4a0b06622421662e1ec  AnvBandit/BaselineComparison.lean
ce9d5c9203d4cd7a5151a9f53f8afadc8f01b37cb7ae4510a3bc7b4d91b8ffbc  AnvBandit/Benchmark.lean
a7705bb1fa65141de325d5af5ae4b3597b1d744242661f049bcef0d75f1d3977  AnvBandit/ExponentialDP.lean
bef4136a99cf30c5327dc93f04d0e5f7c76b6d88919d640c5ebcd1a37b1fdb9f  AnvBandit/PublicDP.lean
89a4a75a6e444ec6d9be7dd4b634f61aa2c2565346f2cc07c4666344438c235c  AnvBandit/ExecutionUCB.lean
```

## P12 构建及编译器运行时伴随声明补充

截至 2026-10-27 16:12 UTC，同一冻结证明源码的 128 个模块目标已完成干净全量构建。`anv_clean_verify/verification/CLEAN_BUILD_LOG.txt` 记录 `Build completed successfully (8782 jobs)`、退出码 0，完成时间为 16:00:44 UTC；最终入口检查 `CLEAN_CHECK_LOG.txt`、全声明审计 `CLEAN_AXIOMS.txt` 和完整签名记录 `CLEAN_SIGNATURES.txt` 均已退出 0。`RESULT.txt` 于 16:12:01 UTC 记录 `FULL_CLEAN_VERIFICATION_PASS`、`SOURCE_HASHES_UNCHANGED true`。审计是在成功干净构建后显式续跑，不是伪称整个过程只运行过一次；未改动冻结证明源码。

初版全声明检查在 `AnvBandit.syncVal._unsafe_rec` 的 `.partial` 元数据上停止。这个名称不是论文源码中的 `partial def` 或 `unsafe def`：`Batch.lean:27–29` 的 `syncVal` 是普通 `def`，递归参数为列表尾部，`syncVal_nil`、`syncVal_cons` 由 `rfl` 证明。已输出的 `syncVal` 及相关证明公理依赖只有标准三项。

固定 Lean 4.32.2 自带源码明确解释此伴随声明的来源（以下路径均相对工具链的 `src/lean/`）：

- `Lean/Elab/PreDefinition/Structural/Main.lean:181–198`：先把结构递归转换为普通、可由内核检查的定义并执行 `addNonRec`，然后调用 `addAndCompilePartialRec`。
- `Lean/Elab/PreDefinition/Basic.lean:280–296`：后者为运行时代码生成额外声明，名称由 `Compiler.mkUnsafeRecName` 产生，安全性元数据显式设为 `DefinitionSafety.partial`，类型和宇宙参数从原定义复制。
- `Lean/Compiler/Old.lean:43–54`：说明常规递归定义也生成这种运行时伴随定义，并提供官方的名称构造/识别函数。`Lean/Compiler/LCNF/ToDecl.lean:96–102` 将此伴随版本用于代码生成；这不同于逻辑定义的内核归约。
- `Lean/Elab/PreDefinition/Main.lean:20–36`：源码级 `partial def` 则生成 **opaque** 逻辑入口，而非上述安全定义；因此不能只凭 `_unsafe_rec` 后缀放行。
- `Lean/Meta/RecExt.lean:26–33` 和 `PreDefinition/Basic.lean:215` 提供结构/良基递归的持久标记，可作为额外元数据检查。

最终审计采用的严格许可分类仅接受同时满足下列条件的伴随声明：它是 `.partial` 定义；官方名称识别得到父声明；父声明是 `.safe` 的 `defnInfo` 而不是 opaque；父声明具有递归标记；父子位于同一项目模块且类型、宇宙参数一致。源码仍拒绝显式 `unsafe`、`partial`、伪造运行时伴随名称及计算绕过；所有声明（包括获准的伴随声明）仍须逐一收集公理并仅允许标准三项。同时逐一检查每个安全项目定义/定理的类型和证明体所直接引用的常量，不含 unsafe/partial 声明。

因此，修正的是审计器把“编译器生成的运行时实现”误作“源码级不安全证明入口”的分类规则，不是放宽论文结论、增加数学公理或修改证明源码。

已独立核对最终 `AllAxioms.lean` 的分类实现及 `CLEAN_AXIOMS.txt`：覆盖 **128 个模块、3002 个声明、2313 个定理**；共 **17 个**运行时伴随声明全部满足上述元数据条件，也全部接受公理检查；所有非 partial 项目声明的类型/证明体引用检查通过。公理并集仅为 `propext`、`Classical.choice`、`Quot.sound`。最终日志明确记录 `safe_kernel_references_checked=true`。`SOURCE_SCAN.txt` 无禁用源码标记，构建前后源码指纹一致，最终依赖版本及工作树检查通过。该编译器元数据分类问题现已闭合。
