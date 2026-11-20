# ANV 多臂老虎机：Lean 理论形式化

目标为 2026-10-27 最新论文《具有个人疲劳与公共疲劳的去中心化合作 ANV 多臂老虎机》的理论部分。权威输入、哈希及新旧版本实质对照见 [SPEC_VERSION.md](SPEC_VERSION.md)。原始审计规划保存在 `reference/ANV_Lean形式化_源码审计与Dot执行规划.md`。

> **验收结果：本任务理论范围已完成，独立语义审查、全源码干净构建、全声明公理/签名审计及发布包一致性检查均通过。** 没有已知未关闭的理论事项；不认证论文实验数据。主要记录见 [STATUS.md](STATUS.md)、[VERIFY.md](VERIFY.md) 和 [OPEN_ISSUES.md](OPEN_ISSUES.md)。

## 证明入口

以下名称均位于 `AnvBandit` 命名空间；不是旧的条件式组合器。

| 目标 | 入口与文件 |
|---|---|
| 定理 4.1，原始非负不可约行随机矩阵、精确网络常数 | `Main.theorem_4_1_canonical`，`AnvBandit/MainTheorems.lean` |
| 定理 4.1，任意满足原始条件联合律的有限观测运行 | `ObservedRegret.original_theorem_4_1`，`AnvBandit/OriginalMain.lean` |
| C.4，同一实际损失的三分支最小值，失败成本只加一次 | `Main.theorem_C_4`；原始律版 `ObservedRegret.original_theorem_C_4` |
| 显式常数 (4.4)–(4.5) | `ActualExplicitRegret.actual_explicit_canonical`，`AnvBandit/ActualExplicitCanonical.lean` |
| 全部合法 H 的 (4.6) | `ActualExplicitRegret.actual_time_order`，`AnvBandit/ActualExplicitRegret.lean` |
| 指定 Hξ 的 (4.7)、固定 h 对数阶、h=o(T) 次线性 | `actual_Hxi_order`、`actual_fixed_h_log_order`、`actual_sublinear`，`ActualAsymptotics.lean` / `ActualSublinear.lean` |
| 全部联合动作上的指数公共全知基准 A.4 | `ExponentialDP.proposition_A_4_full`、`ExponentialDP.greedy_policy_attains`，`AnvBandit/ExponentialDP.lean` |
| 实际无通信全 K 臂基线 (4.8) | `BaselineTrajectory.teamRegret_bound`；原始观测奖励版 `BaselineRealizedReward.original_realized_regret_bound` |
| 推论 4.2 | `BaselineComparison.corollary_4_2`，`AnvBandit/BaselineComparison.lean` |

`teamRegret` 的全知比较域是全部联合动作轨迹。`RealizedReward.expected_realized_eq_pathReward_original` 证明轨迹均值积分等于实际收到奖励总和的期望；不能将其误解为对未来完整动作轨迹条件化后替换奖励均值。

## 关键语义

- 两种机制均由同一真实执行器生成动作；公共疲劳在轮初冻结团队状态，轮末整批更新。节点选臂不读取未知曲线、底值、最优臂或其他人的统计。
- 浓缩只覆盖截至 T 实际观察到的前缀。推荐缓存先生成、再同时接收；累计统计不因阶段或重新插入而清零；最后一轮不通信。
- 原始律入口的 Bool 奖励、零坐标哑元和无请求时的 `id` 是编码约定，不是额外随机假设；奖励与联系人条件律仅约束实际时域和实际请求。
- 精确 `HKappa` 是最大子集和，不是 `κ*mMax`。公共正部预算全团队只计一次。精确 `pmin` 由原始矩阵构造为达到的最小正元素。
- 一般时间阶包含 H<T、H=T、H>T；β 为任意实数 β>1。独立基线无信息交换，但仍共享同一公共物理疲劳状态。
- 推论 4.2 比较**显示上界**，不推出两个实际遗憾的严格排序。

完整条目对照见 [PAPER_LEAN_MAP.md](PAPER_LEAN_MAP.md)，原始条件与派生条件见 [ASSUMPTIONS.md](ASSUMPTIONS.md)，F01–F12 的修复见 [AUDIT.md](AUDIT.md)。旧接口说明见 [LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md)。

## 复现

固定 Lean `leanprover/lean4:v4.32.2`，Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`；传递依赖由 `lake-manifest.json` 锁定。安装 Git、elan 与 Python 3.8+ 后，在项目根目录执行：

```sh
lake exe cache get
bash verification/verify.sh
```

Windows PowerShell 使用：

```powershell
lake exe cache get
py -3 verification\verify_project.py
```

未安装 `py` 启动器时，可改用 `python verification\verify_project.py`；`verify.ps1` 是正常脚本策略允许时的可选包装，不需要修改执行策略。

验证脚本、全源码干净构建、全声明公理与签名检查已通过（`verification/RESULT.txt`）；发布包已核对冻结源码、完整证据、文件哈希及归档完整性。脚本会删除本项目 `.lake/build` 并枚举项目全部 Lean 源文件；允许复用固定依赖缓存。详细步骤、日志判读及信任边界见 [VERIFY.md](VERIFY.md)。

## 范围

交付目标是理论证明与可复现工程，不包括论文第 5 节、附录 D 仿真运行或实验数值真实性认证。`Numerics.lean` 的局部算术事实不能代替实验复现。标准 `propext`、`Classical.choice`、`Quot.sound` 属于声明的逻辑信任边界；数学前提还须检查完整签名，不能仅看公理列表。

## 复现证据与实验代码

- [工程原始验证结果](verification/RESULT.txt)与[验证指南](VERIFY.md)记录固定 Lean 和 Mathlib 版本下的构建、公理审计与签名检查。
- [Windows 独立复现说明](evidence/windows-20261028/复现说明.md)及[验收结果](evidence/windows-20261028/RESULT.txt)记录 2026-10-28 单次全量复现，覆盖 128 个 Lean 模块。对应的构建日志、公理检查和源码校验清单均在同一目录。记录中提到的本机启动器是历史环境的一部分，仓库的复现入口见上面的命令。
- [Python 对照实验](experiments/ANV_comparison_extended_English.py)比较个人疲劳（lambda=0）与公共疲劳（lambda=1）下的算法表现。实验与 Lean 理论验证的范围分别记录。

运行实验前，安装 NumPy、Numba 和 Matplotlib，再运行脚本。

```sh
python -m pip install numpy numba matplotlib
python experiments/ANV_comparison_extended_English.py
```

可将脚本配置中的 `QUICK_CHECK` 设为 `True` 进行短规模检查。脚本默认在所在目录的 `anv_results/` 保存 PNG 图和 CSV 数据。

`RELEASE_SHA256.txt` 是原始发布包的历史清单。本仓库新增了实验脚本和 Windows 复现材料，补充了本页说明与 Git 配置，并遮盖了部分历史文档和日志中的本机用户名。两套 `SOURCE_SHA256.txt` 中的源码和配置可按原有哈希核对。
