# 可复现验证

## 1. 固定输入与依赖

- Lean：`leanprover/lean4:v4.32.2`，由 `lean-toolchain` 选择。
- Mathlib：`905b95818eb32af7874a58b427f50c1711a5e96c`，由 `lakefile.toml` 和 `lake-manifest.json` 固定；传递依赖以锁文件中的完整 revision 为准。
- 目标 PDF：`reference/具有个人疲劳与公共疲劳的去中心化合作 ANV 多臂老虎机(1).pdf`，SHA-256 `92238f55409a4bbdcffd5374e9b56722e6c0b5fed509f057e33ba5255cd2227d`。
- 规划：`reference/ANV_Lean形式化_源码审计与Dot执行规划.md`。原包历史日志不是当前复现结果。

前置工具：Git、elan、Python 3.8+；获取锁定依赖及其缓存时需要相应网络访问。**不要执行 `lake update` 或升级依赖来代替本项目的固定版本验证。**

## 2. 推荐全量验证

从独立解压的项目根目录运行。可使用可信的固定版本依赖缓存，不使用旧项目自身的编译产物。本次重建的是全部项目源码，并非从头重建 Lean 或整个 Mathlib。

Linux / macOS：

```sh
lake env lean --version
lake --version
lake exe cache get
bash verification/verify.sh
```

Windows PowerShell：

```powershell
lake env lean --version
lake --version
lake exe cache get
py -3 verification\verify_project.py
```

未安装 `py` 启动器时，可使用 `python verification\verify_project.py`。`verification/verify.ps1` 仅是正常脚本执行策略允许时的可选包装；无需绕过或修改执行策略。

脚本以 `verification/verify_project.py` 为共同实现，执行：

1. 核对工具链、锁文件以及各依赖的实际 Git revision 和工作树状态。
2. 保存源码与配置的 SHA-256；动态枚举根聚合入口及 `AnvBandit/**/*.lean` 的全部项目模块。
3. 删除**本项目** `.lake/build`（若其为符号链接则拒绝），保留锁定依赖；使用 `--no-cache` 和 `+模块名` 显式重建每个项目模块，并核查对应新 `.olean`，避免未导入文件或旧产物漏检。
4. 运行 `Check.lean`，再导入全部项目模块，执行完整签名检查及声明级依赖审计。按声明的定义模块是否属于 `AnvBandit` / `AnvBandit.*` 判定项目范围，不只看命名空间；拒绝项目自定义公理、源码级 unsafe/partial 与计算绕过，以及任何超出标准三公理的传递公理依赖；编译器生成的递归运行时伴随声明采用下述严格分类。
5. 核对构建前后源码哈希一致，保存原始输出与退出结果。

**当前验证结果：全源码干净构建于 16:00:44 UTC 退出码 0；全声明公理、完整签名、源码扫描及依赖复核于 16:12:01 UTC 全部通过，冻结源码/配置前后哈希一致。** `RESULT.txt` 记录 `FULL_CLEAN_VERIFICATION_PASS`。发布包源码/配置与验证器匹配验证指纹，文件清单、证据副本、交叉引用及归档完整性检查均已通过；包内文件指纹见 `RELEASE_SHA256.txt`。单独 `lake build` 成功不能替代此全量验证。

默认调用总是先清除项目构建产物并全量重建。`--resume-audit` 仅供审计脚本自身故障后的显式恢复：要求既有全量干净构建成功、模块清单和产物完整、冻结源码/配置哈希一致；不会自动启用，也不能用于跳过首次干净构建。正常复现请使用上述不带该选项的命令。

## 3. 最终证据位置

| 文件（`verification/` 下） | 含义 |
|---|---|
| `CLEAN_BUILD_LOG.txt` | 固定环境中的全部源模块干净构建原始日志 |
| `CLEAN_CHECK_LOG.txt` | 检查步骤及审计运行结果 |
| `CLEAN_SIGNATURES.txt` | 最终关键入口/结构的完整签名 |
| `CLEAN_AXIOMS.txt` | 全量项目声明公理依赖审计 |
| `SOURCE_SHA256.txt`、`SOURCE_SHA256_AFTER.txt` | 构建前后源码身份与一致性 |
| `TARGETS.txt`、`BUILT_MODULES.txt` | 实际枚举的项目目标与完成构建的模块 |
| `DEPENDENCY_REVISIONS.txt`、`DEPENDENCY_REVISIONS_AFTER.txt` | 检查前后固定依赖 revision |
| `SOURCE_SCAN.txt`、`RESULT.txt` | 源码静态扫描和最终验证结果 |
| `AllAxioms.lean`、`Signatures.lean` | 自动生成的全量审计与签名检查源文件 |

上述最终验证已通过，实际生成的证据已随包提供。Windows PowerShell 包装脚本随包提供，但本次执行环境是 Linux，不宣称已经在 Windows 上运行验证。普通 linter 警告保留在日志中，不等于证明失败。根目录 `BUILD_LOG.txt`、`AXIOMS.txt` 是同一 P12 快照的实际最终日志副本。阶段日志保存在 `evidence/`；历史失败可保留，但应按 TARGET 和后续成功结果判读。

## 4. 本次审计恢复记录

完整过程见 `verification/VERIFIER_RECOVERY_NOTES.txt`；简表见 `verification/CLEAN_VERIFICATION_SUMMARY.txt`，严格分类的运行时伴随声明清单见 `verification/COMPILER_RUNTIME_HELPERS.txt`。

本次先完成全部源码干净构建，随后修正验证器自身的元数据分类及打印兼容问题，再显式使用 `--resume-audit` 重跑检查。初版将安全递归定义的编译器运行时伴随声明一概当作源码 partial 而停止；最终版采用下文的严格父声明/来源分类。另移除了固定 Lean 版本不支持的 `pp.width` 打印选项。**这些改动仅涉及验证器，不涉及冻结 Lean 证明源码或配置。**

最终 `RESULT.txt` 的 `AUDIT_MODE` 为 `explicit_resume_after_successful_clean_build`；`AUDIT_RESUME_LOG.txt`、`DEPENDENCY_REVISIONS_RESUME.txt` 记录恢复检查，`SOURCE_SHA256.txt` 与 `SOURCE_SHA256_AFTER.txt` 一致。早期失败原始记录保留于 `verification/history/`，不得拿它们替代最终成功日志，也不应隐去它们。用户正常复现仍使用默认全量清洁命令。验证器参数拒绝、哈希不匹配拒绝、旧 PASS 标记清除及源码扫描测试记录于 `verification/VERIFIER_GUARD_TESTS.txt`。

## 5. 单项检查与签名阅读

下面用于定位问题，不替代全量干净构建：

```sh
lake build AnvBandit.MainTheorems AnvBandit.OriginalMain
lake build AnvBandit.ActualSublinear AnvBandit.BaselineRealizedReward
lake build AnvBandit.BaselineComparison AnvBandit.ExponentialDP AnvBandit.PublicDP
lake env lean AnvBandit/OriginalMainCheck.lean
lake env lean AnvBandit/P11Check.lean
lake env lean AnvBandit/CheckBaseline.lean
lake env lean AnvBandit/CheckBaselineComparison.lean
lake env lean AnvBandit/Check.lean
```

需要单独阅读任意入口时，创建临时 `.lean` 文件，示例：

```lean
import AnvBandit.MainTheorems
import AnvBandit.OriginalMain
#print AnvBandit.DecayModel
#print AnvBandit.Execution.Params
#print AnvBandit.ContactMatrix
#check @AnvBandit.Main.theorem_4_1_canonical
#check @AnvBandit.ObservedRegret.original_theorem_4_1
#print axioms AnvBandit.Main.theorem_4_1_canonical
#print axioms AnvBandit.ObservedRegret.original_theorem_4_1
```

用 `lake env lean <文件名>` 检查。主入口应只保留原始模型/合法参数/矩阵或原始条件联合律，不应出现浓缩、推荐、传播、稳定、探索成本或遗憾上界作为自由输入。具体结构解释见 [ASSUMPTIONS.md](ASSUMPTIONS.md)。

## 6. 接受标准与信任边界

- 全量编译无错误；所有最终目标纳入聚合与检查；源码哈希未在检查间改变。
- 已声明允许的逻辑依赖为 `propext`、`Classical.choice`、`Quot.sound`；不接受 `sorryAx`、项目自设数学事实公理或源码级验证绕过。
- Lean 的安全递归定义可自动生成带 `.partial` 元数据的运行时伴随实现；这不等于源码写了 `partial def`。验证器只接受官方名称识别、父声明为安全 `defnInfo` 且有递归标记、父子同模块、类型及宇宙参数一致的编译器伴随声明；不是按名称后缀直接放行。源码扫描仍拒绝手写 unsafe/partial、伪造伴随名称及计算绕过。
- 全部声明（含这些伴随实现）仍逐一检查标准公理闭包；所有非 partial 的项目声明的类型、定义体/证明体也检查引用常量，不得依赖 unsafe/partial 常量。具体分类输出在 `CLEAN_AXIOMS.txt` 的 `AUDIT_COMPILER_RUNTIME_HELPER` 记录。不能声称每个生成声明的元数据都为 safe。
- `#print axioms` 不会把普通前提当作额外公理报告；仍须展开完整签名、结构字段和定义。
- 独立对照 PDF：真实执行/有限事件、同步公共状态、精确预算、原始矩阵最小正元、所有合法 H、实数 β、全联合优化域、无通信基线及显示界含义。14:43 UTC 冻结源码的此项审查已通过，见 `evidence/current/FINAL_SEMANTIC_REVIEW.md`；后续证明源码变化需重审受影响内容。
- 构建或审计失败应保留错误日志，修复后重新验证受影响链与最终全工程，不用编辑成功文字或复用旧项目产物代替。

发布包不需要 `.lake` 依赖树、Git 目录或临时文件；保留工具链、锁文件、源文件、验证脚本、目标 PDF、规划和最终证据即可重新获取依赖复现。理论验收不包含实验图表或数据真实性。
