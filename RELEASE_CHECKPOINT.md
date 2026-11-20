# 发布验证检查点

记录时间：2026-10-27。此页仅记录可复现的技术状态，不替代原始验证日志。

## 固定身份

- 目标论文 SHA-256：`92238f55409a4bbdcffd5374e9b56722e6c0b5fed509f057e33ba5255cd2227d`。
- Lean：`leanprover/lean4:v4.32.2`。
- Mathlib：`905b95818eb32af7874a58b427f50c1711a5e96c`；其余依赖以 `lake-manifest.json` 固定。
- 证明源码冻结时间：2026-10-27 14:43 UTC。完整源码身份由最终 `verification/SOURCE_SHA256.txt` 与 `SOURCE_SHA256_AFTER.txt` 确认。

## 已建立的结果

1. 模型、实际算法、有限已观测前缀浓缩、可靠推荐与传播已接到同一真实运行。
2. 全局等待、逐节点到达、势函数三条实际损失界已分别编译及审计；完整 C.4/4.1 保留三分支最小值、一次失败成本和双截断。
3. 原始矩阵精确最小正元入口与任意原始有限观测律入口已构造；真实奖励期望解释已证明。
4. 一般基准、完整公共 DP、指数全联合基准、显式系数、全部合法尺度时间阶、指定尺度及次线性链已分别验证。
5. 全 K 臂无通信基线确有独立执行器，但公共疲劳仍使用团队共享物理状态；显示界比较已实例化。
6. 冻结源码的独立数学语义审查已通过：`evidence/current/FINAL_SEMANTIC_REVIEW.md`。没有已确认需改变原论文假设或缩小理论范围的数学问题。

主要入口：`AnvBandit.Main.theorem_4_1_canonical` 与 `AnvBandit.ObservedRegret.original_theorem_4_1`。全部条目、前提和旧接口区别分别见 [PAPER_LEAN_MAP.md](PAPER_LEAN_MAP.md)、[ASSUMPTIONS.md](ASSUMPTIONS.md)、[LEAN_FORMALIZATION.md](LEAN_FORMALIZATION.md)。

## 最终验证状态

- **P12-BUILD：通过。** 2026-10-27 16:00:44 UTC，固定依赖、删除旧项目 `.lake/build` 后的全源码显式重建退出码 0；冻结源码/配置身份一致。
- **P12-AUDIT：通过。** 2026-10-27 16:12:01 UTC，最终全声明公理、签名、源码扫描、依赖及哈希复核成功；`RESULT.txt` 为 `FULL_CLEAN_VERIFICATION_PASS`。编译器伴随实现按严格来源分类，逻辑依赖不超出标准三公理。
- **P12-RELEASE：通过。** 发布包源码/配置及验证器匹配最终验证指纹，根目录日志为实际最终副本；文件清单、哈希、交叉引用、安全路径及归档完整性检查通过。未打包依赖构建树、Git 目录、符号链接或私人协调记录。

本次先通过全源码干净构建，再因验证器分类/打印兼容修正而显式恢复审计；`AUDIT_MODE=explicit_resume_after_successful_clean_build`。冻结证明源码及配置未改。默认复现命令仍从清除项目构建产物开始，详见 [VERIFY.md](VERIFY.md)。

**发布记录：** 包内文件指纹见 `RELEASE_SHA256.txt`。每次重新打包都须重新检查文件清单、哈希、安全路径、归档完整性及归档内容与暂存文件逐字节一致；旧归档的校验和不能用于新归档。

后续复现应按 [VERIFY.md](VERIFY.md) 运行 `verification/verify.sh` 或 Windows 下直接运行 Python 验证器，检查 `verification/RESULT.txt` 及各原始日志，而不是依赖本检查点的文字。失败时保留日志并定位首个失败目标；如修改证明源码，重新核查相应语义与最终全工程。

本任务不认证论文实验图表、仿真程序或数值结果真实性。理论范围内没有已知未关闭事项；适用边界见 [OPEN_ISSUES.md](OPEN_ISSUES.md)。
