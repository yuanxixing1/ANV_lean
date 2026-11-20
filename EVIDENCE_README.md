# 证据目录与历史输入

- `verification/` 是最终源码快照的全量干净构建、完整签名、公理审计及源码身份核验。验收状态以其中实际 `RESULT.txt` 和原始日志为准。
- `evidence/current/` 保存本次关键证明链的专项编译、签名与公理检查，以及对照最新论文的语义复核。专项检查不代替最终全量构建。
- `evidence/p0/` 保存对上传原包的独立复现。其成功只说明原包能够构建，不代表原包已证明最新论文全部结论。
- `evidence/P4_*.log`、`evidence/p10/` 保存自适应浓缩与完整优化域基准的专项检查。
- `historical_input/anvbandit-lean-formalization (1).zip` 是未经修改的原始输入，仅供复核历史基线。解压到另一个目录，不要覆盖当前源码。
- `reference/` 中文件名含 `(1)` 的 PDF 是最新权威目标；无该后缀的 PDF 是历史版本，仅用于版本核对。具体身份及 SHA-256 见 `SPEC_VERSION.md`。

历史签名检查驱动保存在 `evidence/p0/P0Signatures.lean.txt`，以避免混入当前工程。复现 P0 时将其复制为独立原始项目根目录的 `P0Signatures.lean`，再按 P0 记录中的命令执行。原始压缩包内旧日志不是本次产生的证据。

阶段日志按其实际生成顺序保留；其中出现的失败、诊断或中断不能改写为成功，也不能忽略同一目标的后续最终验证。最终源文件集合由 `verification/SOURCE_SHA256.txt` 与 `TARGETS.txt` 固定。
