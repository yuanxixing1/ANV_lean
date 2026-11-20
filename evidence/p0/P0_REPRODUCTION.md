# P0：原始工程独立复现记录

## 已验证事实

- 原始压缩包与最新目标 PDF 的 SHA-256 均与执行规划一致；三个原始输入未改写。
- 压缩包条目通过路径穿越及符号链接检查；工作副本与不可改写的复现副本分别建立。
- 原始 29 个 Lean 源文件的哈希在复现后再次核对，完全未变；工具链、lakefile、manifest 未改动。
- 官方 Lean v4.32.2（提交 f3b06c705e6c85f5314019d5d3baab0fec5b580c）真实运行成功；所有九个依赖仓库 HEAD 与原 manifest 精确一致。
- `lake build` 成功，退出码 0。原始默认目标全部构建；旧 `.olean` 不在原包中，本次从原始源码生成项目产物。
- `lake env lean AnvBandit/Check.lean` 成功，退出码 0；119 条依赖报告只出现 propext、Classical.choice、Quot.sound，未发现 sorryAx。
- `lake env lean P0Signatures.lean` 成功，退出码 0；完整输出保留在 baseline-signatures.log。

## 实际发现的语义问题

构建成功不代表论文已完整形式化。签名输出确认 `GoodRun`、`RunModel` 及最终组合定理仍承载规划所述派生假设；原始 TimeOrder 的域确实要求 T≤H；原始 HKappa 使用粗上界。原始 IsExponential 的完整展开为 `(↑s - 1)` 的实数减法，且对所有自然数 s 成立，因此 s=0 的额外条件并非仅有排版歧义。具体修正由后续阶段负责。

## 可复现命令

在原始独立项目根目录，使用 lean-toolchain 与 manifest 指定的版本：

```sh
export LEAN_NUM_THREADS=1
# 若默认缓存目录不可写，指定一个可写目录：
export MATHLIB_CACHE_DIR=/absolute/writable/cache
lake exe cache get
lake build
lake env lean AnvBandit/Check.lean
lake env lean P0Signatures.lean
```

本次平台首次使用默认缓存路径时报告只读文件系统；改用 Mathlib 支持的 MATHLIB_CACHE_DIR 后成功。初次多进程并发加载整个 Mathlib 时出现文件页 I/O 等待，未报告源文件错误；中断该次运行并保留日志后，单线程运行及串行构建成功。没有升级依赖或修改数学源码以使构建通过。

## 证据边界

本目录仅证明上传的原始工程在指定依赖下可构建、可检查，并揭示其实际签名。它不是后续修改的构建证书，也不是论文端到端完成证书。最终工程仍须执行自己的干净回归。
