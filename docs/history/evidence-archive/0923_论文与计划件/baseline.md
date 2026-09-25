# 基线锁定（2026-09-23）

## 仓库状态（legal-math-modeling）

- 远端：github.com/laubeing-droid/legal-math-modeling，**PUBLIC**，main。
- 基线提交：`2d06da6`（论文 1–3 节中英 + INDEX 同步 + unified_math_v2 conftest 隔离修复），已在 origin/main。前一提交 `cd5568b`（三条定理改名）随本次一并首次上远端。
- 本地工作树：干净，与 origin/main 同步。

## CI 回执（GitHub Actions "Lean Authority + Formal Release Pipeline"）

- **run 35819869335（subject 2d06da6）：FAIL**。
  - `lean-full-clean-build`：**SUCCESS**——改名后的三条定理（weightedSupDist_separates_points、horn_result_subset_univ、horn_result_unique_least_fixed_point）在 CI 编译通过。这是首次拿到改名提交的 Lean 构建绿证。
  - `python-gates`：FAIL，根因 `tests/test_theorem_inventory.py::test_committed_inventory_verifies_against_working_tree` 报 200 个文件大面积哈希不匹配（_axiom_audit/_check/_test/ASPWitness/DungDefinitions/FullMath/* 等）。
  - 失败机制（2026-09-23 修正版，实测钉死）：仓库 blob 一直是 LF（i/crlf 计数 0）；故障在 Windows 工作树 67 个 .lean 为 CRLF 磁盘字节，生成器按磁盘字节记 sha256，清单固化了 CRLF 哈希，CI Linux 检出为 LF 即失配（137 行哈希差异）。早前"blob 为 CRLF"的判断是误判，已在仓库 PROGRESS.md 改口。
- **修复全程（2026-09-23，两轮，终局全绿）**：第一轮 1e0875c 刷 67 个 w/crlf 文件并重生成清单 → run 35832550717 仍红但 mismatch 137→2（`_check.lean` 带 BOM+单 CRLF、`DungDefinitions.lean` 48 处混合行尾，属 w/mixed 被第一轮名单漏筛）；第二轮 b00d315 按"非 w/lf 即刷"处理并在 1e0875c 重生成清单 → **run 35833467010 全管线 SUCCESS**（lean-full-clean-build、python-gates、runtime-refinement、seven-axis-acceptance、mathematics-completion、release-certificate、final-gate 全绿）。b00d315 首次取得 CI 绑定的发布证书链。本地判据：200 文件 disk==blob==json 三方哈希全等。
  - `seven-axis-acceptance`/`final-gate` 的失败是 artifact 下载级联，非独立根因。
- **run 35124268367（subject 5084f25）：SUCCESS**（当时清单工件与该测试尚未入库，故未触发此问题）。

## 修复方向（待用户授权后执行，涉及新提交推送）

1. 首选：`git add --renormalize proofs/` 把 .lean blob 统一为 LF（内容不变仅行尾），重新生成 `theorem_inventory_v3.json`，本地 verify + 全量 pytest 后过双闸门再推。
2. 备选：改验证器为行尾不敏感哈希（改 hash_contract 版本号，影响面更大，需评估 JC 侧消费）。
- 注意：修复提交应顺带更新 repo 内 PROGRESS.md 的"CI 回执待拉"为实际结果。

## 跨仓风险（未查，下轮处理）

- juris-calculus（版本 5.0.2，今日有提交）按名消费 Lean 定理；`cd5568b` 改了 horn_result_is_minimal_model→horn_result_unique_least_fixed_point（horn_result_least_fixed_point 未改名，原记述有误，已纠）、horn_soundness→horn_result_subset_univ、weightedSupDist_complete→weightedSupDist_separates_points。HANDOFF 第五问"JC 按名引用了哪些定理"从未查过，**改名波及面 UNKNOWN**。
- 工作区其他仓今日更新：jusbench 6f2caa9（审计 L2/L5 收敛+历史打包）、anonymizer 2386787（Actions 钉 SHA）、codices dbe7665（巡检日志 UTF-8）、manuals ad1891e（09-18）。

## 论文与证据资产位置

- 论文母本（仓库内，2d06da6）：docs/paper-rewrite/{paper_cn,paper_en,PROGRESS,HANDOFF}.md，完成 1–3/9 节，下轮第 4 节。
- wave4 证据（不入库，含商业书引文）：本目录 wave4-evidence.md。蒸馏全库实数 80,430 条（wave1 40,428+wave2 11,405+wave3/4 28,597，2026-09-23 清点）。
- 审查完善提示词：本目录 gpt-prompt.md（面向可访问远端仓库的 ChatGPT）。
- 八份完整读书报告：仅存在于 2026-09-23 会话记录。
