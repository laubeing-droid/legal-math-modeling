# 原题 10.1：授权绑定、经验建议与循环自证

**状态：** Source R2 changed-module CI、原 11 项 required record checks、CI-index 检查及 12 项 index tests 已通过；PR121 H1 的 Python gate 发现文稿计数滞后，现已按 shape 报告重生成两篇稿件并通过两项定向回归测试。修复 commit 的新全链 CI 与独立复核待完成。

## 冻结条文与源证据

冻结题单 `10_授权变更与多步法律轨迹.md` L99–106，子项 L101、L103、L105，关联 U10.1。旧 U10.1 的刷新续行协议与 Authorization/Compiler/Pipeline 定义直接复用，本轮不重开旧债务。

- **L101：** `four_binding_erasure_witnesses` 以同一实际 checker 展示 object、subject、contentVersion、time 绑定被分别删去时的反事实通过，而完整 checker 拒绝错误对象、主体、版本及过期日期；时间反例同时处理 Gamma.lawDate 与有效期，避免把冗余日期绑定误称单点漏洞。`three_stages_have_actual_distinct_witnesses` 区分授权规则获准、实际状态刷新、Temporal 版本可用；`draft_markers_do_not_authorize` 显示 `improved/finalized` 标记不授权，`new_rule_check_does_not_authorize_its_installation` 显示候选新规则不能用自身授权旧 Gamma 下的安装。
- **L103：** `rooted_refresh_is_actual_authorized_step` 将由图派生的完整 Grant 接到实际 `Pipeline.refresh` 与 `Trace.Step`。`TrustedSeeds.externalTrust` 和 `Issued` 是外部给定的根信任/委托事实支持输入，不由 Nat token、程序检查或经验分数推出。每条 admitted 边还要求父节点 delegable、来源支持双方完整节点、Grant 范围与有效时间覆盖、父子节点在当前 Gamma 下有效。`rooted_cycle_is_authorized` 给出带外部根的有限有根循环；`unrooted_cycles_create_no_permission` 证明空根不产生派生权限；`scope_and_time_are_independent_edge_gates` 隔离展示范围与当前时间门各自可拒边。`incomplete_graph_check_keeps_refresh_unknown` 保留图检查未完成的 unknown 分支。实际提交仍使用 Grant 的完整字段，不把计算出的 Nat 权限标签冒充法律授权。
- **L105：** `evidence_reuse_exact_current_condition` 要求授权仍在当前 catalog，且对当前 Query 的主体、案件、动作、Gamma、对象、payload、nextContext、内容版本、授权规则版本和有效日期范围逐项通过原 checker；`historical_validity_is_not_current_authority` 区分历史通过与当前目录/当前时间授权。`unavailable_or_conflicting_evidence_never_enables` 保留 evidence unknown/conflict；不将冲突折成肯定。

本模型是当前接口的有限证明与反例，不证明根信任或 Issued 来源在现实中真实、授权在现实法域有效，亦不证明任意委托图/外部解析器。U00 当前 15 条消费边没有实际 caller 受本新增接口影响，本轮 `affected_edges=[]`；不改 caller、public callee 或 edge 评级，不新造接线边。105 工程要求、6 cuts、U50 与全局 discharges / Step 2 / `math_flip` 均不因 source CI 改变。

## 失败历史与源检查边界

R1 run [`41851077228:1`](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41851077228)，job `126647246255`，Artifact `changed-module-only-41851077228-1`, ID `13336510940` 是失败历史：`three_stages_have_actual_distinct_witnesses` 处未展开 `Granted` 导致 `Decidable` 合成失败；`actual_rule_evaluation_keeps_usable_version` 的证明把合取型 `hselected` 当作等式使用，导致 `.trans` 字段错误。失败恢复日志曾在受影响目标输出 `sorryAx`，R1 不计通过。R2 仅展开 `Granted`、删除与既有 U10.1 theorem 同义的新 theorem，并把 footer 改为检查/打印既有 theorem；冻结定义、其他声明和前提未变。R1 ZIP、plan、raw 与 R2 ZIP、plan、raw 分别保留。

17 项结构测试只在 R1 source 提交前运行一次：`python -X utf8 -m pytest -q tests/spec/test_import_reachability.py tests/test_declaration_collisions.py`，stdout `17 passed in 5.65s`；R2 仅改 proof body/footer，未重跑。物理收据见 `D:/tmp/original10-1-source-r1/pytest-receipt.json`。Changed-module success 不等于全链、records、PR 或现实授权验收。

## Source pins
Source R2 run [41852112057:1](https://github.com/laubeing-droid/legal-math-modeling/actions/runs/41852112057) is the accepted source checkpoint CI referenced by this packet.

- 新 Candidate：30990 bytes，SHA-256 `be740b3b5ef8296b7c6364430ce34d0c926337f07684d4ffed531e956c3c3e3a`，Git blob `83e3689d8dc80aef2c6ed2ec72f08d8783bd1741`。
- `JurisLean.lean`：16573 bytes，SHA-256 `fb0faedc0aed2e2a31d204eb8ec4325c1879380920e5dc768c4ec2eb95edd779`，Git blob `4f9913459aa70aa088b3cffa5e676b498dc34960`；仅含本模块一个 generated root import。
- frozen `Final20261021/AxiomAudit.lean`：43514 bytes，SHA-256 `41346ee4a3a0729e4e31852a94fdf0a315eb18812acdbbe481a47a46f70a7099`，Git blob `6c8afdec64c2e1a37baba22b18b2c757cfa17198`；AA writer 执行后仓库为 0 diff，没有 metadata checkpoint。
- Manifest writer 实际生成 `theorem_inventory_v3.json`，subject 绑定本 source checkpoint/tree，`BOUND_TO_SUBJECT`，587 source files、`files_diverging_from_subject=[]`、`worktree_dirty_under_proofs=false`。manifest `--verify --require-bound` 属于后续必需 record check。
- `lean-toolchain` 与 `lake-manifest.json` 的物理 CRLF bytes 不等于 LF 归一后的 Git blob；verification 记录 raw 与 normalized 两套 pin，不把行尾差异伪称 source drift。


## Record validation

本轮 11 项 required record checks 均以实际命令运行并 exit 0；另有 gap-status check exit 0。各命令的 argv、cwd、PID、UTC 起止、stdout/stderr 字节与 SHA-256 均列在 `verification.json`，物理流与收据保存在 `D:/tmp/original10-1-records-20261104/checks/`。官方 CI run index 已从旧基线 602 runs / 1456 quotes 更新为 604 runs / 1458 quotes，仅新增 R1/R2 两个 run；12 项 CI-index tests 已通过（12 passed in 6.33s）。最终 index `--check` 与 CRLF-aware staged diff check 将独立记录在 Dtmp，不写回本文件或 verification，以避免自引用。

## PR121 H1 downstream finding and correction

PR121 的 H1 Python-gates 曾报告 774 passed、2 failed：两篇稿件仍写 closed-no-binders 1783，而 `declaration_shape_report.json` 已给出 1790。失败 artifact、逐字节 ZIP 成员、run/job 身份与原始失败历史保存在 `D:/tmp/original10-1-pr121-r1/failure-history.json` 及同目录下；本仓 packet 不新增该轮 run 引用。
原 11 项 required checks 中的无参数 `scripts/rebind_paper_derived_accounting.py` 实际是 dry-run：它匹配替换模板并打印生成计数，exit 0 不代表现有文稿内容等于生成结果。本次保留该真实通过记录及其 scope；形状报告和输入先更新，文稿重绑定必须最后运行 `python -X utf8 scripts/rebind_paper_derived_accounting.py --write`。
本次官方 writer 只将中文稿与英文稿的 1783 改为 1790，其余文稿字节均与原稿相同。之后仅运行原先失败的两项 paper-consistency regression tests，结果为 2 passed in 1.20s。该定向结果修复了可复现差异，新的全链 CI 仍待运行。
