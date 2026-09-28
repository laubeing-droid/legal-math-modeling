子代理回报已全部由我本人复现，其中一条它报错的我也纠正了。以下为 v1 报告的**补充与修订**（未列出的判定维持原报）。

---

## 补充 A｜D12 分卷进度（原列 UNKNOWN，现给判定：**FAIL / 11 卷全缺逐文件清单**）

- 卷数 11 成立，但**跨两个文件**：`docs/master-plan/基线/T谱/R20附件_分卷计划PLAN.md:15-25` 的卷表只到 V10（V11 由 `排卷回执_T112_T127.md:1` 增立："已完成排卷：保留 V01–V10，新增 V11 行为主义卷"，`README.md:13` 亦记 "V01–V11"）。→ 新增 **P3-22**。
- 计划文件自己不认账：`:5` "**生产源码尚未开写**；本计划的确认不等于Git推送、CI触发…"；`:83` "T01—T111全部具有计划归属，**不等于实现**。"
- 计划点名的机器件不在仓：`registry/` 目录**不存在**（`ls -d registry` → No such file），故 `registry/PLANNED_FILES.json`、`SOURCE_OBLIGATIONS.json`、`STATEMENT_RESOLUTION.json` 全部无落点。
- 空卷（我核过的最低证据）：**V07**（JC 运行时/公共合同——无 `multijurisdiction.py`/`win_model_adapter.py`，`win_model` 只在 `01_编号台账.md:123` 被提及）、**V08**（Harness/JusBench 桥）、**V09**（全集独立回归与交付验收）。V11 行为主义卷与我判据 3 的实测一致：只有 `Batch4.lean` 的 rfl 占位与 `action_decision.py:147` 自陈非纳什。

## 补充 B｜复用总账锚点抽样（原列 UNKNOWN，现给判定：**部分名实不符**）

抽 X 档 8 条、Y 档 7 条、Z 档 9 条。X/Y 绝大多数实存且对得上（`Hohfeld.lean:48,54,60,66` 恰 4 条对 P-005"四定理"；`LegalModelV2.lean:233 relation_shared_constraints_participate` 对 P-006；`FactAdmissionSpec.lean:67,72` 对 P-041）。两处不符：

- **P2-23**：`docs/master-plan/02_复用总账.md:66` "P-022 A62 | 改造 | Override 算子（**TemporalApplicability scoped_override** 邻接）" —— `grep -c scoped_override proofs/lean/juris_lean/JurisLean/TemporalApplicability.lean` = **0**；该定理真身在 `Genealogy/TSpectrum/Batch1.lean:774 theorem scoped_override_preserves_unaffected_rules`。反证：上面那条 grep。
- **并入 P1-4 的实锤**：`02_复用总账.md:186` "P-118 补户 | **直接挂** | approximation_contract.py+**BanachCertificateV3**（NN-01/02，**军令级已施**）" —— 仓库无 `BanachCertificateV3.lean` 文件（`ls` 仅 `BanachCertificate.lean` 等 8 个 Banach*），它是 `BanachCertificate.lean:50 namespace JurisLean.BanachCertificateV3`；而该文件 `:14` 自陈 "Status: certificate schema only"。军令件 4 在活文档里被记为"直接挂·已施"。
- **P1-13**：`02_复用总账.md:28` "现全谱 **直接挂 132/132**" 与它同一屏的 `:16-27` 合计表（X57/Y41/Z34）自相矛盾；且 `02_复用总账.md` 全文**零次**出现 `Genealogy`（实测），75 项新 Lean 锚只活在 `p_registry.json` 一侧 → 两本账已分叉，复用总账的逐条锚点列停留在战役前口径。

## 补充 C｜台账与门测试（新增 3 条 P2）

- **P2-24｜论文守卫不链接主张清单。** `tests/spec/test_paper_rewrite_guard.py:27` 的禁词元组是 `("85/94", "97 jobs", "91-module", "2993", "46/46 mutations killed", "score 1.0", "发布层 fail-closed")` —— 全是**旧数字串**，与 `docs/formal-release/FORBIDDEN_CLAIMS.md:5/9/14` 无一条对应；`01_编号台账.md:118` 却称该守卫职责含"每节监控数字同行绑 subject/run"。**这正是 P0-3（"全部经 CI 权威验证，无一条 sorry"）能穿过 QA 门的直接原因**——门测的是历史口误，不防新口误。
- **P2-25｜横切A/横切B 没有回执行。** `theory/spec/receipt_ledger.json` 的 layer id 实测只有 `['L0','L1','L2','L3','L4','L5','L6']`（49 格＝7×7，41 pending / 8 AUTHORIZED，与论文 `:135` 完全一致，这项主张我判**成立**）。但 `基线/法律概念总谱.md:27` 要求"**每层每句输出**必须带可主张等级"并把两横切列为贯穿规矩；论文 `:123` 另主张"经验输出恒为参考级"。横切A 无行 → 这句话不在授权面上，只是散文。
- **P2-26｜CI 证据未落盘。** run `36258901155` 经 `gh run view` 核实为真（`success`、`headSha=bd364c5…`、push 事件、7 个作业含 `lean-full-clean-build`+`release-certificate`+`final-gate`），但仓库内 `verification/`、`reports/`、`.github/` 无任何该 run 号记录 → 第三方复核必须依赖外部系统查询权限。注：子代理据此判"不可核验"，我不采纳该定性（gh 可查即属可核验），但落盘缺失本身记 P2。（同时澄清一条**不是缺陷**的：`01:125` 1452→1475、`03:56` 1617→1642 与论文 1775 是不同 commit 的时序快照，非互相矛盾。）
- **P2-27｜冻结件与论文口径并存。** 四条 ❓ 在 `总谱:123/144/163/199` 仍标 ❓、`03_证明战役台账.md:33` 仍写"定理级 OPEN_THEOREM"，而我确认四条定理全部实存（`Part2.lean:59,66`、`Part3.lean:137,142`、`Part4.lean` P066、`Part5.lean` clamp 恰 6 条）。冻结走程序锁没错，但论文与总谱引用同一概念时一档两制。

## 修订后的合计与判定

| 项 | v1 | v1.1 |
|---|---|---|
| Q1 执行度明细 | 已 6 / 部分 4 / 未 2 | 已 6 / 部分 4 / **未执行实质 3**（新增：11 卷无逐文件清单） |
| Q4 发现数 | 19（P0 3/P1 7/P2 7/P3 2） | **28（P0 3 / P1 8 / P2 14 / P3 3）** |
| D12 | UNKNOWN | FAIL（V07/V08/V09 空，全卷缺 manifest） |
| UNKNOWN 清单 | 7 项 | **5 项**（移除 D12 与 X/Y/Z 抽样；仍剩：CI artifact 逐字内容、`Iff.rfl` 全仓定向扫、双侧 5 对等价性论证、ALLOWED/FORBIDDEN 逐条比对、新工程师从零演练） |

一句话增量结论：三条 P0 全部**加强**而非削弱——覆盖账与源码降级注的矛盾（P0-1）、T112 假锚（P0-2）、"无一条 sorry／全部经 CI 验证"（P0-3）现在都各自多了一条独立证据链（`02:28` 的 132/132、`02:186` 的军令已施、`test_paper_rewrite_guard.py:27` 的空转守卫）。要止住这类口误，最高性价比的一处改动不是补证明，而是**把 `FORBIDDEN_CLAIMS.md` 变成守卫的数据源**，让门测试禁的是主张而不是旧数字。
