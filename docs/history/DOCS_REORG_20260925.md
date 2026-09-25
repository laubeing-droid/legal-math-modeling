# Docs 树整理台账（2026-09-25）

授权：用户明示"该删的删，该移的移，该归档的归档"。全部变动经 git 工作树可见（未 commit），历史可回溯。

## 删（4 个空夹，均未被 git 跟踪的本地空壳）
- final-closure/、modeling/、theory/、（analysis/ 与 audit/ 清空后随删）

## 归档（→ history/，纯历史件）
- audit/documentation_rewrite_20260701.md → history/（INDEX 行已改路径）
- unified-v2.1/FINAL_IMPLEMENTATION_SPEC.md → history/（v2.1 旧总规格；tools/unified_math_v2/README.md 引用已同步）
- full-math 五件 → history/full-math/：V21_ORIGINAL_SPEC、ORIGINAL_57_CARDS、ORIGINAL_134_ANALYSIS、MASTER_MATH_COMPLETION、ALL_EXT_IMPLEMENTATION（full-math/HANDOFF.md 与 MASTER_MATH_COMPLETION 内部引用已同步）

## 移（机读件归位）
- audit 三件机读账本 → formal-release/：counterexample_registry.json、proof_ledger.json、trust_label_schema.json（.planning/findings.md 引用已同步）
- analysis/k3_analysis_result.json → data/（theory/k3_empirical_analysis.py 输出路径已同步 :211）

## 留（现行，10 夹）
disclosure / formal-release（13 件）/ full-math（10 件）/ history（归档）/ master-plan（施工总账）/ ontology / paper-rewrite / remediation / spec / ulm-consolidated

## INDEX.md 变更
- audit 行路径改 history/；新增 ontology/core_ontology.yaml 行（原漏登记）；新增 history/ 归档说明行；此前已加 master-plan 五行+从属条款。

## 未动
四空夹外的其余文件名与内容零改动；paper-rewrite/.mimosa 未触碰；git 未 commit。


## 二次迁移（2026-09-25 同日）
网盘 `D:\同步网盘\我的文档\legal-math-evidence\` 整体废弃（用户明示）：27+1 件全部迁入 `docs/history/evidence-archive/`（五子夹+三基线副本+归档README+0925 占位说明）；master-plan 总纲与基线三件的网盘路径引用已改仓内相对路径；INDEX.md 增 evidence-archive 行；网盘原夹已删除。wave4-evidence.md（书证十三维表）随迁，全量方案的来源指针同步生效。
