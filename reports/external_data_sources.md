# 外部数据源报告（联网收集）

> 日期：2026-06-19
> 用途：#94 MDL vs FP 实证 + #95 贝叶斯校准

---

## 已下载并分析

### COMPAS 累犯预测数据集

- **来源：** ProPublica / GitHub
- **URL：** `https://github.com/propublica/compas-analysis`
- **文件：** `data/external/compas_scores_two_years.csv`
- **记录数：** 7,214 条
- **关键字段：** `decile_score`（1-10 风险分）、`two_year_recid`（二元再犯）、`race`、`age_cat`、`sex`
- **校准结果：**
  - Brier score: 0.2295
  - ECE (5 bins): 0.0785
  - COMPAS 对高分（7-10）高估风险（gap -0.11 到 -0.23）
  - COMPAS 对低分（1-3）低估风险（gap +0.08 到 +0.11）

### LegalBench 法律推理基准

- **来源：** Stanford HazyResearch / HuggingFace
- **URL：** `https://huggingface.co/datasets/nguha/legalbench`
- **文件：** `data/external/legalbench/*.json`（11 个任务）
- **记录数：** 2,529 条
- **二元标签任务：** 4 个（consumer_contracts_qa: 396, diversity_6: 300, hearsay: 94, international_citizenship: 500）

---

## 已识别但未下载

| 数据集 | 域 | 记录数 | 法域 | 访问 | 用途 |
|---|---|---|---|---|---|
| CAIL2018 | 刑事 | 260K+ | CN | GitHub（需手动下载） | 中国法律罪名预测校准 |
| JEC-QA | 多域 QA | 26K+ | CN | 学术共享 | 中国法律推理校准 |
| CaseHOLD | 案例法 | 53K+ | US | HuggingFace | 案例法推理校准 |
| LexGLUE | 7 任务 | 数万 | EU/US | HuggingFace | 跨法域 NLP 校准 |
| ECHR/ECtHR | 人权 | 11K+ | EU | HuggingFace | 多标签校准 |
| ILDC | 法院判决 | 35K+ | India | HuggingFace | 二元判决预测 |
| SCOTUS Database | 最高法院 | 8K+ | US | 网站直接下载 | 美国最高法院预测 |
| OpenLaw | 法院案例 | 百万级 | CN | 部分免费 | 中国裁判文书结构化 |
| Pkulaw | 全法律 | 百万级 | CN | 需订阅 | 最高质量中国法律数据 |

---

## 关键发现

1. **COMPAS 是唯一已下载的包含真实预测概率 + 真实结果的数据集。** 它的校准特征（高分高估、低分低估）为 juris-calculus 的校准提供了 baseline 参考。

2. **LegalBench 提供了 4 个二元标签任务**，可用于测试 juris-calculus 推理引擎在不同法律推理类型上的准确率和校准度。

3. **CAIL2018 是最相关的中国法律数据集**（260K+ 刑事案例），但需要通过 GitHub 手动下载（HuggingFace 镜像不可用）。

4. **跨 CN/US/HK 法域映射数据集不存在。** 这是领域空白，juris-calculus 的 `claim_mapping.csv`（44 条）是目前已知的唯一跨 CN/US/HK 结构化映射数据。

---

## 下一步建议

1. 用 COMPAS 做校准方法论验证（已有数据）
2. 用 LegalBench 4 个二元任务做推理引擎基准测试
3. 手动下载 CAIL2018 做中国法律校准（需 GitHub clone）
4. 用 juris-calculus 自有数据（180 claims + 17 proof outcomes）做内部校准
