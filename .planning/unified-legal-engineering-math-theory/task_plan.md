# 本轮任务计划：编制独立施工方案

## 目标

在 `docs/theory/统一法律工程数学理论施工方案.md` 交付一份独立、详尽、可执行的施工方案；内部 `task_plan.md` 只记录本轮编制进度。

## 当前阶段

Phase 3：正式施工文档复核与交付（完成）。

## Phases

### Phase 1：事实与边界盘点

- [x] 定位 LMM 实际 Git 根与仓库规则
- [x] 清点现有 Lean、Python、CI 与证明证书链
- [x] 固定 theory/JC 两外部仓库为只读输入
- **Status:** complete

### Phase 2：独立施工方案编制

- [x] 写入 T01—T19 工作包
- [x] 写入 C01—C04 P0 组合定理
- [x] 写入文件清单、施工 DAG、验证门、回滚和完成标准
- [x] 将正文放入独立 `docs/theory/统一法律工程数学理论施工方案.md`
- **Status:** complete

### Phase 3：复核与交付

- [x] 从磁盘回读独立施工方案
- [x] 检查四条用户指定组合定理存在
- [x] 检查不含全实现/全链条证明偷换
- [x] 检查本轮只改计划与文档文件
- **Status:** complete

## 本轮非目标

- 不实现 Lean/Python 理论代码。
- 不修改 theory/JC 两外部仓库。
- 不运行 Lean、不 push、不 dispatch CI、不 commit。

## 错误记录

| 错误 | 次数 | 处理 |
|---|---:|---|
| 初次把正式施工正文写入内部 `task_plan.md` | 1 | 已迁到独立 `docs/theory/统一法律工程数学理论施工方案.md`，内部文件恢复为进度用途 |
| JC 形式边界路径误写 | 1 | 已定位为 `docs/contracts/` |
| theory proof ledger 预期路径不存在 | 1 | 已改读实际 R7/R14 汇总 |
