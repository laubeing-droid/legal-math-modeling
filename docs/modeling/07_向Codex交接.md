# 07 向 Codex 交接：代码提升任务书

日期：2026-06-11

## 1. 当前状态

数学模型已经从早期草稿升级为证据校准版。下一阶段不是继续写证明报告，而是进入代码提升。

## 2. 交接输入

1. `theory\model_status.py`
2. `20260611 kimi proof\strict_math_proof_rework`
3. `20260611kimi\01_legal_validation_experiments`
4. `20260611kimi\JURIS-CALCULUS 数据收集交付包（kimi）\data_collection_delivery`

## 3. 代码提升 P0

1. 实现 `EvidenceStatus` / `TrustLabel`。
2. 拆分 evaluator：
   - `horn_closure`
   - `build_attack_graph`
   - `grounded_extension`
3. 增加 source manifest validator。
4. 增加 pricing data-quality gate。
5. 增加 DP policy loader。

## 4. 不可违反的边界

1. 不得把 toy proof 标成 real proof。
2. 不得把 fee_schedule 标成 real_timesheet。
3. 不得从法律 privilege 自动推出 epsilon。
4. 不得把 original evaluator 称为 monotone。
5. 不得把 Lean draft 称为 Lean proof。

## 5. 验收命令

代码提升后至少要保留以下验证：

```powershell
python -m theory --summary
python run_all_math_proofs.py
python run_legal_validation_experiments.py
```

并新增主工程测试：

1. evaluator nonmonotone counterexample regression；
2. AAF 100 case fixture validation；
3. pricing proxy downgrade test；
4. DP epsilon policy test。

