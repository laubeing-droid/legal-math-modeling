# U07.3 固定历史绑定与实际语义读回关债包：OPEN 10 → 9

本包绑定一次独立 changed-module CI，在固定历史的实际 `sourceModel = .ok out` 条件下，核对被选择的有限解释行、`recordOf` 的 key/claimedAmount/registered、观测关系解释，以及首笔付款的 history key 与完整 payload 语义。两个 `actual_source_model_projection_unique` 观察使用相同背景、材料、分支和目录；它们比较实际成功输出的 paymentFields。另有金额不识别支付事件/义务人的投影反例，以及固定 binding 边界的注释、案例和缺历史 UNKNOWN 例。

- 十二个具名目标的真实类型与公理输出见 `axiom-audit.raw.txt`，只抽 driver 的十二组 `#check` / `#print axioms`，没有把依赖 replay 当成额外目标。
- 模块 run `40771310113` / job `123108948361` 成功；subject 为源码提交 `4b88591bb4f48712adb54c1b40557f0ebcd0c23b`。独立模块构建完成 8552 jobs。
- Artifact `changed-module-only-40771310113-1`，ID `12853086110`，大小 7526 bytes，SHA256 `49f4af9fc0a0614dc4a1a05f4157eee3ac000342ff20006e213590b392a735cc`。逐源文件 SHA256 与目标审计解析见 `verification.json`。
- 十二目标只依赖 `propext`、`Classical.choice`、`Quot.sound` 子集；无 `sorryAx` 或非标准公理。
- `actual_record_and_binding_interpretation` 的 `objectMeaning`、`paymentMeaning` 与被选行解释关系是显式外部条件。它们未被证明可由原始材料自动导出；这不是现实来源真值或任意 extractor 忠实性证明，历史身份 O05 仍开放。反例只说明相同 raw `CaseRecord` 不足以确定不同 catalog 的语义，不否定固定 material/branch/catalog/history 下的绑定唯一性。
- 本包只关闭 archive 中 U07.3 的固定历史绑定/实际连接残余，不关闭原题 07.3 的全部问题、原题 07.5/07.6，也不接通旧 `Final20261021.Pipeline` 调用链。原题进度和消费边状态分别保留其既有 PARTIAL/原状态。

本包是独立模块 CI 与源码绑定回执，不是完整发布验收。全局 `discharges_archived_manuscript_gaps=false`、`math_flip=false`、Step 2 开放，冻结 tip pin 与其余债务保持不变。
