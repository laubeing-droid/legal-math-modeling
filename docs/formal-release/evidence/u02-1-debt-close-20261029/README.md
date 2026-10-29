# U02.1 实际 Pipeline 精化关债包：OPEN 9 → 8

本包绑定独立 changed-module CI 对固定源码提交的真实结果。新的具名证明把实际公开 `Pipeline.run` 的成功付款绑定、检查后的动作、Bool 世界动作表与已报告后态连接起来；对报告的具体后态证明原 `Trace.Invariant` 保持，并将投影为 successor 表中的 `true`。开账非负前提沿用冻结总稿 §14 的 `d0 ≥ 0`。有限反例保留 schema/norm、检查动作/执行动作和规范版本变化造成旧证据失效的区别，并保留共同 idle 与空后继边界。

- 本次独立审计的 12 个真实 `#check` / `#print axioms` 输出只见 `axiom-audit.raw.txt`；没有把依赖回放计作目标。
- Run `40791067212` / job `123176137083` 对提交 `1bd8db47b728249fe240312fc5e570ce7290b62a` 的 changed-module 构建成功（8511 jobs）。Artifact `changed-module-only-40791067212-1`，ID `12861283251`，ZIP SHA256 `20cbbe172c3bc787c6daf13f479612eb010bc006fb3148e87b2fdc9b603f2152`。五个实际源文件的哈希见 `verification.json`。
- 12 个目标只依赖标准 `propext`、`Classical.choice`、`Quot.sound`；没有 `sorryAx`。
- 结论依赖原稿 d0 非负条件、有限 Bool 世界和所给动作表；证明不从材料推导现实世界的允许域或动作表。它只涵盖带有具体已报告后态的运行，不为没有已知后态的 `unknownCommit` 声称不变量结果，也不表示已部署。
- 本包只关闭 U02.1 的冻结条件命题及其逐段要求；保留全局 discharges/math flip/Step 2 未关闭及冻结 tip pin。它不是全仓或现实法律验收。
