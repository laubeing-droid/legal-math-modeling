读取 program/PLANS.md、PROGRAM_STATE.json 和三个仓库的 AGENTS.md，按照依赖图推进 legal-math-modeling、juris-calculus、Deli AutoResearch 的 Track A-E。

本次运行优先级：
1. Track A 发布真实性：测试口径核查、clean build、AxiomAudit、theorem manifest
2. Track C0 四阶段 no-uncertainty-upgrade
3. Track C1 Horn/Grounded 独立证明证书及 sound checker
4. Track C2/C3 Horn→AAF 参数和攻击保持性 MVM
5. Track B 独立 worktree：完备加权距离、Lw≤qw→ContractingWith、固定点和误差界
6. 在 C1/C4 后推进 Track D 的规则影响和增量 Grounded
7. 仅在前序门禁通过后推进 Track E 最小支撑集/破局集 MVM

执行规则：
- 先读取真实工作树和现有报告，不重复已完成工作
- 每个写 Track 使用独立 worktree
- 同一文件只允许一个 writer
- subagent 只承担只读审计、测试、API 搜索和互不冲突任务
- 每阶段更新 program/PLANS.md 和 PROGRAM_STATE.json
- 每阶段运行验收测试并创建本地 checkpoint
- 禁止 sorry/admit/自定义 axiom/True theorem/削弱命题
- UNKNOWN/TIMEOUT/SKIP fail-closed
- 证书 checker 不得调用主求值器
- 增量验证失败必须 fallback 全量重算
- 不伪造数据、不自动发布、不 force push

失败策略：
- 单项阻塞时保存最小复现、proof state 和日志
- 继续执行不依赖任务
- 不得以外围功能代偿核心门禁
- 不得重新修改已封板的有限单调/AAF/Horn theorem，除非出现真实反例或构建失败

最终合法状态：
- NIGHT_RUN_COMPLETE
- NIGHT_RUN_PARTIAL
- FORMAL_CORE_RELEASED_BANACH_BLOCKED
- PRODUCTION_ASSURANCE_BLOCKED
- FAILED

最终报告必须列出三仓 commit、测试、Lean theorem 状态、AxiomAudit、Banach 状态、certificate 状态、Horn→AAF 保持性状态、增量状态、最小支撑/破局 MVM、所有剩余阻塞及下一可运行任务。
