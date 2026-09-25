PLAN.md
R20 分卷计划：CE2在确认后开写
当前交付与确认门

本次交付两件：CE1第9节中英对齐终稿，以及CE2逐文件分卷计划。生产源码尚未开写；本计划的确认不等于Git推送、CI触发、数据上传或对外法律提交授权。

CE1以当前证据状态写成终稿：已有源码证明体可以按实际前提引用，新增登记及纸面反例不能写成已编译。后续只凭同一subject的新真实证据更新状态，不预填成功。CE1在本次先交付，V10是最终源码发布中对论文母本、证据表和双语文本的整合，不影响源码的优先施工顺序。

分卷与逐文件清单

以下每一卷的链接给出全部当前计划目的文件、仓库、T锚点和具名声明。完整机器清单在registry/PLANNED_FILES.json；原声明和来源身份在registry/SOURCE_OBLIGATIONS.json。

分卷是打包和责任归属，不是逐批删范围，也不是人工等待检查点。共享目的文件只交一份完整正文；跨卷依赖在根manifest中引用。所有基础T目标都有落卷，伴生目标逐来源入账。

卷	内容	基础T主覆盖	当前具体路径数
V01	概率主线完整源码	T37, T38, T39, T40, T41, T42, T43, T44, T45, T46, T47, T48, T49, T50, T51, T52, T55, T64	28
V02	统一法律离散基础与确定计算	T01, T02, T03, T04, T05, T06, T07, T08, T09, T10, T11, T12, T13, T14, T15, T16, T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, T28	37
V03	结构检索、因素—Horn—Dung与谱桥	T56, T57, T58, T59, T60, T61, T62, T63, T65, T87, T91	52
V04	NN三维证书、IG与Banach接线	T66, T67, T68, T69, T70, T71, T72, T73, T74, T75	43
V05	概率时序与十科决策扩展	T76, T77, T78, T79, T80, T81, T82, T83, T84, T85, T86, T88, T89, T90	47
V06	工作台操作语义与四层组合	T92, T93, T94, T95, T96, T97, T98, T99, T100, T101, T102, T103, T104, T109	44
V07	JC运行时、公共合同与精化测试	T29, T30, T31, T32, T53, T54	26
V08	Harness、JusBench桥与实际功能接线	T33, T34, T105, T106	13
V09	全集独立回归、资产覆盖与交付验收	T36, T107, T108, T111	14
V10	论文第9节与声明证据交付	T35, T110	9

路径数和来源记录数仅用于查漏，不是完工证书。新增helper或原仓共享文件必须列入manifest和目标映射，不得以新增文件没有原T号而逃逸验收，也不得为维持计划路径数而砍功能。

优先施工次序，不制造假依赖

概率骨架T38—T55为第一工作主线，连同T37、结构类T42及选择机制T64。遇到真正依赖，深度优先完成其完整源码后再回主线；依赖文件仍归其原卷。不得以任意假设、空函数、sorry或future import让V01看似先通过。

概率核心就绪后，先接JC的实际胜诉率委托及多法域入口，再接原Harness桥；剩余数学、检索、NN、时序、工作台与全栈义务全部按依赖继续，不因优先级被取消。

JC中的两个主spec为multijurisdiction.py与win_model_adapter.py。原R6的record_admission.py、rule_packs.py及tests/test_multijurisdiction_refinement.py全部保留；contracts.py仍是公共合同权威，不另建注册表。

Harness桥接既有实际consumer，JusBench按真实providers、method-policy、功能清单和新增分母接线。若登记路径与实际位置不同，保留登记路径、实际路径及迁移说明，不建平行假入口。

最终同一次附件交付全部源码卷和根manifest，不交“V01已好其余以后”的半包。文件先写入可验证路径，打包、清单与证据检查完成后再给链接。

本计划不承诺后台或跨夜自动运行。确认后的源码生成仍需在实际响应中执行并提交工件。

编译和陈述纪律

数学仓基线b00d3156b20851fa90c459bb8eba282b72bf3578；Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f；Lean v4.30.0。

每个使用到的旧import、完整namespace和声明须对相应固定提交实读；路径猜中不等于API已核。

每个新增Lean头统一为：Status: NOT COMPILED in this response; repo CI (lean-full-clean-build) authoritative。即便后来实际执行校验，保留用户要求的头并由独立回执说明执行范围，不据此预填绿证。

禁sorry、admit、axiom、native_decide；禁把目标结论写成hypothesis；禁以未定义谓词藏前提。可核有限决策证明必须绑定实际对象，不能将结论塞入任意auto/decide输入。

新文件完整源码；既有文件修改交完整修改后文件，diff仅辅助。每个声明绑定原文hash和有效采纳关系；旧文本不静默改写。

相同数学义务的复用可通过真实已证定理及显式映射实现，不复制第二实现；不同语义、范围和权重政策不能以复用之名合并。

构建、python测试、运行时精化与真实数据有效性分别有证。说明NOT COMPILED并不豁免源码完整性要求，也不允许将未完成目标包装为已交付。

对抗测试与golden

保留第五轮原14项代码和原结果原字节，标记为历史结果；新生产测试生成新回执。R6必测项目包括：24%/36%与4×LPR混放、最新文件先读、同版本重复副本、跨2014-08-01、月中部分清偿、清偿换序、ΣQ≠QΣ、除零、版本不默认取新、dom(g)=F。

再合并R7—R19全部负结果及每项登记对抗测试；原测试来源由GOLDEN_SOURCE_INDEX.json定位。不得以同一被测运行器生成golden，不得只验证schema、自报Bool或名字存在。

有限有理量使用精确分数；真实无理端点保存其数学定义和有理外包证据，不能虚称无理数本身为精确分数。CP双Beta、Beta(2,1)四步[1/8,1]、MCS 10、污染6/7≠3/4等已经裁清的金例不随实现漂移。

原包与恢复件

registry/STATEMENT_RESOLUTION.json列出明确裁定的四处同名差异和多稿处理规则。基础T01—T111原文保留；所有伴生来源记录也保留，来源条数不冒充独立定理数。

R14恢复件只有28项索引而缺该版原逐条声明，这是逐字锁定文档缺口，不是重新质疑已经裁清的数学。对照实际答复及原包建立来源映射；未完成映射的项不得宣称CE2逐字验收通过。其他真实材料不可见时，相关数据验证保持未执行，而不是删除功能。

最终CE2每文件manifest字段

repository, path, volume, source_sha256, T_ids, source_obligation_ids, frozen_statement_sha256, declaration_namespace, statement_resolution, imports_verified_at, existing_declarations_verified_at, assumptions, adversarial_tests, golden_sources, registration_state, proof_state, compilation_state, runtime_refinement_state, empirical_state, delivery_state。

根manifest记录全部卷的字节摘要和文件集合；集成检查要求无悬空路径、无遗漏基础目标、无未处置伴生义务、无重复消费造成虚增覆盖，且真实测试/构建回执与同一源版本对应。

全部满足才称全集交付。做不到的项单列“未交付＋原因”，不得拿计划本身或者声明数量补证。

本次自检结论

CE1双语正文已落盘；分卷文件表、原始声明副本、来源变体和规划脚本已落盘。T01—T111全部具有计划归属，不等于实现。没有写入生产源码、执行Lean、触发CI或提交仓库。详见reports/PLAN_CHECK.json与reports/UNDELIVERED_AND_GAPS.md。