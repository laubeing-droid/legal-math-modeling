# D001–D134：完整原需求、形式目标及七轴映射

以下全部是独立业务需求的待实例化义务；编号保留，不代表已证明。

## D001｜咨询属于什么法律主题，是否存在多个并列问题？

分组：01 接案、问题与主体识别。原评测：CN01, CN02, CN03。

输入：用户问题、案情、合同及文书

输出：主体/案由/争点候选及定位

形式目标：topics(out)⊆Topics_scope；每个已确认并列争点有唯一需求对象，未分类段落进入residual

前提：议题分类表与范围由任务与法律研究确定，不能由分类器输出自定

外部验证：自然语言多议题召回及误分类率

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明

反例：同一咨询含欠款与名誉请求，不能因主主题只报一个

任务：EXT09, REV02, ROOT02, ROOT03, ROOT06, ROOT08, T01, T02, T03, T22, T24；证明族：M01, M04, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=topics(out)⊆Topics_scope；每个已确认并列争点有唯一需求对象，未分类段落进入residual

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=议题分类表与范围由任务与法律研究确定，不能由分类器输出自定；sources=https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1
https://github.com/Dai-shen/LAiW/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=自然语言多议题召回及误分类率

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=主体/案由/争点候选及定位；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=漏附件、跨页引用、修订痕迹、同名主体与证据地位必须保留；counterexample=同一咨询含欠款与名誉请求，不能因主主题只报一个

来源（原表范围）：
https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1
https://github.com/Dai-shen/LAiW/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D002｜材料反映民事还是刑事性质，标签是否足以支持该判断？

分组：01 接案、问题与主体识别。原评测：CN01, CN02, CN03。

输入：用户问题、案情、合同及文书

输出：主体/案由/争点候选及定位

形式目标：route(s)允许民事、刑事、并行或待定；分类不得自动改变准入事实

前提：法域/阶段及竞合路由政策明确；民刑不是互斥穷尽标签

外部验证：案情性质判断需法律审核

证明路线：文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收

反例：同一行为同时涉民事责任与犯罪线索，不强制二选一

任务：EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T16, T17, T18, T19, T22, T24；证明族：M04, M07, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=route(s)允许民事、刑事、并行或待定；分类不得自动改变准入事实

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=法域/阶段及竞合路由政策明确；民刑不是互斥穷尽标签；sources=https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1
https://github.com/Dai-shen/LAiW/blob/main/README.md

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=案情性质判断需法律审核

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=主体/案由/争点候选及定位；proof_route=文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=漏附件、跨页引用、修订痕迹、同名主体与证据地位必须保留；counterexample=同一行为同时涉民事责任与犯罪线索，不强制二选一

来源（原表范围）：
https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1
https://github.com/Dai-shen/LAiW/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D003｜谁是原告、被告、承包人、借款人、保证人或非诉交易主体？

分组：01 接案、问题与主体识别。原评测：CN01, CN02, CN03。

输入：用户问题、案情、合同及文书

输出：主体/案由/争点候选及定位

形式目标：Role(person,matter,stage)的每个绑定都有出处；主体、角色、名称为不同类型

前提：经核对的身份依据与文本角色解释

外部验证：同名人物、代表人及角色抽取

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明

反例：法定代表人签字不得自动变成其个人承担全部公司债务

任务：EXT09, REV02, ROOT02, ROOT03, ROOT06, ROOT08, T01, T02, T03, T22, T24；证明族：M01, M04, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=Role(person,matter,stage)的每个绑定都有出处；主体、角色、名称为不同类型

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=经核对的身份依据与文本角色解释；sources=https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1
https://github.com/Dai-shen/LAiW/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=同名人物、代表人及角色抽取

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=主体/案由/争点候选及定位；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=漏附件、跨页引用、修订痕迹、同名主体与证据地位必须保留；counterexample=法定代表人签字不得自动变成其个人承担全部公司债务

来源（原表范围）：
https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1
https://github.com/Dai-shen/LAiW/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D004｜同一案件中每名被告对应哪些行为、罪名及处分？

分组：01 接案、问题与主体识别。原评测：CN07, CN10。

输入：用户问题、案情、合同及文书

输出：主体/案由/争点候选及定位

形式目标：逐被告结果图的边均保留同一actor_id、行为集合和案件；整案正确=所有必查映射正确

前提：参与、共同犯罪及归责规则另行准入

外部验证：行为人与行为对应是否真实

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：交换两被告刑期而整案平均不变，检查仍须失败

任务：EXT03, EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T05, T06, T16, T17, T18, T19, T22, T24；证明族：M01, M06, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=逐被告结果图的边均保留同一actor_id、行为集合和案件；整案正确=所有必查映射正确

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=参与、共同犯罪及归责规则另行准入；sources=https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=行为人与行为对应是否真实

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=主体/案由/争点候选及定位；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=漏附件、跨页引用、修订痕迹、同名主体与证据地位必须保留；counterexample=交换两被告刑期而整案平均不变，检查仍须失败

来源（原表范围）：
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D005｜公司全称、简称、曾用名与登记代码能否一致解析？

分组：01 接案、问题与主体识别。原评测：CN04。

输入：用户问题、案情、合同及文书

输出：主体/案由/争点候选及定位

形式目标：对固定登记快照，规范主体键连接和别名解析与独立查表语义相同

前提：统一代码、别名有效期、实体合并依据已核对

外部验证：登记数据更新与错误修复

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；法源query与原文回读已有工程；固定语料与适用法域完整性另证

反例：同名异码不合并；更名前后同码按时间处理

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T03, T20, T22, T24；证明族：M01, M02, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=对固定登记快照，规范主体键连接和别名解析与独立查表语义相同

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=统一代码、别名有效期、实体合并依据已核对；sources=https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=登记数据更新与错误修复

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=主体/案由/争点候选及定位；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=漏附件、跨页引用、修订痕迹、同名主体与证据地位必须保留；counterexample=同名异码不合并；更名前后同码按时间处理

来源（原表范围）：
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D006｜自然人、公司、关联方与代表人是否被混同？

分组：01 接案、问题与主体识别。原评测：CN04, CN11。

输入：用户问题、案情、合同及文书

输出：主体/案由/争点候选及定位

形式目标：自然人、法人、关联、代表关系不等同于身份相等；责任边须经明确规则生成

前提：人格、代理及穿透规则经法律解释

外部验证：共同地址/股东事实与人格混同评价

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：两公司同地址不能由等号传播成同一债务人

任务：EXT04, EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T09, T22, T24；证明族：M01, M11, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=自然人、法人、关联、代表关系不等同于身份相等；责任边须经明确规则生成

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=人格、代理及穿透规则经法律解释；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=共同地址/股东事实与人格混同评价

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=主体/案由/争点候选及定位；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=漏附件、跨页引用、修订痕迹、同名主体与证据地位必须保留；counterexample=两公司同地址不能由等号传播成同一债务人

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D007｜法院代字、法院级别与管辖机关信息如何关联？

分组：01 接案、问题与主体识别。原评测：CN04。

输入：用户问题、案情、合同及文书

输出：主体/案由/争点候选及定位

形式目标：法院代字到机构和级别的查表结果正确；管辖判断使用另外的适用规则

前提：机构有效期、管辖法源与事件地等前提已准入

外部验证：机构数据及时性与事实地点

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；法源query与原文回读已有工程；固定语料与适用法域完整性另证；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收

反例：正确解析法院代字不等于该法院有管辖权

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T03, T16, T17, T18, T19, T20, T22, T24；证明族：M01, M02, M07, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=法院代字到机构和级别的查表结果正确；管辖判断使用另外的适用规则

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=机构有效期、管辖法源与事件地等前提已准入；sources=https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=机构数据及时性与事实地点

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=主体/案由/争点候选及定位；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=漏附件、跨页引用、修订痕迹、同名主体与证据地位必须保留；counterexample=正确解析法院代字不等于该法院有管辖权

来源（原表范围）：
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D008｜某项请求针对谁、要求什么救济，而不是只提取关键词？

分组：01 接案、问题与主体识别。原评测：CN14, CN15。

输入：用户问题、案情、合同及文书

输出：主体/案由/争点候选及定位

形式目标：Claim=(claimant,respondent,basis,object,remedy,scope)；保留请求之间关联与差异

前提：谁主张对谁以及救济对象已确定或显式假设

外部验证：诉求理解与最优请求选择

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：本金请求与担保责任请求不得共用无主体的金额字段

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T16, T17, T18, T19, T22, T24；证明族：M01, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=Claim=(claimant,respondent,basis,object,remedy,scope)；保留请求之间关联与差异

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=谁主张对谁以及救济对象已确定或显式假设；sources=https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=诉求理解与最优请求选择

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=主体/案由/争点候选及定位；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=漏附件、跨页引用、修订痕迹、同名主体与证据地位必须保留；counterexample=本金请求与担保责任请求不得共用无主体的金额字段

来源（原表范围）：
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D009｜指定法律概念和法条内容是什么，能否准确回到原文？

分组：02 法源、解释与类案研究。原评测：CN01, CN02, US03。

输入：规范查询、事实情景、法条与候选案例

输出：来源明确的候选依据/引用/相关性

形式目标：quoted_span=source[start:end]；概念答案每个受保护命题绑定可回读出处

前提：正式版本、定义范围和引文转码政策已选定

外部验证：原文语义支持不是字节相等可独证

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明

反例：真实引文但引用错版本，版本检查须拒绝

任务：EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T20, T22, T24；证明族：M02, M04, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=quoted_span=source[start:end]；概念答案每个受保护命题绑定可回读出处

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=正式版本、定义范围和引文转码政策已选定；sources=https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1
https://hazyresearch.stanford.edu/legalbench/tasks/

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=原文语义支持不是字节相等可独证

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=来源明确的候选依据/引用/相关性；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=Top-k未命中不能推出法律不存在；金标对应历史版本与当前法重分析分轨；counterexample=真实引文但引用错版本，版本检查须拒绝

来源（原表范围）：
https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1
https://hazyresearch.stanford.edu/legalbench/tasks/

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D010｜给定事实或场景涉及哪些法条，而非只给相似词？

分组：02 法源、解释与类案研究。原评测：CN01, CN02, US03。

输入：规范查询、事实情景、法条与候选案例

输出：来源明确的候选依据/引用/相关性

形式目标：结果在已冻结规则库及候选解释中满足适用谓词；全适用声称需独立候选覆盖

前提：规则与事实适用关系被明确编译

外部验证：规则库之外的遗漏与文本解释

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：只召回相似法条不能签全部适用法条证书

任务：EXT03, EXT09, ROOT06, ROOT08, T01, T03, T05, T06, T16, T17, T18, T19, T20, T22, T24；证明族：M02, M06, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=结果在已冻结规则库及候选解释中满足适用谓词；全适用声称需独立候选覆盖

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=规则与事实适用关系被明确编译；sources=https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1
https://hazyresearch.stanford.edu/legalbench/tasks/

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=规则库之外的遗漏与文本解释

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=来源明确的候选依据/引用/相关性；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=Top-k未命中不能推出法律不存在；金标对应历史版本与当前法重分析分轨；counterexample=只召回相似法条不能签全部适用法条证书

来源（原表范围）：
https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1
https://hazyresearch.stanford.edu/legalbench/tasks/

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D011｜规则是否发生变更，题目考查的是哪个历史版本？

分组：02 法源、解释与类案研究。原评测：CN02, US01。

输入：规范查询、事实情景、法条与候选案例

输出：来源明确的候选依据/引用/相关性

形式目标：Applicable(v,eventTime,stage,transitionRule)；法效时间与登记时间分别保存

前提：过渡条款、溯及力和持续事件政策明确

外部验证：官方修订和废止状态核验

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：后上传旧文本不得按新上传日期当新法

任务：EXT09, ROOT06, ROOT08, T01, T03, T08, T20, T22, T24；证明族：M02, M10, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=Applicable(v,eventTime,stage,transitionRule)；法效时间与登记时间分别保存

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=过渡条款、溯及力和持续事件政策明确；sources=https://arxiv.org/html/2409.20288v1
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=官方修订和废止状态核验

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=来源明确的候选依据/引用/相关性；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=Top-k未命中不能推出法律不存在；金标对应历史版本与当前法重分析分轨；counterexample=后上传旧文本不得按新上传日期当新法

来源（原表范围）：
https://arxiv.org/html/2409.20288v1
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D012｜定义词、上下文与跨条引用怎样改变条款含义？

分组：02 法源、解释与类案研究。原评测：US03, US04, US05。

输入：规范查询、事实情景、法条与候选案例

输出：来源明确的候选依据/引用/相关性

形式目标：限定词、定义作用域与引用图的解释器保持语义；递归引用有明确不动点或拒绝路径

前提：引用目标和例外解释经登记

外部验证：语言歧义和隐含引用识别

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：定义中排除关联方，主文不得重新无条件纳入

任务：EXT04, EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T09, T16, T17, T18, T19, T22, T24；证明族：M03, M04, M11, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=限定词、定义作用域与引用图的解释器保持语义；递归引用有明确不动点或拒绝路径

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=引用目标和例外解释经登记；sources=https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://hazyresearch.stanford.edu/legalbench/tasks/

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=语言歧义和隐含引用识别

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=来源明确的候选依据/引用/相关性；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=Top-k未命中不能推出法律不存在；金标对应历史版本与当前法重分析分轨；counterexample=定义中排除关联方，主文不得重新无条件纳入

来源（原表范围）：
https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://hazyresearch.stanford.edu/legalbench/tasks/

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D013｜哪件类案在定性、量刑或程序问题上相关？

分组：02 法源、解释与类案研究。原评测：CN08。

输入：规范查询、事实情景、法条与候选案例

输出：来源明确的候选依据/引用/相关性

形式目标：固定争点/语义下排序与指定score一致；类案迁移需相关特征保留见证

前提：相关性维度、案件事实和规则解释固定

外部验证：人工相关标签、外推与类比质量

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；V2.1概率/胜率参考与保留时间切分；真实经验效果、因果识别及EXT保证未整体验收

反例：程序上相关但实体事实不同，不复制实体结论

任务：EXT03, EXT06, EXT07, EXT09, ROOT06, ROOT08, T01, T03, T05, T06, T12, T13, T14, T15, T20, T22, T24；证明族：M02, M06, M12, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=固定争点/语义下排序与指定score一致；类案迁移需相关特征保留见证

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=相关性维度、案件事实和规则解释固定；sources=https://github.com/THUIR/LeCaRDv2/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=人工相关标签、外推与类比质量

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=来源明确的候选依据/引用/相关性；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=Top-k未命中不能推出法律不存在；金标对应历史版本与当前法重分析分轨；counterexample=程序上相关但实体事实不同，不复制实体结论

来源（原表范围）：
https://github.com/THUIR/LeCaRDv2/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D014｜固定候选池重排与全库检索分别找到了什么、漏了什么？

分组：02 法源、解释与类案研究。原评测：CN08。

输入：规范查询、事实情景、法条与候选案例

输出：来源明确的候选依据/引用/相关性

形式目标：Returned⊆Relevant_D；只有覆盖D并完成判定才可声称Returned=Relevant_D

前提：固定语料全集及独立相关性定义

外部验证：开放网页和人工未标相关性的召回

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证

反例：100项pool全命中不能改写成全库无遗漏

任务：EXT09, ROOT06, ROOT08, T01, T03, T20, T22, T24；证明族：M02, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=Returned⊆Relevant_D；只有覆盖D并完成判定才可声称Returned=Relevant_D

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=固定语料全集及独立相关性定义；sources=https://github.com/THUIR/LeCaRDv2/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=开放网页和人工未标相关性的召回

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=来源明确的候选依据/引用/相关性；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=Top-k未命中不能推出法律不存在；金标对应历史版本与当前法重分析分轨；counterexample=100项pool全命中不能改写成全库无遗漏

来源（原表范围）：
https://github.com/THUIR/LeCaRDv2/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D015｜所引案例是否真的支持当前命题，能否准确定位引用？

分组：02 法源、解释与类案研究。原评测：US01, US03。

输入：规范查询、事实情景、法条与候选案例

输出：来源明确的候选依据/引用/相关性

形式目标：每个引用命题保留span与已核准语义支持边；支持图闭合后才可升级声明

前提：来源解释/蕴涵见证获得独立审核或受限语言证明

外部验证：任意自然语言是否支持论点

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭

反例：案号真实但只支持相反观点，不准当正向依据

任务：EXT03, EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T05, T06, T20, T22, T24；证明族：M02, M04, M06, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=每个引用命题保留span与已核准语义支持边；支持图闭合后才可升级声明

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=来源解释/蕴涵见证获得独立审核或受限语言证明；sources=https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=任意自然语言是否支持论点

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=来源明确的候选依据/引用/相关性；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=Top-k未命中不能推出法律不存在；金标对应历史版本与当前法重分析分轨；counterexample=案号真实但只支持相反观点，不准当正向依据

来源（原表范围）：
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D016｜判例被推翻或限制时，原引文还能否支撑结论？

分组：02 法源、解释与类案研究。原评测：US03。

输入：规范查询、事实情景、法条与候选案例

输出：来源明确的候选依据/引用/相关性

形式目标：先例效力图与引用时点关联；过时支持路径失效并重新计算受影响结论

前提：推翻/限制的范围、法域和争点由法源解释

外部验证：判例效力材料是否齐全

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：推翻一个争点不得删除该案所有无关论点，亦不得保留被推翻点

任务：EXT09, ROOT06, ROOT08, T01, T03, T08, T16, T17, T18, T19, T20, T22, T24；证明族：M02, M03, M10, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=先例效力图与引用时点关联；过时支持路径失效并重新计算受影响结论

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=推翻/限制的范围、法域和争点由法源解释；sources=https://hazyresearch.stanford.edu/legalbench/tasks/

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=判例效力材料是否齐全

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=来源明确的候选依据/引用/相关性；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=Top-k未命中不能推出法律不存在；金标对应历史版本与当前法重分析分轨；counterexample=推翻一个争点不得删除该案所有无关论点，亦不得保留被推翻点

来源（原表范围）：
https://hazyresearch.stanford.edu/legalbench/tasks/

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D017｜应适用普通法还是UCC等特别法律框架？

分组：02 法源、解释与类案研究。原评测：US03。

输入：规范查询、事实情景、法条与候选案例

输出：来源明确的候选依据/引用/相关性

形式目标：LegalFramework候选按管辖、标的、冲突法及适用条件筛选，保留未决分支

前提：普通法/UCC等适用条件准入

外部验证：混合合同性质的法律判断

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：不能按英文合同或美国当事人自动选UCC

任务：EXT09, ROOT06, ROOT08, T01, T03, T16, T17, T18, T19, T20, T22, T24；证明族：M02, M03, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=LegalFramework候选按管辖、标的、冲突法及适用条件筛选，保留未决分支

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=普通法/UCC等适用条件准入；sources=https://hazyresearch.stanford.edu/legalbench/tasks/

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=混合合同性质的法律判断

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=来源明确的候选依据/引用/相关性；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=Top-k未命中不能推出法律不存在；金标对应历史版本与当前法重分析分轨；counterexample=不能按英文合同或美国当事人自动选UCC

来源（原表范围）：
https://hazyresearch.stanford.edu/legalbench/tasks/

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D018｜不同法域并购申报规则如何比较并保留法域区别？

分组：02 法源、解释与类案研究。原评测：US02。

输入：规范查询、事实情景、法条与候选案例

输出：来源明确的候选依据/引用/相关性

形式目标：跨法域比较保持每个域的主体/阈值/时间/效果；无保持映射则返回差异见证

前提：各域源与比较维度已核验

外部验证：无损迁移或制度等同性的开放判断

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；法源query与原文回读已有工程；固定语料与适用法域完整性另证；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：将申报门槛相同误当申报后果相同须被区分

任务：EXT04, EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T03, T09, T20, T22, T24；证明族：M01, M02, M11, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=跨法域比较保持每个域的主体/阈值/时间/效果；无保持映射则返回差异见证

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=各域源与比较维度已核验；sources=https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=无损迁移或制度等同性的开放判断

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=来源明确的候选依据/引用/相关性；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=Top-k未命中不能推出法律不存在；金标对应历史版本与当前法重分析分轨；counterexample=将申报门槛相同误当申报后果相同须被区分

来源（原表范围）：
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D019｜文本中发生了哪些法律事件，其触发词和范围在哪里？

分组：03 证据内容、事件与冲突。原评测：CN09, CN10, CN11, US01。

输入：法律文本、邮件、通话/证言、附件

输出：事件/句级依据/时间线/冲突清单

形式目标：Event(type,actors,object,span)均回指原文；标签映射无碰撞

前提：事件schema和分词/跨度规范冻结

外部验证：触发词识别召回与事件理解

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明

反例：触发词来自引述假设，不得变成已发生事件

任务：EXT09, REV02, ROOT02, ROOT03, ROOT06, ROOT08, T01, T02, T03, T22, T24；证明族：M01, M04, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=Event(type,actors,object,span)均回指原文；标签映射无碰撞

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=事件schema和分词/跨度规范冻结；sources=https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=触发词识别召回与事件理解

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=事件/句级依据/时间线/冲突清单；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=首个被害人占位不能变真实责任边；跨扩展结论不得拼接；counterexample=触发词来自引述假设，不得变成已发生事件

来源（原表范围）：
https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D020｜事件参与人、对象与案件阶段是否对应正确？

分组：03 证据内容、事件与冲突。原评测：CN09, CN10, CN11, US01。

输入：法律文本、邮件、通话/证言、附件

输出：事件/句级依据/时间线/冲突清单

形式目标：事件参与人、对象、法律阶段与证据地位逐边绑定

前提：角色关系与阶段政策已确认

外部验证：多主体指代消解

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明

反例：前案被害人不得由位置默认绑定到本案

任务：EXT09, REV02, ROOT02, ROOT03, ROOT06, ROOT08, T01, T02, T03, T16, T17, T18, T19, T22, T24；证明族：M01, M03, M04, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=事件参与人、对象、法律阶段与证据地位逐边绑定

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=角色关系与阶段政策已确认；sources=https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=多主体指代消解

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=事件/句级依据/时间线/冲突清单；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=首个被害人占位不能变真实责任边；跨扩展结论不得拼接；counterexample=前案被害人不得由位置默认绑定到本案

来源（原表范围）：
https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D021｜多份材料能否组成有出处的时间线，而非补写不存在的日期？

分组：03 证据内容、事件与冲突。原评测：CN09, CN10, CN11, US01。

输入：法律文本、邮件、通话/证言、附件

输出：事件/句级依据/时间线/冲突清单

形式目标：明确日期形成偏序；无日期标为区间/未知，输出时间线为有效拓扑排序

前提：时区、日期解释、先后证据规则明确

外部验证：事件日期与先后关系提取

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：没有时间的事件不凭叙述顺序补造精确日期

任务：EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T08, T16, T17, T18, T19, T20, T22, T24；证明族：M03, M04, M10, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=明确日期形成偏序；无日期标为区间/未知，输出时间线为有效拓扑排序

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=时区、日期解释、先后证据规则明确；sources=https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=事件日期与先后关系提取

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=事件/句级依据/时间线/冲突清单；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=首个被害人占位不能变真实责任边；跨扩展结论不得拼接；counterexample=没有时间的事件不凭叙述顺序补造精确日期

来源（原表范围）：
https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D022｜陈述、邮件和记录之间有哪些实质矛盾或含混？

分组：03 证据内容、事件与冲突。原评测：CN09, CN10, CN11, US01。

输入：法律文本、邮件、通话/证言、附件

输出：事件/句级依据/时间线/冲突清单

形式目标：给出矛盾需明确命题、同一主体/时间及不相容见证；含混保留多解释

前提：Contrary关系和共同语境已定义

外部验证：冲突发现召回与语用解释

证明路线：文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：两个不同时点地址不能自动判为同一时点矛盾

任务：EXT03, EXT04, EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T05, T06, T09, T22, T24；证明族：M04, M06, M11, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=给出矛盾需明确命题、同一主体/时间及不相容见证；含混保留多解释

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=Contrary关系和共同语境已定义；sources=https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=冲突发现召回与语用解释

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=事件/句级依据/时间线/冲突清单；proof_route=文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=首个被害人占位不能变真实责任边；跨扩展结论不得拼接；counterexample=两个不同时点地址不能自动判为同一时点矛盾

来源（原表范围）：
https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D023｜哪些结论缺少直接材料，哪些只是文书没有记载？

分组：03 证据内容、事件与冲突。原评测：CN09, CN10, CN11, US01。

输入：法律文本、邮件、通话/证言、附件

输出：事件/句级依据/时间线/冲突清单

形式目标：missing_support(q)不推出¬q；无记录与否定证据构造分开

前提：只在声明的完整记录范围内允许负查询

外部验证：现实证据是否存在与可取得

证明路线：文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；现有依赖/增量复用；EXT05替代来源与支持反链仍为深化目标；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收

反例：材料未附付款凭证不得推出肯定未付款

任务：EXT05, EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T04, T16, T17, T18, T19, T22, T24；证明族：M04, M05, M07, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=missing_support(q)不推出¬q；无记录与否定证据构造分开

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=只在声明的完整记录范围内允许负查询；sources=https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=现实证据是否存在与可取得

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=事件/句级依据/时间线/冲突清单；proof_route=文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=首个被害人占位不能变真实责任边；跨扩展结论不得拼接；counterexample=材料未附付款凭证不得推出肯定未付款

来源（原表范围）：
https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D024｜回答是否能定位到支持该答案的原句？

分组：03 证据内容、事件与冲突。原评测：CN09, CN10, CN11, US01。

输入：法律文本、邮件、通话/证言、附件

输出：事件/句级依据/时间线/冲突清单

形式目标：每个答案的支持片段存在、边界合法且链到对应命题；冗余支持可保留

前提：自然语言支持判断已审核或受限解释器可判定

外部验证：标注忠实性及遗漏支持

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；现有依赖/增量复用；EXT05替代来源与支持反链仍为深化目标

反例：给正确答案但引用无关原句，不通过支持检查

任务：EXT05, EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T04, T20, T22, T24；证明族：M02, M04, M05, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=每个答案的支持片段存在、边界合法且链到对应命题；冗余支持可保留

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=自然语言支持判断已审核或受限解释器可判定；sources=https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=标注忠实性及遗漏支持

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=事件/句级依据/时间线/冲突清单；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=首个被害人占位不能变真实责任边；跨扩展结论不得拼接；counterexample=给正确答案但引用无关原句，不通过支持检查

来源（原表范围）：
https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D025｜“是”“否”“不知道”是否保持区别？

分组：03 证据内容、事件与冲突。原评测：CN09, CN10, CN11, US01。

输入：法律文本、邮件、通话/证言、附件

输出：事件/句级依据/时间线/冲突清单

形式目标：true/false/unknown/conflict（或现有状态的等价投影）不互相强转

前提：否定形式、开放/闭世界范围明确

外部验证：实际认定可靠性

证明路线：文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收

反例：unknown进if分支当False产生否定结论须拦截

任务：EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T16, T17, T18, T19, T22, T24；证明族：M04, M07, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=true/false/unknown/conflict（或现有状态的等价投影）不互相强转

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=否定形式、开放/闭世界范围明确；sources=https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=实际认定可靠性

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=事件/句级依据/时间线/冲突清单；proof_route=文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=首个被害人占位不能变真实责任边；跨扩展结论不得拼接；counterexample=unknown进if分支当False产生否定结论须拦截

来源（原表范围）：
https://github.com/thunlp/LEVEN/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D026｜记录中的主张、证据内容与法院认定是否被区分？

分组：03 证据内容、事件与冲突。原评测：CN11, CN13。

输入：法律文本、邮件、通话/证言、附件

输出：事件/句级依据/时间线/冲突清单

形式目标：asserted/evidenceContent/adjudicated分别带来源和用途；不得隐式升格

前提：机构认定有效使用范围和本地分析权限

外部验证：证据真实与机构身份核验

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收

反例：原告诉称不得经摘要变成法院查明

任务：EXT09, REV02, ROOT02, ROOT03, ROOT06, ROOT08, T01, T02, T03, T16, T17, T18, T19, T22, T24；证明族：M01, M04, M07, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=asserted/evidenceContent/adjudicated分别带来源和用途；不得隐式升格

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=机构认定有效使用范围和本地分析权限；sources=https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=证据真实与机构身份核验

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=事件/句级依据/时间线/冲突清单；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=首个被害人占位不能变真实责任边；跨扩展结论不得拼接；counterexample=原告诉称不得经摘要变成法院查明

来源（原表范围）：
https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D027｜现有文本事实能否支持拟写的审理事实段？

分组：03 证据内容、事件与冲突。原评测：CN13。

输入：法律文本、邮件、通话/证言、附件

输出：事件/句级依据/时间线/冲突清单

形式目标：事实段的受保护命题包含于准入事实或明确条件语义；保留未决项

前提：被保护命题提取与模板投影明确定义

外部验证：自由叙事是否漏义、误义

证明路线：文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；现有依赖/增量复用；EXT05替代来源与支持反链仍为深化目标；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：把未确认行为改写为既成事实应使语义差量失败

任务：EXT05, EXT09, ROOT03, ROOT05, ROOT06, ROOT08, T01, T03, T04, T22, T24；证明族：M04, M05, M13, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=事实段的受保护命题包含于准入事实或明确条件语义；保留未决项

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=被保护命题提取与模板投影明确定义；sources=https://github.com/CSHaitao/CaseGen/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=自由叙事是否漏义、误义

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=事件/句级依据/时间线/冲突清单；proof_route=文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=首个被害人占位不能变真实责任边；跨扩展结论不得拼接；counterexample=把未确认行为改写为既成事实应使语义差量失败

来源（原表范围）：
https://github.com/CSHaitao/CaseGen/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D028｜是否把前科、其他案件与本次被诉事实混在一起？

分组：03 证据内容、事件与冲突。原评测：CN12。

输入：法律文本、邮件、通话/证言、附件

输出：事件/句级依据/时间线/冲突清单

形式目标：每个行为带case/event作用域；历史经历只能经指定规则进入本次分析

前提：前科和本案归责作用明确

外部验证：跨段指代与案情核验

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明

反例：过去抢劫经历不能直接加入本次危险驾驶罪名清单

任务：EXT09, REV02, ROOT02, ROOT03, ROOT06, ROOT08, T01, T02, T03, T16, T17, T18, T19, T22, T24；证明族：M01, M03, M04, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=每个行为带case/event作用域；历史经历只能经指定规则进入本次分析

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=前科和本案归责作用明确；sources=https://github.com/oneal2000/JuDGE/blob/main/README.md

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=跨段指代与案情核验

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=事件/句级依据/时间线/冲突清单；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=首个被害人占位不能变真实责任边；跨扩展结论不得拼接；counterexample=过去抢劫经历不能直接加入本次危险驾驶罪名清单

来源（原表范围）：
https://github.com/oneal2000/JuDGE/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D029｜从原告事实可以拟出哪些诉讼请求，主给付与附随费用如何分开？

分组：04 请求权、抗辩及争点处理。原评测：CN03, CN11, CN14, CN15。

输入：原告事实、请求、被告抗辩与材料

输出：请求集合/抗辩/问题链及依据

形式目标：请求候选=给定事实与规则允许的remedy组合；主给付/附随费保持独立债项

前提：请求基础、并列/备位及费用政策准入

外部验证：诉请策略、文本到请求理解

证明路线：请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：互斥备位请求不能默认同时全额受偿

任务：EXT04, EXT09, ROOT05, ROOT06, ROOT08, T01, T09, T16, T17, T18, T19, T22, T24；证明族：M08, M11, M13, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=请求候选=给定事实与规则允许的remedy组合；主给付/附随费保持独立债项

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=请求基础、并列/备位及费用政策准入；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=诉请策略、文本到请求理解

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=请求集合/抗辩/问题链及依据；proof_route=请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=互斥备位请求不能默认同时全额受偿

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D030｜实际提出的诉请与依法可能获得支持的请求是否区分？

分组：04 请求权、抗辩及争点处理。原评测：CN03, CN11, CN14, CN15。

输入：原告事实、请求、被告抗辩与材料

输出：请求集合/抗辩/问题链及依据

形式目标：FiledClaims、AllowedClaims、SupportedClaims、AwardedClaims为不同对象并显式连接

前提：阶段与所问集合明确

外部验证：历史金标只是实际诉请或裁判，不给全解覆盖

证明路线：请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：生成与原告诉请相同不获得全部合法请求证书

任务：EXT09, ROOT06, ROOT08, T01, T16, T17, T18, T19, T22, T24；证明族：M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=FiledClaims、AllowedClaims、SupportedClaims、AwardedClaims为不同对象并显式连接

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=阶段与所问集合明确；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=历史金标只是实际诉请或裁判，不给全解覆盖

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=请求集合/抗辩/问题链及依据；proof_route=请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=生成与原告诉请相同不获得全部合法请求证书

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D031｜被告称款项属于投资而非借款时，应形成哪个争点？

分组：04 请求权、抗辩及争点处理。原评测：CN03, CN11, CN14, CN15。

输入：原告事实、请求、被告抗辩与材料

输出：请求集合/抗辩/问题链及依据

形式目标：借贷与投资等备选法律关系是相互关联的情景，分别导出前提与结果

前提：款项性质解释及证据规则已确认

外部验证：合同实质关系认定

证明路线：文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：不得把被告的投资抗辩既当承认借款又作相反事实

任务：EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T16, T17, T18, T19, T22, T24；证明族：M04, M07, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=借贷与投资等备选法律关系是相互关联的情景，分别导出前提与结果

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=款项性质解释及证据规则已确认；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=合同实质关系认定

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=请求集合/抗辩/问题链及依据；proof_route=文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=不得把被告的投资抗辩既当承认借款又作相反事实

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D032｜主张履行、已付款、合同无效和其他法律关系如何分支？

分组：04 请求权、抗辩及争点处理。原评测：CN03, CN11, CN14, CN15。

输入：原告事实、请求、被告抗辩与材料

输出：请求集合/抗辩/问题链及依据

形式目标：分支共享身份、输入版本，保留成立/履行/无效/清偿等相容性约束

前提：无效与清偿等法律后果关系明定

外部验证：事实认定与解释选择

证明路线：结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：在有效分支取本金规则、无效分支取收益规则拼接不合法结果

任务：EXT03, EXT09, ROOT06, ROOT08, T01, T05, T06, T16, T17, T18, T19, T22, T24；证明族：M06, M07, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=分支共享身份、输入版本，保留成立/履行/无效/清偿等相容性约束

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=无效与清偿等法律后果关系明定；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=事实认定与解释选择

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=请求集合/抗辩/问题链及依据；proof_route=结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=在有效分支取本金规则、无效分支取收益规则拼接不合法结果

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D033｜借贷中时效争议是否存在，而不是法院自动消灭债权？

分组：04 请求权、抗辩及争点处理。原评测：CN03, CN11, CN14, CN15。

输入：原告事实、请求、被告抗辩与材料

输出：请求集合/抗辩/问题链及依据

形式目标：时效到期、抗辩提出、后续承诺及期间变化分别计算；到期不自动删债权

前提：适用时效制度及中止中断前提明确

外部验证：知悉时间和请求行为证明

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：只有到期，无抗辩提出，不自动按时效驳回

任务：EXT09, ROOT06, ROOT08, T01, T08, T16, T17, T18, T19, T20, T22, T24；证明族：M03, M07, M10, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=时效到期、抗辩提出、后续承诺及期间变化分别计算；到期不自动删债权

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=适用时效制度及中止中断前提明确；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=知悉时间和请求行为证明

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=请求集合/抗辩/问题链及依据；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=只有到期，无抗辩提出，不自动按时效驳回

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D034｜原告、被告各自提出的事实与反驳如何组织为焦点？

分组：04 请求权、抗辩及争点处理。原评测：CN03, CN11, CN14, CN15。

输入：原告事实、请求、被告抗辩与材料

输出：请求集合/抗辩/问题链及依据

形式目标：Issue图分别链接主张、反驳、责任主体、支持集及攻击靶点

前提：各争点证明责任政策明定

外部验证：焦点发现是否齐全

证明路线：来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有依赖/增量复用；EXT05替代来源与支持反链仍为深化目标；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收

反例：把反驳未成立当作对方主张已证明，须拒绝此跳步

任务：EXT03, EXT05, EXT09, ROOT06, ROOT08, T01, T04, T05, T06, T16, T17, T18, T19, T22, T24；证明族：M05, M06, M07, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=Issue图分别链接主张、反驳、责任主体、支持集及攻击靶点

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=各争点证明责任政策明定；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=焦点发现是否齐全

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=请求集合/抗辩/问题链及依据；proof_route=来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=把反驳未成立当作对方主张已证明，须拒绝此跳步

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D035｜答辩是否回应现有请求和证据，而非虚构承认或抗辩？

分组：04 请求权、抗辩及争点处理。原评测：CN03, CN11, CN14, CN15。

输入：原告事实、请求、被告抗辩与材料

输出：请求集合/抗辩/问题链及依据

形式目标：每个答辩命题链接所回应请求/证据；新承认必须有单独授权来源

前提：代理权限和可用抗辩政策

外部验证：答辩质量、论证充分性

证明路线：来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有依赖/增量复用；EXT05替代来源与支持反链仍为深化目标；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：模板中无来源的债务承认应触发审查而非静默写入

任务：EXT05, EXT09, ROOT05, ROOT06, ROOT08, T01, T04, T16, T17, T18, T19, T22, T24；证明族：M05, M08, M13, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=每个答辩命题链接所回应请求/证据；新承认必须有单独授权来源

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=代理权限和可用抗辩政策；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=答辩质量、论证充分性

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=请求集合/抗辩/问题链及依据；proof_route=来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=模板中无来源的债务承认应触发审查而非静默写入

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/thunlp/LexChain/blob/main/README.md
https://github.com/Dai-shen/LAiW/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D036｜同一侵权请求的责任、比例、给付方式与结论能否衔接？

分组：04 请求权、抗辩及争点处理。原评测：CN15。

输入：原告事实、请求、被告抗辩与材料

输出：请求集合/抗辩/问题链及依据

形式目标：责任主体、方式、份额与金额由同一责任模型联算

前提：责任方式、追偿和赔偿项目规则准入

外部验证：比例评价与损害事实

证明路线：请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：连带责任外部给付与内部份额不得混为每人比例给付

任务：EXT04, EXT09, ROOT04, ROOT06, ROOT08, T01, T08, T09, T10, T16, T17, T18, T19, T22, T24；证明族：M08, M09, M11, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=责任主体、方式、份额与金额由同一责任模型联算

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=责任方式、追偿和赔偿项目规则准入；sources=https://github.com/thunlp/LexChain/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=比例评价与损害事实

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=请求集合/抗辩/问题链及依据；proof_route=请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=连带责任外部给付与内部份额不得混为每人比例给付

来源（原表范围）：
https://github.com/thunlp/LexChain/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D037｜应匹配哪些罪名标签，是否存在多罪而非单一分类？

分组：05 刑事定罪、量刑与多被告。原评测：CN06, CN07, CN10, CN12。

输入：事实叙述、要素与法条资料

输出：逐主体标签、刑种刑期与理由

形式目标：每被告罪名集合满足选定要件/阻却/竞合政策；输出标签与语义双向映射

前提：刑法版本及采用的教义学结构已明确

外部验证：构成要件事实与开放概念

证明路线：结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：单标签接口不得悄悄丢掉第二项合法罪名候选

任务：EXT03, EXT09, ROOT06, ROOT08, T01, T05, T06, T16, T17, T18, T19, T22, T24；证明族：M06, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=每被告罪名集合满足选定要件/阻却/竞合政策；输出标签与语义双向映射

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=刑法版本及采用的教义学结构已明确；sources=https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=构成要件事实与开放概念

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=逐主体标签、刑种刑期与理由；proof_route=结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=单标签接口不得悄悄丢掉第二项合法罪名候选

来源（原表范围）：
https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D038｜法条类别ID对应哪一个法条，索引是否正确转换？

分组：05 刑事定罪、量刑与多被告。原评测：CN06, CN07, CN10, CN12。

输入：事实叙述、要素与法条资料

输出：逐主体标签、刑种刑期与理由

形式目标：encode/decode满足标签往返；标签ID、法条编号、款项保持不同类型

前提：实际数据版本的词典冻结

外部验证：词典来源及时效核验

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；法源query与原文回读已有工程；固定语料与适用法域完整性另证

反例：law.txt第1项不自动打印为刑法第1条

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T03, T20, T22, T24；证明族：M01, M02, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=encode/decode满足标签往返；标签ID、法条编号、款项保持不同类型

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=实际数据版本的词典冻结；sources=https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=词典来源及时效核验

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=逐主体标签、刑种刑期与理由；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=law.txt第1项不自动打印为刑法第1条

来源（原表范围）：
https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D039｜有期、无期和死刑是否采用不同类型而非普通数值？

分组：05 刑事定罪、量刑与多被告。原评测：CN06, CN07, CN10, CN12。

输入：事实叙述、要素与法条资料

输出：逐主体标签、刑种刑期与理由

形式目标：刑种为和类型；Term(months)、Life、Death等不可用普通加法混算

前提：刑种组合与计算规则单独注册

外部验证：刑种适用的实质判断

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化

反例：−1/−2哨兵不进入刑期均值或罚金计算

任务：EXT09, REV02, ROOT02, ROOT04, ROOT06, ROOT08, T01, T02, T08, T09, T10, T22, T24；证明族：M01, M09, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=刑种为和类型；Term(months)、Life、Death等不可用普通加法混算

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=刑种组合与计算规则单独注册；sources=https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=刑种适用的实质判断

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=逐主体标签、刑种刑期与理由；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=−1/−2哨兵不进入刑期均值或罚金计算

来源（原表范围）：
https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D040｜有无给定法条文本时，刑期预测条件有何不同？

分组：05 刑事定罪、量刑与多被告。原评测：CN06, CN07, CN10, CN12。

输入：事实叙述、要素与法条资料

输出：逐主体标签、刑种刑期与理由

形式目标：预测目标及输入特征预算固定；有法条/无法条为两个配置，不混分母

前提：时间切分、标签模型与法条可得性

外部验证：真实留出准确性和漂移

证明路线：概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：V2.1概率/胜率参考与保留时间切分；真实经验效果、因果识别及EXT保证未整体验收

反例：有金标法条的预测分数不可标为无依据独立定罪能力

任务：EXT06, EXT07, EXT09, ROOT06, ROOT08, T01, T12, T13, T14, T15, T22, T24；证明族：M12, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=预测目标及输入特征预算固定；有法条/无法条为两个配置，不混分母

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=时间切分、标签模型与法条可得性；sources=https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=真实留出准确性和漂移

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=逐主体标签、刑种刑期与理由；proof_route=概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=有金标法条的预测分数不可标为无依据独立定罪能力

来源（原表范围）：
https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D041｜多被告罪名与刑期是否分别对应正确主体？

分组：05 刑事定罪、量刑与多被告。原评测：CN06, CN07, CN10, CN12。

输入：事实叙述、要素与法条资料

输出：逐主体标签、刑种刑期与理由

形式目标：逐被告构成、情节、刑罚映射共同身份保持，集合结果可独立检查

前提：个别化量刑与共同责任规则

外部验证：事实归属核验

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化

反例：互换姓名仍维持全案金额/刑期合计但检查须失败

任务：EXT03, EXT09, REV02, ROOT02, ROOT04, ROOT06, ROOT08, T01, T02, T05, T06, T08, T09, T10, T22, T24；证明族：M01, M06, M09, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=逐被告构成、情节、刑罚映射共同身份保持，集合结果可独立检查

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=个别化量刑与共同责任规则；sources=https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=事实归属核验

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=逐主体标签、刑种刑期与理由；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=互换姓名仍维持全案金额/刑期合计但检查须失败

来源（原表范围）：
https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D042｜案件级结果是否全部一致，而非平均分掩盖一个被告错配？

分组：05 刑事定罪、量刑与多被告。原评测：CN06, CN07, CN10, CN12。

输入：事实叙述、要素与法条资料

输出：逐主体标签、刑种刑期与理由

形式目标：CaseCorrect=∀d∈RequiredDefendants,Correct_d∧RelationConsistency；不足者显式未决

前提：RequiredDefendants来自独立案卷清单

外部验证：案卷被告是否穷尽

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收

反例：逐人平均99%不得声称每名被告都正确

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T22, T24；证明族：M01, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=CaseCorrect=∀d∈RequiredDefendants,Correct_d∧RelationConsistency；不足者显式未决

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=RequiredDefendants来自独立案卷清单；sources=https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=案卷被告是否穷尽

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=逐主体标签、刑种刑期与理由；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=逐人平均99%不得声称每名被告都正确

来源（原表范围）：
https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D043｜裁判文书中的刑期、罚金与裁判主文是否一致？

分组：05 刑事定罪、量刑与多被告。原评测：CN06, CN07, CN10, CN12。

输入：事实叙述、要素与法条资料

输出：逐主体标签、刑种刑期与理由

形式目标：主文中刑种、期间、罚金等投影等于核验后的结构记录

前提：模板与显示单位、涉数政策明定

外部验证：额外叙事内容审核

证明路线：数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：结构罚金5000，正文误写50000应被回读发现

任务：EXT09, ROOT04, ROOT05, ROOT06, ROOT08, T01, T08, T09, T10, T22, T24；证明族：M09, M13, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=主文中刑种、期间、罚金等投影等于核验后的结构记录

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=模板与显示单位、涉数政策明定；sources=https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=额外叙事内容审核

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=逐主体标签、刑种刑期与理由；proof_route=数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=结构罚金5000，正文误写50000应被回读发现

来源（原表范围）：
https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D044｜定罪所用法条、理由和结论是否前后一致？

分组：05 刑事定罪、量刑与多被告。原评测：CN06, CN07, CN10, CN12。

输入：事实叙述、要素与法条资料

输出：逐主体标签、刑种刑期与理由

形式目标：每项定罪结论有对应理由/规则路径；自由文书不得添加无路径罪名

前提：理由结构与实际适用法条准入

外部验证：法律解释充分性

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：理由解释一罪、主文出现另一罪不因文风相似而通过

任务：EXT03, EXT09, ROOT05, ROOT06, ROOT08, T01, T03, T05, T06, T20, T22, T24；证明族：M02, M06, M13, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=每项定罪结论有对应理由/规则路径；自由文书不得添加无路径罪名

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=理由结构与实际适用法条准入；sources=https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=法律解释充分性

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=逐主体标签、刑种刑期与理由；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=理由解释一罪、主文出现另一罪不因文风相似而通过

来源（原表范围）：
https://github.com/china-ai-law-challenge/CAIL2018/blob/master/README.md
https://github.com/littlebowlnju/CMDL/blob/main/README.md
https://github.com/THUlawtech/LEEC/blob/main/README.md
https://github.com/oneal2000/JuDGE/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D045｜犯罪金额需要计入哪些项目，能否正确归属后再相加？

分组：05 刑事定罪、量刑与多被告。原评测：CN01。

输入：事实叙述、要素与法条资料

输出：逐主体标签、刑种刑期与理由

形式目标：计入金额前逐项验证财物/行为/主体归属及可加性；同源财物去重复

前提：犯罪数额认定与计价规则明确

外部验证：财物价值、次数和归属证明

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化

反例：赃款在两份记录出现不得加两遍

任务：EXT09, REV02, ROOT02, ROOT04, ROOT06, ROOT08, T01, T02, T08, T09, T10, T16, T17, T18, T19, T22, T24；证明族：M01, M08, M09, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=计入金额前逐项验证财物/行为/主体归属及可加性；同源财物去重复

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=犯罪数额认定与计价规则明确；sources=https://github.com/open-compass/LawBench/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=财物价值、次数和归属证明

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=逐主体标签、刑种刑期与理由；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=赃款在两份记录出现不得加两遍

来源（原表范围）：
https://github.com/open-compass/LawBench/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D046｜传闻证据规则问题是否满足其具体要件和例外？

分组：05 刑事定罪、量刑与多被告。原评测：US03。

输入：事实叙述、要素与法条资料

输出：逐主体标签、刑种刑期与理由

形式目标：在指定美国证据法版本内，逐要件/例外/用途给出允许或未决分支

前提：法域、法庭程序和证据用途固定

外部验证：陈述目的及例外事实认定

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收

反例：不得把美国传闻标签直接变成中国证据排除结论

任务：EXT03, EXT09, ROOT06, ROOT08, T01, T03, T05, T06, T16, T17, T18, T19, T20, T22, T24；证明族：M02, M06, M07, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=在指定美国证据法版本内，逐要件/例外/用途给出允许或未决分支

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=法域、法庭程序和证据用途固定；sources=https://hazyresearch.stanford.edu/legalbench/tasks/

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=陈述目的及例外事实认定

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=逐主体标签、刑种刑期与理由；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=不得把美国传闻标签直接变成中国证据排除结论

来源（原表范围）：
https://hazyresearch.stanford.edu/legalbench/tasks/

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D047｜借款是否实际交付，是否已经清偿？

分组：06 借贷、担保与共同债务。原评测：CN11。

输入：借条、交易记录、公司及婚姻关系记载

输出：要素答案、担保/债务关系与金额条件

形式目标：交付事实与清偿事实分别进入责任链；输出对应认定/假设条件

前提：借款成立、生效和清偿政策明确

外部验证：银行记录真实性、资金用途

证明路线：文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：出借记录不能自动证明后来未清偿

任务：EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T16, T17, T18, T19, T22, T24；证明族：M04, M07, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=交付事实与清偿事实分别进入责任链；输出对应认定/假设条件

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=借款成立、生效和清偿政策明确；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=银行记录真实性、资金用途

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=要素答案、担保/债务关系与金额条件；proof_route=文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=出借记录不能自动证明后来未清偿

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D048｜还款用于本金还是利息，能否识别抵充对象？

分组：06 借贷、担保与共同债务。原评测：CN11。

输入：借条、交易记录、公司及婚姻关系记载

输出：要素答案、担保/债务关系与金额条件

形式目标：抵充账本按准入顺序更新；每笔分配非负且不超过该笔付款，可追踪余额

前提：约定/法定抵充规则与本息项目明确

外部验证：实际付款和指定用途

证明路线：请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化

反例：同一还款同时全额扣本金、又全额扣利息应拒绝

任务：EXT09, ROOT04, ROOT06, ROOT08, T01, T08, T09, T10, T16, T17, T18, T19, T22, T24；证明族：M08, M09, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=抵充账本按准入顺序更新；每笔分配非负且不超过该笔付款，可追踪余额

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=约定/法定抵充规则与本息项目明确；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=实际付款和指定用途

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=要素答案、担保/债务关系与金额条件；proof_route=请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=同一还款同时全额扣本金、又全额扣利息应拒绝

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D049｜借期利息、逾期利率、违约金各有什么约定？

分组：06 借贷、担保与共同债务。原评测：CN11。

输入：借条、交易记录、公司及婚姻关系记载

输出：要素答案、担保/债务关系与金额条件

形式目标：借期利息、逾期利息、违约金分别形成计算组件，组合受适用政策限制

前提：约定有效性与重叠项目规则

外部验证：条款含义和实际违约期间

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化

反例：相似百分比不能默认三项全叠加

任务：EXT09, ROOT04, ROOT06, ROOT08, T01, T08, T09, T10, T16, T17, T18, T19, T22, T24；证明族：M03, M09, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=借期利息、逾期利息、违约金分别形成计算组件，组合受适用政策限制

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=约定有效性与重叠项目规则；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=条款含义和实际违约期间

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=要素答案、担保/债务关系与金额条件；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=相似百分比不能默认三项全叠加

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D050｜是否存在保证或物保，主体、登记、交付是否清楚？

分组：06 借贷、担保与共同债务。原评测：CN11。

输入：借条、交易记录、公司及婚姻关系记载

输出：要素答案、担保/债务关系与金额条件

形式目标：保证/抵押/质押以不同法律关系、设立事件、效力与救济表示

前提：特定担保类型法源及物权成立条件

外部验证：登记/交付事实与担保文件核验

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：签担保文件不自动证明登记完成或财产已交付

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T16, T17, T18, T19, T22, T24；证明族：M01, M03, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=保证/抵押/质押以不同法律关系、设立事件、效力与救济表示

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=特定担保类型法源及物权成立条件；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=登记/交付事实与担保文件核验

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=要素答案、担保/债务关系与金额条件；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=签担保文件不自动证明登记完成或财产已交付

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D051｜公司担保是否经过内部决议，是否涉及分支机构或对外担保？

分组：06 借贷、担保与共同债务。原评测：CN11。

输入：借条、交易记录、公司及婚姻关系记载

输出：要素答案、担保/债务关系与金额条件

形式目标：决议存在、程序、代表权限及担保效力分别建谓词并按规则连接

前提：公司类型、担保类型和适用时间明确

外部验证：善意/应知等判断

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收

反例：仅无决议字段不得由一条统一规则宣布所有担保无效

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T16, T17, T18, T19, T22, T24；证明族：M01, M03, M07, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=决议存在、程序、代表权限及担保效力分别建谓词并按规则连接

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=公司类型、担保类型和适用时间明确；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=善意/应知等判断

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=要素答案、担保/债务关系与金额条件；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=仅无决议字段不得由一条统一规则宣布所有担保无效

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D052｜法定代表人以自己名义签约时责任主体如何标注？

分组：06 借贷、担保与共同债务。原评测：CN11。

输入：借条、交易记录、公司及婚姻关系记载

输出：要素答案、担保/债务关系与金额条件

形式目标：签字人、名义、代表关系、合同当事人和责任人分别编码

前提：代理/代表和合同解释准入

外部验证：签署意图、相对人认识

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：签名文本为自然人名不自动由其个人承担全部合同义务

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T16, T17, T18, T19, T22, T24；证明族：M01, M03, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=签字人、名义、代表关系、合同当事人和责任人分别编码

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=代理/代表和合同解释准入；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=签署意图、相对人认识

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=要素答案、担保/债务关系与金额条件；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=签名文本为自然人名不自动由其个人承担全部合同义务

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D053｜配偶是否签字、是否共同举债及用于共同生活/经营？

分组：06 借贷、担保与共同债务。原评测：CN11。

输入：借条、交易记录、公司及婚姻关系记载

输出：要素答案、担保/债务关系与金额条件

形式目标：婚姻期间、签字、共同意思、用途和债务归属为独立争点

前提：夫妻债务规则及特殊责任分配明定

外部验证：用途、共同举债意思的事实证明

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：婚内借款不自动推出夫妻共同债务

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T16, T17, T18, T19, T22, T24；证明族：M01, M07, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=婚姻期间、签字、共同意思、用途和债务归属为独立争点

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=夫妻债务规则及特殊责任分配明定；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=用途、共同举债意思的事实证明

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=要素答案、担保/债务关系与金额条件；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=婚内借款不自动推出夫妻共同债务

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D054｜主张公司人格混同或连带责任时，哪些事实材料支持？

分组：06 借贷、担保与共同债务。原评测：CN11。

输入：借条、交易记录、公司及婚姻关系记载

输出：要素答案、担保/债务关系与金额条件

形式目标：公司关系证据形成支持图；人格混同等评价与连带后果单独规则连接

前提：穿透责任适用条件和证明责任

外部验证：开放法律评价与真实关系调查

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；现有依赖/增量复用；EXT05替代来源与支持反链仍为深化目标；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：共用电话不直接生成无限连带责任边

任务：EXT05, EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T04, T16, T17, T18, T19, T22, T24；证明族：M01, M05, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=公司关系证据形成支持图；人格混同等评价与连带后果单独规则连接

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=穿透责任适用条件和证明责任；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=开放法律评价与真实关系调查

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=要素答案、担保/债务关系与金额条件；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=共用电话不直接生成无限连带责任边

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D055｜资金是否来自金融机构贷款，现金出借能力和惯例有无材料？

分组：06 借贷、担保与共同债务。原评测：CN11。

输入：借条、交易记录、公司及婚姻关系记载

输出：要素答案、担保/债务关系与金额条件

形式目标：资金来源和现金能力是有来源的事实候选；不足即未证而非虚构负事实

前提：所涉法律关系及来源限制政策明确

外部验证：出借能力、惯例及贷款来源真实性

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收

反例：收入低不自动证明不可能现金出借

任务：EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T16, T17, T18, T19, T20, T22, T24；证明族：M02, M04, M07, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=资金来源和现金能力是有来源的事实候选；不足即未证而非虚构负事实

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=所涉法律关系及来源限制政策明确；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=出借能力、惯例及贷款来源真实性

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=要素答案、担保/债务关系与金额条件；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=收入低不自动证明不可能现金出借

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D056｜律师费、诉讼费等承担约定和请求是否被明确区分？

分组：06 借贷、担保与共同债务。原评测：CN11。

输入：借条、交易记录、公司及婚姻关系记载

输出：要素答案、担保/债务关系与金额条件

形式目标：律师费、诉讼费、保全费等使用独立债项/基础/受益人/请求状态

前提：转嫁费用条件、法院收费与委托收费区分

外部验证：合理性与实际支付证明

证明路线：请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：自身工时报价不能自动作为对方应赔律师费

任务：EXT09, ROOT04, ROOT05, ROOT06, ROOT08, T01, T08, T09, T10, T16, T17, T18, T19, T22, T24；证明族：M08, M09, M13, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=律师费、诉讼费、保全费等使用独立债项/基础/受益人/请求状态

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=转嫁费用条件、法院收费与委托收费区分；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=合理性与实际支付证明

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=要素答案、担保/债务关系与金额条件；proof_route=请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=不知道不自动当不存在；模板字段不自动成为法定裁判；counterexample=自身工时报价不能自动作为对方应赔律师费

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D057｜发生的纠纷属于哪一种侵权类型？

分组：07 侵权责任与损害。原评测：CN15。

输入：侵权事实、请求、损失记录

输出：责任分析、比例、方式与金额

形式目标：侵权类型候选按要件选择，开放残余不强制塞既有类别

前提：类型库范围与一般/特别规则准入

外部验证：侵权类型解释

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：分类器不认识的新情形不能返回无任何请求权

任务：EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T16, T17, T18, T19, T20, T22, T24；证明族：M02, M04, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=侵权类型候选按要件选择，开放残余不强制塞既有类别

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=类型库范围与一般/特别规则准入；sources=https://github.com/thunlp/LexChain/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=侵权类型解释

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=责任分析、比例、方式与金额；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=分类器不认识的新情形不能返回无任何请求权

来源（原表范围）：
https://github.com/thunlp/LexChain/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D058｜不同当事人的行为、损害、因果联系与过错如何组织？

分组：07 侵权责任与损害。原评测：CN15。

输入：侵权事实、请求、损失记录

输出：责任分析、比例、方式与金额

形式目标：行为—损害—因果—过错是类型化关系；统计因果与法律归责分层

前提：实体归责规则与因果模型分别明确

外部验证：因果假设、损害及过错事实

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；V2.1概率/胜率参考与保留时间切分；真实经验效果、因果识别及EXT保证未整体验收

反例：相关性显著不直接推出法律上的相当因果或责任

任务：EXT03, EXT06, EXT07, EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T05, T06, T12, T13, T14, T15, T22, T24；证明族：M01, M06, M12, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=行为—损害—因果—过错是类型化关系；统计因果与法律归责分层

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=实体归责规则与因果模型分别明确；sources=https://github.com/thunlp/LexChain/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=因果假设、损害及过错事实

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=责任分析、比例、方式与金额；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=相关性显著不直接推出法律上的相当因果或责任

来源（原表范围）：
https://github.com/thunlp/LexChain/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D059｜责任是否成立，与责任比例大小是否分开？

分组：07 侵权责任与损害。原评测：CN15。

输入：侵权事实、请求、损失记录

输出：责任分析、比例、方式与金额

形式目标：成立门和份额选择分开；无责任不得被赋正赔偿份额

前提：成立/免责/减责适用政策

外部验证：比例裁量与因果评价

证明路线：请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化

反例：用小比例掩盖根本不承担该责任的主体

任务：EXT09, ROOT04, ROOT06, ROOT08, T01, T08, T09, T10, T16, T17, T18, T19, T22, T24；证明族：M08, M09, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=成立门和份额选择分开；无责任不得被赋正赔偿份额

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=成立/免责/减责适用政策；sources=https://github.com/thunlp/LexChain/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=比例裁量与因果评价

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=责任分析、比例、方式与金额；proof_route=请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=用小比例掩盖根本不承担该责任的主体

来源（原表范围）：
https://github.com/thunlp/LexChain/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D060｜不同主体以何种责任方式承担，而不是只分百分比？

分组：07 侵权责任与损害。原评测：CN15。

输入：侵权事实、请求、损失记录

输出：责任分析、比例、方式与金额

形式目标：分别建按份、连带、补充等外部给付义务与内部追偿关系

前提：所用责任模式与先后顺序政策准入

外部验证：责任方式的法律认定

证明路线：请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：同一损害多个连带债务全额相加造成超额受偿

任务：EXT04, EXT09, ROOT04, ROOT06, ROOT08, T01, T08, T09, T10, T16, T17, T18, T19, T22, T24；证明族：M08, M09, M11, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=分别建按份、连带、补充等外部给付义务与内部追偿关系

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=所用责任模式与先后顺序政策准入；sources=https://github.com/thunlp/LexChain/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=责任方式的法律认定

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=责任分析、比例、方式与金额；proof_route=请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=同一损害多个连带债务全额相加造成超额受偿

来源（原表范围）：
https://github.com/thunlp/LexChain/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D061｜总损失由哪些项目构成？

分组：07 侵权责任与损害。原评测：CN15。

输入：侵权事实、请求、损失记录

输出：责任分析、比例、方式与金额

形式目标：损失账本按损害事件、受益人、项目和时间去重，再执行明确聚合

前提：哪些项目可赔和计价口径经准入

外部验证：损失存在、必要性、未来损害估计

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化

反例：发票额和同一损失评估额不得无条件双计

任务：EXT09, REV02, ROOT02, ROOT04, ROOT06, ROOT08, T01, T02, T08, T09, T10, T22, T24；证明族：M01, M09, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=损失账本按损害事件、受益人、项目和时间去重，再执行明确聚合

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=哪些项目可赔和计价口径经准入；sources=https://github.com/thunlp/LexChain/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=损失存在、必要性、未来损害估计

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=责任分析、比例、方式与金额；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=发票额和同一损失评估额不得无条件双计

来源（原表范围）：
https://github.com/thunlp/LexChain/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D062｜按责任比例、责任方式计算每方给付是否一致？

分组：07 侵权责任与损害。原评测：CN15。

输入：侵权事实、请求、损失记录

输出：责任分析、比例、方式与金额

形式目标：逐方给付满足外部偿付总约束及内部规则；共享损失基数一致

前提：比例、连带、已付及追偿口径明定

外部验证：裁量比例与事实余额

证明路线：请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：把外部连带金额按内部份额削减，须发现语义不符

任务：EXT04, EXT09, ROOT04, ROOT06, ROOT08, T01, T08, T09, T10, T16, T17, T18, T19, T22, T24；证明族：M08, M09, M11, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=逐方给付满足外部偿付总约束及内部规则；共享损失基数一致

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=比例、连带、已付及追偿口径明定；sources=https://github.com/thunlp/LexChain/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=裁量比例与事实余额

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=责任分析、比例、方式与金额；proof_route=请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=把外部连带金额按内部份额削减，须发现语义不符

来源（原表范围）：
https://github.com/thunlp/LexChain/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D063｜金钱赔偿之外是否还有其他承担责任方式？

分组：07 侵权责任与损害。原评测：CN15。

输入：侵权事实、请求、损失记录

输出：责任分析、比例、方式与金额

形式目标：恢复原状、停止侵害等非金钱救济为动作/状态目标，不强转人民币

前提：救济允许条件、可履行性及相容性

外部验证：现实履行可能与比例原则判断

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：道歉或禁令不能当赔偿金额零而消失

任务：EXT09, ROOT06, ROOT08, T01, T16, T17, T18, T19, T22, T24；证明族：M03, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=恢复原状、停止侵害等非金钱救济为动作/状态目标，不强转人民币

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=救济允许条件、可履行性及相容性；sources=https://github.com/thunlp/LexChain/blob/main/README.md

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=现实履行可能与比例原则判断

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=责任分析、比例、方式与金额；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=道歉或禁令不能当赔偿金额零而消失

来源（原表范围）：
https://github.com/thunlp/LexChain/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D064｜最终裁判总结是否保留责任分析、比例和金额的条件？

分组：07 侵权责任与损害。原评测：CN15。

输入：侵权事实、请求、损失记录

输出：责任分析、比例、方式与金额

形式目标：总结中每项责任、比例、数值和限制来自同一场景见证

前提：文书受保护观察集合独立确定

外部验证：自由表达语义审核

证明路线：请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：不同情景各取最有利结果拼成无条件总结

任务：EXT04, EXT09, ROOT05, ROOT06, ROOT08, T01, T09, T16, T17, T18, T19, T22, T24；证明族：M08, M11, M13, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=总结中每项责任、比例、数值和限制来自同一场景见证

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=文书受保护观察集合独立确定；sources=https://github.com/thunlp/LexChain/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=自由表达语义审核

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=责任分析、比例、方式与金额；proof_route=请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=不同情景各取最有利结果拼成无条件总结

来源（原表范围）：
https://github.com/thunlp/LexChain/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D065｜合同主体、签订、生效、到期和续展条件是什么？

分组：08 合同条款与权利义务审核。原评测：US02, US04, US05。

输入：完整协议、附件、定义与修订

输出：条款字段、引用及条件法律效果

形式目标：合同状态依成立、生效、终止、续展等不同事件更新

前提：触发条款、效力条件和时间语义明确

外部验证：签署/到达/审批/履行事实

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：签订日不自动等于生效日；到期不自动抹去存续义务

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T08, T16, T17, T18, T19, T20, T22, T24；证明族：M01, M03, M10, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=合同状态依成立、生效、终止、续展等不同事件更新

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=触发条款、效力条件和时间语义明确；sources=https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=签署/到达/审批/履行事实

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=条款字段、引用及条件法律效果；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=签订日不自动等于生效日；到期不自动抹去存续义务

来源（原表范围）：
https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D066｜准据法条款指向哪个法域，不能仅凭当事人所在地推断？

分组：08 合同条款与权利义务审核。原评测：US02, US04, US05。

输入：完整协议、附件、定义与修订

输出：条款字段、引用及条件法律效果

形式目标：准据法条款候选与最终适用法判断分离并保留冲突法路径

前提：选择法有效性与强制性规范政策

外部验证：条款解释及连接点核验

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；法源query与原文回读已有工程；固定语料与适用法域完整性另证；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展

反例：当事人在某州设立不自动推定该州法管全部合同

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T03, T16, T17, T18, T19, T20, T22, T24；证明族：M01, M02, M03, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=准据法条款候选与最终适用法判断分离并保留冲突法路径

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=选择法有效性与强制性规范政策；sources=https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=条款解释及连接点核验

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=条款字段、引用及条件法律效果；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=当事人在某州设立不自动推定该州法管全部合同

来源（原表范围）：
https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D067｜最惠待遇、排他、竞业和不招揽义务如何约束各方？

分组：08 合同条款与权利义务审核。原评测：US02, US04, US05。

输入：完整协议、附件、定义与修订

输出：条款字段、引用及条件法律效果

形式目标：限制按主体、行为、区域、期间、例外及规范效力表达

前提：限制条款解释和可执行性政策

外部验证：合理范围、市场与事实判断

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：排他义务不是自动转让排他知识产权

任务：EXT09, ROOT06, ROOT08, T01, T16, T17, T18, T19, T22, T24；证明族：M03, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=限制按主体、行为、区域、期间、例外及规范效力表达

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=限制条款解释和可执行性政策；sources=https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=合理范围、市场与事实判断

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=条款字段、引用及条件法律效果；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=排他义务不是自动转让排他知识产权

来源（原表范围）：
https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D068｜限制的例外或保留条款是否改变主条款效果？

分组：08 合同条款与权利义务审核。原评测：US02, US04, US05。

输入：完整协议、附件、定义与修订

输出：条款字段、引用及条件法律效果

形式目标：规则、例外、例外之例外采用明确优先或作用域语义

前提：可废止/严格分类及适用政策已确认

外部验证：例外文本含义

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭

反例：正向主条款命中后不得跳过后文除外事项

任务：EXT03, EXT09, ROOT06, ROOT08, T01, T05, T06, T16, T17, T18, T19, T22, T24；证明族：M03, M06, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=规则、例外、例外之例外采用明确优先或作用域语义

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=可废止/严格分类及适用政策已确认；sources=https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=例外文本含义

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=条款字段、引用及条件法律效果；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=正向主条款命中后不得跳过后文除外事项

来源（原表范围）：
https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D069｜无因终止、通知期与停止续展之间有何差异？

分组：08 合同条款与权利义务审核。原评测：US02, US04, US05。

输入：完整协议、附件、定义与修订

输出：条款字段、引用及条件法律效果

形式目标：终止权行使、通知到达、终止生效、拒绝续展分别为事件

前提：合同与适用法对期限/生效的政策明确

外部验证：通知有效送达事实

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：发出停止续展通知不能直接终止当前履行期

任务：EXT09, ROOT06, ROOT08, T01, T08, T16, T17, T18, T19, T20, T22, T24；证明族：M03, M10, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=终止权行使、通知到达、终止生效、拒绝续展分别为事件

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=合同与适用法对期限/生效的政策明确；sources=https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=通知有效送达事实

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=条款字段、引用及条件法律效果；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=发出停止续展通知不能直接终止当前履行期

来源（原表范围）：
https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D070｜控制权变更与转让是否同义，触发同意、通知还是终止？

分组：08 合同条款与权利义务审核。原评测：US02, US04, US05。

输入：完整协议、附件、定义与修订

输出：条款字段、引用及条件法律效果

形式目标：控制权变化按每份合同定义求触发，再分别产生通知、同意、终止等后果

前提：各合同定义及事件范围已解释

外部验证：控制关系和交易实质

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：同一交易事实不可用统一阈值覆盖全部合同

任务：EXT04, EXT09, ROOT06, ROOT08, T01, T09, T16, T17, T18, T19, T22, T24；证明族：M03, M11, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=控制权变化按每份合同定义求触发，再分别产生通知、同意、终止等后果

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=各合同定义及事件范围已解释；sources=https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=控制关系和交易实质

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=条款字段、引用及条件法律效果；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=同一交易事实不可用统一阈值覆盖全部合同

来源（原表范围）：
https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D071｜许可从排他转为非排他时，是否误认整个许可终止？

分组：08 合同条款与权利义务审核。原评测：US02, US04, US05。

输入：完整协议、附件、定义与修订

输出：条款字段、引用及条件法律效果

形式目标：转换license_exclusive→license_nonexclusive不推出license_terminated

前提：条款对转换与终止有明确语义

外部验证：条款有效性、触发事实

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：只失去排他性时删除全部使用许可，应拦截

任务：EXT09, ROOT06, ROOT08, T01, T16, T17, T18, T19, T22, T24；证明族：M03, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=转换license_exclusive→license_nonexclusive不推出license_terminated

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=条款对转换与终止有明确语义；sources=https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=条款有效性、触发事实

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=条款字段、引用及条件法律效果；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=只失去排他性时删除全部使用许可，应拦截

来源（原表范围）：
https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D072｜知识产权归属、共有及关联方许可范围是什么？

分组：08 合同条款与权利义务审核。原评测：US02, US04, US05。

输入：完整协议、附件、定义与修订

输出：条款字段、引用及条件法律效果

形式目标：IP归属、共有份额、许可、再许可和关联方范围使用不同关系

前提：权属转移与许可政策准入

外部验证：成果性质与权属事实

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：有许可不等于成为权利人；关联方不因集团标签自动获许可

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T16, T17, T18, T19, T22, T24；证明族：M01, M03, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=IP归属、共有份额、许可、再许可和关联方范围使用不同关系

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=权属转移与许可政策准入；sources=https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=成果性质与权属事实

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=条款字段、引用及条件法律效果；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=有许可不等于成为权利人；关联方不因集团标签自动获许可

来源（原表范围）：
https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D073｜永久、不可撤销、不可转让与用量限制许可是否区分？

分组：08 合同条款与权利义务审核。原评测：US02, US04, US05。

输入：完整协议、附件、定义与修订

输出：条款字段、引用及条件法律效果

形式目标：永久性、可撤销性、可转让性、用量上限为独立属性和事件规则

前提：“永久”等文字范围与法律效力明定

外部验证：开放条款解释

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：永久许可不自动等于不可撤销且无限量

任务：EXT09, ROOT06, ROOT08, T01, T08, T16, T17, T18, T19, T20, T22, T24；证明族：M03, M10, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=永久性、可撤销性、可转让性、用量上限为独立属性和事件规则

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=“永久”等文字范围与法律效力明定；sources=https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=开放条款解释

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=条款字段、引用及条件法律效果；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=永久许可不自动等于不可撤销且无限量

来源（原表范围）：
https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D074｜最低采购、价格限制、收益分成与用量费用是什么？

分组：08 合同条款与权利义务审核。原评测：US02, US04, US05。

输入：完整协议、附件、定义与修订

输出：条款字段、引用及条件法律效果

形式目标：采购量、价格机制、分成基数及用量费分别计算并保留期间/单位

前提：最低承诺和费用触发政策

外部验证：销量、净收入定义及审计事实

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化

反例：销售额分成误用利润基数或跨期重复汇总

任务：EXT09, ROOT04, ROOT06, ROOT08, T01, T08, T09, T10, T16, T17, T18, T19, T22, T24；证明族：M03, M09, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=采购量、价格机制、分成基数及用量费分别计算并保留期间/单位

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=最低承诺和费用触发政策；sources=https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=销量、净收入定义及审计事实

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=条款字段、引用及条件法律效果；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=销售额分成误用利润基数或跨期重复汇总

来源（原表范围）：
https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D075｜责任上限、无上限例外、约定赔偿和保险怎样衔接？

分组：08 合同条款与权利义务审核。原评测：US02, US04, US05。

输入：完整协议、附件、定义与修订

输出：条款字段、引用及条件法律效果

形式目标：赔偿分项先归类，再应用cap、carveout、时间/责任模式约束

前提：上限有效性、例外和保险责任另行明确

外部验证：损失性质、可保性与比例评价

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：对保密例外也机械套一般cap，或将保险限额当责任上限

任务：EXT04, EXT09, ROOT04, ROOT06, ROOT08, T01, T08, T09, T10, T16, T17, T18, T19, T22, T24；证明族：M03, M09, M11, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=赔偿分项先归类，再应用cap、carveout、时间/责任模式约束

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=上限有效性、例外和保险责任另行明确；sources=https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=损失性质、可保性与比例评价

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=条款字段、引用及条件法律效果；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=对保密例外也机械套一般cap，或将保险限额当责任上限

来源（原表范围）：
https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D076｜终止后服务、源代码托管、审计权及第三方受益如何存续？

分组：08 合同条款与权利义务审核。原评测：US02, US04, US05。

输入：完整协议、附件、定义与修订

输出：条款字段、引用及条件法律效果

形式目标：终止后服务、审计、托管及第三方权利按survival规则独立维持

前提：存续条款与适用法政策

外部验证：托管条件及第三方地位

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：合同状态终止不得全量删除结算清理等存续效果

任务：EXT09, ROOT06, ROOT08, T01, T08, T16, T17, T18, T19, T20, T22, T24；证明族：M03, M10, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=终止后服务、审计、托管及第三方权利按survival规则独立维持

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=存续条款与适用法政策；sources=https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=托管条件及第三方地位

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=条款字段、引用及条件法律效果；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=合同状态终止不得全量删除结算清理等存续效果

来源（原表范围）：
https://github.com/The-Atticus-Project/cuad/blob/main/category_descriptions.csv
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D077｜交割时陈述保证的准确性标准及bring-down时点是什么？

分组：09 并购与交割条件。原评测：US02, US05。

输入：并购协议、资料室、股权及管理层安排

输出：交易要点、条件依赖、风险与处理表

形式目标：每项陈述绑定被评价时间及bring-down标准，分别测试各交割时点

前提：重要性、知识限定及免责政策准入

外部验证：陈述真假和重大性

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：签约时真实不自动证明交割时真实

任务：EXT09, ROOT06, ROOT08, T01, T08, T16, T17, T18, T19, T20, T22, T24；证明族：M03, M10, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=每项陈述绑定被评价时间及bring-down标准，分别测试各交割时点

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=重要性、知识限定及免责政策准入；sources=https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=陈述真假和重大性

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=交易要点、条件依赖、风险与处理表；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=签约时真实不自动证明交割时真实

来源（原表范围）：
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D078｜MAE定义、除外事项与不成比例影响修饰怎样组合？

分组：09 并购与交割条件。原评测：US02, US05。

输入：并购协议、资料室、股权及管理层安排

输出：交易要点、条件依赖、风险与处理表

形式目标：MAE主定义、例外与不成比例影响修饰使用有作用域的表达式

前提：具体合同的语义与法律政策固定

外部验证：重大性与不成比例影响的开放评价

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：除外事件无论怎样影响都排除，丢失修饰条款

任务：EXT03, EXT04, EXT09, ROOT06, ROOT08, T01, T05, T06, T09, T16, T17, T18, T19, T22, T24；证明族：M03, M06, M11, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=MAE主定义、例外与不成比例影响修饰使用有作用域的表达式

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=具体合同的语义与法律政策固定；sources=https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=重大性与不成比例影响的开放评价

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=交易要点、条件依赖、风险与处理表；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=除外事件无论怎样影响都排除，丢失修饰条款

来源（原表范围）：
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D079｜知识标准是实际知道、推定知道还是调查后知道？

分组：09 并购与交割条件。原评测：US02, US05。

输入：并购协议、资料室、股权及管理层安排

输出：交易要点、条件依赖、风险与处理表

形式目标：实际知道、推定知道、合理调查后知道分类型，不能作同一布尔字段

前提：知识限定所指人员和调查义务范围明定

外部验证：主观知道及调查事实

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明

反例：一员工知道不自动等于定义中的管理层知道

任务：EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T16, T17, T18, T19, T22, T24；证明族：M03, M04, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=实际知道、推定知道、合理调查后知道分类型，不能作同一布尔字段

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=知识限定所指人员和调查义务范围明定；sources=https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=主观知道及调查事实

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=交易要点、条件依赖、风险与处理表；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=一员工知道不自动等于定义中的管理层知道

来源（原表范围）：
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D080｜no-shop与受托义务例外在何种条件下允许接触其他报价？

分组：09 并购与交割条件。原评测：US02, US05。

输入：并购协议、资料室、股权及管理层安排

输出：交易要点、条件依赖、风险与处理表

形式目标：no-shop禁止、允许例外和行使前提构成合法行动集

前提：受托义务例外、保密协议等条件准入

外部验证：更优报价和董事会评价

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；V2.1机制/策略参考与EXT08路线；不等于实际行为效果或全局策略已经证明

反例：一般禁止不能抹去明确例外，例外也不能取消全部限制

任务：EXT08, EXT09, ROOT06, ROOT08, T01, T16, T17, T18, T19, T21, T22, T24；证明族：M03, M15, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=no-shop禁止、允许例外和行使前提构成合法行动集

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=受托义务例外、保密协议等条件准入；sources=https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=更优报价和董事会评价

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=交易要点、条件依赖、风险与处理表；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=一般禁止不能抹去明确例外，例外也不能取消全部限制

来源（原表范围）：
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D081｜变更推荐、终止权及匹配期分别在何时触发？

分组：09 并购与交割条件。原评测：US02, US05。

输入：并购协议、资料室、股权及管理层安排

输出：交易要点、条件依赖、风险与处理表

形式目标：报价通知、匹配窗口、推荐变更与终止按事件先后和可行策略求解

前提：每一权利的期限和前提单独规定

外部验证：是否满足商业/法律评价条件

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明；V2.1机制/策略参考与EXT08路线；不等于实际行为效果或全局策略已经证明

反例：在匹配期届满前自动生成已可终止状态

任务：EXT08, EXT09, ROOT06, ROOT08, T01, T08, T16, T17, T18, T19, T20, T21, T22, T24；证明族：M03, M10, M15, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=报价通知、匹配窗口、推荐变更与终止按事件先后和可行策略求解

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=每一权利的期限和前提单独规定；sources=https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=是否满足商业/法律评价条件

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=交易要点、条件依赖、风险与处理表；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=在匹配期届满前自动生成已可终止状态

来源（原表范围）：
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D082｜Superior Offer和Intervening Event的定义及时间限制是什么？

分组：09 并购与交割条件。原评测：US02, US05。

输入：并购协议、资料室、股权及管理层安排

输出：交易要点、条件依赖、风险与处理表

形式目标：SuperiorOffer与InterveningEvent分别匹配定义与时间界

前提：具体定义及知悉标准明定

外部验证：实质更优/不可预见判断

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：所有新报价都算介入事件导致错误权利触发

任务：EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T08, T16, T17, T18, T19, T20, T22, T24；证明族：M03, M04, M10, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=SuperiorOffer与InterveningEvent分别匹配定义与时间界

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=具体定义及知悉标准明定；sources=https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=实质更优/不可预见判断

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=交易要点、条件依赖、风险与处理表；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=所有新报价都算介入事件导致错误权利触发

来源（原表范围）：
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D083｜通常经营承诺、买方同意和禁止性中间承诺如何约束行为？

分组：09 并购与交割条件。原评测：US02, US05。

输入：并购协议、资料室、股权及管理层安排

输出：交易要点、条件依赖、风险与处理表

形式目标：经营承诺、禁止事项及买方同意形成各自条件，行动同时通过必要门

前提：通常经营及合理同意政策

外部验证：经营正常性与交易事实

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；V2.1机制/策略参考与EXT08路线；不等于实际行为效果或全局策略已经证明

反例：一个同意回执不得豁免其他独立禁止事项

任务：EXT08, EXT09, ROOT06, ROOT08, T01, T16, T17, T18, T19, T21, T22, T24；证明族：M03, M15, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=经营承诺、禁止事项及买方同意形成各自条件，行动同时通过必要门

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=通常经营及合理同意政策；sources=https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=经营正常性与交易事实

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=交易要点、条件依赖、风险与处理表；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=一个同意回执不得豁免其他独立禁止事项

来源（原表范围）：
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D084｜特定履行等救济的条件是否与交割及终止条款一致？

分组：09 并购与交割条件。原评测：US02, US05。

输入：并购协议、资料室、股权及管理层安排

输出：交易要点、条件依赖、风险与处理表

形式目标：特定履行、终止、交割义务与赔偿集合按相容政策求联合结果

前提：救济可用性与互斥/可并行关系准入

外部验证：可履行性与法院裁量

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：相互排斥救济无条件同时列为最终可得

任务：EXT04, EXT09, ROOT06, ROOT08, T01, T09, T16, T17, T18, T19, T22, T24；证明族：M03, M08, M11, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=特定履行、终止、交割义务与赔偿集合按相容政策求联合结果

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=救济可用性与互斥/可并行关系准入；sources=https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=可履行性与法院裁量

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=交易要点、条件依赖、风险与处理表；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=相互排斥救济无条件同时列为最终可得

来源（原表范围）：
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D085｜期权、RSU、离职员工权益与双重触发补偿如何处理？

分组：09 并购与交割条件。原评测：US02, US05。

输入：并购协议、资料室、股权及管理层安排

输出：交易要点、条件依赖、风险与处理表

形式目标：权益种类、归属、服务身份、价格和双触发事件同一记录联算

前提：交易协议和雇佣权益规则明定

外部验证：身份、离职事由与价格事实

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化

反例：未发生第二触发仍支付全部双触发补偿

任务：EXT09, REV02, ROOT02, ROOT04, ROOT06, ROOT08, T01, T02, T08, T09, T10, T16, T17, T18, T19, T22, T24；证明族：M01, M03, M09, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=权益种类、归属、服务身份、价格和双触发事件同一记录联算

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=交易协议和雇佣权益规则明定；sources=https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=身份、离职事由与价格事实

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=交易要点、条件依赖、风险与处理表；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=未发生第二触发仍支付全部双触发补偿

来源（原表范围）：
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D086｜交易结构、披露附表与尽调发现之间是否矛盾？

分组：09 并购与交割条件。原评测：US02, US05。

输入：并购协议、资料室、股权及管理层安排

输出：交易要点、条件依赖、风险与处理表

形式目标：交易结构、披露附表与尽调命题按同一实体/时期比较，输出差异见证

前提：披露效力和修订优先语义已定

外部验证：实质矛盾与披露充分性

证明路线：文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：披露表的未知条目被视为保证完全真实

任务：EXT03, EXT04, EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T05, T06, T09, T22, T24；证明族：M04, M06, M11, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=交易结构、披露附表与尽调命题按同一实体/时期比较，输出差异见证

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=披露效力和修订优先语义已定；sources=https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=实质矛盾与披露充分性

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=交易要点、条件依赖、风险与处理表；proof_route=文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=端点不得各自选互不相容假设；部分扫描区间不是全局外界；counterexample=披露表的未知条目被视为保证完全真实

来源（原表范围）：
https://arxiv.org/html/2301.00876
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D087｜公司登记状态、注册资本、法定代表人与上市信息是否对应同一主体？

分组：10 企业调查、诉讼与执行数据。原评测：CN04。

输入：企业、股权、裁判和执行数据接口

输出：可回溯查询、筛选、汇总及调查报告

形式目标：多表join使用主体键与有效时间；不同快照值作为不同记录

前提：来源表主键、函数依赖和时间字段明确

外部验证：工商数据真实及时性

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；法源query与原文回读已有工程；固定语料与适用法域完整性另证

反例：混用更名前名称和另一同名公司的资本

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T03, T20, T22, T24；证明族：M01, M02, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=多表join使用主体键与有效时间；不同快照值作为不同记录

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=来源表主键、函数依赖和时间字段明确；sources=https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=工商数据真实及时性

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可回溯查询、筛选、汇总及调查报告；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=服务错误≠无记录；schema字段、主体身份、筛选条件、执行次数可重放；counterexample=混用更名前名称和另一同名公司的资本

来源（原表范围）：
https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D088｜子公司、参股比例与投资金额如何穿透关联？

分组：10 企业调查、诉讼与执行数据。原评测：CN04。

输入：企业、股权、裁判和执行数据接口

输出：可回溯查询、筛选、汇总及调查报告

形式目标：穿透关系为带边类型的图查询；持股链、控制和投资额分别表达

前提：穿透定义、闭环及权益计算规则明确

外部验证：间接控制与代持调查

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；法源query与原文回读已有工程；固定语料与适用法域完整性另证；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：循环持股反复乘加产生虚假权益

任务：EXT04, EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T03, T09, T20, T22, T24；证明族：M01, M02, M11, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=穿透关系为带边类型的图查询；持股链、控制和投资额分别表达

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=穿透定义、闭环及权益计算规则明确；sources=https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=间接控制与代持调查

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可回溯查询、筛选、汇总及调查报告；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=服务错误≠无记录；schema字段、主体身份、筛选条件、执行次数可重放；counterexample=循环持股反复乘加产生虚假权益

来源（原表范围）：
https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D089｜企业涉诉案件的原被告、案由、法院、时间和金额分别是什么？

分组：10 企业调查、诉讼与执行数据。原评测：CN04。

输入：企业、股权、裁判和执行数据接口

输出：可回溯查询、筛选、汇总及调查报告

形式目标：企业—案件—角色—金额按键连接，保留原文与记录去重

前提：查询范围和关联谓词明确

外部验证：案件库覆盖与名称关系核验

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；法源query与原文回读已有工程；固定语料与适用法域完整性另证

反例：同一案件不同文书重复算作多案

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T03, T20, T22, T24；证明族：M01, M02, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=企业—案件—角色—金额按键连接，保留原文与记录去重

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=查询范围和关联谓词明确；sources=https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=案件库覆盖与名称关系核验

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可回溯查询、筛选、汇总及调查报告；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=服务错误≠无记录；schema字段、主体身份、筛选条件、执行次数可重放；counterexample=同一案件不同文书重复算作多案

来源（原表范围）：
https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D090｜公司是否有限高、失信或终本记录，各自是什么意思？

分组：10 企业调查、诉讼与执行数据。原评测：CN04。

输入：企业、股权、裁判和执行数据接口

输出：可回溯查询、筛选、汇总及调查报告

形式目标：限高、失信、终本为不同程序记录/状态，不能隐式互推

前提：各状态含义与有效时间法源

外部验证：执行记录更新、解除与注销信息

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展

反例：终本不自动等于永久失信或债务消灭

任务：EXT09, ROOT06, ROOT08, T01, T03, T16, T17, T18, T19, T20, T22, T24；证明族：M02, M03, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=限高、失信、终本为不同程序记录/状态，不能隐式互推

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=各状态含义与有效时间法源；sources=https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=执行记录更新、解除与注销信息

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可回溯查询、筛选、汇总及调查报告；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=服务错误≠无记录；schema字段、主体身份、筛选条件、执行次数可重放；counterexample=终本不自动等于永久失信或债务消灭

来源（原表范围）：
https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D091｜未履行金额、执行标的与原涉案金额能否区别汇总？

分组：10 企业调查、诉讼与执行数据。原评测：CN04。

输入：企业、股权、裁判和执行数据接口

输出：可回溯查询、筛选、汇总及调查报告

形式目标：涉案额、执行标的、未履行额、已付额不同数量类型；归并保留债项键

前提：统计业务口径与扣重政策明确

外部验证：记录完整与金额实际变动

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化

反例：把未履行额与执行标的加成总债务

任务：EXT09, REV02, ROOT02, ROOT04, ROOT06, ROOT08, T01, T02, T08, T09, T10, T22, T24；证明族：M01, M09, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=涉案额、执行标的、未履行额、已付额不同数量类型；归并保留债项键

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=统计业务口径与扣重政策明确；sources=https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=记录完整与金额实际变动

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可回溯查询、筛选、汇总及调查报告；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=服务错误≠无记录；schema字段、主体身份、筛选条件、执行次数可重放；counterexample=把未履行额与执行标的加成总债务

来源（原表范围）：
https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D092｜行政处罚的事实、机关、时间和金额能否与企业关联？

分组：10 企业调查、诉讼与执行数据。原评测：CN04。

输入：企业、股权、裁判和执行数据接口

输出：可回溯查询、筛选、汇总及调查报告

形式目标：行政处罚记录保留机关、主体、行为、日期及结果效力链

前提：决定状态、撤销变更政策明定

外部验证：官方信息核验与申诉状态

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；法源query与原文回读已有工程；固定语料与适用法域完整性另证；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展

反例：已撤销处罚继续标为当前有效违法结论

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T03, T16, T17, T18, T19, T20, T22, T24；证明族：M01, M02, M03, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=行政处罚记录保留机关、主体、行为、日期及结果效力链

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=决定状态、撤销变更政策明定；sources=https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=官方信息核验与申诉状态

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可回溯查询、筛选、汇总及调查报告；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=服务错误≠无记录；schema字段、主体身份、筛选条件、执行次数可重放；counterexample=已撤销处罚继续标为当前有效违法结论

来源（原表范围）：
https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D093｜承办法院、代字、行政区划和联系信息如何多跳查询？

分组：10 企业调查、诉讼与执行数据。原评测：CN04。

输入：企业、股权、裁判和执行数据接口

输出：可回溯查询、筛选、汇总及调查报告

形式目标：代码、机关、地址与区划的连接有版本/有效期，不丢中间见证

前提：机构键和区划变动映射已准入

外部验证：最新地址与办公变动

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；法源query与原文回读已有工程；固定语料与适用法域完整性另证

反例：区划改名不得制造两个不同法院或错用旧送达地址

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T03, T20, T22, T24；证明族：M01, M02, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=代码、机关、地址与区划的连接有版本/有效期，不丢中间见证

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=机构键和区划变动映射已准入；sources=https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=最新地址与办公变动

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可回溯查询、筛选、汇总及调查报告；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=服务错误≠无记录；schema字段、主体身份、筛选条件、执行次数可重放；counterexample=区划改名不得制造两个不同法院或错用旧送达地址

来源（原表范围）：
https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D094｜律所服务记录与案件代理信息如何查询而不虚构关联？

分组：10 企业调查、诉讼与执行数据。原评测：CN04。

输入：企业、股权、裁判和执行数据接口

输出：可回溯查询、筛选、汇总及调查报告

形式目标：案件代理边与律所服务记录分别引用原始关系，不作逆向无根据推断

前提：数据库各表关系语义明确

外部验证：代理信息真实及隐私许可

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；法源query与原文回读已有工程；固定语料与适用法域完整性另证

反例：服务某上市公司不能推出代理该公司全部案件

任务：EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T03, T20, T22, T24；证明族：M01, M02, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=案件代理边与律所服务记录分别引用原始关系，不作逆向无根据推断

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=数据库各表关系语义明确；sources=https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=代理信息真实及隐私许可

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可回溯查询、筛选、汇总及调查报告；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=服务错误≠无记录；schema字段、主体身份、筛选条件、执行次数可重放；counterexample=服务某上市公司不能推出代理该公司全部案件

来源（原表范围）：
https://github.com/CSHaitao/LegalAgentBench/blob/main/README.md
https://github.com/CSHaitao/LegalAgentBench/blob/main/src/schema.py

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D095｜本金、利息、违约金与费用应分别怎样计算？

分组：11 金额、时间和经济敞口。原评测：CN11, US01, US02。

输入：来源数值、利率、日期、合同触发条件

输出：精确值/分段计划/带条件敞口

形式目标：本息违约金费用按独立基数、期间和组合规则解释并守恒抵充

前提：具体可计项目和请求范围明确

外部验证：实际欠款与费用证明

证明路线：请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化

反例：还款后仍用旧本金累计全部期间利息

任务：EXT09, ROOT04, ROOT06, ROOT08, T01, T08, T09, T10, T16, T17, T18, T19, T22, T24；证明族：M08, M09, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=本息违约金费用按独立基数、期间和组合规则解释并守恒抵充

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=具体可计项目和请求范围明确；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=实际欠款与费用证明

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=精确值/分段计划/带条件敞口；proof_route=请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=金额单位与责任性质、计息分段、日期规则、四舍五入及阈值不混用；counterexample=还款后仍用旧本金累计全部期间利息

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D096｜利率倍数问题对应的基准与适用时点是否明确？

分组：11 金额、时间和经济敞口。原评测：CN11, US01, US02。

输入：来源数值、利率、日期、合同触发条件

输出：精确值/分段计划/带条件敞口

形式目标：基准率取值由事件与法律政策决定，倍数运算只作用于被确认基准

前提：利率上限法源、合同类型及过渡规则

外部验证：实际基准发布数据核验

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：用当前LPR倒填所有历史借款期间

任务：EXT09, ROOT04, ROOT06, ROOT08, T01, T03, T08, T09, T10, T20, T22, T24；证明族：M02, M09, M10, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=基准率取值由事件与法律政策决定，倍数运算只作用于被确认基准

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=利率上限法源、合同类型及过渡规则；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=实际基准发布数据核验

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=精确值/分段计划/带条件敞口；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=金额单位与责任性质、计息分段、日期规则、四舍五入及阈值不混用；counterexample=用当前LPR倒填所有历史借款期间

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D097｜现金加股票对价、换股比例与期权行权价如何换算？

分组：11 金额、时间和经济敞口。原评测：CN11, US01, US02。

输入：来源数值、利率、日期、合同触发条件

输出：精确值/分段计划/带条件敞口

形式目标：现金、股份数、股价、汇率和转换比例按维度推导，舍入阶段显式

前提：交易条款、估值时点及舍入规则

外部验证：价格源与员工身份事实

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化

反例：按股计价格与总价混用使倍率相差股份数

任务：EXT09, REV02, ROOT02, ROOT04, ROOT06, ROOT08, T01, T02, T08, T09, T10, T22, T24；证明族：M01, M09, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=现金、股份数、股价、汇率和转换比例按维度推导，舍入阶段显式

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=交易条款、估值时点及舍入规则；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=价格源与员工身份事实

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=精确值/分段计划/带条件敞口；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=金额单位与责任性质、计息分段、日期规则、四舍五入及阈值不混用；counterexample=按股计价格与总价混用使倍率相差股份数

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D098｜提前清偿本金与make-whole溢价是否分别计算？

分组：11 金额、时间和经济敞口。原评测：CN11, US01, US02。

输入：来源数值、利率、日期、合同触发条件

输出：精确值/分段计划/带条件敞口

形式目标：提前清偿本金与premium分账；触发日和适用比例共同验证

前提：提前清偿与豁免条款政策

外部验证：偿债余额和预计交割日期

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：2%溢价计在原授信额度而非应清偿余额

任务：EXT09, ROOT04, ROOT06, ROOT08, T01, T08, T09, T10, T16, T17, T18, T19, T20, T22, T24；证明族：M03, M09, M10, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=提前清偿本金与premium分账；触发日和适用比例共同验证

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=提前清偿与豁免条款政策；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=偿债余额和预计交割日期

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=精确值/分段计划/带条件敞口；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=金额单位与责任性质、计息分段、日期规则、四舍五入及阈值不混用；counterexample=2%溢价计在原授信额度而非应清偿余额

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D099｜30/60/90/120/180天等通知、补正和行使期怎样区分？

分组：11 金额、时间和经济敞口。原评测：CN11, US01, US02。

输入：来源数值、利率、日期、合同触发条件

输出：精确值/分段计划/带条件敞口

形式目标：不同期限带anchor、length、calendar、deadline_effect和证据状态

前提：自然日/工作日、包含日及顺延政策明确

外部验证：到达/知悉/履行事件核验

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：60日补正期未到，仅因30日通知期到便认定终止

任务：EXT09, ROOT06, ROOT08, T01, T08, T16, T17, T18, T19, T20, T22, T24；证明族：M03, M10, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=不同期限带anchor、length、calendar、deadline_effect和证据状态

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=自然日/工作日、包含日及顺延政策明确；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=到达/知悉/履行事件核验

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=精确值/分段计划/带条件敞口；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=金额单位与责任性质、计息分段、日期规则、四舍五入及阈值不混用；counterexample=60日补正期未到，仅因30日通知期到便认定终止

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D100｜相对交割日倒排通知、同意和交付期限是否一致？

分组：11 金额、时间和经济敞口。原评测：CN11, US01, US02。

输入：来源数值、利率、日期、合同触发条件

输出：精确值/分段计划/带条件敞口

形式目标：倒排得到的时间表满足所有前置和日历约束；不可行时报告冲突

前提：交割日期、资源和审批条件明确

外部验证：第三方处理时长及可达性

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明；V2.1机制/策略参考与EXT08路线；不等于实际行为效果或全局策略已经证明

反例：倒排某项日期在过去，不能仍输出可执行完整计划

任务：EXT08, EXT09, ROOT06, ROOT08, T01, T08, T16, T17, T18, T19, T20, T21, T22, T24；证明族：M03, M10, M15, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=倒排得到的时间表满足所有前置和日历约束；不可行时报告冲突

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=交割日期、资源和审批条件明确；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=第三方处理时长及可达性

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=精确值/分段计划/带条件敞口；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=金额单位与责任性质、计息分段、日期规则、四舍五入及阈值不混用；counterexample=倒排某项日期在过去，不能仍输出可执行完整计划

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D101｜债务偿还、收入风险、无偿服务敞口与离职补偿是否错误混加？

分组：11 金额、时间和经济敞口。原评测：CN11, US01, US02。

输入：来源数值、利率、日期、合同触发条件

输出：精确值/分段计划/带条件敞口

形式目标：债务本金、成本、收入风险、或有赔偿用不同数量/条件；只按声明风险函数聚合

前提：现金流、存量、概率与场景口径明确

外部验证：相关性、概率和经济损失评价

证明路线：数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker；V2.1概率/胜率参考与保留时间切分；真实经验效果、因果识别及EXT保证未整体验收

反例：将收入风险当已实现损失并与原收入重复相加

任务：EXT04, EXT06, EXT07, EXT09, ROOT04, ROOT06, ROOT08, T01, T08, T09, T10, T12, T13, T14, T15, T22, T24；证明族：M09, M11, M12, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=债务本金、成本、收入风险、或有赔偿用不同数量/条件；只按声明风险函数聚合

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=现金流、存量、概率与场景口径明确；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=相关性、概率和经济损失评价

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=精确值/分段计划/带条件敞口；proof_route=数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=金额单位与责任性质、计息分段、日期规则、四舍五入及阈值不混用；counterexample=将收入风险当已实现损失并与原收入重复相加

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D102｜终止权行使后服务义务和后续付款是否继续存在？

分组：11 金额、时间和经济敞口。原评测：CN11, US01, US02。

输入：来源数值、利率、日期、合同触发条件

输出：精确值/分段计划/带条件敞口

形式目标：终止后的义务由存续规则更新，不与主履行义务一并清空

前提：终止生效、清理和过渡服务政策

外部验证：后续履行和付款事实

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明

反例：删除终止前已发生的应付款或已产生责任

任务：EXT09, ROOT04, ROOT06, ROOT08, T01, T08, T09, T10, T16, T17, T18, T19, T20, T22, T24；证明族：M03, M09, M10, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=终止后的义务由存续规则更新，不与主履行义务一并清空

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=终止生效、清理和过渡服务政策；sources=https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=后续履行和付款事实

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=精确值/分段计划/带条件敞口；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=金额单位与责任性质、计息分段、日期规则、四舍五入及阈值不混用；counterexample=删除终止前已发生的应付款或已产生责任

来源（原表范围）：
https://github.com/BulouLiu/LeDQA/blob/main/QuestionSchema.json
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D103｜目标营运资金与最终营运资金、收益质量核对怎样支撑价格调整？

分组：11 金额、时间和经济敞口。原评测：US02。

输入：来源数值、利率、日期、合同触发条件

输出：精确值/分段计划/带条件敞口

形式目标：价格调整由同一营运资金定义、参考日、排除项和对账差异计算

前提：SPA价格公式和会计约定准入

外部验证：报表真实、收益质量及审计判断

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：目标与期末使用不同科目范围仍报告精确差额

任务：EXT04, EXT09, ROOT04, ROOT06, ROOT08, T01, T03, T08, T09, T10, T20, T22, T24；证明族：M02, M09, M11, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=价格调整由同一营运资金定义、参考日、排除项和对账差异计算

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=SPA价格公式和会计约定准入；sources=https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=报表真实、收益质量及审计判断

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=精确值/分段计划/带条件敞口；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=金额单位与责任性质、计息分段、日期规则、四舍五入及阈值不混用；counterexample=目标与期末使用不同科目范围仍报告精确差额

来源（原表范围）：
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D104｜能否起草回应对方主张的答辩，而不是重复案情？

分组：12 起草、修订与交付。原评测：CN13, CN14, US01, US02。

输入：已分析案件/合同、模板及修改意见

输出：可读正文、红线、结构表与实际文件

形式目标：答辩覆盖必答请求，命题有出处/假设，承认与保留明确

前提：必答清单和代理授权独立提供

外部验证：论证质量和语言说服力

证明路线：来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有依赖/增量复用；EXT05替代来源与支持反链仍为深化目标；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：只复制原告事实也获文本相似高分不能称有效答辩

任务：EXT05, EXT09, ROOT05, ROOT06, ROOT08, T01, T04, T16, T17, T18, T19, T22, T24；证明族：M05, M08, M13, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=答辩覆盖必答请求，命题有出处/假设，承认与保留明确

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=必答清单和代理授权独立提供；sources=https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=论证质量和语言说服力

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可读正文、红线、结构表与实际文件；proof_route=来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=修改后重抽取核对语义差量、无关条款、定义、交叉引用与金额一致；counterexample=只复制原告事实也获文本相似高分不能称有效答辩

来源（原表范围）：
https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D105｜能否写出只依现有材料的事实段、理由段与裁判段？

分组：12 起草、修订与交付。原评测：CN13, CN14, US01, US02。

输入：已分析案件/合同、模板及修改意见

输出：可读正文、红线、结构表与实际文件

形式目标：各段受保护命题与同一事实/论证/结果对象一致，不跳过上游条件

前提：段落生成关系与允许修辞范围明确

外部验证：任意文本全语义正确与法律充分性

证明路线：文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：给金标事实的阶段分数不得当原始卷宗全链分数

任务：EXT03, EXT09, ROOT03, ROOT05, ROOT06, ROOT08, T01, T03, T05, T06, T22, T24；证明族：M04, M06, M13, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=各段受保护命题与同一事实/论证/结果对象一致，不跳过上游条件

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=段落生成关系与允许修辞范围明确；sources=https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=任意文本全语义正确与法律充分性

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可读正文、红线、结构表与实际文件；proof_route=文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=修改后重抽取核对语义差量、无关条款、定义、交叉引用与金额一致；counterexample=给金标事实的阶段分数不得当原始卷宗全链分数

来源（原表范围）：
https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D106｜原告诉讼请求列表是否完整保留各项给付与费用？

分组：12 起草、修订与交付。原评测：CN13, CN14, US01, US02。

输入：已分析案件/合同、模板及修改意见

输出：可读正文、红线、结构表与实际文件

形式目标：已确认诉请列表到文书列表为身份保持的覆盖映射，无遗漏/错误合并

前提：主/备位及分项请求清单独立确认

外部验证：诉请是否最优或法定可支持

证明路线：请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：两项同金额但不同请求对象不能在去重时删一项

任务：EXT09, ROOT05, ROOT06, ROOT08, T01, T16, T17, T18, T19, T22, T24；证明族：M08, M13, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=已确认诉请列表到文书列表为身份保持的覆盖映射，无遗漏/错误合并

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=主/备位及分项请求清单独立确认；sources=https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=诉请是否最优或法定可支持

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可读正文、红线、结构表与实际文件；proof_route=请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=修改后重抽取核对语义差量、无关条款、定义、交叉引用与金额一致；counterexample=两项同金额但不同请求对象不能在去重时删一项

来源（原表范围）：
https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D107｜客户提示是否说明裁判或监管变化对业务的影响及不确定处？

分组：12 起草、修订与交付。原评测：CN13, CN14, US01, US02。

输入：已分析案件/合同、模板及修改意见

输出：可读正文、红线、结构表与实际文件

形式目标：法律变化、裁判效果、执法姿态、预期修法分别呈现并带时间来源

前提：所涉业务影响路径与法律解释

外部验证：未来执法预测和面向客户的解释质量

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：“暂不执法”写成“规范已经废止”应失败

任务：EXT09, ROOT05, ROOT06, ROOT08, T01, T03, T16, T17, T18, T19, T20, T22, T24；证明族：M02, M03, M13, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=法律变化、裁判效果、执法姿态、预期修法分别呈现并带时间来源

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=所涉业务影响路径与法律解释；sources=https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=未来执法预测和面向客户的解释质量

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可读正文、红线、结构表与实际文件；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=修改后重抽取核对语义差量、无关条款、定义、交叉引用与金额一致；counterexample=“暂不执法”写成“规范已经废止”应失败

来源（原表范围）：
https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D108｜律师备忘录是否兼顾结论、结构、法律依据和数值例子？

分组：12 起草、修订与交付。原评测：CN13, CN14, US01, US02。

输入：已分析案件/合同、模板及修改意见

输出：可读正文、红线、结构表与实际文件

形式目标：指定章节/结论/引文/数值样例可逐项验证；核心观察保持

前提：需求清单、模板与可用依据明确

外部验证：组织、说服力、受众适配由经验/审核评价

证明路线：数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：数值正确但结论删去假设条件不得通过业务合同

任务：EXT09, ROOT04, ROOT05, ROOT06, ROOT08, T01, T08, T09, T10, T22, T24；证明族：M09, M13, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=指定章节/结论/引文/数值样例可逐项验证；核心观察保持

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=需求清单、模板与可用依据明确；sources=https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=组织、说服力、受众适配由经验/审核评价

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可读正文、红线、结构表与实际文件；proof_route=数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=修改后重抽取核对语义差量、无关条款、定义、交叉引用与金额一致；counterexample=数值正确但结论删去假设条件不得通过业务合同

来源（原表范围）：
https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D109｜董事会决议是否含明确批准事项、理由与利益冲突保障？

分组：12 起草、修订与交付。原评测：CN13, CN14, US01, US02。

输入：已分析案件/合同、模板及修改意见

输出：可读正文、红线、结构表与实际文件

形式目标：决议生成保留机关、表决、授权事项、冲突保障；草稿不构成实际批准事件

前提：公司治理规则、真实程序材料

外部验证：真实授权、利益冲突评价

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：生成“已决议”措辞不能使法定程序自动视为完成

任务：EXT09, REV02, ROOT02, ROOT05, ROOT06, ROOT08, T01, T02, T16, T17, T18, T19, T22, T24；证明族：M01, M03, M13, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=决议生成保留机关、表决、授权事项、冲突保障；草稿不构成实际批准事件

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=公司治理规则、真实程序材料；sources=https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=真实授权、利益冲突评价

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可读正文、红线、结构表与实际文件；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=修改后重抽取核对语义差量、无关条款、定义、交叉引用与金额一致；counterexample=生成“已决议”措辞不能使法定程序自动视为完成

来源（原表范围）：
https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D110｜合同或附属协议草稿是否遵循提供的先例和termsheet？

分组：12 起草、修订与交付。原评测：CN13, CN14, US01, US02。

输入：已分析案件/合同、模板及修改意见

输出：可读正文、红线、结构表与实际文件

形式目标：草案满足termsheet已核验约束；模板变换保持未授权变动区域

前提：先例适用、目标条款及冲突处理政策

外部验证：条款商业/法律质量

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：复用模板中的旧客户名或互斥条款应被识别

任务：EXT04, EXT09, ROOT05, ROOT06, ROOT08, T01, T09, T16, T17, T18, T19, T22, T24；证明族：M03, M11, M13, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=草案满足termsheet已核验约束；模板变换保持未授权变动区域

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=先例适用、目标条款及冲突处理政策；sources=https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=条款商业/法律质量

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可读正文、红线、结构表与实际文件；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=修改后重抽取核对语义差量、无关条款、定义、交叉引用与金额一致；counterexample=复用模板中的旧客户名或互斥条款应被识别

来源（原表范围）：
https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D111｜对方红线修改影响哪些权利、义务、风险与其他定义？

分组：12 起草、修订与交付。原评测：CN13, CN14, US01, US02。

输入：已分析案件/合同、模板及修改意见

输出：可读正文、红线、结构表与实际文件

形式目标：修改点及所有依赖闭包形成受影响区；区外受保护观察不变

前提：依赖图健全、编辑目标和条款语义准入

外部验证：隐含影响与开放语言理解

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：修改定义后正文不变不代表法律效果未变

任务：EXT04, EXT09, ROOT05, ROOT06, ROOT08, T01, T09, T16, T17, T18, T19, T22, T24；证明族：M03, M11, M13, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=修改点及所有依赖闭包形成受影响区；区外受保护观察不变

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=依赖图健全、编辑目标和条款语义准入；sources=https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=隐含影响与开放语言理解

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可读正文、红线、结构表与实际文件；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=修改后重抽取核对语义差量、无关条款、定义、交叉引用与金额一致；counterexample=修改定义后正文不变不代表法律效果未变

来源（原表范围）：
https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D112｜披露附表、并购协议、融资承诺与最终文档是否一致？

分组：12 起草、修订与交付。原评测：CN13, CN14, US01, US02。

输入：已分析案件/合同、模板及修改意见

输出：可读正文、红线、结构表与实际文件

形式目标：多文书对同一承诺/金额/事件满足共享约束Γ，差异不被静默覆盖

前提：各文档优先/整合条款政策明确

外部验证：不明条款和遗漏附件的解释

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：融资承诺和终版额度不同仍输出“全部一致”须失败

任务：EXT04, EXT09, ROOT05, ROOT06, ROOT08, T01, T09, T16, T17, T18, T19, T22, T24；证明族：M03, M11, M13, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=多文书对同一承诺/金额/事件满足共享约束Γ，差异不被静默覆盖

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=各文档优先/整合条款政策明确；sources=https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=不明条款和遗漏附件的解释

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可读正文、红线、结构表与实际文件；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=修改后重抽取核对语义差量、无关条款、定义、交叉引用与金额一致；counterexample=融资承诺和终版额度不同仍输出“全部一致”须失败

来源（原表范围）：
https://github.com/CSHaitao/CaseGen/blob/main/README.md
https://github.com/JosieZhou00/ClaimGen-CN/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D113｜法律术语翻译、文书错字与语言校对是否保持原意思？

分组：12 起草、修订与交付。原评测：CN01, CN02。

输入：已分析案件/合同、模板及修改意见

输出：可读正文、红线、结构表与实际文件

形式目标：受控术语翻译保持角色/否定/例外/数值；不支持结构保留人工审核

前提：术语映射与目标语法范围固定

外部验证：自由法律翻译全语义等价

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：“may”译成无条件“应当”、否定词丢失

任务：EXT09, ROOT03, ROOT05, ROOT06, ROOT08, T01, T03, T20, T22, T24；证明族：M02, M04, M13, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=受控术语翻译保持角色/否定/例外/数值；不支持结构保留人工审核

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=术语映射与目标语法范围固定；sources=https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=自由法律翻译全语义等价

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可读正文、红线、结构表与实际文件；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=修改后重抽取核对语义差量、无关条款、定义、交叉引用与金额一致；counterexample=“may”译成无条件“应当”、否定词丢失

来源（原表范围）：
https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D114｜摘要是否覆盖材料要点且不生成无依据事实？

分组：12 起草、修订与交付。原评测：CN01, CN02, CN03。

输入：已分析案件/合同、模板及修改意见

输出：可读正文、红线、结构表与实际文件

形式目标：摘要的受保护命题有来源；已独立确定的关键要点均覆盖

前提：摘要目标、重要性口径和要点清单明确

外部验证：语义压缩质量及未知关键点遗漏

证明路线：文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；现有依赖/增量复用；EXT05替代来源与支持反链仍为深化目标；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：只保留支持方论据，删掉关键例外，不可称完整摘要

任务：EXT05, EXT09, ROOT03, ROOT05, ROOT06, ROOT08, T01, T03, T04, T22, T24；证明族：M04, M05, M13, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=摘要的受保护命题有来源；已独立确定的关键要点均覆盖

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=摘要目标、重要性口径和要点清单明确；sources=https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1
https://github.com/Dai-shen/LAiW/blob/main/README.md

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=语义压缩质量及未知关键点遗漏

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可读正文、红线、结构表与实际文件；proof_route=文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=修改后重抽取核对语义差量、无关条款、定义、交叉引用与金额一致；counterexample=只保留支持方论据，删掉关键例外，不可称完整摘要

来源（原表范围）：
https://github.com/open-compass/LawBench/blob/main/README.md
https://arxiv.org/html/2409.20288v1
https://github.com/Dai-shen/LAiW/blob/main/README.md

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D115｜输出文件名、格式、表格和指定多份交付物是否真实存在且可读取？

分组：12 起草、修订与交付。原评测：US02。

输入：已分析案件/合同、模板及修改意见

输出：可读正文、红线、结构表与实际文件

形式目标：必交文件存在、可解析、名称格式正确；回读的关键语义/表格等于核验对象

前提：输出语言、格式规范、解析器可信范围明确

外部验证：跨阅读器呈现和自由文本语义

证明路线：交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；工具、权限与跨运行安全：调用小步语义与作用域归纳；双运行自组合证明非干涉；允许披露投影明确；进程沙箱另验；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标；现有出域硬门/本机免密钥/按案绑定；跨运行性质及威胁模型仍需单独证明

反例：文件存在但正文为空，或批注暴露内部备算，必须失败

任务：EXT09, ROOT05, ROOT06, ROOT07, ROOT08, T01, T22, T23, T24；证明族：M13, M14, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=必交文件存在、可解析、名称格式正确；回读的关键语义/表格等于核验对象

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=输出语言、格式规范、解析器可信范围明确；sources=https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/docs/eval-strategies.md
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=跨阅读器呈现和自由文本语义

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可读正文、红线、结构表与实际文件；proof_route=交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；工具、权限与跨运行安全：调用小步语义与作用域归纳；双运行自组合证明非干涉；允许披露投影明确；进程沙箱另验；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=修改后重抽取核对语义差量、无关条款、定义、交叉引用与金额一致；counterexample=文件存在但正文为空，或批注暴露内部备算，必须失败

来源（原表范围）：
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/docs/eval-strategies.md
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D116｜尽调请求清单与资料室目录是否对应，哪些材料仍缺失？

分组：13 办案、交易工作流与策略。原评测：US01, US02。

输入：资料室、任务目标、时间表与工具

输出：可执行事项表、调查/谈判建议和交付轨迹

形式目标：required_documents与VDR清单差集精确，未提交流转为明确未决

前提：必需文件清单从任务及规则独立建立

外部验证：未知文件与资料室完整性

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证

反例：缺失材料不得通过从现有目录生成“必需清单”抹去

任务：EXT09, ROOT06, ROOT08, T01, T03, T20, T22, T24；证明族：M02, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=required_documents与VDR清单差集精确，未提交流转为明确未决

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=必需文件清单从任务及规则独立建立；sources=https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=未知文件与资料室完整性

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可执行事项表、调查/谈判建议和交付轨迹；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=规范允许、商业偏好、观察相关性与因果效果分别绑定；counterexample=缺失材料不得通过从现有目录生成“必需清单”抹去

来源（原表范围）：
https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D117｜交割清单、审批、同意与解除条件是否满足先后依赖？

分组：13 办案、交易工作流与策略。原评测：US01, US02。

输入：资料室、任务目标、时间表与工具

输出：可执行事项表、调查/谈判建议和交付轨迹

形式目标：行动/条件图中的发生事件、权限与前置满足；不存在合法排序则报告不可行

前提：独立法定和交易前置条件明确

外部验证：第三方是否配合和材料真实性

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；Harness锚点/日历计算已有作者测试记录；跨政策时态含义还需证明；V2.1机制/策略参考与EXT08路线；不等于实际行为效果或全局策略已经证明

反例：互相依赖形成环仍生成无条件可执行清单

任务：EXT08, EXT09, ROOT06, ROOT08, T01, T08, T16, T17, T18, T19, T20, T21, T22, T24；证明族：M03, M10, M15, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=行动/条件图中的发生事件、权限与前置满足；不存在合法排序则报告不可行

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=独立法定和交易前置条件明确；sources=https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=第三方是否配合和材料真实性

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可执行事项表、调查/谈判建议和交付轨迹；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；日历、期限与效力时间：对已选日历规则证明变换；表驱动节假日为外部参数；失效/中断/中止通过状态转换；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=规范允许、商业偏好、观察相关性与因果效果分别绑定；counterexample=互相依赖形成环仍生成无条件可执行清单

来源（原表范围）：
https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D118｜对模糊条款应何时寻求书面确认、同意或豁免？

分组：13 办案、交易工作流与策略。原评测：US01, US02。

输入：资料室、任务目标、时间表与工具

输出：可执行事项表、调查/谈判建议和交付轨迹

形式目标：书面确认、豁免与补证为合法行动；价值由明确预测/信息模型计算

前提：可用行动权限、不可豁免规范及成本明定

外部验证：解释不确定性、对手响应和因果假设

证明路线：法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；V2.1概率/胜率参考与保留时间切分；真实经验效果、因果识别及EXT保证未整体验收；V2.1机制/策略参考与EXT08路线；不等于实际行为效果或全局策略已经证明

反例：强制法义务不能由私人豁免事件删除

任务：EXT06, EXT07, EXT08, EXT09, ROOT06, ROOT08, T01, T12, T13, T14, T15, T16, T17, T18, T19, T21, T22, T24；证明族：M03, M12, M15, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=书面确认、豁免与补证为合法行动；价值由明确预测/信息模型计算

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=可用行动权限、不可豁免规范及成本明定；sources=https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=解释不确定性、对手响应和因果假设

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可执行事项表、调查/谈判建议和交付轨迹；proof_route=法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=规范允许、商业偏好、观察相关性与因果效果分别绑定；counterexample=强制法义务不能由私人豁免事件删除

来源（原表范围）：
https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D119｜对关键基础设施和收入来源的风险应怎样排序？

分组：13 办案、交易工作流与策略。原评测：US01, US02。

输入：资料室、任务目标、时间表与工具

输出：可执行事项表、调查/谈判建议和交付轨迹

形式目标：排序按明示偏好/风险度量执行，硬法律约束不被权重抵消

前提：风险维度、客户偏好与共有依赖已确定

外部验证：风险概率、效用和外部校准

证明路线：数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker；V2.1机制/策略参考与EXT08路线；不等于实际行为效果或全局策略已经证明

反例：将任意重要性权重误标法定唯一优先序

任务：EXT04, EXT08, EXT09, ROOT04, ROOT06, ROOT08, T01, T08, T09, T10, T21, T22, T24；证明族：M09, M11, M15, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=排序按明示偏好/风险度量执行，硬法律约束不被权重抵消

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=风险维度、客户偏好与共有依赖已确定；sources=https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=风险概率、效用和外部校准

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可执行事项表、调查/谈判建议和交付轨迹；proof_route=数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=规范允许、商业偏好、观察相关性与因果效果分别绑定；counterexample=将任意重要性权重误标法定唯一优先序

来源（原表范围）：
https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D120｜先例市场条款比较如何支持谈判立场而非成为法律规则？

分组：13 办案、交易工作流与策略。原评测：US01, US02。

输入：资料室、任务目标、时间表与工具

输出：可执行事项表、调查/谈判建议和交付轨迹

形式目标：先例条款分布与规范效力分类型；建议明确来自市场样本而非法律义务

前提：样本口径和谈判目标明定

外部验证：选择偏差和对手反应

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；V2.1概率/胜率参考与保留时间切分；真实经验效果、因果识别及EXT保证未整体验收；V2.1机制/策略参考与EXT08路线；不等于实际行为效果或全局策略已经证明

反例：多数合同如此写不自动推导依法必须如此

任务：EXT06, EXT07, EXT08, EXT09, ROOT06, ROOT08, T01, T03, T12, T13, T14, T15, T20, T21, T22, T24；证明族：M02, M12, M15, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=先例条款分布与规范效力分类型；建议明确来自市场样本而非法律义务

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=样本口径和谈判目标明定；sources=https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=选择偏差和对手反应

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可执行事项表、调查/谈判建议和交付轨迹；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=规范允许、商业偏好、观察相关性与因果效果分别绑定；counterexample=多数合同如此写不自动推导依法必须如此

来源（原表范围）：
https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D121｜第三方传票应提出何种异议、撤销申请或保护措施？

分组：13 办案、交易工作流与策略。原评测：US01, US02。

输入：资料室、任务目标、时间表与工具

输出：可执行事项表、调查/谈判建议和交付轨迹

形式目标：异议/撤销/保护措施按法域、主体资格、阶段及期限组成合法选项

前提：美国对应程序规则与具体事实准入

外部验证：最佳策略与法官反应

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；ULM12已有类型化认定及程序基础；V2.1全领域规则族仍待逐族验收；V2.1机制/策略参考与EXT08路线；不等于实际行为效果或全局策略已经证明

反例：将非当事人异议路径无条件给另一诉讼当事人

任务：EXT08, EXT09, ROOT06, ROOT08, T01, T03, T16, T17, T18, T19, T20, T21, T22, T24；证明族：M02, M03, M07, M15, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=异议/撤销/保护措施按法域、主体资格、阶段及期限组成合法选项

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=美国对应程序规则与具体事实准入；sources=https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=最佳策略与法官反应

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可执行事项表、调查/谈判建议和交付轨迹；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；证明责任与程序：规则级条件决策树归纳；反证测试；使用时点/权限和结果类型逐层保持；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=规范允许、商业偏好、观察相关性与因果效果分别绑定；counterexample=将非当事人异议路径无条件给另一诉讼当事人

来源（原表范围）：
https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D122｜庭审或口头辩论提纲能否回应最佳反方观点与具体事实？

分组：13 办案、交易工作流与策略。原评测：US01, US02。

输入：资料室、任务目标、时间表与工具

输出：可执行事项表、调查/谈判建议和交付轨迹

形式目标：提纲覆盖冻结的主要主张/反驳图并保留证据依赖与备位结构

前提：论证候选范围及对抗目标明确

外部验证：未知最佳反方、庭审表现和说服力

证明路线：来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：现有依赖/增量复用；EXT05替代来源与支持反链仍为深化目标；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：只列弱反方并以数量宣称已回应最强反方

任务：EXT03, EXT05, EXT09, ROOT05, ROOT06, ROOT08, T01, T04, T05, T06, T22, T24；证明族：M05, M06, M13, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=提纲覆盖冻结的主要主张/反驳图并保留证据依赖与备位结构

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=论证候选范围及对抗目标明确；sources=https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=未知最佳反方、庭审表现和说服力

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可执行事项表、调查/谈判建议和交付轨迹；proof_route=来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=规范允许、商业偏好、观察相关性与因果效果分别绑定；counterexample=只列弱反方并以数量宣称已回应最强反方

来源（原表范围）：
https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D123｜多跳法律工具查询是否足以支撑最后报告中的每项陈述？

分组：13 办案、交易工作流与策略。原评测：US01, US02。

输入：资料室、任务目标、时间表与工具

输出：可执行事项表、调查/谈判建议和交付轨迹

形式目标：最终每个数据断言链接查询输入、中间连接、原记录与转换见证

前提：查询器/库快照及字段语义固定

外部验证：原始服务真实性和覆盖

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；工具、权限与跨运行安全：调用小步语义与作用域归纳；双运行自组合证明非干涉；允许披露投影明确；进程沙箱另验；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；现有依赖/增量复用；EXT05替代来源与支持反链仍为深化目标；现有出域硬门/本机免密钥/按案绑定；跨运行性质及威胁模型仍需单独证明

反例：接口超时返回空列表，不能写成查无诉讼

任务：EXT05, EXT09, ROOT06, ROOT07, ROOT08, T01, T03, T04, T20, T22, T23, T24；证明族：M02, M05, M14, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=最终每个数据断言链接查询输入、中间连接、原记录与转换见证

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=查询器/库快照及字段语义固定；sources=https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=原始服务真实性和覆盖

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=可执行事项表、调查/谈判建议和交付轨迹；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；工具、权限与跨运行安全：调用小步语义与作用域归纳；双运行自组合证明非干涉；允许披露投影明确；进程沙箱另验；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=规范允许、商业偏好、观察相关性与因果效果分别绑定；counterexample=接口超时返回空列表，不能写成查无诉讼

来源（原表范围）：
https://github.com/harveyai/biglaw-bench/blob/main/README.md
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv
https://github.com/harveyai/harvey-labs/blob/dfd17ab1e0e20fd3a53d4b976b31585b1ebf94c2/tasks/corporate-ma/analyze-change-of-control-provisions-across-targets-material-contracts/task.json
https://api.github.com/repos/harveyai/harvey-labs/git/trees/07f3786af20cfb7bcc4546d8da1133bf72ffa1b4

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D124｜专业利益冲突是否被识别并在批准中给出保障措施？

分组：14 伦理、隐私与表达可靠性。原评测：CN02, CN05, US01, US03。

输入：伦理题、披露政策、敏感材料及工作产品

输出：范围明确的伦理判断与披露/风险说明

形式目标：利益关系图触发已登记的冲突与处置义务；豁免或批准需适当权限

前提：职业/公司规则和不可豁免冲突明确

外部验证：未披露关系及法律伦理评价

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；工具、权限与跨运行安全：调用小步语义与作用域归纳；双运行自组合证明非干涉；允许披露投影明确；进程沙箱另验；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；现有出域硬门/本机免密钥/按案绑定；跨运行性质及威胁模型仍需单独证明

反例：只生成董事会批准草稿就自动消除实际利益冲突

任务：EXT09, REV02, ROOT02, ROOT06, ROOT07, ROOT08, T01, T02, T16, T17, T18, T19, T22, T23, T24；证明族：M01, M03, M14, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=利益关系图触发已登记的冲突与处置义务；豁免或批准需适当权限

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=职业/公司规则和不可豁免冲突明确；sources=https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=未披露关系及法律伦理评价

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=范围明确的伦理判断与披露/风险说明；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；工具、权限与跨运行安全：调用小步语义与作用域归纳；双运行自组合证明非干涉；允许披露投影明确；进程沙箱另验；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=原生rubric、机器检查、法律审核、统计验证分别记录；不得从all-pass升级形式完备；counterexample=只生成董事会批准草稿就自动消除实际利益冲突

来源（原表范围）：
https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D125｜回答是否体现偏见、歧视或不当的法律伦理判断？

分组：14 伦理、隐私与表达可靠性。原评测：CN02, CN05, US01, US03。

输入：伦理题、披露政策、敏感材料及工作产品

输出：范围明确的伦理判断与披露/风险说明

形式目标：可指定的反事实输入不变性/群体风险指标分别检验；不自动等同公平全概念

前提：哪些属性不应影响哪些输出由法律政策确定

外部验证：结构偏差、测量误差及价值争议

证明路线：概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；工具、权限与跨运行安全：调用小步语义与作用域归纳；双运行自组合证明非干涉；允许披露投影明确；进程沙箱另验；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：V2.1概率/胜率参考与保留时间切分；真实经验效果、因果识别及EXT保证未整体验收；现有出域硬门/本机免密钥/按案绑定；跨运行性质及威胁模型仍需单独证明

反例：移除敏感属性但代理变量仍泄露，不得声称已证明公平

任务：EXT06, EXT07, EXT09, ROOT06, ROOT07, ROOT08, T01, T12, T13, T14, T15, T22, T23, T24；证明族：M12, M14, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=可指定的反事实输入不变性/群体风险指标分别检验；不自动等同公平全概念

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=哪些属性不应影响哪些输出由法律政策确定；sources=https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=结构偏差、测量误差及价值争议

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=范围明确的伦理判断与披露/风险说明；proof_route=概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；工具、权限与跨运行安全：调用小步语义与作用域归纳；双运行自组合证明非干涉；允许披露投影明确；进程沙箱另验；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=原生rubric、机器检查、法律审核、统计验证分别记录；不得从all-pass升级形式完备；counterexample=移除敏感属性但代理变量仍泄露，不得声称已证明公平

来源（原表范围）：
https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D126｜隐私政策如何描述收集、使用、共享、保存与用户权利？

分组：14 伦理、隐私与表达可靠性。原评测：CN02, CN05, US01, US03。

输入：伦理题、披露政策、敏感材料及工作产品

输出：范围明确的伦理判断与披露/风险说明

形式目标：隐私政策承诺、实际数据流与准许用途分开，检查指定披露/行为规则

前提：数据类别、目的、许可及保存政策

外部验证：真实运营是否遵守、用户理解

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；工具、权限与跨运行安全：调用小步语义与作用域归纳；双运行自组合证明非干涉；允许披露投影明确；进程沙箱另验；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；现有出域硬门/本机免密钥/按案绑定；跨运行性质及威胁模型仍需单独证明

反例：文本写“不共享”不能直接证明代码与运营从不共享

任务：EXT09, ROOT06, ROOT07, ROOT08, T01, T03, T16, T17, T18, T19, T20, T22, T23, T24；证明族：M02, M03, M14, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=隐私政策承诺、实际数据流与准许用途分开，检查指定披露/行为规则

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=数据类别、目的、许可及保存政策；sources=https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=真实运营是否遵守、用户理解

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=范围明确的伦理判断与披露/风险说明；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；工具、权限与跨运行安全：调用小步语义与作用域归纳；双运行自组合证明非干涉；允许披露投影明确；进程沙箱另验；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=原生rubric、机器检查、法律审核、统计验证分别记录；不得从all-pass升级形式完备；counterexample=文本写“不共享”不能直接证明代码与运营从不共享

来源（原表范围）：
https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D127｜供应链披露是否包含规定项目，与最佳实践是否区分？

分组：14 伦理、隐私与表达可靠性。原评测：CN02, CN05, US01, US03。

输入：伦理题、披露政策、敏感材料及工作产品

输出：范围明确的伦理判断与披露/风险说明

形式目标：法定必需披露集合逐项覆盖；最佳实践保持建议类型

前提：适用主体、年度、披露规范明定

外部验证：实质信息真实充分

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展

反例：遗漏法定项目却用更多可选披露补分，不算满足

任务：EXT09, ROOT06, ROOT08, T01, T03, T16, T17, T18, T19, T20, T22, T24；证明族：M02, M03, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=法定必需披露集合逐项覆盖；最佳实践保持建议类型

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=适用主体、年度、披露规范明定；sources=https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=实质信息真实充分

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=范围明确的伦理判断与披露/风险说明；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=原生rubric、机器检查、法律审核、统计验证分别记录；不得从all-pass升级形式完备；counterexample=遗漏法定项目却用更多可选披露补分，不算满足

来源（原表范围）：
https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D128｜法律与道德、社会影响问题能否给出符合题目要求的判断？

分组：14 伦理、隐私与表达可靠性。原评测：CN02, CN05, US01, US03。

输入：伦理题、披露政策、敏感材料及工作产品

输出：范围明确的伦理判断与披露/风险说明

形式目标：可形式化的是明示价值序/约束下的决策与敏感性，不从事实推出价值

前提：价值前提及冲突取舍明确授权

外部验证：道德正当性与社会影响评价

证明路线：概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：V2.1概率/胜率参考与保留时间切分；真实经验效果、因果识别及EXT保证未整体验收；V2.1机制/策略参考与EXT08路线；不等于实际行为效果或全局策略已经证明

反例：把评分rubric或历史多数偏好当规范真理

任务：EXT06, EXT07, EXT08, EXT09, ROOT06, ROOT08, T01, T12, T13, T14, T15, T21, T22, T24；证明族：M12, M15, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=可形式化的是明示价值序/约束下的决策与敏感性，不从事实推出价值

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=价值前提及冲突取舍明确授权；sources=https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=道德正当性与社会影响评价

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=范围明确的伦理判断与披露/风险说明；proof_route=概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；合法策略与决策：反向归纳/贝尔曼；共享参数不矩形时保留耦合；外部行为不能由软件保证；统计因果分层；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=原生rubric、机器检查、法律审核、统计验证分别记录；不得从all-pass升级形式完备；counterexample=把评分rubric或历史多数偏好当规范真理

来源（原表范围）：
https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D129｜引文、事实和数值是否有据，是否有幻觉或相关但误用的信息？

分组：14 伦理、隐私与表达可靠性。原评测：CN02, CN05, US01, US03。

输入：伦理题、披露政策、敏感材料及工作产品

输出：范围明确的伦理判断与披露/风险说明

形式目标：引文回读、数值重算、支持范围与声明逐项绑定；冲突未决不升级

前提：保护命题及已选语义定义

外部验证：自由文本幻觉识别召回

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；现有依赖/增量复用；EXT05替代来源与支持反链仍为深化目标；ULM13精确表达与Harness Decimal参考；实务计算政策仍需法源绑定和实现精化；Harness真实DOCX终局检查已有；有意义的语义frame/lens是新增证明目标

反例：引用真实但不支持该命题仍应失败

任务：EXT05, EXT09, ROOT04, ROOT05, ROOT06, ROOT08, T01, T03, T04, T08, T09, T10, T20, T22, T24；证明族：M02, M05, M09, M13, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=引文回读、数值重算、支持范围与声明逐项绑定；冲突未决不升级

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=保护命题及已选语义定义；sources=https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=自由文本幻觉识别召回

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=范围明确的伦理判断与披露/风险说明；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；来源代数与替代支持：有限正Horn迭代归纳；布尔评价与闭包对应；单项极小性与全反链完备性分开；数量与账本：递归解释器等价；账本逐交易守恒；对偶/区间/分支证书，不把全部连续域化为有限点；交付与修改：受限模板及编辑程序结构归纳；部分lens定律；独立回读，任意自由文字不默认总逆变换；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=原生rubric、机器检查、法律审核、统计验证分别记录；不得从all-pass升级形式完备；counterexample=引用真实但不支持该命题仍应失败

来源（原表范围）：
https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D130｜不同事实、规则、法域及假设的结论是否被不当混成单一确定答案？

分组：14 伦理、隐私与表达可靠性。原评测：CN02, CN05, US01, US03。

输入：伦理题、披露政策、敏感材料及工作产品

输出：范围明确的伦理判断与披露/风险说明

形式目标：不同κ、事实假设或解释的结果不得组成一个无条件见证

前提：共同身份及相容关系明确

外部验证：跨情景自然语言投影审核

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭；V2.1已有表示层与共同键，EXT04约化/共享关系新增，不重新描述成尚无checker

反例：从互斥分支各取有利结论合并必须拒绝

任务：EXT03, EXT04, EXT09, REV02, ROOT02, ROOT06, ROOT08, T01, T02, T05, T06, T09, T22, T24；证明族：M01, M06, M11, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=不同κ、事实假设或解释的结果不得组成一个无条件见证

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=共同身份及相容关系明确；sources=https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=跨情景自然语言投影审核

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=范围明确的伦理判断与披露/风险说明；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；共同约束与约化：固定Γ下证明双包含；更新Γ要换主体；局部边界经逆像连接，不凭局部可行直接拼全局可行；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=原生rubric、机器检查、法律审核、统计验证分别记录；不得从all-pass升级形式完备；counterexample=从互斥分支各取有利结论合并必须拒绝

来源（原表范围）：
https://arxiv.org/html/2409.20288v1
https://arxiv.org/html/2512.04578v2
https://hazyresearch.stanford.edu/legalbench/tasks/
https://github.com/harveyai/biglaw-bench/blob/main/blb-core/core-samples.csv

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D131｜法条是否明文赋予私人起诉实施权利的途径？

分组：15 美国法特定问题与法律语言任务。原评测：US03。

输入：美国法条、最高法院问题、证券起诉状或判决节选

输出：任务特定的解释、匹配和抽取

形式目标：规定的私人起诉途径/权限与实体权利分别标识，并在选择法片段内判定

前提：具体美国法条语义及题型范围已核定

外部验证：隐含诉权与法条解释不由字符串解决

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；四模态、规则及程序转换已有；交易权能/存续/引用作用域完整业务语义需扩展；现有LegalClaim、DomainBundle及V2.1可行域基础；完整业务请求空间未全闭合

反例：存在禁止性条文不自动推出任何私人可起诉

任务：EXT09, ROOT06, ROOT08, T01, T03, T16, T17, T18, T19, T20, T22, T24；证明族：M02, M03, M08, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=规定的私人起诉途径/权限与实体权利分别标识，并在选择法片段内判定

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=具体美国法条语义及题型范围已核定；sources=https://hazyresearch.stanford.edu/legalbench/tasks/proa.html

**BR03_何时**：mode=EVENT_AND_EFFECT；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=隐含诉权与法条解释不由字符串解决

**BR05_效果**：mode=LEGAL_STATE_OR_REMEDY；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=任务特定的解释、匹配和抽取；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；法律关系、权能与事件：对已编译规则与事件解释器建立逐步模拟；列明作用域、例外、负事件信息与冲突策略；请求与救济空间：由规范需求独立定义集合，再验证有限枚举或符号关系；联合责任及诉请范围用单一见证；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=存在禁止性条文不自动推出任何私人可起诉

来源（原表范围）：
https://hazyresearch.stanford.edu/legalbench/tasks/proa.html

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D132｜最高法院审理问题应对应哪一个核心裁判要旨，而非相近措辞？

分组：15 美国法特定问题与法律语言任务。原评测：US03。

输入：美国法条、最高法院问题、证券起诉状或判决节选

输出：任务特定的解释、匹配和抽取

形式目标：holding匹配在给定候选与问题语义下检查；类案迁移另证相关特征

前提：问题、核心要旨和候选含义明确

外部验证：法律语言理解与先例控制力

证明路线：来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：法源query与原文回读已有工程；固定语料与适用法域完整性另证；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；ULM08-11、JC论证语义已有；生成映射/截断/合理性依具体profile关闭

反例：关键词相似的旁论不能替代核心裁判要旨

任务：EXT03, EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T05, T06, T20, T22, T24；证明族：M02, M04, M06, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=holding匹配在给定候选与问题语义下检查；类案迁移另证相关特征

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=问题、核心要旨和候选含义明确；sources=https://hazyresearch.stanford.edu/legalbench/tasks/scalr.html

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=法律语言理解与先例控制力

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=任务特定的解释、匹配和抽取；proof_route=来源、版本与查询：对选择/投影/连接/去重结构归纳；证明每个结果的来源路径；负查询另要独立域完整性；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；结构化论证与扩展：生成树高度/出现图归纳；对具体profile证明反射/覆盖；严格闭包与一致性不能靠过滤后改题；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=关键词相似的旁论不能替代核心裁判要旨

来源（原表范围）：
https://hazyresearch.stanford.edu/legalbench/tasks/scalr.html

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D133｜证券集体诉讼片段是否载明原告；有多人时是否全部抽取？

分组：15 美国法特定问题与法律语言任务。原评测：US03。

输入：美国法条、最高法院问题、证券起诉状或判决节选

输出：任务特定的解释、匹配和抽取

形式目标：片段原告提及集合完整抽取需独立跨度标注；多主体键不合并

前提：给定文段范围和mention/person映射准入

外部验证：新文本召回和指代消解

证明路线：主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：结构身份和按案绑定已有代码/合同；全业务角色映射尚未据此验收；Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明

反例：首个名字抽对不等于全体原告齐全

任务：EXT09, REV02, ROOT02, ROOT03, ROOT06, ROOT08, T01, T02, T03, T22, T24；证明族：M01, M04, M16。

**BR01_谁对谁**：mode=DIRECT_RELATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=片段原告提及集合完整抽取需独立跨度标注；多主体键不合并

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=给定文段范围和mention/person映射准入；sources=https://hazyresearch.stanford.edu/legalbench/tasks/ssla_plaintiff.html

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=新文本召回和指代消解

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=任务特定的解释、匹配和抽取；proof_route=主体与作用域：编码结构归纳；对规范化前等价关系先定商空间；证明键转换保持而非哈希无碰撞；文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=首个名字抽对不等于全体原告齐全

来源（原表范围）：
https://hazyresearch.stanford.edu/legalbench/tasks/ssla_plaintiff.html

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。

## D134｜劳动歧视案因果论证使用统计还是直接证据？这不是估计干预效果。

分组：15 美国法特定问题与法律语言任务。原评测：US03。

输入：美国法条、最高法院问题、证券起诉状或判决节选

输出：任务特定的解释、匹配和抽取

形式目标：输出“统计/直接证据使用”是文本分类；不得自动生成do效果结论

前提：该任务标签与法律论证语义明确

外部验证：分类器真实表现

证明路线：文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

原能力重新评估：Harness真实解析与事实候选已具备工程基础；抽取语义和范围覆盖未全证明；V2.1概率/胜率参考与保留时间切分；真实经验效果、因果识别及EXT保证未整体验收

反例：统计证据类别命中不意味着识别了个案因果效应

任务：EXT06, EXT07, EXT09, ROOT03, ROOT06, ROOT08, T01, T03, T12, T13, T14, T15, T22, T24；证明族：M04, M12, M16。

**BR01_谁对谁**：mode=CONTEXT_PRESERVATION；obligation=主体、角色、对象、案件/争点作用域分别绑定；关联不作身份等号。；specific_target=输出“统计/直接证据使用”是文本分类；不得自动生成do效果结论

**BR02_依据**：obligation=原始来源定位、版本、可使用地位与规则编译语义分别检查；不以哈希或文字出处推出真实性。；specific_preconditions=该任务标签与法律论证语义明确；sources=https://hazyresearch.stanford.edu/legalbench/tasks/legal_reasoning_causality.html

**BR03_何时**：mode=ASOF_AND_VERSION；obligation=使用本项适用的事件/效力/获知/记录/预测时间，其他时间角色只作绑定；不为静态查询强加法律期限。

**BR04_条件**：obligation=把本项前提编成可解释条件或显式待判断对象；未决不作为否定；空补全域不得制造无条件真。；external_obligation=分类器真实表现

**BR05_效果**：mode=TYPED_INFORMATION_OR_CALCULATION；obligation=法律权利/义务/权能/程序后果与信息抽取/预测/建议分开；以实际生成规则证明输出性质，不把信息输出当机构决定。

**BR06_允许结果**：obligation=由独立任务语义定义答案空间；按本项原目标选择一个解、全部解、外界或统计事件。总根不反向从模型输出定义全集。；answer_shape=任务特定的解释、匹配和抽取；proof_route=文本理解与语义接地：先证明解析/跨度/身份；受限语言可结构归纳；自由文本语义由独立标注、审核或校准提供证据；概率、预测及因果：有限概率代数/算法反射；校准和覆盖另给抽样定理；识别模型族与现实适用另审核；业务需求满足与总根：需求分解蕴涵＋联合非空/合法控制策略；连接规范、实现、交付和风险事件；不从注册数反推需求穷尽

**BR07_文件忠实**：obligation=回读实际交付的关键主体、依据、时点、条件、效果和范围；受保护内容不漏不增、不降限定、不升级完成状态。；acceptance_focus=许可转非排他、提前到期、终止、同意权不得归成同一效果；counterexample=统计证据类别命中不意味着识别了个案因果效应

来源（原表范围）：
https://hazyresearch.stanford.edu/legalbench/tasks/legal_reasoning_causality.html

状态：OBLIGATIONS_INSTANTIATION_PENDING_NOT_PROVED。
