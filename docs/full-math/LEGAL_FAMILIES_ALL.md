# 14个已登记法律族：形式政策编译全表

每族都要有具名且有内容的规范条件AST、独立requiredSlots与反例。来源现行性/解释采用是独立证据，不可只凭目录做法律审核通过。

## CIV_CONTRACT｜合同债权、担保与金融
研究及模型对象：产生/履行/变更/消灭、独立抗辩、代理、损失范围、时效行使
已有来源登记（需按使用版本核验）：L-CIVIL-CODE, L-CIVPROC-2022
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。

## PROPERTY｜物权与占有
研究及模型对象：物权基础、登记/交付、占有、返还及抗辩
已有来源登记（需按使用版本核验）：L-CIVIL-CODE, L-CIVPROC-2022
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。

## TORT｜一般侵权与产品/消费
研究及模型对象：过错、损害、因果关系、无过错及法定倒置的适用条件
已有来源登记（需按使用版本核验）：L-CIVIL-CODE
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。

## MEDICAL｜医疗损害
研究及模型对象：诊疗过错、因果、病历控制及特定过错推定，不能把参与度当事实概率
已有来源登记（需按使用版本核验）：L-CIVIL-CODE
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。

## ENVIRONMENT｜环境与生态
研究及模型对象：污染生态行为、因果责任、法典时间效力、持续行为与公益程序
已有来源登记（需按使用版本核验）：L-ENV-TIME-2026, L-CIVIL-CODE
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。

## FAMILY_SUCCESSION｜婚姻家事与继承
研究及模型对象：身份事项、自认限制、夫妻债务、遗嘱/赠与特殊证明与有效性
已有来源登记（需按使用版本核验）：L-CIVIL-CODE, L-CIV-EVIDENCE-2019
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。

## LABOR｜劳动与人事
研究及模型对象：关系成立、加班、用工决定、证据控制、解释（二）新规
已有来源登记（需按使用版本核验）：L-LABOR-2007, L-LABOR-II-2025
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。

## CORPORATE_INSOLVENCY｜公司、股权与破产
研究及模型对象：独立财产、出资、责任类型、破产专门程序、公司法时间效力
已有来源登记（需按使用版本核验）：L-COMPANY-2023
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。

## IP｜知识产权
研究及模型对象：权利/侵权/损失及证据控制、专利特殊责任、惩罚性赔偿新解释
已有来源登记（需按使用版本核验）：L-UPDATE-INDEX
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。

## CRIMINAL｜刑事公诉、自诉与量刑
研究及模型对象：要件、违法/责任评价配置、排除非法证据、免证限制、证明不足后果
已有来源登记（需按使用版本核验）：L-CRIMPROC-2018, L-CRIM-INTERP-2021, L-PLEA-2026, L-SENTENCING-2021
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。

## ADMIN｜行政诉讼
研究及模型对象：行政行为合法性与原告履职申请/损害例外、第三人证据、时限
已有来源登记（需按使用版本核验）：L-ADMIN-2017, L-ADMIN-TIME-2026
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。

## RECONSIDER_COMPENSATION｜行政复议与国家赔偿
研究及模型对象：复议对象/程序、被申请人证明、损害及国家赔偿特别规则
已有来源登记（需按使用版本核验）：L-RECONSIDER-2026
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。

## PROCEDURE_EXECUTION｜执行、保全、回避、上诉与再审
研究及模型对象：实体/程序状态分开；不同阶段的证明事项、负担和标准
已有来源登记（需按使用版本核验）：L-CIVPROC-2022, L-CIV-EVIDENCE-2019
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。

## ARBITRATION_MARITIME_PUBLIC｜仲裁、海事与公益
研究及模型对象：新版仲裁法、仲裁庭权限、海商时间效力、公益原告/救济
已有来源登记（需按使用版本核验）：L-ARB-2025, L-UPDATE-INDEX
必须具体实现的槽：适用范围；权利/程序对象；证据提供责任；最终说服责任；本证反证/推定；证明标准；例外；阶段就绪；法律后果；版本及过渡；金额/非金钱结果；回归反例
产物：`law_models/<family>/policy.json`、`source_manifest.json`、`required_slots.json`、`tests/`及对应Lean政策编译定理。
不得用空AST、同一主张更换family名称、任意布尔court授权或模板字符串替换通过。槽完备性只相对于独立冻结清单，不宣传穷尽所有中国法。
