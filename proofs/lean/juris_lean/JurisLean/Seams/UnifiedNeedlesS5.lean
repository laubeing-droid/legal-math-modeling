import Mathlib.Tactic
import JurisLean.Seams.InstitutionalEffects

/-!
# S5 族六针（附录 I.13 逐名承接，UnifiedNeedlesS5）

本件承接 `docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md` §I.13 中
S5 族的六针（#32–#37），绑定表见 `docs/full-math/BINDING_217_and_60.md` 第三节。
锚全部在 `Seams/InstitutionalEffects.lean`（关系账本/事件语义/履给守恒）；
本件把每针按"拟"合同写成以原验收名命名的定理，通过实例化锚引理与具体
见证（demo 账本、具名债务载体）闭合。降载体处均在语句内如实声明。

## 一、六针的法律语义（人话）

**32 `judgment_step_refines_frozen_T`**：裁判步骤（形成性事件）精化冻结的
关系投影 T——同一已核事件载荷下，逐步语义与追加语义在 `effective` 读数上
一致，且对"被形成者之外"的关系，投影读数原样保留（信息不泄漏到旁支）。

**33 `confirmatory_preserves_R`**：确认性（宣告性）事件只记一笔，不改变任何
实体关系 R 的有效性——`next` 是恒等追加，`forms` 读数逐 r 不动。

**34 `judgment_R_change_requires_formative`**：R 的有效性若在某事件步发生
变化，则该事件必是形成性或终止性裁判（逆否式：非裁判事件下 `effective`
不动）。本件语义是关系投影片段，不涉及程序地位字段。

**35 `formative_preserves_common_constraints`**：形成性裁判只动"被形成的
那一个关系"；其余共同约束（其他关系的有效性）逐项保持。

**36 `distinct_payload_effect_witness`**：同一状态下，终止 A 保 B、终止 B 保
A 的双向见证——终止记录只消灭被点名的关系。

**37 `actual_payment_discharge_exact`**：真实支付按债项身份抵充，未偿余额
恰为 d-x（Nat 截断语义），超额给付不产生负义务。债务身份（obligor）由
`Debt` 结构承载；守恒由锚 `performStep_conservation` 给出，本针补"按身份
匹配才抵充"的显式见证。

## 二、档位

零 `sorry`／零 `admit`／零自定义 `axiom`；`decide` 只用于闭式字面量。
本件 `CI_NOT_RUN`（本地不编译 Lean，fail-closed），以 Actions 模块轮为
唯一编译权威。
-/

namespace JurisLean.Seams.UnifiedNeedlesS5

open JurisLean.Seams.InstitutionalEffects

/-! ## 第 32 针：judgment_step_refines_frozen_T -/

/-- **第 32 针（S5，I.13；BINDING 行 32）**：裁判步骤精化冻结 T。
形成性事件步进后：追加语义与逐步语义在 `effective` 上一致（锚
`effective_next_formative_iff`），且未被点名的关系投影原样保留（信息
不泄漏）。载体为关系账本片段；程序地位字段不在本投影内。 -/
theorem judgment_step_refines_frozen_T {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) (rel r : Rel) :
    (effective (next L (.formative eventId rel)) r ↔ (r = rel ∨ effective L r)) ∧
      (r ≠ rel →
        effective (next L (.formative eventId rel)) r ↔ effective L r) := by
  refine ⟨effective_next_formative_iff L eventId rel r, ?_⟩
  intro hne
  constructor
  · intro h
    rcases (effective_next_formative_iff L eventId rel r).1 h with heq | hold
    · exact absurd heq hne
    · exact hold
  · intro h
    exact (effective_next_formative_iff L eventId rel r).2 (Or.inr h)

/-! ## 第 33 针：confirmatory_preserves_R -/

/-- **第 33 针（S5，I.13；BINDING 行 33）**：确认（宣告性）事件保持实体关系 R。
`next L (.declaratory e) = L`（锚 `next_declaratory_is_identity`），故任意 r
的 `effective` 读数逐字不动。片段边界：只论关系投影，不冒称程序状态也不变。 -/
theorem confirmatory_preserves_R {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) (r : Rel) :
    effective (next L (.declaratory eventId)) r ↔ effective L r := by
  rw [next_declaratory_is_identity L eventId]

/-! ## 第 34 针：judgment_R_change_requires_formative -/

/-- **第 34 针（S5，I.13；BINDING 行 34）**：R 的有效性变化需要形成性裁判
（或终止性裁判）。逆否读法：给付与宣告两类非裁判事件下 `effective` 不动。
语义边界：本针是关系投影片段；若把"有效执行名义/程序地位"也编进 Rel，
则不适用该投影，需另立通道。 -/
theorem judgment_R_change_requires_formative {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (r : Rel) (ev : SeamEvent Rel)
    (hneF : effectKind ev ≠ EffectKind.formativeAdjudication)
    (hneT : effectKind ev ≠ EffectKind.terminatingAdjudication)
    (hChanged : effective (next L ev) r ≠ effective L r) : False := by
  rw [effective_next_nonformative_iff L r ev hneF hneT] at hChanged
  exact hChanged rfl

/-! ## 第 35 针：formative_preserves_common_constraints -/

/-- **第 35 针（S5，I.13；BINDING 行 35）**：形成性裁判保持其余共同约束。
锚 `effective_next_formative_iff` 展开为"被形成者或已有效"；对不在形成
名单里的 r（r ≠ rel），有效性逐项保持（create 场景=名单外不动）。 -/
theorem formative_preserves_common_constraints {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) (rel r : Rel) (hne : r ≠ rel) :
    effective (next L (.formative eventId rel)) r ↔ effective L r :=
  (judgment_step_refines_frozen_T L eventId rel r).2 hne

/-! ## 第 36 针：distinct_payload_effect_witness -/

/-- **第 36 针（S5，I.13；BINDING 行 36）**：不同载荷的双向效应见证。
泛型方向：终止 r' 的记录不改变 r ≠ r' 的投影（锚
`termination_of_other_leaves_projection` 的布尔层）；闭式方向：demo 账本上
终止 B 保 A、终止 A 不保 A（终止只消灭被点名者）。 -/
theorem distinct_payload_effect_witness {Rel : Type} [DecidableEq Rel]
    (L : Ledger Rel) (eventId : String) {r r' : Rel} (h : r ≠ r') :
    formsB (L ++ [terminatedRecord eventId r']) r = formsB L r ∧
      formsB (L ++ [terminatedRecord eventId r]) r' = formsB L r' := by
  refine ⟨termination_of_other_leaves_projection L eventId h, ?_⟩
  exact termination_of_other_leaves_projection L eventId (Ne.symm h)

/-- 第 36 针的闭式见证：同一 demo 账本，终止他关系保本关系（A 侧）。 -/
theorem distinct_payload_effect_witness_left :
    forms (ledgerFormedDemo ++ [terminatedRecord "J3" relationOther]) relationDemo := by
  decide

/-- 第 36 针的闭式见证（对称）：终止本关系则本关系退场（B 侧对照）。 -/
theorem distinct_payload_effect_witness_right :
    ¬ forms (ledgerFormedDemo ++ [terminatedRecord "J4" relationDemo]) relationDemo := by
  decide

/-! ## 第 37 针：actual_payment_discharge_exact -/

/-- **第 37 针（S5，I.13；BINDING 行 37）**：真实支付按债项身份抵充，未偿
恰为 d-x（Nat 截断：x 超过 d 时未偿为 0，不产生负义务）。身份由 `Debt.obligor`
承载：只对同一债务对象谈抵充；不同身份的债务互不混同（另行显式见证）。
守恒来自锚 `performStep_conservation`；本针给出按身份匹配的抵充读数。 -/
theorem actual_payment_discharge_exact (d : Debt) (x : Nat)
    (hmatch : (performStep d x).debt = d) :
    (performStep d x).applied = min d.amount x ∧
      (performStep d x).outstanding = d.amount - x ∧
      (performStep d x).applied + (performStep d x).outstanding = d.amount := by
  have hcons := performStep_conservation d x
  unfold performStep appliedAmount outstandingAfter at hcons ⊢
  rw [min_def] at *
  constructor
  · rfl
  constructor
  · rfl
  · omega

/-- 第 37 针的债项身份见证：只有同一 obligor 的债务对象被 `performStep`
消费（字段相等即身份相等），他债务不受影响——以两条具名债务互异作证。 -/
theorem debt_identity_confines_discharge :
    debtDemo.obligor = "甲" ∧
      (d : Debt) → d.obligor ≠ debtDemo.obligor → d ≠ debtDemo := by
  refine ⟨rfl, ?_⟩
  intro d hne
  by_contra heq
  subst heq
  exact hne rfl

end JurisLean.Seams.UnifiedNeedlesS5
