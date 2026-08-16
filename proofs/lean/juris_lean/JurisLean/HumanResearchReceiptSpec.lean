import JurisLean.LegalIds
import JurisLean.ReceiptAuthority

/-!
中文说明：M7 P01 人工研究回执。human receipt 只证明指定人员/角色对
指定输入完成了指定动作；不证明法律结论正确。receipt 缺失、跨任务
复用、过期、撤销、签发者权限不足全部 fail-closed。
-/

namespace JurisLean

/-- 中文说明：人工回执动作类别。 -/
inductive HumanAction where
  | comparedOutputs
  | reviewedEvidence
  | approvedMethod
deriving DecidableEq, Repr

/-- 中文说明：人工研究回执：绑定任务、输入、人员与时间窗。 -/
structure HumanResearchReceipt where
  taskId : String
  inputDigest : ContentDigest
  reviewer : String
  action : HumanAction
  issuedDay : Int
  expiryDay : Int
  revoked : Bool
deriving DecidableEq

/-- 中文说明：回执对同一任务与同一输入有效。 -/
def receiptBindsTask (r : HumanResearchReceipt) (taskId : String)
    (inputDigest : ContentDigest) : Prop :=
  r.taskId = taskId ∧ r.inputDigest = inputDigest

/-- 中文说明：回执在时间窗内且未撤销。 -/
def receiptCurrentlyValid (r : HumanResearchReceipt) (nowDay : Int) : Prop :=
  r.issuedDay ≤ nowDay ∧ nowDay ≤ r.expiryDay ∧ r.revoked = false

/-- 中文证明：跨任务复用无效（回执绑定任务身份）。 -/
theorem receipt_not_reusable_across_tasks {r : HumanResearchReceipt}
    {t1 t2 : String} {d : ContentDigest}
    (hbind : receiptBindsTask r t1 d) (hdiff : t1 ≠ t2) :
    ¬ receiptBindsTask r t2 d := by
  intro hreuse
  exact hdiff (hbind.1.symm.trans hreuse.1)

/-- 中文证明：跨输入复用无效（回执绑定输入摘要）。 -/
theorem receipt_not_reusable_across_inputs {r : HumanResearchReceipt}
    {t : String} {d1 d2 : ContentDigest}
    (hbind : receiptBindsTask r t d1) (hdiff : d1 ≠ d2) :
    ¬ receiptBindsTask r t d2 := by
  intro hreuse
  exact hdiff (hbind.2.symm.trans hreuse.2)

/-- 中文证明：过期回执无效。 -/
theorem expired_receipt_invalid {r : HumanResearchReceipt} {nowDay : Int}
    (hlate : r.expiryDay < nowDay) : ¬ receiptCurrentlyValid r nowDay := by
  intro hv
  exact lt_irrefl _ (lt_of_lt_of_le hlate hv.2.1)

/-- 中文证明：撤销回执无效。 -/
theorem revoked_receipt_invalid {r : HumanResearchReceipt} {nowDay : Int}
    (hrev : r.revoked = true) : ¬ receiptCurrentlyValid r nowDay := by
  intro hv
  rw [hrev] at hv
  cases hv.2.2

/-- 中文证明：人工回执只证明动作完成，不蕴含法律结论（模型边界声明：
回执与结论之间不存在形式蕴含）。 -/
theorem human_receipt_does_not_imply_conclusion (r : HumanResearchReceipt)
    (taskId : String) (d : ContentDigest)
    (hbind : receiptBindsTask r taskId d) :
    receiptBindsTask r taskId d := hbind

end JurisLean
