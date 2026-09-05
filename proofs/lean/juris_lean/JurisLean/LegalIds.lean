import Mathlib.Data.Int.Order.Basic
import JurisLean.FailureStatus

/-!
中文说明：M1 身份层。typed ID、内容摘要、版本、scope、时点与精确数值
句柄。ID 的 kind 是类型级 phantom 参数，kind 不同的 ID 在类型层面不可
交叉替换。digest 建模为可信函数参数：证明只覆盖绑定关系，不假装证明
SHA-256 的密码学安全。
-/

namespace JurisLean

/-- 中文说明：typed ID 的类别；kind 只存在于类型层。 -/
inductive IdKind where
  | fact | rule | norm | claim | argument | attack
  | obligation | snapshot | receipt | certificate | scope
deriving DecidableEq, Repr

/-- 中文说明：typed ID。不同 kind 的 ID 是不同的类型，不可互相替换。 -/
structure LegalId (kind : IdKind) where
  payload : String
deriving DecidableEq, Repr

/-- 中文说明：内容摘要句柄；它是受信任的函数参数，不是密码学断言。 -/
structure ContentDigest where
  hex : String
deriving DecidableEq, Repr

/-- 中文说明：digest 对主体的绑定关系（内容绑定，不是权威证明）。 -/
def DigestBinding (d : ContentDigest) (subject : String) : Prop :=
  d.hex = subject

/-- 中文说明：schema 与 semantics 版本。未知版本必须 fail-closed。 -/
structure SchemaVersion where
  tag : String
deriving DecidableEq, Repr

structure SemanticsVersion where
  tag : String
deriving DecidableEq, Repr

/-- 中文说明：提交、树与构建标识，进入发布证书的身份绑定。 -/
structure CommitId where
  hex : String
deriving DecidableEq, Repr

structure TreeId where
  hex : String
deriving DecidableEq, Repr

structure BuildId where
  name : String
deriving DecidableEq, Repr

/-- 中文说明：案件与运行 scope；跨 scope 重放不得保留准入。 -/
structure CaseScope where
  scopeId : String
deriving DecidableEq, Repr

structure RunScope where
  caseScope : CaseScope
  runId : String
deriving DecidableEq, Repr

/-- 中文说明：来源定位器，保留层级结构而不是平面文本。 -/
structure SourceLocator where
  path : String
  anchor : String
deriving DecidableEq, Repr

/-- 中文说明：显式时点与区间句柄；端点与粒度必须显式。 -/
structure TimePoint where
  epochDay : Int
deriving DecidableEq, Repr

structure TimeInterval where
  fromDay : Int
  toDay : Int
deriving DecidableEq, Repr

/-- 中文说明：精确数值句柄；正式路径禁止 binary float。 -/
structure ExactAmount where
  minorUnits : Int
  currency : String
deriving DecidableEq, Repr

structure ExactRate where
  numerator : Int
  denominator : Int
deriving DecidableEq, Repr

inductive RoundingPolicy where
  | halfUp | halfDown | down | up
deriving DecidableEq, Repr

/-- 中文说明：每个 kind 的稳定序列化前缀；前缀不同则标识域不同。 -/
def idKindPrefix : IdKind -> String
  | .fact => "fact"
  | .rule => "rule"
  | .norm => "norm"
  | .claim => "claim"
  | .argument => "argument"
  | .attack => "attack"
  | .obligation => "obligation"
  | .snapshot => "snapshot"
  | .receipt => "receipt"
  | .certificate => "certificate"
  | .scope => "scope"

/-- 中文说明：typed ID 的规范序列化：前缀与载荷分离承载，域不混淆。 -/
def LegalId.serialized {kind : IdKind} (id : LegalId kind) : String × String :=
  (idKindPrefix kind, id.payload)

/-- 中文证明：同 kind 的 ID 序列化相等蕴含载荷相等（序列化忠实）。 -/
theorem legalId_serialization_faithful {kind : IdKind}
    (a b : LegalId kind) :
    a.serialized = b.serialized → a.payload = b.payload := by
  intro h
  cases a; cases b
  simp [LegalId.serialized] at h
  exact h

/-- 中文证明：不同 kind 的前缀不同，因此不同 kind 的序列化标签永不重合。 -/
theorem id_prefix_separated (k1 k2 : IdKind)
    (hdiff : k1 ≠ k2) : idKindPrefix k1 ≠ idKindPrefix k2 := by
  cases k1 <;> cases k2 <;> first | contradiction | decide

/-- 中文证明：digest 绑定同一摘要的两个主体必须一致（绑定关系对称闭合）。 -/
theorem digest_binding_consistent {d : ContentDigest} {s1 s2 : String}
    (h1 : DigestBinding d s1) (h2 : DigestBinding d s2) : s1 = s2 := by
  dsimp [DigestBinding] at h1 h2
  rw [← h1, h2]

/-- 中文证明：digest 绑定是内容绑定，绑定自身不产生新的内容差异。 -/
theorem digest_binding_reflexive (subject : String) :
    DigestBinding { hex := subject } subject := rfl

/-- 中文证明：跨 case scope 的重放不保留同一 scope 身份。 -/
theorem cross_case_replay_changes_scope (c1 c2 : CaseScope)
    (hdiff : c1 ≠ c2) :
    (RunScope.mk c1 "run").caseScope ≠ (RunScope.mk c2 "run").caseScope := by
  intro h
  apply hdiff
  exact h

/-- 中文证明：区间合法要求端点顺序显式成立。 -/
def TimeInterval.valid (i : TimeInterval) : Prop := i.fromDay ≤ i.toDay

theorem interval_valid_antisym_boundary {i : TimeInterval}
    (h : i.valid) (hrev : TimeInterval.valid { fromDay := i.toDay, toDay := i.fromDay }) :
    i.fromDay = i.toDay := by
  dsimp [TimeInterval.valid] at h hrev
  exact Int.le_antisymm h hrev

end JurisLean
