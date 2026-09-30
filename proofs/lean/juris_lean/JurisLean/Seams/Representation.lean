import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
S0 —— 表示层缝合（L0 法律对象 → L1 模型载体）的法律语义、数学对象与边界。

## 一、法律语义（人话）
建模时先把法律对象（当事人、意思表示、合同、请求权、登记簿条目……）送进某个数学载体
（图、Horn 基、超距空间、状态机），这一步就是一次**表示**。本件只管一件事实：

**一次表示什么时候有资格被说成"与原对象层同构"？**

答案是两件事必须同时成立，缺一不可：

1. **往返性（忠实）**：每个法律对象从模型侧读回来仍是它自己。法律上的反面例子是把
   "意思表示已撤回"与"意思表示自始未生效"压成同一个状态位——读回来时二者不可分辨，
   往返性当场失效，此后模型里的任何结论都不能再声称是关于原法律对象的结论。
2. **覆盖性（不遗漏）**：模型载体里的每个状态都真的对应某个法律对象。反面例子是模型里
   留了一个"已登记"状态而法律对象层根本没有对应对象，于是可以把模型内的可达性误当成
   法律上的既存事实。

本件把这两件事做成可命名的假设（`RoundTrip`、`Coverage`），并证明同构结论确实由它们
**合成**（`iso_of_roundtrip_and_cover`、`representation_scope`，登记表条目 P-002），
同时给出两个具体有限见证，说明两个假设互不蕴含、也不能彼此顶替：
`coverage_is_genuinely_extra`（往返成立而覆盖失败）与
`coverage_alone_has_no_inverse_roundtrip`（覆盖成立而反向往返必不成立）。

联合法律模型（"统一"的含义）：同一个法律对象层 α 上并置多个观察层——合同相对性层、
登记层、时效层——联合载体取两枚像的纤维积（对角嵌入的像）。本件给出联合载体上的观测
按投影计算的定理（`joint_projections_agree_on_declared`）、联合载体不退化的判据
（`joint_model_is_not_collapsed`）与一个具体的非退化联合模型见证
（`joint_legal_model_exists`）。联合模型的成立不是引用某份既有定义就说"存在"，
而是交出两个可分辨的联合元素与一个把它们分开的声明观测。

## 二、数学对象
- `Fragment α`：声明片段 = 载体类型 `β`、观测指标类型 `ι`、声明值类型 `γ`、观测族
  `obs : ι → (α → γ)`、表示 `enc : α → β` 与回读 `dec : β → α`。范围（scope）是被命名
  的假设，不是隐含的全称信念。
- `RoundTrip f` / `Coverage f` / `FaithfulRep f`：往返性、覆盖性、两者之和。
- `Equiv α β`：同构；本件要求它的 `toFun`、`invFun` 字面就是 `enc`、`dec`。
- `Joint f₁ f₂`：`{ ⟨b₁, b₂⟩ | ∃ a, enc₁ a = b₁ ∧ enc₂ a = b₂ }`，即对角嵌入的像。
- `castUp : Fin 2 → Fin 3`（即 `Fin.castSucc`）与 `dropDown : Fin 3 → Fin 2`
  （`fun b => Nat.min b.val 1`）：具体有限见证对。

## 三、本件证什么、不证什么
**证**：往返 ⇒ 单射；往返 ∧ 覆盖 ⇒ 以给定 `enc`/`dec` 为两侧的同构，且反向也成立
（故 `representation_scope` 是双向刻画）；忠实表示下声明观测沿 `dec` 搬到模型侧后在原像
处不变，且在覆盖性下这一搬运是唯一确定的延长；两个假设互不蕴含由具体见证给出；
联合载体的投影计算与不退化判据；声明不足的片段无法分辨两个不同法律对象。

**不证**：
- 不证任何具体法律领域的表示是忠实的：往返性与覆盖性在本件里始终是**假设**或**具体
  有限见证**，没有为任何真实法律对象层声明过它们。
- 不证 L0→L1 的运行时实现（Python、Horn、图算法）与本件的形式语义相 refinement。
- 不证观测族能把任意两个法律对象分开：`observations_do_not_separate_until_declared`
  恰好是这一点的反面见证；要拿到该结论必须额外声明分离性
  （`separating_fragment_agreement_implies_equality` 把这一额外假设写进签名）。
- 不证联合模型在超过两层时的情形，也不证联合载体的有限性、可计算性或构造复杂度。
- 不认定任何真实案件事实，不引入任何规范内容。

## 四、声明片段与未覆盖片段（本件的自我设限）
- [已证] `injective_of_roundtrip`、`iso_of_roundtrip_and_cover`、`representation_scope`
  （P-002，双向）、`representation_observations_preserved`、`obsModel_unique`。
- [已证] `coverage_is_genuinely_extra`、`no_equiv_for_castUp`、
  `coverage_alone_has_no_inverse_roundtrip`、`dropDown_has_section`。
- [已证，条件] `joint_model_is_not_collapsed` 必须把"层一存在可分辨观测"写成假设 `hsep`。
- [已证，具体] `joint_legal_model_exists` 只在 `Fin 2` 上两枚具体片段处成立。
- [未覆盖] 一般 α 上联合模型的非退化性（需分离性公设）；多于两层的联合；
  任何真实法律领域（合同、登记、时效）的 `RoundTrip`、`Coverage` 验证；
  与既有 S1–S5 各层片段的接口对接（本件只给抽象范围机制，不代其他层声明其片段）。

## 五、档位
定义为 [构造性定义]；定理在本件内给出完整证明，未使用占位证明，也未新增未证公理。
按仓库边界约定，Lean 权威认定在 CI；本地编译仅为自检，称 provisional。
-/

namespace JurisLean.Seams.Representation

/-- 声明片段（Fragment）：一次 L0→L1 表示的全部可命名范围。
    `β` 是模型侧载体类型，`ι` 是已声明的观测指标类型，`γ` 是已声明的取值类型，
    `obs` 是已声明的法律观测族（例如"该意思表示是否已到达""登记状态为何"），
    `enc` 是把法律对象送进模型的表示，`dec` 是从模型载体回读法律对象。
    本类型不含"所有观测都已被声明"的意思：范围只到 `ι`、`γ` 声明到哪里为止。 -/
structure Fragment (α : Type) where
  β : Type
  ι : Type
  γ : Type
  obs : ι → (α → γ)
  enc : α → β
  dec : β → α

/-- 往返性（不失真）：每个法律对象被表示出去再读回来仍是它自己。
    法律读法：模型不得改变法律对象的同一性——不得把"已撤回"与"自始未生效"压成一位。 -/
def RoundTrip (f : Fragment α) : Prop := ∀ a, f.dec (f.enc a) = a

/-- 覆盖性（不遗漏）：模型载体里的每个状态都是某个法律对象的像。
    法律读法：模型内存在的状态必须有法律依据，否则模型内的"可达"会被误当成法律上的"既存"。 -/
def Coverage (f : Fragment α) : Prop := ∀ b, ∃ a, f.enc a = b

/-- 双向忠实：既不失真（往返）也不遗漏（覆盖）。本件中"有资格的表示"只有这一种说法。 -/
def FaithfulRep (f : Fragment α) : Prop := RoundTrip f ∧ Coverage f

/-- 往返性给出单射：两个法律对象若在模型里长成同一个像，它们本来就相同。
    法律读法：表示不会把两个不同对象合并，前提是回读真能把它们分回原样。 -/
theorem injective_of_roundtrip {α β : Type} (enc : α → β) (dec : β → α)
    (h : ∀ a, dec (enc a) = a) : Function.Injective enc := by
  intro a₁ a₂ heq
  have key : dec (enc a₁) = dec (enc a₂) := congrArg dec heq
  rw [h a₁, h a₂] at key
  exact key

/-- 往返 + 覆盖 ⇒ 同构：可以造出以 `enc` 为正向、`dec` 为反向的等价。
    结论写成"存在一个两侧字面等于 enc/dec 的等价"，而不是预先索要 `Function.Bijective`
    再假装覆盖性没被用过：覆盖性在此被真实消费，它正是提供 `enc (dec b) = b` 的那一步。
    法律读法：只有不失真且不遗漏的表示，才允许说"模型层与法律对象层是同一结构的两种写法"。 -/
theorem iso_of_roundtrip_and_cover {α β : Type} (enc : α → β) (dec : β → α)
    (hrt : ∀ a, dec (enc a) = a) (hcv : ∀ b, ∃ a, enc a = b) :
    ∃ e : Equiv α β, e.toFun = enc ∧ e.invFun = dec := by
  have hright : ∀ b, enc (dec b) = b := by
    intro b
    obtain ⟨a, ha⟩ := hcv b
    have hdb : dec b = a := by rw [← ha, hrt a]
    rw [hdb]
    exact ha
  exact ⟨{ toFun := enc, invFun := dec, left_inv := hrt, right_inv := hright }, rfl, rfl⟩

/-- P-002（表示层范围定理）：把"某表示是同构"这句话精确化，两个方向都证。
    左侧（存在两侧恰为 `enc`/`dec` 的等价）与右侧（往返性 ∧ 覆盖性）等价。
    法律读法：宣称模型与法律对象层同构，既不只需往返、也不只需覆盖，而是两者同时成立；
    右端也不是定义耍赖——由它可在本件内构造出同构本身。 -/
theorem representation_scope {α β : Type} (enc : α → β) (dec : β → α) :
    (∃ e : Equiv α β, e.toFun = enc ∧ e.invFun = dec) ↔
      ((∀ a, dec (enc a) = a) ∧ (∀ b, ∃ a, enc a = b)) := by
  constructor
  · rintro ⟨e, hto, hinv⟩
    constructor
    · intro a
      rw [← hto, ← hinv]
      exact e.left_inv a
    · intro b
      refine ⟨e.invFun b, ?_⟩
      rw [← hto]
      exact e.right_inv b
  · rintro ⟨hrt, hcv⟩
    exact iso_of_roundtrip_and_cover enc dec hrt hcv

/-- 模型侧观测：把声明观测沿回读 `dec` 搬到模型载体上，即"先读回法律对象，再按声明观测取值"。 -/
def obsModel {α : Type} (f : Fragment α) (i : f.ι) (b : f.β) : f.γ := f.obs i (f.dec b)

/-- 往返性已足以把声明观测搬回原像处：在原对象的像上，模型侧观测等于声明观测。
    这一条单独列出，是为了让"哪一步用到哪个假设"在证明项里可见。 -/
theorem obsModel_roundTrip {α : Type} (f : Fragment α) (hrt : RoundTrip f)
    (a : α) (i : f.ι) : obsModel f i (f.enc a) = f.obs i a :=
  congrArg (f.obs i) (hrt a)

/-- 表示保持声明观测：在双向忠实的表示下，模型侧搬运后的观测在原对象像处与声明观测相等。
    法律读法：一个在此精确双向意义下忠实的表示，不可能改变任何已被声明的法律观测的取值；
    因此"模型里算出来的该观测变了"只能意味着表示不忠实，或该观测本不在声明范围内。
    说明：这条等式只用到往返性分量；覆盖性分量是同构刻画（`representation_scope`）
    与观测搬运唯一性（`obsModel_unique`）的必要条件。 -/
theorem representation_observations_preserved {α : Type} (f : Fragment α)
    (hf : FaithfulRep f) : ∀ (a : α) (i : f.ι), obsModel f i (f.enc a) = f.obs i a :=
  fun a i => obsModel_roundTrip f hf.1 a i

/-- 覆盖性使模型侧观测成为唯一延长：任何在像上与声明观测一致的模型侧函数，
    处处等于搬运后的观测。法律读法：不遗漏才谈得上"模型侧的取值由法律侧决定"；
    若载体里存在无原像的状态，那里的观测取值就没有法律依据。 -/
theorem obsModel_unique {α : Type} (f : Fragment α) (hf : FaithfulRep f) (i : f.ι)
    (g : f.β → f.γ) (hg : ∀ a, g (f.enc a) = f.obs i a) : ∀ b, g b = obsModel f i b := by
  intro b
  obtain ⟨a, ha⟩ := hf.2 b
  show g b = f.obs i (f.dec b)
  rw [← ha, hg]
  rw [hf.1 a]

/-- 见证用的表示：`Fin 2`（两个法律状态）嵌入 `Fin 3`（三个模型状态），即 `Fin.castSucc`
    ——像里少了最后一个模型状态。 -/
def castUp : Fin 2 → Fin 3 := Fin.castSucc

/-- 见证用的回读：`Nat.min · 1` 把 `Fin 3` 的第三个模型状态并入第二个状态。 -/
def dropDown : Fin 3 → Fin 2 :=
  fun b => ⟨Nat.min b.val 1, Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by decide : (1 : Nat) < 2)⟩

/-- 往返性对这个见证对成立：嵌入后用 `dropDown` 读回来是原状态。 -/
theorem castUp_retraction_roundTrip (a : Fin 2) : dropDown (castUp a) = a := by
  fin_cases a <;> decide

/-- 覆盖性对这个见证对失败：模型里第三个状态没有法律原像。 -/
theorem castUp_coverageFails : ∃ b : Fin 3, ∀ a : Fin 2, castUp a ≠ b := by
  refine ⟨⟨2, by decide⟩, ?_⟩
  intro a
  fin_cases a <;> decide

/-- 覆盖性真的是额外的假设：存在一对 `enc`/`dec` 使往返性成立而覆盖性不成立。
    这就是同构定理不可化简的原因——只有往返性时同构根本不存在。
    法律读法：一个"读回来不失真"的表示，仍可能在模型里凭空多出无原像的状态位。 -/
theorem coverage_is_genuinely_extra :
    ∃ (enc : Fin 2 → Fin 3) (dec : Fin 3 → Fin 2),
      (∀ a : Fin 2, dec (enc a) = a) ∧ ¬ (∀ b : Fin 3, ∃ a : Fin 2, enc a = b) :=
  ⟨castUp, dropDown, castUp_retraction_roundTrip, by
    intro hcv
    obtain ⟨b, hb⟩ := castUp_coverageFails
    obtain ⟨a, ha⟩ := hcv b
    exact hb a ha⟩

/-- 该见证对确实不构成同构：不存在两侧恰为 `castUp`/`dropDown` 的等价。
    法律读法：范围不足的表示不能被称为"模型就是法律对象层"，即使它在每个原像上都无损。 -/
theorem no_equiv_for_castUp :
    ¬ ∃ e : Equiv (Fin 2) (Fin 3), e.toFun = castUp ∧ e.invFun = dropDown := by
  intro h
  obtain ⟨_, hcv⟩ := (representation_scope castUp dropDown).mp h
  obtain ⟨b, hb⟩ := castUp_coverageFails
  obtain ⟨a, ha⟩ := hcv b
  exact hb a ha

/-- `dropDown` 是满射：`Fin 2` 的每个状态都有 `Fin 3` 中的原像。 -/
theorem dropDown_surjective : ∀ b : Fin 2, ∃ a : Fin 3, dropDown a = b :=
  fun b => ⟨castUp b, castUp_retraction_roundTrip b⟩

/-- 满射确有截面（Lean 的选择公理使然）。这一条特意写下，是为了说明
    "满射没有右逆"这一常见口头说法在 Lean 中为假，本件不声明它；本件声明的是另一侧。 -/
theorem dropDown_has_section : ∃ sec : Fin 2 → Fin 3, ∀ b : Fin 2, dropDown (sec b) = b :=
  ⟨castUp, castUp_retraction_roundTrip⟩

/-- `dropDown` 把 `Fin 3` 的两个不同状态并成一个，故非单射（鸽巢）。 -/
theorem dropDown_not_injective : ¬ Function.Injective dropDown := by
  intro hinj
  have heq : dropDown (⟨1, by decide⟩ : Fin 3) = dropDown (⟨2, by decide⟩ : Fin 3) := by decide
  have hne : (⟨1, by decide⟩ : Fin 3) ≠ (⟨2, by decide⟩ : Fin 3) := by decide
  exact hne (hinj heq)

/-- 覆盖性单独也不够：对任意 `dec : Fin 2 → Fin 3`，反向往返 `∀ a, dec (dropDown a) = a`
    都不可能成立——它会使 `dropDown` 成为单射，而鸽巢原理已给出它不是单射。
    法律读法：只保证"模型每个状态都有法律依据"，仍可能已经把两个法律状态并成一个；
    要拿到同构必须有以给定 `enc`/`dec` 为两侧的往返，二者合起来才是 P-002 的右端。 -/
theorem coverage_alone_has_no_inverse_roundtrip :
    ∀ dec : Fin 2 → Fin 3, ¬ (∀ a : Fin 3, dec (dropDown a) = a) := by
  intro dec habs
  exact dropDown_not_injective (injective_of_roundtrip dropDown dec habs)

/-- 层一的具体片段：法律对象层是 `Fin 2`（例如意思表示的两种生效状态），
    载体同为 `Fin 2`，声明观测只有一个且取值就是该状态本身（因此可分辨）。 -/
def layerStatus : Fragment (Fin 2) where
  β := Fin 2
  ι := Fin 1
  γ := Fin 2
  obs := fun _ a => a
  enc := id
  dec := id

/-- 层二的具体片段：同一法律对象层，载体仍为 `Fin 2`，但声明观测是常值 `true`
    （例如登记层只记"已入簿"这一件事）。它双向忠实，却分辨不出任何两个对象。 -/
def layerRegister : Fragment (Fin 2) where
  β := Fin 2
  ι := Fin 1
  γ := Bool
  obs := fun _ _ => true
  enc := id
  dec := id

/-- 层一满足往返性。 -/
theorem layerStatus_roundTrip : RoundTrip layerStatus := fun _ => rfl

/-- 层一满足覆盖性。 -/
theorem layerStatus_coverage : Coverage layerStatus := fun b => ⟨b, rfl⟩

/-- 层二满足往返性。 -/
theorem layerRegister_roundTrip : RoundTrip layerRegister := fun _ => rfl

/-- 联合模型载体：两个声明片段共用以同一法律对象层时，载体取两枚表示像的配对，
    并要求这对像真的有共同法律原像（纤维积，即对角嵌入的像）。
    法律读法：统一模型不是把两个模型并排放着，而是只承认"两侧都指同一法律对象"的状态组合。 -/
structure Joint {α : Type} (f₁ f₂ : Fragment α) where
  b₁ : f₁.β
  b₂ : f₂.β
  witnessed : ∃ a : α, f₁.enc a = b₁ ∧ f₂.enc a = b₂

/-- 把法律对象送进联合载体：两侧同时取各自片段的表示。 -/
def jointDiag {α : Type} (f₁ f₂ : Fragment α) (a : α) : Joint f₁ f₂ :=
  ⟨f₁.enc a, f₂.enc a, a, rfl, rfl⟩

/-- 从联合载体回读法律对象：用层一的表示回读第一分量（层一已声明往返性）。 -/
def jointRetract {α : Type} (f₁ f₂ : Fragment α) (j : Joint f₁ f₂) : α := f₁.dec j.b₁

/-- 联合表示满足往返性：送进联合载体再回读仍是原法律对象。 -/
theorem jointDiag_roundTrip {α : Type} (f₁ f₂ : Fragment α) (hrt : RoundTrip f₁) (a : α) :
    jointRetract f₁ f₂ (jointDiag f₁ f₂ a) = a := hrt a

/-- 联合表示满足覆盖性：联合载体按定义只由有共同原像的对构成，故每个元素都在像里。
    这正是取纤维积而非直积的理由——直积会引入无法律原像的状态组合。 -/
theorem jointDiag_coverage {α : Type} (f₁ f₂ : Fragment α) (j : Joint f₁ f₂) :
    ∃ a : α, jointDiag f₁ f₂ a = j := by
  obtain ⟨b₁, b₂, w⟩ := j
  obtain ⟨a, h₁, h₂⟩ := w
  refine ⟨a, ?_⟩
  subst h₁
  subst h₂
  rfl

/-- 联合载体上层一的模型侧观测：沿层一投影回读，再取该层声明观测。 -/
def jointObs₁ {α : Type} (f₁ f₂ : Fragment α) (i : f₁.ι) (j : Joint f₁ f₂) : f₁.γ :=
  f₁.obs i (f₁.dec j.b₁)

/-- 联合载体上层二的模型侧观测：沿层二投影回读，再取该层声明观测。 -/
def jointObs₂ {α : Type} (f₁ f₂ : Fragment α) (i : f₂.ι) (j : Joint f₁ f₂) : f₂.γ :=
  f₂.obs i (f₂.dec j.b₂)

/-- 层一的声明观测在联合载体上由第一投影计算得出。 -/
theorem joint_obs₁_agrees {α : Type} (f₁ f₂ : Fragment α) (hrt : RoundTrip f₁)
    (a : α) (i : f₁.ι) : jointObs₁ f₁ f₂ i (jointDiag f₁ f₂ a) = f₁.obs i a :=
  congrArg (f₁.obs i) (hrt a)

/-- 层二的声明观测在联合载体上由第二投影计算得出。 -/
theorem joint_obs₂_agrees {α : Type} (f₁ f₂ : Fragment α) (hrt : RoundTrip f₂)
    (a : α) (i : f₂.ι) : jointObs₂ f₁ f₂ i (jointDiag f₁ f₂ a) = f₂.obs i a :=
  congrArg (f₂.obs i) (hrt a)

/-- 联合投影在声明观测上一致：两层的每一个声明观测都可由联合载体经相应投影算出，
    且在原法律对象处与声明值相等。法律读法：统一之后各层仍然只说自己声明过的事，
    合并层不改变任何一层的观测取值。 -/
theorem joint_projections_agree_on_declared {α : Type} (f₁ f₂ : Fragment α)
    (h₁ : RoundTrip f₁) (h₂ : RoundTrip f₂) :
    (∀ (a : α) (i : f₁.ι), jointObs₁ f₁ f₂ i (jointDiag f₁ f₂ a) = f₁.obs i a) ∧
      (∀ (a : α) (i : f₂.ι), jointObs₂ f₁ f₂ i (jointDiag f₁ f₂ a) = f₂.obs i a) :=
  ⟨joint_obs₁_agrees f₁ f₂ h₁, joint_obs₂_agrees f₁ f₂ h₂⟩

/-- 联合对角嵌入是单射：只要层一可回读，两个法律对象在联合载体里的像不同就意味对象本身不同。 -/
theorem joint_diagonal_injective {α : Type} (f₁ f₂ : Fragment α) (hrt : RoundTrip f₁) :
    Function.Injective (jointDiag f₁ f₂) :=
  injective_of_roundtrip (jointDiag f₁ f₂) (jointRetract f₁ f₂)
    (jointDiag_roundTrip f₁ f₂ hrt)

/-- 联合模型不退化（判据版）：若层一存在把 `x`、`y` 分开的声明观测，则联合载体里
    存在两个不同元素，且层一的某个模型侧观测把它们分开。
    法律读法：统一模型不会把所有层次压成一个数——只要某一层声明了可分辨的观测，
    联合载体就至少有两个状态。
    条件说明：不退化在此只能作为**条件定理**证明，假设是 `hsep`（层一存在分离观测）；
    没有这条假设时本件不声称联合载体非退化
    （反面见证见 `observations_do_not_separate_until_declared`）。 -/
theorem joint_model_is_not_collapsed {α : Type} (f₁ f₂ : Fragment α) (x y : α)
    (h₁ : RoundTrip f₁) (hsep : ∃ i : f₁.ι, f₁.obs i x ≠ f₁.obs i y) :
    ∃ (p q : Joint f₁ f₂), p ≠ q ∧ ∃ i : f₁.ι,
      jointObs₁ f₁ f₂ i p ≠ jointObs₁ f₁ f₂ i q := by
  obtain ⟨i, hi⟩ := hsep
  refine ⟨jointDiag f₁ f₂ x, jointDiag f₁ f₂ y, ?_, i, ?_⟩
  · intro heq
    exact hi (congrArg (f₁.obs i) (joint_diagonal_injective f₁ f₂ h₁ heq))
  · rw [joint_obs₁_agrees f₁ f₂ h₁ x i, joint_obs₁_agrees f₁ f₂ h₁ y i]
    exact hi

/-- 层一的声明观测确实分开 `Fin 2` 的两个状态：该观测的取值就是状态本身，
    于是两个状态给出不同取值。这一条是 `joint_legal_model_exists` 所用的分离见证，
    也就是 `joint_model_is_not_collapsed` 里假设 `hsep` 在具体片段上的兑现。 -/
theorem layerStatus_obs_separates :
    ∃ i : layerStatus.ι,
      layerStatus.obs i (⟨0, by decide⟩ : Fin 2) ≠ layerStatus.obs i (⟨1, by decide⟩ : Fin 2) := by
  refine ⟨⟨0, by decide⟩, fun h => ?_⟩
  have hv : ((⟨0, by decide⟩ : Fin 2) : Nat) ≠ ((⟨1, by decide⟩ : Fin 2) : Nat) := by decide
  exact hv (congrArg Fin.val h)

/-- 联合法律模型存在（具体非退化见证）：层一（可分辨的生效状态观测）与层二（常值的入簿观测）
    在同一法律对象层 `Fin 2` 上合成的联合载体里，确实有两个不同元素，
    且层一的声明观测把它们分开。法律读法：统一模型不是引用一个定义就宣称存在——
    这里交出的是一对具体状态和一个真正区分它们的标准。 -/
theorem joint_legal_model_exists :
    ∃ (p q : Joint layerStatus layerRegister), p ≠ q ∧
      ∃ i : layerStatus.ι,
        jointObs₁ layerStatus layerRegister i p ≠ jointObs₁ layerStatus layerRegister i q :=
  joint_model_is_not_collapsed layerStatus layerRegister (⟨0, by decide⟩ : Fin 2)
    (⟨1, by decide⟩ : Fin 2) layerStatus_roundTrip layerStatus_obs_separates

/-- 联合法律模型与法律对象层同构：具体两片段的联合载体经对角嵌入与投影回读构成等价。
    法律读法：在已声明的两层之上，联合模型确实是法律对象层的另一种写法，不多也不少。 -/
theorem joint_legal_model_is_isomorphic_to_domain :
    ∃ e : Equiv (Fin 2) (Joint layerStatus layerRegister),
      e.toFun = jointDiag layerStatus layerRegister ∧
        e.invFun = jointRetract layerStatus layerRegister :=
  iso_of_roundtrip_and_cover (jointDiag layerStatus layerRegister)
    (jointRetract layerStatus layerRegister)
    (jointDiag_roundTrip layerStatus layerRegister layerStatus_roundTrip)
    (fun b => jointDiag_coverage layerStatus layerRegister b)

/-- 一个刻意声明得过小的片段：法律对象层是 `Fin 2`（两个不同对象），
    载体是 `Unit`（模型里只有一个状态），声明观测只有一个且恒为 `true`。 -/
def coarseFragment : Fragment (Fin 2) where
  β := Unit
  ι := Fin 1
  γ := Bool
  obs := fun _ _ => true
  enc := fun _ => ()
  dec := fun _ => (⟨0, by decide⟩ : Fin 2)

/-- 声明之前，观测分不开对象：存在两个不同法律对象，其全部声明观测取值相同。
    法律读法：只比"所有已声明观测都一致"就断言"两个对象相同"，是把声明范围当成了事实范围；
    例如两份合同在"是否书面"这一观测上一致，绝不等于两份合同是同一份。 -/
theorem observations_do_not_separate_until_declared :
    ∃ (x y : Fin 2), x ≠ y ∧ ∀ i : coarseFragment.ι,
      coarseFragment.obs i x = coarseFragment.obs i y :=
  ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by decide, fun _ => rfl⟩

/-- 上述见证的逻辑后果：对本片段而言"观测一致 ⇒ 对象相等"这一蕴含式为假。
    法律读法：本件不把"观测等价即对象同一"当作可用推理规则。 -/
theorem observation_agreement_does_not_imply_equality :
    ¬ ∀ (x y : Fin 2),
      (∀ i : coarseFragment.ι, coarseFragment.obs i x = coarseFragment.obs i y) → x = y := by
  intro hall
  have hne : (⟨0, by decide⟩ : Fin 2) ≠ (⟨1, by decide⟩ : Fin 2) := by decide
  exact hne (hall (⟨0, by decide⟩ : Fin 2) (⟨1, by decide⟩ : Fin 2) fun _ => rfl)

/-- 补上缺的那条假设才有分离结论：若片段被声明为分离观测族（观测一致即对象相等），
    则模型侧观测在原像上一致便可推出对象相等。
    法律读法：分离性是片段自身的声明强度，不是表示定理自动附赠的东西。 -/
theorem separating_fragment_agreement_implies_equality {α : Type} (f : Fragment α)
    (hrt : RoundTrip f)
    (hsep : ∀ x y : α, (∀ i : f.ι, f.obs i x = f.obs i y) → x = y) (x y : α)
    (h : ∀ i : f.ι, obsModel f i (f.enc x) = obsModel f i (f.enc y)) : x = y :=
  hsep x y fun i => by
    rw [← obsModel_roundTrip f hrt x i, ← obsModel_roundTrip f hrt y i]
    exact h i

end JurisLean.Seams.Representation
