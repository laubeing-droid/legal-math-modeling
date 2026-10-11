import Mathlib.Tactic
import JurisLean.Seams.PrecedentFlow
import JurisLean.Seams.UnifiedNeedlesXU

/-!
# 第二波针强度差额清算 41/44/58（UnifiedNeedlesGapLate）

中文说明：本件承接 R1 评审第 2 条表点名、排入 W1-10/W1-11 的三针差额：

- **第 41 针（S6，`docs/spec/20261007-统一法律数学模型_附录I_Lean施工明细.md:795`
  `receipt_has_semantic_derivation`）**：`UnifiedNeedlesS6S7.lean:53-54` 如实声明的
  开放点＝BND04（全量施工方案 §12.6.5，"不完备不得成为不利裁判的替代依据"）的
  **绑定级消费链**。本件把它从"存在级"升级为三级显式定理链：**版本绑定 →
  数据面加载 → 下游消费**（每级一个定理，后级证明字面消费前级结论），并证
  **绑定一致性**（同版本绑定的读写打在同一数据面上：无旁路通道
  `same_binding_same_plane`、无陈旧缓存 `read_after_write_same_plane`）。
  S6S7 已交付的回执侧（初态来源合同＋回执堆不进转移）不重做；本件补的是
  该针明确留开的 BND04 绑定消费侧。
- **第 44 针（S7，附录 I:798 `precedent_update_preserves_norm_structure`）**：
  `UnifiedNeedlesS6S7.lean:321-334` 的开放点＝`applicableVersions` 查询层的
  **双向等式未展开**。本件新建"绑定面"（键＝快照 payload 的登记读法），证
  **查询结果 = v ↔ 绑定面记录 = v 的两个方向**（正向无条件成立；反向在命中
  唯一性／键唯一 `FaceWf` 下成立），并展开**版本变更后的可观察性**（新版本
  可查、被取代旧版本不可回读）与**唯一例外通道＝显式回流事件**（不自动复活）。
- **第 58 针（XU，附录 I:812 `nn_interval_certificate_sound`）**：
  `UnifiedNeedlesXU.lean:573-593` 的一般式把 `hstab` 作为**整域假设**引入，且
  供给端只有两输入两隐元一片段网络、证书接受判据与格式对接开放。本件给出
  **有限一般网络、指定域**的 η 证书：显式证书格式（域描述＋逐段界＋验证位）、
  数据级可判定预检、**供给侧实际构造**（由逐段（逐边）数据算出胞腔锚点、半径、
  局部常数，逐段验证条件被证明而非假设）、接受判据与健全性（接受 ⇒ 指定域内
  传播误差界成立）；**hstab 不作整域假设**：指定域上的 hstab 形状由逐段证书
  推导（`designated_hstab_from_segs`），且证明有限段表永不覆盖全空间
  （`finite_segs_never_cover_whole_space`——全空间 hstab 只能如实留作显式假设
  或声明域外）；并给对 `UnifiedNeedlesXU` 既有消费面（NN 区间证书／观测歧义／
  RadiusCert 证书格式）的适配定理——不改 XU 文件本身。

## 载体与开放点（诚实声明）

- 第 41/44 针复用 `PrecedentFlow` 的 `VersionEnv / SourceVersionRecord /
  precedentUpdate / applicableAtBool` 冻结载体，不重建版本语义；BND04 下游入口
  的"独立终结推导是否已闭"在载体内是显式 `Bool` 检查位 `derivationClosed`
  （真实检查器在 BoundaryClosure/ULM12 侧，本件只约束消费链的结构封闭）。
- 第 44 针反向等式需要的**命中唯一**写成显式具名前提（一般形 `huni`，键唯一
  形 `FaceWf`）；新键不撞旧键写成 `hfresh`（可由 `EnvWf.fresh` 经
  `bindKey_fresh_of_EnvWf` 得到）。显式回流是显式事件构造子
  （`backflowReactivate` 重新登记 active），不是被取代记录的自动复活。
- 第 58 针的有限网络载体＝逐段线性网 `pwlNet`（段表＋段内仿射式求值，段两两
  不交 `SegsDisjoint`、段宽正 `lo < hi` 为显式前提；域外未命中段表时 fail-closed
  读 0，不参与指定域内传播）。其他网络类（深层 ReLU 网等）不在本件构造域内，
  但证书格式／预检／接受判据／健全性对任意 `f : ℚ × ℚ → ℚ` 一般成立。

## 档位

零 `sorry`、零 `admit`、零自定义 `axiom`、零 `True` 逃避。本件 `CI_NOT_RUN`
（本地不编译 Lean，fail-closed），以 GitHub Actions 模块轮为唯一编译权威。
-/

namespace JurisLean.Seams.UnifiedNeedlesGapLate

open JurisLean.Seams.PrecedentFlow
open JurisLean.Seams.Uncertainty

/-! ## 第 44 针（差额一）：版本查询的双向等式 -/

/-- 绑定键＝快照 payload。绑定面以键读记录；键可区分性由 `FaceWf` 声明。 -/
def bindKey (v : SourceVersionRecord) : String :=
  v.snapshot.payload

/-- 键相等 ⇒ 快照相等（快照由 payload 决定）。 -/
theorem snapshot_eq_of_bindKey_eq {v w : SourceVersionRecord} (h : bindKey v = bindKey w) :
    v.snapshot = w.snapshot := by
  cases v with
  | mk s _ _ _ _ =>
    cases w with
    | mk t _ _ _ _ =>
      have h' : s.payload = t.payload := h
      cases s
      cases t
      exact congrArg LegalId.mk h'

/-- 绑定面良态：同键必同记录（键在环境内唯一）。这是查询反向等式的
    键唯一形前提。 -/
def FaceWf (E : VersionEnv) : Prop :=
  ∀ (k : String) (v w : SourceVersionRecord), v ∈ E.versions → w ∈ E.versions →
    bindKey v = k → bindKey w = k → v = w

/-- 通用辅助：表中元素满足谓词且谓词命中者唯一时，`find?` 精确返回该元素。 -/
theorem find?_eq_some_of_unique {α : Type} (p : α → Bool) :
    ∀ (l : List α) (v : α), v ∈ l → p v = true → (∀ u ∈ l, p u = true → u = v) →
      l.find? p = some v := by
  intro l
  induction l with
  | nil => intro v hv _ _; cases hv
  | cons a l ih =>
    intro v hv hpv huni
    by_cases hpa : p a = true
    · rw [List.find?_cons_of_pos hpa]
      exact congrArg some (huni a List.mem_cons_self hpa)
    · rw [List.find?_cons_of_neg hpa]
      refine ih v ?_ hpv ?_
      · rcases List.mem_cons.mp hv with heq | hm
        · subst heq
          exact absurd hpv hpa
        · exact hm
      · intro u hu hpu
        exact huni u (List.mem_cons_of_mem _ hu) hpu

/-- 变谓词版取值：`find?` 命中即谓词成立。v4.30 的 `List.find?_some` 是常谓词形
    （`find? (fun _ => decide p) l = some a → p`），对逐元素谓词不适用，本件自备。 -/
theorem find?_eq_some_pred {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), l.find? p = some a → p a = true := by
  intro l
  induction l with
  | nil => intro a h; cases h
  | cons b l ih =>
    intro a h
    by_cases hpb : p b = true
    · rw [List.find?_cons_of_pos hpb] at h
      injection h with hba
      subst hba
      exact hpb
    · rw [List.find?_cons_of_neg hpb] at h
      exact ih a h

/-- **查询面**：时点 `t` 对键 `k` 的版本查询——经可适用性过滤后取首个命中键。 -/
def queryVersion (E : VersionEnv) (t : Int) (k : String) : Option SourceVersionRecord :=
  (applicableVersions E t).find? (fun u => bindKey u = k)

/-- **第 44 针·双向等式（一般形）**：查询结果 = v ↔ 绑定面记录 = v（且 v 在时点
    可适用）。正向无条件；反向由命中唯一性（`huni`）闭合——这正是 S6S7 第 44 针
    留开的"双向等式重述"。 -/
theorem query_eq_some_iff_face (E : VersionEnv) (t : Int) (k : String)
    (v : SourceVersionRecord)
    (huni : ∀ u ∈ E.versions, bindKey u = k → applicableAtBool u t = true → u = v) :
    queryVersion E t k = some v ↔
      (v ∈ E.versions ∧ bindKey v = k ∧ applicableAtBool v t = true) := by
  constructor
  · intro h
    have hf : (applicableVersions E t).find? (fun u => decide (bindKey u = k)) = some v := h
    have hmem : v ∈ applicableVersions E t := List.mem_of_find?_eq_some hf
    have hpv : (fun u => decide (bindKey u = k)) v = true :=
      find?_eq_some_pred (fun u => decide (bindKey u = k)) (applicableVersions E t) v hf
    obtain ⟨hin, happ⟩ := mem_applicableVersions E t v |>.mp hmem
    exact ⟨hin, decide_eq_true_iff.mp hpv, happ⟩
  · rintro ⟨hin, hkey, happ⟩
    refine find?_eq_some_of_unique (fun u => decide (bindKey u = k)) (applicableVersions E t) v
      (mem_applicableVersions E t v |>.mpr ⟨hin, happ⟩) (decide_eq_true_iff.mpr hkey) ?_
    intro u hu huk
    obtain ⟨huin, huap⟩ := mem_applicableVersions E t u |>.mp hu
    exact huni u huin (decide_eq_true_iff.mp huk) huap

/-- **第 44 针·双向等式（绑定面良态形）**：`FaceWf` 下，键恰为 k 的记录 v 的查询
    结果是 v 当且仅当 v 在环境中且时点可适用——"查询结果=v ↔ 绑定面记录=v"
    两个方向都是定理，不再只有单向成员读数。 -/
theorem query_eq_some_iff_face_of_faceWf (E : VersionEnv) (hwf : FaceWf E) (t : Int)
    (k : String) (v : SourceVersionRecord) (hmemv : v ∈ E.versions)
    (hkey : bindKey v = k) :
    queryVersion E t k = some v ↔ (v ∈ E.versions ∧ applicableAtBool v t = true) := by
  refine (query_eq_some_iff_face E t k v fun u hu huk _ =>
    hwf k u v hu hmemv huk hkey).trans ?_
  constructor
  · rintro ⟨hin, _, happ⟩
    exact ⟨hin, happ⟩
  · rintro ⟨hin, happ⟩
    exact ⟨hin, hkey, happ⟩

/-- 正向读数无条件成立（无 `FaceWf` 也真）：查询命中 ⇒ 绑定面确有该键登记且
    记录在时点可适用。 -/
theorem query_some_imp_face (E : VersionEnv) (t : Int) (k : String)
    (v : SourceVersionRecord) (h : queryVersion E t k = some v) :
    v ∈ E.versions ∧ bindKey v = k ∧ applicableAtBool v t = true := by
  have hf : (applicableVersions E t).find? (fun u => decide (bindKey u = k)) = some v := h
  have hmem : v ∈ applicableVersions E t := List.mem_of_find?_eq_some hf
  have hpv : (fun u => decide (bindKey u = k)) v = true :=
    find?_eq_some_pred (fun u => decide (bindKey u = k)) (applicableVersions E t) v hf
  obtain ⟨hin, happ⟩ := mem_applicableVersions E t v |>.mp hmem
  exact ⟨hin, decide_eq_true_iff.mp hpv, happ⟩

/-- 键唯一性穿过授权前例更新（键不因更新改变：取代只动 status，新键由
    `hfresh` 保证不撞旧键）。 -/
theorem faceWf_precedentUpdate (E : VersionEnv) (ad : AuthorizedDecision)
    (hwf : FaceWf E)
    (hfresh : ∀ u ∈ E.versions, bindKey u ≠ bindKey ad.decision.newRecord)
    (hfire : updateFires ad.decision = true) :
    FaceWf (precedentUpdate ad E) := by
  intro k v w hv hw hkv hkw
  rw [update_versions_fires ad E hfire] at hv hw
  rcases List.mem_cons.mp hv with hev | hv'
  · subst hev
    rcases List.mem_cons.mp hw with hew | hw'
    · subst hew
      exact rfl
    · obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw'
      subst huw
      have hku : bindKey u = bindKey ad.decision.newRecord := by
        have e2 : bindKey (supersedeRecord ad.decision u) = bindKey u := by
          show (supersedeRecord ad.decision u).snapshot.payload = u.snapshot.payload
          rw [supersedeRecord_snapshot ad.decision u]
        rw [← e2]
        exact hkw.trans hkv.symm
      exact absurd hku (hfresh u hu)
  · obtain ⟨u, hu, huv⟩ := List.mem_map.mp hv'
    subst huv
    have hku : bindKey u = k := by
      have e2 : bindKey (supersedeRecord ad.decision u) = bindKey u := by
        show (supersedeRecord ad.decision u).snapshot.payload = u.snapshot.payload
        rw [supersedeRecord_snapshot ad.decision u]
      rw [← e2]
      exact hkv
    rcases List.mem_cons.mp hw with hew | hw'
    · subst hew
      exact absurd (hku.trans hkw.symm) (hfresh u hu)
    · obtain ⟨u', hu', huw⟩ := List.mem_map.mp hw'
      subst huw
      have hku' : bindKey u' = k := by
        have e2 : bindKey (supersedeRecord ad.decision u') = bindKey u' := by
          show (supersedeRecord ad.decision u').snapshot.payload = u'.snapshot.payload
          rw [supersedeRecord_snapshot ad.decision u']
        rw [← e2]
        exact hkw
      rw [hwf k u u' hu hu' hku hku']

/-- `EnvWf` 的快照新鲜度翻成键新鲜度（`bindKey` 读法），供消费链定理取用。 -/
theorem bindKey_fresh_of_EnvWf (E : VersionEnv) (ad : AuthorizedDecision) (hwf : EnvWf E ad)
    (u : SourceVersionRecord) (hu : u ∈ E.versions) :
    bindKey u ≠ bindKey ad.decision.newRecord := by
  intro he
  exact hwf.fresh u hu ((snapshot_eq_of_bindKey_eq he).trans hwf.recordMatchesSnapshot)

/-- **第 44 针·变更后可观察性（新版本可查）**：授权前例更新触发后，凡时点落在
    新版本生效区间内，键查询精确返回新版本——版本变更经查询面**可观察**。 -/
theorem query_new_version_readable_after_update (E : VersionEnv) (ad : AuthorizedDecision)
    (t : Int) (hfire : updateFires ad.decision = true)
    (happ : versionApplicableAt ad.decision.newRecord t)
    (hfresh : ∀ u ∈ E.versions, bindKey u ≠ bindKey ad.decision.newRecord) :
    queryVersion (precedentUpdate ad E) t (bindKey ad.decision.newRecord) =
      some ad.decision.newRecord := by
  refine (query_eq_some_iff_face _ _ _ _ ?_).mpr
    ⟨?_, rfl, applicableAtBool_true_iff _ _ |>.mpr happ⟩
  · rw [update_versions_fires ad E hfire]
    intro u hu huk _
    rcases List.mem_cons.mp hu with heq | hm
    · exact heq
    · obtain ⟨w, hw, hwu⟩ := List.mem_map.mp hm
      subst hwu
      have hk : bindKey w = bindKey ad.decision.newRecord := by
        simpa only [bindKey, supersedeRecord_snapshot] using huk
      exact absurd hk (hfresh w hw)
  · rw [update_versions_fires ad E hfire]
    exact List.mem_cons_self

/-- **第 44 针·旧版本不可回读**：被取代（touched）的旧版本在任何时点都不再是
    查询结果——读取通道精确返回 none（键唯一＋新键新鲜），无陈旧缓存可回读。 -/
theorem query_old_version_unreadable_after_update (E : VersionEnv) (ad : AuthorizedDecision)
    (v : SourceVersionRecord) (t : Int)
    (hwf : FaceWf E) (hfire : updateFires ad.decision = true)
    (hv : isTouchedBy ad E v)
    (hfresh : ∀ u ∈ E.versions, bindKey u ≠ bindKey ad.decision.newRecord) :
    queryVersion (precedentUpdate ad E) t (bindKey v) = none := by
  refine List.find?_eq_none.mpr ?_
  intro u hu huk
  have hmem : u ∈ (precedentUpdate ad E).versions ∧ applicableAtBool u t = true :=
    mem_applicableVersions (precedentUpdate ad E) t u |>.mp hu
  rw [update_versions_fires ad E hfire] at hmem
  rcases List.mem_cons.mp hmem.1 with heq | hm
  · subst heq
    have huk' : bindKey ad.decision.newRecord = bindKey v := decide_eq_true_iff.mp huk
    exact hfresh v hv.1 huk'.symm
  · obtain ⟨w, hwmem, hwu⟩ := List.mem_map.mp hm
    subst hwu
    have hk : bindKey w = bindKey v := by
      have h1 : bindKey (supersedeRecord ad.decision w) = bindKey v :=
        decide_eq_true_iff.mp huk
      simp only [bindKey] at h1
      rw [supersedeRecord_snapshot ad.decision w] at h1
      exact h1
    have hweqv : w = v := hwf (bindKey v) w v hwmem hv.1 hk rfl
    subst hweqv
    have hstat : (supersedeRecord ad.decision w).status = VersionStatus.superseded := by
      rw [supersedeRecord_drops_hit_active ad.decision w hv.2.1 hv.2.2]
    exact absurd (applicableAtBool_true_iff _ _ |>.mp hmem.2)
      (superseded_source_invalidates _ t hstat)

/-- **第 44 针·可观察性合取**：同一键、同一时点，更新前查询命中旧版本、更新后
    精确为 none——版本变更在查询面上是可观察的两面。 -/
theorem query_observable_change_on_supersession (E : VersionEnv) (ad : AuthorizedDecision)
    (v : SourceVersionRecord) (t : Int)
    (hwf : FaceWf E) (hfire : updateFires ad.decision = true)
    (hv : isTouchedBy ad E v) (happ : versionApplicableAt v t)
    (hfresh : ∀ u ∈ E.versions, bindKey u ≠ bindKey ad.decision.newRecord) :
    queryVersion E t (bindKey v) = some v ∧
      queryVersion (precedentUpdate ad E) t (bindKey v) = none := by
  refine ⟨?_, query_old_version_unreadable_after_update E ad v t hwf hfire hv hfresh⟩
  rw [query_eq_some_iff_face_of_faceWf E hwf t (bindKey v) v hv.1 rfl]
  exact ⟨hv.1, applicableAtBool_true_iff v t |>.mpr happ⟩

/-- **显式回流事件**（旧版本可回读的唯一通道）：把被降级记录以 active 状态
    重新登记（同快照，其余字段不动）。没有这一显式事件，被取代版本不可回读。 -/
def backflowReactivate (v : SourceVersionRecord) : SourceVersionRecord :=
  { v with status := VersionStatus.active }

/-- 显式回流事件的环境改写：把重新登记的记录挂到环境最前。 -/
def explicitBackflow (E : VersionEnv) (v : SourceVersionRecord) : VersionEnv :=
  { versions := backflowReactivate v :: E.versions }

/-- **第 44 针·例外通道**：显式回流事件之后，键查询重新读到该版本（重新登记的
    active 副本）——"不可回读"的例外恰为显式回流，不存在隐式复活。 -/
theorem explicit_backflow_restores_readability (E : VersionEnv) (v : SourceVersionRecord)
    (t : Int)
    (huni : ∀ u ∈ E.versions, bindKey u = bindKey v → applicableAtBool u t = true → u = v)
    (hnotapp : ¬ versionApplicableAt v t)
    (heff : effectiveAt v t) :
    queryVersion (explicitBackflow E v) t (bindKey v) = some (backflowReactivate v) := by
  have hbf : applicableAtBool v t = false := by
    cases hb : applicableAtBool v t with
    | false => rfl
    | true => exact absurd (applicableAtBool_true_iff v t |>.mp hb) hnotapp
  refine (query_eq_some_iff_face _ _ _ _ ?_).mpr ⟨List.mem_cons_self, rfl, ?_⟩
  · intro u hu hkey happ'
    rcases List.mem_cons.mp hu with heq | hm
    · exact heq
    · have hueq : u = v := huni u hm hkey happ'
      subst hueq
      rw [hbf] at happ'
      exact Bool.noConfusion happ'
  · exact applicableAtBool_true_iff (backflowReactivate v) t |>.mpr ⟨heff, rfl⟩

/-! ## 第 41 针（差额二）：BND04 绑定级消费链 -/

/-- **版本绑定**：一次裁判运行绑定的版本键＋绑定时点。 -/
structure RunBinding where
  key : String
  t : Int

/-- **数据面加载**：绑定在环境中经查询面加载出的记录。加载失败显式 `none`
    （fail-closed），下游不得伪造载荷。全部加载走这一个函数——单一通道。 -/
def loadDataPlane (E : VersionEnv) (b : RunBinding) : Option SourceVersionRecord :=
  queryVersion E b.t b.key

/-- **第 41 针·链级 1（版本绑定级）**：良构绑定把键解析到绑定面记录——绑定的
    记录在环境中、键吻合、且在绑定时点可适用，则加载面精确返回它。
    （证明消费第 44 针双向等式的反向。） -/
theorem binding_resolves_to_face_record (E : VersionEnv) (b : RunBinding)
    (v : SourceVersionRecord)
    (hmem : v ∈ E.versions) (hkey : bindKey v = b.key) (happ : versionApplicableAt v b.t)
    (huni : ∀ u ∈ E.versions, bindKey u = b.key → versionApplicableAt u b.t → u = v) :
    loadDataPlane E b = some v := by
  refine (query_eq_some_iff_face E b.t b.key v ?_).mpr
    ⟨hmem, hkey, applicableAtBool_true_iff v b.t |>.mpr happ⟩
  intro u hu huk happ'
  exact huni u hu huk (applicableAtBool_true_iff u b.t |>.mp happ')

/-- **第 41 针·链级 2（数据面加载级）**：凡加载面返回的记录，键吻合绑定且在
    绑定时点可适用——加载面只可能是绑定解析的产物，不可能是自报载荷。
    （证明消费第 44 针正向读数 `query_some_imp_face`。） -/
theorem load_plane_consumes_binding (E : VersionEnv) (b : RunBinding)
    (v : SourceVersionRecord) (hload : loadDataPlane E b = some v) :
    bindKey v = b.key ∧ versionApplicableAt v b.t := by
  obtain ⟨_, hkey, happ⟩ := query_some_imp_face E b.t b.key v hload
  exact ⟨hkey, applicableAtBool_true_iff v b.t |>.mp happ⟩

/-- **下游判定**：下游消费入口面对绑定的两级输出——不出不利，或以**数据面
    加载出的那条记录**出不利。判定是加载面与推导闭合位的纯函数：
    面空或推导未闭 ⇒ 一律不出不利（fail-closed）。 -/
inductive DownstreamVerdict where
  | noAdverse
  | adverseOf (v : SourceVersionRecord)

def downstreamVerdict (E : VersionEnv) (b : RunBinding) (derivationClosed : Bool) :
    DownstreamVerdict :=
  match loadDataPlane E b with
  | none => DownstreamVerdict.noAdverse
  | some v =>
      if derivationClosed then DownstreamVerdict.adverseOf v
      else DownstreamVerdict.noAdverse

/-- **第 41 针·链级 3（下游消费级·BND04 主文）**：下游出了不利实体结论 ⇒
    引用的记录**恰是**数据面加载的记录，且独立终结推导已闭——判定引用由
    加载面决定，不由回执／自报反造权威。 -/
theorem adverse_citation_is_loaded_plane (E : VersionEnv) (b : RunBinding) (d : Bool)
    (v : SourceVersionRecord)
    (hadv : downstreamVerdict E b d = DownstreamVerdict.adverseOf v) :
    loadDataPlane E b = some v ∧ d = true := by
  cases hload : loadDataPlane E b with
  | none =>
    have hdm : downstreamVerdict E b d = DownstreamVerdict.noAdverse := by
      simp only [downstreamVerdict, hload]
    rw [hdm] at hadv
    exact DownstreamVerdict.noConfusion hadv
  | some u =>
    have hdm : downstreamVerdict E b d =
        if d then DownstreamVerdict.adverseOf u else DownstreamVerdict.noAdverse := by
      simp only [downstreamVerdict, hload]
    by_cases hd : d = true
    · rw [hdm, if_pos hd] at hadv
      injection hadv with huv
      subst huv
      exact ⟨rfl, hd⟩
    · rw [hdm, if_neg hd] at hadv
      exact DownstreamVerdict.noConfusion hadv

/-- **第 41 针·BND04 反向**：独立终结推导未闭 ⇒ 下游不可能出不利——
    "不完备不得成为不利裁判的替代依据"在绑定级消费链上的结构封闭
    （族内封闭锚见 `BoundaryClosure.closure_boundary4_incomplete_not_adverse`；
    本条把同一法定约束打到消费入口的形状上）。 -/
theorem incomplete_derivation_never_adverse (E : VersionEnv) (b : RunBinding) (d : Bool)
    (hd : d = false) :
    downstreamVerdict E b d = DownstreamVerdict.noAdverse := by
  cases hload : loadDataPlane E b with
  | none => simp only [downstreamVerdict, hload]
  | some u =>
    have hnd : ¬ (d = true) := by rw [hd]; simp
    simp only [downstreamVerdict, hload, if_neg hnd]

/-- **第 41 针·全链收口**：不利判定 ⇒ 三级链逐级闭合——引用记录键吻合绑定
    （链级 3+2）、记录在绑定时点适用（链级 2+1）、推导已闭（链级 3）。
    每级显式定理，链式 consumes。 -/
theorem adverse_full_chain (E : VersionEnv) (b : RunBinding) (d : Bool)
    (v : SourceVersionRecord)
    (hadv : downstreamVerdict E b d = DownstreamVerdict.adverseOf v) :
    bindKey v = b.key ∧ versionApplicableAt v b.t ∧ d = true := by
  obtain ⟨hload, hd⟩ := adverse_citation_is_loaded_plane E b d v hadv
  obtain ⟨hkey, happ⟩ := load_plane_consumes_binding E b v hload
  exact ⟨hkey, happ, hd⟩

/-- 消费会话：以绑定打开的数据面读数＋判定。 -/
structure Session where
  plane : Option SourceVersionRecord
  verdict : DownstreamVerdict

/-- 以绑定打开会话：加载与判定都只经绑定单通道。 -/
def openSession (E : VersionEnv) (b : RunBinding) (d : Bool) : Session :=
  { plane := loadDataPlane E b, verdict := downstreamVerdict E b d }

/-- **第 41 针·绑定一致性①**：同一版本绑定打开的两个会话读到**同一**数据面
    （无旁路通道、无会话私有载荷）。 -/
theorem same_binding_same_plane (E : VersionEnv) (b : RunBinding) (d₁ d₂ : Bool) :
    (openSession E b d₁).plane = (openSession E b d₂).plane := rfl

/-- **第 41 针·绑定一致性②（读写同面）**：写通道（授权前例更新）改写被绑定
    记录后，同一绑定的读通道可观察地变化且精确变为 none——读与写打在同一
    数据面上，不存在读旧写新的陈旧缓存。 -/
theorem read_after_write_same_plane (E : VersionEnv) (ad : AuthorizedDecision)
    (b : RunBinding) (v : SourceVersionRecord)
    (hwf : FaceWf E) (hfire : updateFires ad.decision = true)
    (hv : isTouchedBy ad E v) (hkey : b.key = bindKey v) (happ : versionApplicableAt v b.t)
    (hfresh : ∀ u ∈ E.versions, bindKey u ≠ bindKey ad.decision.newRecord) :
    loadDataPlane E b = some v ∧ loadDataPlane (precedentUpdate ad E) b = none := by
  have hb := query_observable_change_on_supersession E ad v b.t hwf hfire hv happ hfresh
  constructor
  · show queryVersion E b.t b.key = some v
    rw [hkey]
    exact hb.1
  · show queryVersion (precedentUpdate ad E) b.t b.key = none
    rw [hkey]
    exact hb.2

/-! ## 第 58 针（差额三）：指定域 η 证书的格式、构造、验证与对接 -/

/-- 指定域的胞腔：锚点＋半径（ℚ×ℚ 盒，与 `Uncertainty.withinBall` 同形）。 -/
structure EtaCell where
  anchor : ℚ × ℚ
  eta : ℚ

/-- 逐段界条目：胞腔＋该段局部 Lipschitz 常数（构造时由网络逐段数据算出）。 -/
structure SegEntry where
  cell : EtaCell
  lip : ℚ

/-- **η 证书格式**：域描述（指定域＝有限点表）＋逐段界＋验证位（与段等长）。 -/
structure EtaCert where
  dom : List (ℚ × ℚ)
  segs : List SegEntry
  bits : List Bool

/-- **逐段验证条件**（每段界的义务，Prop 层）：半径与常数非负，且段内每点的
    网络输出落在锚点可达带内。供给侧逐段证明，不假设整域稳定。 -/
def segBound (f : ℚ × ℚ → ℚ) (s : SegEntry) : Prop :=
  0 ≤ s.cell.eta ∧ 0 ≤ s.lip ∧
    ∀ x : ℚ × ℚ, withinBall s.cell.eta x s.cell.anchor →
      f s.cell.anchor - s.lip * s.cell.eta ≤ f x ∧
      f x ≤ f s.cell.anchor + s.lip * s.cell.eta

/-- 指定域覆盖：域表每点落在某段胞腔内。 -/
def coversDom (c : EtaCert) : Prop :=
  ∀ p ∈ c.dom, ∃ s ∈ c.segs, withinBall s.cell.eta p s.cell.anchor

/-- **证书数据级预检**（可判定部分）：验证位与段数一致、位全真。逐段界本身是
    Prop 义务，不冒充可判定。 -/
def certPrecheckOk (c : EtaCert) : Bool :=
  (c.bits.length == c.segs.length) && c.bits.all (fun b => b)

/-- **证书接受判据**：数据级预检＋指定域覆盖＋每段验证条件＋每段可达带被声明
    区间 [lo, hi] 包住。四条齐备才接受。 -/
def etaCertAccepted (f : ℚ × ℚ → ℚ) (c : EtaCert) (lo hi : ℚ) : Prop :=
  certPrecheckOk c = true ∧
  coversDom c ∧
  (∀ s ∈ c.segs, segBound f s) ∧
  (∀ s ∈ c.segs, lo ≤ f s.cell.anchor - s.lip * s.cell.eta ∧
                  f s.cell.anchor + s.lip * s.cell.eta ≤ hi)

/-- **第 58 针·健全性**：证书被接受 ⇒ 指定域内每点的真实输出落在声明区间内
    （传播误差界成立）。证明纯由覆盖与逐段带拼接，无整域假设。 -/
theorem etaCert_sound {f : ℚ × ℚ → ℚ} {c : EtaCert} {lo hi : ℚ}
    (hacc : etaCertAccepted f c lo hi) :
    ∀ p ∈ c.dom, lo ≤ f p ∧ f p ≤ hi := by
  intro p hp
  obtain ⟨_, hcov, hsegs, hband⟩ := hacc
  obtain ⟨s, hs, hball⟩ := hcov p hp
  obtain ⟨hbl, hbr⟩ := hband s hs
  obtain ⟨hseg1, hseg2⟩ := hsegs s hs |>.2.2 p hball
  exact ⟨le_trans hbl hseg1, le_trans hseg2 hbr⟩

/-- **第 58 针·hstab 纪律（推导侧）**：XU 一般式的 `hstab` 形状——限定在指定域
    上——由逐段证书**推导**，不假设：域内每点落在某段胞腔内且带界成立。 -/
theorem designated_hstab_from_segs (f : ℚ × ℚ → ℚ) (c : EtaCert)
    (hsegs : ∀ s ∈ c.segs, segBound f s) (hcov : coversDom c)
    (p : ℚ × ℚ) (hp : p ∈ c.dom) :
    ∃ s ∈ c.segs, withinBall s.cell.eta p s.cell.anchor ∧
      f s.cell.anchor - s.lip * s.cell.eta ≤ f p ∧
      f p ≤ f s.cell.anchor + s.lip * s.cell.eta := by
  obtain ⟨s, hs, hball⟩ := hcov p hp
  exact ⟨s, hs, hball, (hsegs s hs).2.2 p hball⟩

/-- 段表的坐标包络（构造非覆盖见证用）。 -/
def coordBound : List SegEntry → ℚ
  | [] => 0
  | s :: rest => max (s.cell.anchor.1 + s.cell.eta) (coordBound rest)

theorem le_coordBound : ∀ (segs : List SegEntry) (s : SegEntry), s ∈ segs →
    s.cell.anchor.1 + s.cell.eta ≤ coordBound segs := by
  intro segs s hs
  induction segs with
  | nil => cases hs
  | cons t rest ih =>
    rcases List.mem_cons.mp hs with heq | hm
    · subst heq
      simp only [coordBound]
      exact le_max_left _ _
    · simp only [coordBound]
      exact le_trans (ih hm) (le_max_right _ _)

/-- **第 58 针·hstab 纪律（不覆盖侧）**：有限段表**永不**覆盖全空间——任取有限
    胞腔表，存在点不在任何胞腔内。所以"整域 hstab"不可能由有限逐段证书替身
    供给：整域稳定要么如实留作显式假设（XU 原样），要么把指定域声明为有限
    点表由本件格式承载。 -/
theorem finite_segs_never_cover_whole_space (segs : List SegEntry) :
    ∃ x : ℚ × ℚ, ∀ s ∈ segs, ¬ withinBall s.cell.eta x s.cell.anchor := by
  refine ⟨(coordBound segs + 1, 0), ?_⟩
  intro s hs hball
  have h1 : s.cell.anchor.1 + s.cell.eta ≤ coordBound segs := le_coordBound segs s hs
  have h2 : (coordBound segs + 1, 0).1 - s.cell.anchor.1 ≤ s.cell.eta := hball.2.1
  have hx1 : (coordBound segs + 1, 0).1 = coordBound segs + 1 := rfl
  linarith

/-! ### 供给侧实际构造：逐段线性有限网络 -/

/-- 有限网络的段（逐边数据）：区间 [lo, hi] 上斜率 m、在 lo 处取值 v。 -/
structure Seg1 where
  lo : ℚ
  hi : ℚ
  m : ℚ
  v : ℚ

/-- 段命中判定（数据级）。 -/
def inSeg (s : Seg1) (q : ℚ) : Bool := decide (s.lo ≤ q) && decide (q ≤ s.hi)

/-- 段表两两不交：同一坐标至多被一段命中（构造定理的显式前提）。 -/
def SegsDisjoint (segs : List Seg1) : Prop :=
  ∀ s t q, s ∈ segs → t ∈ segs → inSeg s q = true → inSeg t q = true → s = t

/-- 有限逐段线性网络：查点所在段，段内仿射式求值；域外未命中 fail-closed 读 0
    （不参与指定域内传播）。段数任意（有限），逐段斜率由表内数据给出。 -/
def pwlNet (segs : List Seg1) (q : ℚ) : ℚ :=
  match segs.find? (fun s => inSeg s q) with
  | some s => s.v + s.m * (q - s.lo)
  | none => 0

/-- **构造函数**：由两通道的一段数据算出胞腔（锚＝区间中点、半径＝半宽的
    较小者）与局部常数（两段斜率绝对值之和）——逐段计算，不假设整域稳定。 -/
def mkCellSeg (s₁ s₂ : Seg1) : SegEntry :=
  { cell := { anchor := ((s₁.lo + s₁.hi) / 2, (s₂.lo + s₂.hi) / 2)
              eta := min ((s₁.hi - s₁.lo) / 2) ((s₂.hi - s₂.lo) / 2) }
    lip := abs s₁.m + abs s₂.m }

/-- **第 58 针·供给侧实际构造**：对两通道各取一段（逐边数据），构造出的段条目
    **满足**其逐段验证条件——每段界是被证明的，不是假设的；局部常数由数据
    算出。这是"构造函数返回证书＋每段界的验证条件"的成对收口。 -/
theorem mkCellSeg_segBound (S₁ S₂ : List Seg1) (s₁ s₂ : Seg1)
    (h₁ : s₁ ∈ S₁) (h₂ : s₂ ∈ S₂) (hlo₁ : s₁.lo < s₁.hi) (hlo₂ : s₂.lo < s₂.hi)
    (hd₁ : SegsDisjoint S₁) (hd₂ : SegsDisjoint S₂) :
    segBound (fun p => pwlNet S₁ p.1 + pwlNet S₂ p.2) (mkCellSeg s₁ s₂) := by
  have keyA₁ : (s₁.lo + s₁.hi) / 2 = s₁.lo + (s₁.hi - s₁.lo) / 2 := by ring
  have keyH₁ : 2 * ((s₁.hi - s₁.lo) / 2) = s₁.hi - s₁.lo := by ring
  have keyA₂ : (s₂.lo + s₂.hi) / 2 = s₂.lo + (s₂.hi - s₂.lo) / 2 := by ring
  have keyH₂ : 2 * ((s₂.hi - s₂.lo) / 2) = s₂.hi - s₂.lo := by ring
  have hEt : (mkCellSeg s₁ s₂).cell.eta =
      min ((s₁.hi - s₁.lo) / 2) ((s₂.hi - s₂.lo) / 2) := rfl
  have hLp : (mkCellSeg s₁ s₂).lip = abs s₁.m + abs s₂.m := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hEt]
    exact le_min (by linarith) (by linarith)
  · rw [hLp]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro x hx
    have hx' : withinBall (min ((s₁.hi - s₁.lo) / 2) ((s₂.hi - s₂.lo) / 2)) x
        ((s₁.lo + s₁.hi) / 2, (s₂.lo + s₂.hi) / 2) := hx
    obtain ⟨hx1, hx2, hx3, hx4⟩ := hx'
    have hA₁ : ((s₁.lo + s₁.hi) / 2, (s₂.lo + s₂.hi) / 2).1 = (s₁.lo + s₁.hi) / 2 := rfl
    have hA₂ : ((s₁.lo + s₁.hi) / 2, (s₂.lo + s₂.hi) / 2).2 = (s₂.lo + s₂.hi) / 2 := rfl
    have hE₁ : min ((s₁.hi - s₁.lo) / 2) ((s₂.hi - s₂.lo) / 2) ≤ (s₁.hi - s₁.lo) / 2 :=
      min_le_left _ _
    have hE₂ : min ((s₁.hi - s₁.lo) / 2) ((s₂.hi - s₂.lo) / 2) ≤ (s₂.hi - s₂.lo) / 2 :=
      min_le_right _ _
    have hx1lo : s₁.lo ≤ x.1 := by linarith
    have hx1hi : x.1 ≤ s₁.hi := by linarith
    have hx2lo : s₂.lo ≤ x.2 := by linarith
    have hx2hi : x.2 ≤ s₂.hi := by linarith
    have hinx1 : inSeg s₁ x.1 = true := by
      simp only [inSeg, Bool.and_eq_true, decide_eq_true_iff]
      exact ⟨hx1lo, hx1hi⟩
    have hinx2 : inSeg s₂ x.2 = true := by
      simp only [inSeg, Bool.and_eq_true, decide_eq_true_iff]
      exact ⟨hx2lo, hx2hi⟩
    have hina1 : inSeg s₁ ((s₁.lo + s₁.hi) / 2) = true := by
      simp only [inSeg, Bool.and_eq_true, decide_eq_true_iff]
      exact ⟨by linarith, by linarith⟩
    have hina2 : inSeg s₂ ((s₂.lo + s₂.hi) / 2) = true := by
      simp only [inSeg, Bool.and_eq_true, decide_eq_true_iff]
      exact ⟨by linarith, by linarith⟩
    have hfindx1 : S₁.find? (fun s => inSeg s x.1) = some s₁ :=
      find?_eq_some_of_unique (fun s => inSeg s x.1) S₁ s₁ h₁ hinx1
        (fun u hu hpu => hd₁ u s₁ x.1 hu h₁ hpu hinx1)
    have hfindx2 : S₂.find? (fun s => inSeg s x.2) = some s₂ :=
      find?_eq_some_of_unique (fun s => inSeg s x.2) S₂ s₂ h₂ hinx2
        (fun u hu hpu => hd₂ u s₂ x.2 hu h₂ hpu hinx2)
    have hfinda1 : S₁.find? (fun s => inSeg s ((s₁.lo + s₁.hi) / 2)) = some s₁ :=
      find?_eq_some_of_unique (fun s => inSeg s ((s₁.lo + s₁.hi) / 2)) S₁ s₁ h₁ hina1
        (fun u hu hpu => hd₁ u s₁ ((s₁.lo + s₁.hi) / 2) hu h₁ hpu hina1)
    have hfinda2 : S₂.find? (fun s => inSeg s ((s₂.lo + s₂.hi) / 2)) = some s₂ :=
      find?_eq_some_of_unique (fun s => inSeg s ((s₂.lo + s₂.hi) / 2)) S₂ s₂ h₂ hina2
        (fun u hu hpu => hd₂ u s₂ ((s₂.lo + s₂.hi) / 2) hu h₂ hpu hina2)
    have hnetx1 : pwlNet S₁ x.1 = s₁.v + s₁.m * (x.1 - s₁.lo) := by
      simp only [pwlNet, hfindx1]
    have hnetx2 : pwlNet S₂ x.2 = s₂.v + s₂.m * (x.2 - s₂.lo) := by
      simp only [pwlNet, hfindx2]
    have hnetA1 : pwlNet S₁ ((s₁.lo + s₁.hi) / 2) =
        s₁.v + s₁.m * ((s₁.lo + s₁.hi) / 2 - s₁.lo) := by
      simp only [pwlNet, hfinda1]
    have hnetA2 : pwlNet S₂ ((s₂.lo + s₂.hi) / 2) =
        s₂.v + s₂.m * ((s₂.lo + s₂.hi) / 2 - s₂.lo) := by
      simp only [pwlNet, hfinda2]
    have hδ : pwlNet S₁ x.1 + pwlNet S₂ x.2 -
        (pwlNet S₁ ((s₁.lo + s₁.hi) / 2) + pwlNet S₂ ((s₂.lo + s₂.hi) / 2)) =
        s₁.m * (x.1 - (s₁.lo + s₁.hi) / 2) + s₂.m * (x.2 - (s₂.lo + s₂.hi) / 2) := by
      rw [hnetx1, hnetx2, hnetA1, hnetA2]
      ring
    have ha₁ : abs (s₁.m * (x.1 - (s₁.lo + s₁.hi) / 2)) ≤
        abs s₁.m * min ((s₁.hi - s₁.lo) / 2) ((s₂.hi - s₂.lo) / 2) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hx1, hx2⟩) (abs_nonneg _)
    have ha₂ : abs (s₂.m * (x.2 - (s₂.lo + s₂.hi) / 2)) ≤
        abs s₂.m * min ((s₁.hi - s₁.lo) / 2) ((s₂.hi - s₂.lo) / 2) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hx3, hx4⟩) (abs_nonneg _)
    have hsum : abs (s₁.m * (x.1 - (s₁.lo + s₁.hi) / 2) +
        s₂.m * (x.2 - (s₂.lo + s₂.hi) / 2)) ≤
        (abs s₁.m + abs s₂.m) * min ((s₁.hi - s₁.lo) / 2) ((s₂.hi - s₂.lo) / 2) := by
      have hab := abs_add_le (s₁.m * (x.1 - (s₁.lo + s₁.hi) / 2))
        (s₂.m * (x.2 - (s₂.lo + s₂.hi) / 2))
      have hsplit := mul_add (abs s₁.m) (abs s₂.m)
        (min ((s₁.hi - s₁.lo) / 2) ((s₂.hi - s₂.lo) / 2))
      linarith
    have hbandabs := hsum
    rw [abs_le] at hbandabs
    show pwlNet S₁ ((s₁.lo + s₁.hi) / 2) + pwlNet S₂ ((s₂.lo + s₂.hi) / 2) -
          (abs s₁.m + abs s₂.m) * min ((s₁.hi - s₁.lo) / 2) ((s₂.hi - s₂.lo) / 2) ≤
        pwlNet S₁ x.1 + pwlNet S₂ x.2 ∧
      pwlNet S₁ x.1 + pwlNet S₂ x.2 ≤
        pwlNet S₁ ((s₁.lo + s₁.hi) / 2) + pwlNet S₂ ((s₂.lo + s₂.hi) / 2) +
          (abs s₁.m + abs s₂.m) * min ((s₁.hi - s₁.lo) / 2) ((s₂.hi - s₂.lo) / 2)
    exact ⟨by linarith [hδ, hbandabs.1], by linarith [hδ, hbandabs.2]⟩

/-- **全网证书构造**：配对表 → 逐段界表；验证位与段等长、全真；指定域点表
    原样进证书域描述。逐段界由 `mkCellSeg` 从两通道逐段数据算出。 -/
def buildEtaCert (pairing : List (Seg1 × Seg1)) (dom : List (ℚ × ℚ)) : EtaCert :=
  { dom := dom
    segs := pairing.map (fun pr => mkCellSeg pr.1 pr.2)
    bits := List.replicate pairing.length true }

/-- **全网构造**：对配对表中每对段应用构造函数——有限一般网络的所有逐段
    界一次收齐。 -/
theorem buildEtaCert_all_segBound (S₁ S₂ : List Seg1) (pairing : List (Seg1 × Seg1))
    (dom : List (ℚ × ℚ))
    (hwidth : ∀ pr ∈ pairing, pr.1.lo < pr.1.hi ∧ pr.2.lo < pr.2.hi)
    (hmem : ∀ pr ∈ pairing, pr.1 ∈ S₁ ∧ pr.2 ∈ S₂)
    (hd₁ : SegsDisjoint S₁) (hd₂ : SegsDisjoint S₂) :
    ∀ s ∈ (buildEtaCert pairing dom).segs,
      segBound (fun p => pwlNet S₁ p.1 + pwlNet S₂ p.2) s := by
  intro s hs
  simp only [buildEtaCert] at hs
  obtain ⟨pr, hpr, heq⟩ := List.mem_map.mp hs
  subst heq
  exact mkCellSeg_segBound S₁ S₂ pr.1 pr.2 (hmem pr hpr).1 (hmem pr hpr).2
    (hwidth pr hpr).1 (hwidth pr hpr).2 hd₁ hd₂

/-- 构造出的证书通过数据级预检（位长一致、位全真）。 -/
theorem buildEtaCert_precheck (pairing : List (Seg1 × Seg1)) (dom : List (ℚ × ℚ)) :
    certPrecheckOk (buildEtaCert pairing dom) = true := by
  have hlen : (buildEtaCert pairing dom).bits.length =
      (buildEtaCert pairing dom).segs.length := by
    simp only [buildEtaCert, List.length_map, List.length_replicate]
  have hall : ((buildEtaCert pairing dom).bits.all fun b => b) = true := by
    rw [List.all_eq_true]
    intro b hb
    have hbr : b ∈ List.replicate pairing.length true := hb
    exact List.mem_replicate.mp hbr |>.2
  have hbeq : ((buildEtaCert pairing dom).bits.length ==
      (buildEtaCert pairing dom).segs.length) = true := by
    rw [hlen]
    exact beq_self_eq_true _
  simp only [certPrecheckOk]
  rw [hbeq, Bool.true_and, hall]

/-- 逐点胞腔判定：点坐标到两段中点的距离都不超过半径（半宽较小者）⇒ 该点
    在构造出的胞腔内——哪些域点可被覆盖的具名判定。 -/
theorem inCell_of_coord_le (s₁ s₂ : Seg1) (p : ℚ × ℚ)
    (h1 : |p.1 - (s₁.lo + s₁.hi) / 2| ≤ min ((s₁.hi - s₁.lo) / 2) ((s₂.hi - s₂.lo) / 2))
    (h2 : |p.2 - (s₂.lo + s₂.hi) / 2| ≤ min ((s₁.hi - s₁.lo) / 2) ((s₂.hi - s₂.lo) / 2)) :
    withinBall (mkCellSeg s₁ s₂).cell.eta p (mkCellSeg s₁ s₂).cell.anchor :=
  ⟨(abs_le.mp h1).1, (abs_le.mp h1).2, (abs_le.mp h2).1, (abs_le.mp h2).2⟩

/-- 构造出的证书覆盖指定域：域表每点已落在某配对段的胞腔内（具名判定见
    `inCell_of_coord_le`）⇒ `coversDom` 成立——判定结果接进证书格式。 -/
theorem buildEtaCert_coversDom (pairing : List (Seg1 × Seg1)) (dom : List (ℚ × ℚ))
    (hcover : ∀ p ∈ dom, ∃ pr ∈ pairing,
      withinBall (mkCellSeg pr.1 pr.2).cell.eta p (mkCellSeg pr.1 pr.2).cell.anchor) :
    coversDom (buildEtaCert pairing dom) := by
  intro p hp
  obtain ⟨pr, hpr, hball⟩ := hcover p hp
  exact ⟨mkCellSeg pr.1 pr.2, List.mem_map.mpr ⟨pr, hpr, rfl⟩, hball⟩

/-- **第 58 针·构造的证书被接受**：预检＋覆盖＋全网逐段界＋每段带包住 ⇒
    `etaCertAccepted`。逐段带（`hband`）以段条目层面给出，健全性定理把它们
    拼成指定域内的传播界。 -/
theorem buildEtaCert_accepted (S₁ S₂ : List Seg1) (pairing : List (Seg1 × Seg1))
    (dom : List (ℚ × ℚ)) (lo hi : ℚ)
    (hwidth : ∀ pr ∈ pairing, pr.1.lo < pr.1.hi ∧ pr.2.lo < pr.2.hi)
    (hmem : ∀ pr ∈ pairing, pr.1 ∈ S₁ ∧ pr.2 ∈ S₂)
    (hd₁ : SegsDisjoint S₁) (hd₂ : SegsDisjoint S₂)
    (hcover : ∀ p ∈ dom, ∃ pr ∈ pairing,
      withinBall (mkCellSeg pr.1 pr.2).cell.eta p (mkCellSeg pr.1 pr.2).cell.anchor)
    (hband : ∀ s ∈ (buildEtaCert pairing dom).segs,
      lo ≤ (fun p => pwlNet S₁ p.1 + pwlNet S₂ p.2) s.cell.anchor -
            s.lip * s.cell.eta ∧
        (fun p => pwlNet S₁ p.1 + pwlNet S₂ p.2) s.cell.anchor +
            s.lip * s.cell.eta ≤ hi) :
    etaCertAccepted (fun p => pwlNet S₁ p.1 + pwlNet S₂ p.2)
      (buildEtaCert pairing dom) lo hi :=
  ⟨buildEtaCert_precheck pairing dom,
    buildEtaCert_coversDom pairing dom hcover,
    buildEtaCert_all_segBound S₁ S₂ pairing dom hwidth hmem hd₁ hd₂,
    hband⟩

/-! ### 与 UnifiedNeedlesXU 既有消费面的适配（不改 XU 文件本身） -/

/-- **适配①（NN 区间证书消费面）**：单段证书喂给 XU 一般式
    `nn_interval_certificate_sound` 的 `hstab` 形状——该一般式不再需要假设整域
    稳定，其前提由本件逐段界供给。 -/
theorem xu_nn_propagation_of_single_cell (f : ℚ × ℚ → ℚ) (s : SegEntry) (lo hi : ℚ)
    (hs : segBound f s)
    (hband : lo ≤ f s.cell.anchor - s.lip * s.cell.eta ∧
             f s.cell.anchor + s.lip * s.cell.eta ≤ hi)
    (dom : List (ℚ × ℚ))
    (hcov : ∀ p ∈ dom, withinBall s.cell.eta p s.cell.anchor)
    (p : ℚ × ℚ) (hp : p ∈ dom) :
    lo ≤ f p ∧ f p ≤ hi := by
  have hgen := JurisLean.Seams.UnifiedNeedlesXU.nn_interval_certificate_sound f
    s.cell.anchor s.cell.eta s.lip lo hi hs.1 hs.2.1 hs.2.2 hband
  exact hgen.2 p (hcov p hp)

/-- **适配②（观测歧义消费面）**：可靠区间生产者由证书健全性实例化——
    指定域内两点若目标值不同，声明区间不可能收成单点（实例化 XU 第 59 针的
    一般机制，XU 文件一字未改）。 -/
theorem xu_ambiguity_nonsingleton_of_cert (f : ℚ × ℚ → ℚ) (c : EtaCert) (lo hi : ℚ)
    (hacc : etaCertAccepted f c lo hi)
    (x y : {p : ℚ × ℚ // p ∈ c.dom}) (hne : f x.val ≠ f y.val) :
    lo < hi := by
  have hrel : ∀ m : {p : ℚ × ℚ // p ∈ c.dom}, (lo, hi).1 ≤ f m.val ∧ f m.val ≤ (lo, hi).2 :=
    fun m => etaCert_sound hacc m.val m.property
  exact JurisLean.Seams.UnifiedNeedlesXU.observational_ambiguity_preserved
    (fun _ : {p : ℚ × ℚ // p ∈ c.dom} => ())
    (fun m : {p : ℚ × ℚ // p ∈ c.dom} => f m.val) (fun _ => (lo, hi)) hrel x y rfl hne

/-- **适配③（证书格式对接）**：以 `Mandate/ReLUApprox.out` 为目标函数的段条目
    一经锚点对齐且局部常数取 `ReLUApprox.lip`，即产出 XU 面 `RadiusCert` 并过
    其接受判据 `admitsRadiusCert`；且胞腔球内真实输出确落在证书声明的区间内
    （`hcell` 保证证书锚与段锚一致， soundness 由逐段界承接）——本件证书格式
    与 XU 既有证书面互联。 -/
theorem xu_admitsRadiusCert_of_segBound (s : SegEntry) (anchor : ℚ × ℚ)
    (hs : segBound JurisLean.Mandate.ReLUApprox.out s)
    (hcell : s.cell.anchor = anchor)
    (hlip : s.lip = JurisLean.Mandate.ReLUApprox.lip) :
    JurisLean.Seams.Uncertainty.admitsRadiusCert anchor
      { E := s.cell.eta
        lo := JurisLean.Mandate.ReLUApprox.out anchor - s.lip * s.cell.eta
        hi := JurisLean.Mandate.ReLUApprox.out anchor + s.lip * s.cell.eta } ∧
      ∀ x : ℚ × ℚ, withinBall s.cell.eta x anchor →
        JurisLean.Mandate.ReLUApprox.out anchor - s.lip * s.cell.eta ≤
            JurisLean.Mandate.ReLUApprox.out x ∧
          JurisLean.Mandate.ReLUApprox.out x ≤
            JurisLean.Mandate.ReLUApprox.out anchor + s.lip * s.cell.eta := by
  refine ⟨⟨hs.1, ?_, ?_⟩, ?_⟩
  · rw [hlip]
  · rw [hlip]
  · intro x hx
    rw [← hcell] at hx ⊢
    exact hs.2.2 x hx

end JurisLean.Seams.UnifiedNeedlesGapLate
