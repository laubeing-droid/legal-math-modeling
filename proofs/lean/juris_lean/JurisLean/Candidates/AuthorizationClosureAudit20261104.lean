import JurisLean.Candidates.U10_1RefreshRuleProtocol20261030
import JurisLean.Candidates.Final20261021.Acceptance

/-!
新增义务只对应冻结10.1 L101/L103/L105：四种完整绑定删除反例、实际授权三阶段、
有外部可信根且逐边范围/时间可核验的委托图、旧授权证据的精确复用条件。
覆盖与验收以独立CI和权威原题台账的绑定为准；本文件不自行改账。
根信任和真实发出委托的关系是独立外部输入，不由Nat seed、程序检查或经验标记生成。
现有Authorization/Compiler/Pipeline与已关闭U10.1刷新续行证明保持原样复用。
-/
namespace JurisLean.Candidates.AuthorizationClosureAudit20261104

open JurisLean.Candidates.Final20261021

/-- 完整的实际checkGrant请求；身份、对象、目标版本和当前Gamma分列。 -/
structure Query where
  gamma : Gamma
  subject : PartyId
  action : Nat
  version : Nat
  object : ObjectId
  payload : Option PaymentPayload
  nextContext : Option Gamma
  deriving DecidableEq

def check (q : Query) (a : Authorization.Grant) : Bool :=
  Authorization.checkGrant q.gamma q.subject q.action q.version q.object
    q.payload q.nextContext a

def permits (catalog : List Authorization.Grant) (q : Query) : Bool :=
  Authorization.authorized catalog q.gamma q.subject q.action q.version q.object
    q.payload q.nextContext

theorem permits_exact_current_witness (catalog : List Authorization.Grant) (q : Query) :
    permits catalog q = true ↔ ∃ a ∈ catalog, check q a = true := by
  exact List.any_eq_true

theorem check_full_bindings (q : Query) (a : Authorization.Grant) (h : check q a = true) :
    a.subject = q.subject ∧ a.caseId = q.gamma.caseId ∧ a.action = q.action ∧
    a.context = q.gamma ∧ a.object = q.object ∧ a.payload = q.payload ∧
    a.nextContext = q.nextContext ∧ a.contentVersion = q.version ∧
    a.authorityRuleVersion = q.gamma.normVersion ∧
    a.fromDate.ordinal ≤ q.gamma.lawDate.ordinal ∧
    q.gamma.lawDate.ordinal < a.untilDate.ordinal := by
  simpa only [check, Authorization.checkGrant, decide_eq_true_eq] using h

inductive Erasure where
  | object | subject | version | time
  deriving DecidableEq

/-- 反事实弱化器，不改实际checker。时间信息在完整Gamma和有效期中都有出现。 -/
def eraseGrant (erased : Erasure) (q : Query) (a : Authorization.Grant) : Authorization.Grant :=
  match erased with
  | .object => { a with object := q.object }
  | .subject => { a with subject := q.subject }
  | .version => { a with contentVersion := q.version }
  | .time =>
      { a with
        context := { a.context with lawDate := q.gamma.lawDate }
        fromDate := q.gamma.lawDate
        untilDate := ⟨q.gamma.lawDate.ordinal + 1⟩ }

def weakCheck (erased : Erasure) (q : Query) (a : Authorization.Grant) : Bool :=
  check q (eraseGrant erased q a)

def baseGamma : Gamma :=
  { Acceptance.gamma with lawDate := ⟨5⟩, normVersion := 0 }

def baseQuery : Query := ⟨baseGamma, ⟨1⟩, 1, 7, .document 10, none, none⟩

def grantFor (q : Query) : Authorization.Grant :=
  ⟨⟨100⟩, q.subject, q.gamma.caseId, q.gamma, q.object, q.action, q.version,
    q.payload, q.nextContext, q.gamma.normVersion, ⟨0⟩, ⟨10⟩⟩

def baseGrant : Authorization.Grant := grantFor baseQuery

def wrongObject : Query := { baseQuery with object := .document 11 }
def wrongSubject : Query := { baseQuery with subject := ⟨2⟩ }
def wrongVersion : Query := { baseQuery with version := 8 }
def wrongTime : Query :=
  { baseQuery with gamma := { baseGamma with lawDate := ⟨15⟩ } }

theorem four_binding_erasure_witnesses :
    check baseQuery baseGrant = true ∧
    weakCheck .object wrongObject baseGrant = true ∧ check wrongObject baseGrant = false ∧
    weakCheck .subject wrongSubject baseGrant = true ∧ check wrongSubject baseGrant = false ∧
    weakCheck .version wrongVersion baseGrant = true ∧ check wrongVersion baseGrant = false ∧
    weakCheck .time wrongTime baseGrant = true ∧ check wrongTime baseGrant = false ∧
    baseGrant.object ≠ wrongObject.object ∧ baseGrant.subject ≠ wrongSubject.subject ∧
    baseGrant.contentVersion ≠ wrongVersion.version ∧
    ¬ wrongTime.gamma.lawDate.ordinal < baseGrant.untilDate.ordinal := by
  decide +kernel

/-- 单删窗口约束仍有Gamma中的日期绑定；不把冗余绑定误报为单点漏洞。 -/
theorem time_binding_also_occurs_in_full_context :
    check wrongTime
      { baseGrant with
        fromDate := wrongTime.gamma.lawDate
        untilDate := ⟨wrongTime.gamma.lawDate.ordinal + 1⟩ } = false := by
  decide +kernel

/-- 每个反例只需恢复此处指出的一个实际约束就能排除；其余绑定仍完整保留。 -/
theorem explicit_binding_blockers (q : Query) (a : Authorization.Grant) :
    (a.object ≠ q.object → check q a = false) ∧
    (a.subject ≠ q.subject → check q a = false) ∧
    (a.contentVersion ≠ q.version → check q a = false) ∧
    (¬ (a.fromDate.ordinal ≤ q.gamma.lawDate.ordinal ∧
        q.gamma.lawDate.ordinal < a.untilDate.ordinal) → check q a = false) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    simp [check, Authorization.checkGrant, h]
  · intro h
    simp [check, Authorization.checkGrant, h]
  · intro h
    simp [check, Authorization.checkGrant, h]
  · intro h
    by_cases hlo : a.fromDate.ordinal ≤ q.gamma.lawDate.ordinal
    · have hhi : ¬ q.gamma.lawDate.ordinal < a.untilDate.ordinal := fun hh => h ⟨hlo, hh⟩
      simp [check, Authorization.checkGrant, hhi]
    · simp [check, Authorization.checkGrant, hlo]

/-- 经验改善和finalize标记是草案字段；实际更新入口仍为Pipeline.refresh。 -/
structure Draft where
  change : Pipeline.RefreshInput
  improved : Bool
  finalized : Bool
  deriving DecidableEq

def submitDraft (catalog : List Authorization.Grant) (before : Ledger.Handle)
    (d : Draft) : Result Ledger.Handle := Pipeline.refresh catalog before d.change

def Granted (catalog : List Authorization.Grant) (before : Ledger.Handle) (d : Draft) : Prop :=
  d.change.gamma.caseId = before.gamma.caseId ∧
  Authorization.authorized catalog before.gamma d.change.actor 1 d.change.event.version
    (.document d.change.event.version) none (some d.change.gamma) = true

def Usable (catalog : List Authorization.Grant) (before : Ledger.Handle) (d : Draft) : Prop :=
  ∃ after, submitDraft catalog before d = .known after ∧
    after.state.env = .known after.gamma.normVersion

theorem actual_refresh_requires_old_authority
    (catalog : List Authorization.Grant) (before after : Ledger.Handle) (d : Draft)
    (h : submitDraft catalog before d = .known after) :
    Granted catalog before d ∧ after.gamma = d.change.gamma ∧
    after.state.normHistory = before.state.normHistory ++ [d.change.event] ∧
    after.state.env = Temporal.proposed_applicability d.change.gamma
      (before.state.normHistory ++ [d.change.event]) := by
  unfold submitDraft Pipeline.refresh at h
  split at h
  · cases h
  · rename_i hcase
    split at h
    · cases h
    · rename_i hauth
      cases h
      refine ⟨⟨?_, ?_⟩, rfl, rfl, rfl⟩
      · simpa using hcase
      · cases hv : Authorization.authorized catalog before.gamma d.change.actor 1
          d.change.event.version (.document d.change.event.version) none (some d.change.gamma)
          <;> simp_all

theorem usable_requires_granted (catalog : List Authorization.Grant)
    (before : Ledger.Handle) (d : Draft) (h : Usable catalog before d) :
    Granted catalog before d := by
  obtain ⟨after, ha, _⟩ := h
  exact (actual_refresh_requires_old_authority catalog before after d ha).1

theorem draft_markers_do_not_authorize
    (before : Ledger.Handle) (change : Pipeline.RefreshInput)
    (hcase : change.gamma.caseId = before.gamma.caseId) :
    submitDraft [] before ⟨change, true, true⟩ = .unknown .authorityUnresolved ∧
    ¬ Usable [] before ⟨change, true, true⟩ ∧
    submitDraft [] before ⟨change, false, false⟩ =
      submitDraft [] before ⟨change, true, true⟩ := by
  have he : submitDraft [] before ⟨change, true, true⟩ = .unknown .authorityUnresolved := by
    simp [submitDraft, Pipeline.refresh, Authorization.authorized, hcase]
  refine ⟨he, ?_, rfl⟩
  rintro ⟨after, h, _⟩
  rw [he] at h
  cases h

/-- 对当前事实可用授权的证据分支逐一保留；冲突不选择、投票或补成肯定。 -/
def refreshWithEvidence (evidence : Result (List Authorization.Grant))
    (before : Ledger.Handle) (d : Draft) : Result Ledger.Handle :=
  match evidence with
  | .known catalog => submitDraft catalog before d
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict left right => .conflict left right

theorem unavailable_or_conflicting_evidence_never_enables
    (before : Ledger.Handle) (d : Draft) (why : Error)
    (left right : Nat) (after : Ledger.Handle) :
    refreshWithEvidence (.unknown why) before d ≠ .known after ∧
    refreshWithEvidence (.conflict left right) before d ≠ .known after := by
  constructor <;> intro h <;> cases h

def reusable (catalog : List Authorization.Grant) (q : Query) (a : Authorization.Grant) : Prop :=
  a ∈ catalog ∧ check q a = true

theorem evidence_reuse_exact_current_condition
    (current : List Authorization.Grant) (oldQuery nowQuery : Query)
    (a : Authorization.Grant) (historical : check oldQuery a = true) :
    check oldQuery a = true ∧
    (reusable current nowQuery a ↔ a ∈ current ∧
      (a.subject = nowQuery.subject ∧ a.caseId = nowQuery.gamma.caseId ∧
      a.action = nowQuery.action ∧ a.context = nowQuery.gamma ∧ a.object = nowQuery.object ∧
      a.payload = nowQuery.payload ∧ a.nextContext = nowQuery.nextContext ∧
      a.contentVersion = nowQuery.version ∧
      a.authorityRuleVersion = nowQuery.gamma.normVersion ∧
      a.fromDate.ordinal ≤ nowQuery.gamma.lawDate.ordinal ∧
      nowQuery.gamma.lawDate.ordinal < a.untilDate.ordinal)) := by
  refine ⟨historical, ?_⟩
  simp only [reusable, check, Authorization.checkGrant, decide_eq_true_eq]

theorem catalog_restriction_is_monotone (old current : List Authorization.Grant)
    (restricted : ∀ a ∈ current, a ∈ old) (q : Query)
    (h : permits current q = true) : permits old q = true := by
  obtain ⟨a, ha, hc⟩ := (permits_exact_current_witness current q).mp h
  exact (permits_exact_current_witness old q).mpr ⟨a, restricted a ha, hc⟩

theorem historical_validity_is_not_current_authority :
    permits [baseGrant] baseQuery = true ∧ permits [] baseQuery = false ∧
    check baseQuery baseGrant = true ∧ check wrongTime baseGrant = false := by
  decide +kernel

/-- 一个有限委托图节点携带实际Grant。delegable表示证据明示可再委托此能力，
不从单纯“获准使用”推成可再授权。 -/
structure AuthorityNode where
  grant : Authorization.Grant
  delegable : Bool
  deriving DecidableEq

/-- 节点是具体许可，范围按实际对象/动作/版本/payload/context逐项比较，
不是把不同权力换算成同一个数值分数。主体和来源在委托边中分列，期间只可缩小。 -/
def scopeCovers (parent child : AuthorityNode) : Bool :=
  decide (parent.grant.caseId = child.grant.caseId ∧
    parent.grant.context = child.grant.context ∧ parent.grant.object = child.grant.object ∧
    parent.grant.action = child.grant.action ∧
    parent.grant.contentVersion = child.grant.contentVersion ∧
    parent.grant.payload = child.grant.payload ∧ parent.grant.nextContext = child.grant.nextContext ∧
    parent.grant.authorityRuleVersion = child.grant.authorityRuleVersion ∧
    parent.grant.fromDate.ordinal ≤ child.grant.fromDate.ordinal ∧
    child.grant.untilDate.ordinal ≤ parent.grant.untilDate.ordinal)

def nodeActive (g : Gamma) (n : AuthorityNode) : Bool :=
  Authorization.checkGrant g n.grant.subject n.grant.action n.grant.contentVersion
    n.grant.object n.grant.payload n.grant.nextContext n.grant

structure Delegation where
  parent : Nat
  child : Nat
  evidence : SourceRef
  deriving DecidableEq

/-- 独立提供的委托事实支持关系读完整节点，包含双方身份、范围、来源及可再委托位。
它只表示该来源支持这次委托事实，不把合法授权结论塞作输入。 -/
abbrev Issued := SourceRef → AuthorityNode → AuthorityNode → Bool

structure TrustedSeeds (node : Nat → AuthorityNode) (trusted : AuthorityNode → Prop) where
  ids : List Nat
  externalTrust : ∀ i ∈ ids, trusted (node i)

def activeRoots {trusted : AuthorityNode → Prop} (g : Gamma) (node : Nat → AuthorityNode)
    (roots : TrustedSeeds node trusted) : List Nat := roots.ids.filter (fun i => nodeActive g (node i))

def admitted (g : Gamma) (node : Nat → AuthorityNode) (issued : Issued) (e : Delegation) : Bool :=
  (node e.parent).delegable && issued e.evidence (node e.parent) (node e.child) &&
    scopeCovers (node e.parent) (node e.child) && nodeActive g (node e.parent) &&
    nodeActive g (node e.child)

def edgeRule (e : Delegation) : Compiler.Rule Nat := ⟨[e.parent], e.child⟩

def delegationRules (g : Gamma) (node : Nat → AuthorityNode) (issued : Issued)
    (edges : List Delegation) : List (Compiler.Rule Nat) :=
  (edges.filter (admitted g node issued)).map edgeRule

def computedPermissions {trusted : AuthorityNode → Prop}
    (g : Gamma) (node : Nat → AuthorityNode) (issued : Issued)
    (roots : TrustedSeeds node trusted) (edges : List Delegation) (fuel : Nat) : List Nat :=
  Authorization.rootedPermissions (activeRoots g node roots) (delegationRules g node issued edges) fuel

/-- 用已有closed检查决定是否饱和；fuel耗尽不冒充完整许可否定。 -/
def checkedPermissions {trusted : AuthorityNode → Prop}
    (g : Gamma) (node : Nat → AuthorityNode) (issued : Issued)
    (roots : TrustedSeeds node trusted) (edges : List Delegation) (fuel : Nat) : Result (List Nat) :=
  Compiler.proposed_checked_rule_input (delegationRules g node issued edges) fuel (activeRoots g node roots)

inductive Rooted (g : Gamma) (node : Nat → AuthorityNode) (issued : Issued)
    (trusted : AuthorityNode → Prop) (roots : TrustedSeeds node trusted) (edges : List Delegation) : Nat → Prop where
  | root (i : Nat) (included : i ∈ activeRoots g node roots) (externalTrust : trusted (node i)) :
      Rooted g node issued trusted roots edges i
  | delegated (e : Delegation) (included : e ∈ edges)
      (checked : admitted g node issued e = true)
      (parent : Rooted g node issued trusted roots edges e.parent) :
      Rooted g node issued trusted roots edges e.child

theorem admitted_has_real_scope_and_time (g : Gamma) (node : Nat → AuthorityNode)
    (issued : Issued) (e : Delegation) (h : admitted g node issued e = true) :
    (node e.parent).delegable = true ∧ issued e.evidence (node e.parent) (node e.child) = true ∧
    scopeCovers (node e.parent) (node e.child) = true ∧
    nodeActive g (node e.parent) = true ∧ nodeActive g (node e.child) = true := by
  simpa only [admitted, Bool.and_eq_true, and_assoc] using h

theorem scopeCovers_actual_grant_fields (parent child : AuthorityNode)
    (h : scopeCovers parent child = true) :
    parent.grant.caseId = child.grant.caseId ∧
    parent.grant.context = child.grant.context ∧ parent.grant.object = child.grant.object ∧
    parent.grant.action = child.grant.action ∧
    parent.grant.contentVersion = child.grant.contentVersion ∧
    parent.grant.payload = child.grant.payload ∧ parent.grant.nextContext = child.grant.nextContext ∧
    parent.grant.authorityRuleVersion = child.grant.authorityRuleVersion ∧
    parent.grant.fromDate.ordinal ≤ child.grant.fromDate.ordinal ∧
    child.grant.untilDate.ordinal ≤ parent.grant.untilDate.ordinal := by
  simpa only [scopeCovers, decide_eq_true_eq] using h

theorem rooted_model {trusted : AuthorityNode → Prop}
    (g : Gamma) (node : Nat → AuthorityNode) (issued : Issued)
    (roots : TrustedSeeds node trusted) (edges : List Delegation) :
    Compiler.Models (· ∈ activeRoots g node roots) (· ∈ delegationRules g node issued edges)
      (Rooted g node issued trusted roots edges) := by
  constructor
  · intro i hi
    have horiginal : i ∈ roots.ids := (List.mem_filter.mp hi).1
    exact .root i hi (roots.externalTrust i horiginal)
  · intro r hr hp
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hr
    have hs := List.mem_filter.mp he
    exact .delegated e hs.1 hs.2 (hp e.parent (by simp [edgeRule]))

theorem computed_permissions_have_grounded_derivations {trusted : AuthorityNode → Prop}
    (g : Gamma) (node : Nat → AuthorityNode) (issued : Issued)
    (roots : TrustedSeeds node trusted) (edges : List Delegation) (fuel i : Nat)
    (h : i ∈ computedPermissions g node issued roots edges fuel) :
    Rooted g node issued trusted roots edges i := by
  have hd := Compiler.u03_1_computed_sound (delegationRules g node issued edges)
    (activeRoots g node roots) fuel i h
  exact Compiler.u03_1_relative_soundness (rooted_model g node issued roots edges) hd

theorem rooted_nodes_are_active {trusted : AuthorityNode → Prop}
    {g : Gamma} {node : Nat → AuthorityNode} {issued : Issued}
    {roots : TrustedSeeds node trusted} {edges : List Delegation} {i : Nat}
    (h : Rooted g node issued trusted roots edges i) : nodeActive g (node i) = true := by
  cases h with
  | root i hi _ => exact (List.mem_filter.mp hi).2
  | delegated e _ he _ => exact (admitted_has_real_scope_and_time g node issued e he).2.2.2.2

def derivedCatalog {trusted : AuthorityNode → Prop}
    (g : Gamma) (node : Nat → AuthorityNode) (issued : Issued)
    (roots : TrustedSeeds node trusted) (edges : List Delegation) (fuel : Nat) : List Authorization.Grant :=
  (computedPermissions g node issued roots edges fuel).map (fun i => (node i).grant)

/-- 实际授权查询读的仍是同一个完整Grant，而不是仅看Nat权限token。 -/
theorem computed_authorization_has_actual_grant {trusted : AuthorityNode → Prop}
    (g : Gamma) (node : Nat → AuthorityNode) (issued : Issued)
    (roots : TrustedSeeds node trusted) (edges : List Delegation) (fuel : Nat) (q : Query)
    (h : permits (derivedCatalog g node issued roots edges fuel) q = true) :
    ∃ i ∈ computedPermissions g node issued roots edges fuel,
      Rooted g node issued trusted roots edges i ∧ check q (node i).grant = true ∧
      nodeActive g (node i) = true := by
  obtain ⟨a, ha, hcheck⟩ := (permits_exact_current_witness _ q).mp h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  have hr := computed_permissions_have_grounded_derivations g node issued roots edges fuel i hi
  exact ⟨i, hi, hr, hcheck, rooted_nodes_are_active hr⟩

theorem checked_permissions_exact_positive_semantics {trusted : AuthorityNode → Prop}
    (g : Gamma) (node : Nat → AuthorityNode) (issued : Issued)
    (roots : TrustedSeeds node trusted) (edges : List Delegation) (fuel : Nat) (known : List Nat)
    (h : checkedPermissions g node issued roots edges fuel = .known known) (i : Nat) :
    i ∈ known ↔ Compiler.Derives (· ∈ activeRoots g node roots)
      (· ∈ delegationRules g node issued edges) i := by
  exact Compiler.u03_2_checked_closure_complete (delegationRules g node issued edges)
    (activeRoots g node roots) fuel known h i

/-- 正委托程序的每条规则都有实际父节点，空根循环没有自发授权的来源。 -/
theorem unrooted_cycles_create_no_permission
    (g : Gamma) (node : Nat → AuthorityNode) (issued : Issued)
    (edges : List Delegation) (fuel i : Nat) :
    i ∉ Authorization.rootedPermissions [] (delegationRules g node issued edges) fuel := by
  intro h
  have hd := Compiler.u03_1_computed_sound (delegationRules g node issued edges) [] fuel i h
  have hm : Compiler.Models (· ∈ ([] : List Nat)) (· ∈ delegationRules g node issued edges)
      (fun _ => False) := by
    constructor
    · intro a ha
      simpa using ha
    · intro r hr hp
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hr
      exact hp e.parent (by simp [edgeRule])
  exact Compiler.u03_1_relative_soundness hm hd

/-- 阻断10.1 L103：从已算出的具体Grant许可，接到实际旧Gamma检查和Trace刷新边。 -/
def queryForRefresh (before : Ledger.Handle) (d : Draft) : Query :=
  ⟨before.gamma, d.change.actor, 1, d.change.event.version,
    .document d.change.event.version, none, some d.change.gamma⟩

theorem rooted_refresh_is_actual_authorized_step {trusted : AuthorityNode → Prop}
    (node : Nat → AuthorityNode) (issued : Issued) (roots : TrustedSeeds node trusted)
    (edges : List Delegation) (fuel : Nat) (before after : Ledger.Handle) (d : Draft)
    (h : submitDraft (derivedCatalog before.gamma node issued roots edges fuel) before d =
      .known after) :
    Granted (derivedCatalog before.gamma node issued roots edges fuel) before d ∧
    (∃ i ∈ computedPermissions before.gamma node issued roots edges fuel,
      Rooted before.gamma node issued trusted roots edges i ∧
      check (queryForRefresh before d) (node i).grant = true) ∧
    Trace.Step before after := by
  have hg := (actual_refresh_requires_old_authority
    (derivedCatalog before.gamma node issued roots edges fuel) before after d h).1
  have hp : permits (derivedCatalog before.gamma node issued roots edges fuel)
      (queryForRefresh before d) = true := hg.2
  obtain ⟨i, hi, hr, hc, _⟩ :=
    computed_authorization_has_actual_grant before.gamma node issued roots edges fuel
      (queryForRefresh before d) hp
  exact ⟨hg, ⟨i, hi, hr, hc⟩,
    Pipeline.u10_1_authorized_refresh_is_step _ before after d.change h⟩

/-- 阻断10.1 L103/L105：饱和检查的不确定分支不能经适配器变成肯定授权。 -/
def checkedCatalog {trusted : AuthorityNode → Prop}
    (g : Gamma) (node : Nat → AuthorityNode) (issued : Issued)
    (roots : TrustedSeeds node trusted) (edges : List Delegation) (fuel : Nat) :
    Result (List Authorization.Grant) :=
  match checkedPermissions g node issued roots edges fuel with
  | .known ids => .known (ids.map (fun i => (node i).grant))
  | .unknown e => .unknown e
  | .rejected e => .rejected e
  | .conflict left right => .conflict left right

theorem incomplete_graph_check_keeps_refresh_unknown {trusted : AuthorityNode → Prop}
    (g : Gamma) (node : Nat → AuthorityNode) (issued : Issued)
    (roots : TrustedSeeds node trusted) (edges : List Delegation) (fuel : Nat)
    (why : Error) (before : Ledger.Handle) (d : Draft)
    (h : checkedPermissions g node issued roots edges fuel = .unknown why) :
    refreshWithEvidence (checkedCatalog g node issued roots edges fuel) before d =
      .unknown why := by
  simp only [checkedCatalog, h, refreshWithEvidence]

/-- 阻断10.1 L103：无环不是必要条件的有限非空模型；根信任是外部给定，
本合成模型不声称由程序推出任何现实根授权。边支持读取双方完整具体节点。 -/
def cycleNode (i : Nat) : AuthorityNode :=
  ⟨{ baseGrant with subject := ⟨i⟩, evidence := ⟨100 + i⟩ }, true⟩

def edge12 : Delegation := ⟨1, 2, ⟨7⟩⟩
def edge21 : Delegation := ⟨2, 1, ⟨8⟩⟩
def cycleEdges : List Delegation := [edge12, edge21]

def cycleIssued : Issued := fun source parent child =>
  decide ((source = ⟨7⟩ ∧ parent = cycleNode 1 ∧ child = cycleNode 2) ∨
    (source = ⟨8⟩ ∧ parent = cycleNode 2 ∧ child = cycleNode 1))

def cycleTrusted (n : AuthorityNode) : Prop := n = cycleNode 1

def cycleRoots : TrustedSeeds cycleNode cycleTrusted :=
  { ids := [1]
    externalTrust := by
      intro i hi
      have he : i = 1 := by simpa using hi
      subst i
      rfl }

theorem rooted_cycle_is_authorized :
    edge12 ∈ cycleEdges ∧ edge21 ∈ cycleEdges ∧
    edge12.parent = edge21.child ∧ edge12.child = edge21.parent ∧
    edge12.parent ≠ edge12.child ∧
    admitted baseGamma cycleNode cycleIssued edge12 = true ∧
    admitted baseGamma cycleNode cycleIssued edge21 = true ∧
    checkedPermissions baseGamma cycleNode cycleIssued cycleRoots cycleEdges 2 =
      .known [1, 2, 2, 1] ∧
    permits (derivedCatalog baseGamma cycleNode cycleIssued cycleRoots cycleEdges 2)
      { baseQuery with subject := ⟨2⟩ } = true := by
  decide +kernel

/-- 阻断10.1 L103/L105：对象越界和当前已过期分别被实际边条件阻断。
此处issued=true只用于隔离测试各门的独立作用，不用它推出真实委托事实。 -/
def wrongScopeNode (i : Nat) : AuthorityNode :=
  if i = 2 then
    { cycleNode i with grant := { (cycleNode i).grant with object := .document 11 } }
  else cycleNode i

def expiredNode (i : Nat) : AuthorityNode :=
  if i = 2 then
    { cycleNode i with grant := { (cycleNode i).grant with untilDate := ⟨5⟩ } }
  else cycleNode i

theorem scope_and_time_are_independent_edge_gates :
    scopeCovers (wrongScopeNode 1) (wrongScopeNode 2) = false ∧
    admitted baseGamma wrongScopeNode (fun _ _ _ => true) edge12 = false ∧
    scopeCovers (expiredNode 1) (expiredNode 2) = true ∧
    nodeActive baseGamma (expiredNode 2) = false ∧
    admitted baseGamma expiredNode (fun _ _ _ => true) edge12 = false := by
  decide +kernel

/-- 阻断10.1 L101：三阶段全部使用实际Pipeline.refresh与Temporal选择。
授权事件版本0而目标Gamma要求版本1，提供“获准却不可启用”的有限见证。 -/
def phaseBefore : Ledger.Handle := Trace.initial baseGamma Acceptance.debt

def phaseNextGamma : Gamma := { baseGamma with normVersion := 1 }

def approvedDraft : Draft :=
  ⟨⟨phaseNextGamma, Acceptance.version, ⟨1⟩⟩, true, true⟩

def approvedCatalog : List Authorization.Grant :=
  [grantFor (queryForRefresh phaseBefore approvedDraft)]

def phasePost (d : Draft) : Ledger.Handle :=
  ⟨d.change.gamma, phaseBefore.revision + 1,
    { phaseBefore.state with
      normHistory := phaseBefore.state.normHistory ++ [d.change.event]
      env := Temporal.proposed_applicability d.change.gamma
        (phaseBefore.state.normHistory ++ [d.change.event]) }⟩

def enabledDraft : Draft :=
  ⟨⟨phaseNextGamma, { Acceptance.version with version := 1 }, ⟨1⟩⟩, true, true⟩

def enabledCatalog : List Authorization.Grant :=
  [grantFor (queryForRefresh phaseBefore enabledDraft)]

theorem three_stages_have_actual_distinct_witnesses :
    Granted approvedCatalog phaseBefore approvedDraft ∧
    submitDraft approvedCatalog phaseBefore approvedDraft = .known (phasePost approvedDraft) ∧
    ¬ Usable approvedCatalog phaseBefore approvedDraft ∧
    Usable enabledCatalog phaseBefore enabledDraft := by
  have ha : submitDraft approvedCatalog phaseBefore approvedDraft =
      .known (phasePost approvedDraft) := by decide +kernel
  have hbad : (phasePost approvedDraft).state.env ≠
      .known (phasePost approvedDraft).gamma.normVersion := by decide +kernel
  refine ⟨?_, ha, ?_, ?_⟩
  · decide +kernel
  · rintro ⟨after, hafter, henv⟩
    have he : after = phasePost approvedDraft := Result.known.inj (hafter.symm.trans ha)
    subst after
    exact hbad henv
  · refine ⟨phasePost enabledDraft, ?_, ?_⟩ <;> decide +kernel

/-- 阻断10.1 L101/L103：候选新规则下Grant检查通过，仍不通过实际旧Gamma入口。
变更不能用自己将安装的新authorityRuleVersion自证安装权限。 -/
def candidateSelfGrant : Authorization.Grant :=
  grantFor { queryForRefresh phaseBefore enabledDraft with gamma := phaseNextGamma }

theorem new_rule_check_does_not_authorize_its_installation :
    permits [candidateSelfGrant]
      { queryForRefresh phaseBefore enabledDraft with gamma := phaseNextGamma } = true ∧
    permits [candidateSelfGrant] (queryForRefresh phaseBefore enabledDraft) = false ∧
    submitDraft [candidateSelfGrant] phaseBefore enabledDraft = .unknown .authorityUnresolved := by
  decide +kernel

/-- 阻断10.1 L101：可启用版本与既有实际evaluator相接；直接复用已关闭U10.1，
不另写规则选择或刷新续行证明。 -/
theorem actual_rule_evaluation_keeps_usable_version {W : Type} (current : Ledger.Handle)
    (input : JurisLean.Candidates.LegalActionDomain20261027.LegalInput W) (branch : Nat)
    (bound : JurisLean.Candidates.FiniteLegalValidation20261027.BoundData)
    (out : JurisLean.Candidates.FiniteLegalValidation20261027.HornReport)
    (usable : current.state.env = .known current.gamma.normVersion)
    (accepted : JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.evaluateCurrentRules
      current input branch = .known (bound, out)) :
    input.anchor.gamma = current.gamma ∧ input.history = current.state.normHistory ∧
      out.selectedVersion = current.gamma.normVersion := by
  have hs := JurisLean.Candidates.U10_1RefreshRuleProtocol20261030.evaluated_rules_use_actual_environment
    current input branch bound out accepted
  have hselected := hs.2.2.2.2.2
  exact ⟨hs.1, hs.2.1, Result.known.inj (hselected.symm.trans usable)⟩

/-- 阻断10.1 L103：根图到实际刷新连接的非空实例。合成根明示外部给定，
不从程序或经验改善生成现实根授权，也不需要可再委托权限。 -/
def refreshRootNode (_i : Nat) : AuthorityNode :=
  ⟨grantFor (queryForRefresh phaseBefore enabledDraft), false⟩

def refreshRootTrusted (n : AuthorityNode) : Prop := n = refreshRootNode 0

def refreshRoots : TrustedSeeds refreshRootNode refreshRootTrusted :=
  { ids := [0]
    externalTrust := by
      intro i hi
      have he : i = 0 := by simpa using hi
      subst i
      rfl }

def groundedEnabledCatalog : List Authorization.Grant :=
  derivedCatalog baseGamma refreshRootNode (fun _ _ _ => false) refreshRoots [] 0

theorem grounded_graph_has_actual_usable_refresh :
    submitDraft groundedEnabledCatalog phaseBefore enabledDraft =
      .known (phasePost enabledDraft) ∧
    Usable groundedEnabledCatalog phaseBefore enabledDraft := by
  have ha : submitDraft groundedEnabledCatalog phaseBefore enabledDraft =
      .known (phasePost enabledDraft) := by decide +kernel
  exact ⟨ha, ⟨phasePost enabledDraft, ha, by decide +kernel⟩⟩

#check Draft
#check TrustedSeeds
#check four_binding_erasure_witnesses
#print axioms four_binding_erasure_witnesses
#check explicit_binding_blockers
#print axioms explicit_binding_blockers
#check draft_markers_do_not_authorize
#print axioms draft_markers_do_not_authorize
#check three_stages_have_actual_distinct_witnesses
#print axioms three_stages_have_actual_distinct_witnesses
#check new_rule_check_does_not_authorize_its_installation
#print axioms new_rule_check_does_not_authorize_its_installation
#check rooted_refresh_is_actual_authorized_step
#print axioms rooted_refresh_is_actual_authorized_step
#check rooted_cycle_is_authorized
#print axioms rooted_cycle_is_authorized
#check checked_permissions_exact_positive_semantics
#print axioms checked_permissions_exact_positive_semantics
#check unrooted_cycles_create_no_permission
#print axioms unrooted_cycles_create_no_permission
#check scope_and_time_are_independent_edge_gates
#print axioms scope_and_time_are_independent_edge_gates
#check evidence_reuse_exact_current_condition
#print axioms evidence_reuse_exact_current_condition
#check historical_validity_is_not_current_authority
#print axioms historical_validity_is_not_current_authority
#check unavailable_or_conflicting_evidence_never_enables
#print axioms unavailable_or_conflicting_evidence_never_enables
#check incomplete_graph_check_keeps_refresh_unknown
#print axioms incomplete_graph_check_keeps_refresh_unknown
#check actual_rule_evaluation_keeps_usable_version
#print axioms actual_rule_evaluation_keeps_usable_version
#check grounded_graph_has_actual_usable_refresh
#print axioms grounded_graph_has_actual_usable_refresh

end JurisLean.Candidates.AuthorizationClosureAudit20261104
