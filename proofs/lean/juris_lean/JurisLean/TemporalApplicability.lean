import JurisLean.LegalIds

/-!
中文说明：M2 P06 时态适用性合同。区分 publication、effective interval、
event、observed、as-of、decision、correction/retraction 时点与
supersession 链。observed-at 不得晚于允许的 as-of；未来信息不得回流；
retracted/superseded source 的旧证书失效。区间端点显式闭包。
-/

namespace JurisLean

/-- 中文说明：版本状态。 -/
inductive VersionStatus where
  | active
  | superseded
  | retracted
  | corrected
deriving DecidableEq, Repr

/-- 中文说明：来源版本记录；端点显式，open-ended 用 none 显式标记。 -/
structure SourceVersionRecord where
  snapshot : LegalId .snapshot
  publicationDay : Int
  effectiveFrom : Int
  effectiveTo : Option Int
  status : VersionStatus
deriving DecidableEq

/-- 中文说明：时点 t 落在生效区间内（左闭；右端存在时亦闭）。 -/
def effectiveAt (v : SourceVersionRecord) (t : Int) : Prop :=
  v.effectiveFrom ≤ t ∧
    match v.effectiveTo with
    | none => True
    | some upper => t ≤ upper

/-- 中文说明：观察时点不得晚于 as-of 时点（禁止未来信息回流）。 -/
def observationAllowed (observedDay asOfDay : Int) : Prop :=
  observedDay ≤ asOfDay

/-- 中文说明：版本在时点 t 可适用：处于生效区间且状态为 active。 -/
def versionApplicableAt (v : SourceVersionRecord) (t : Int) : Prop :=
  effectiveAt v t ∧ v.status = .active

/-- 中文说明：supersession 边：旧版本被新版本取代。 -/
structure SupersessionEdge where
  oldSnap : LegalId .snapshot
  newSnap : LegalId .snapshot
deriving DecidableEq

/-- 中文说明：supersession 不得自指。 -/
def supersessionWellFormed (e : SupersessionEdge) : Prop :=
  e.oldSnap ≠ e.newSnap

/-- 中文说明：区间良态：右端存在时不早于左端。 -/
def SourceVersionRecord.intervalValid (v : SourceVersionRecord) : Prop :=
  match v.effectiveTo with
  | none => True
  | some upper => v.effectiveFrom ≤ upper

/-- 中文证明：区间良态时左端点属于生效区间（闭区间端点）。 -/
theorem effective_at_left_boundary (v : SourceVersionRecord)
    (hv : v.intervalValid) : effectiveAt v v.effectiveFrom := by
  dsimp [effectiveAt]
  constructor
  · exact le_rfl
  · cases hto : v.effectiveTo with
    | none => trivial
    | some upper =>
      dsimp [SourceVersionRecord.intervalValid] at hv
      simpa [hto] using hv

/-- 中文证明：早于左端点的时点不在生效区间内。 -/
theorem before_effective_interval_not_effective (v : SourceVersionRecord) (t : Int)
    (h : t < v.effectiveFrom) : ¬ effectiveAt v t := by
  intro heff
  exact lt_irrefl _ (lt_of_lt_of_le h heff.1)

/-- 中文证明：晚于 as-of 的观察是未来信息回流，必须被拒。 -/
theorem future_information_blocked (observedDay asOfDay : Int)
    (h : asOfDay < observedDay) : ¬ observationAllowed observedDay asOfDay := by
  intro hallowed
  exact lt_irrefl _ (lt_of_lt_of_le h hallowed)

/-- 中文证明：retracted 版本在任何时点都不可适用。 -/
theorem retracted_source_invalidates (v : SourceVersionRecord) (t : Int)
    (h : v.status = .retracted) : ¬ versionApplicableAt v t := by
  intro happ
  have himp : VersionStatus.retracted = VersionStatus.active := h.symm.trans happ.2
  cases himp

/-- 中文证明：superseded 版本同样不可适用（旧证书失去效力）。 -/
theorem superseded_source_invalidates (v : SourceVersionRecord) (t : Int)
    (h : v.status = .superseded) : ¬ versionApplicableAt v t := by
  intro happ
  have himp : VersionStatus.superseded = VersionStatus.active := h.symm.trans happ.2
  cases himp

/-- 中文证明：supersession 自指不合法。 -/
theorem self_supersession_invalid {e : SupersessionEdge}
    (h : e.oldSnap = e.newSnap) : ¬ supersessionWellFormed e := by
  intro hwf
  exact hwf h

/-- 中文证明：适用判定对状态单调敏感：active 之外的状态都不可适用。 -/
theorem only_active_versions_applicable (v : SourceVersionRecord) (t : Int)
    (happ : versionApplicableAt v t) : v.status = .active :=
  happ.2

end JurisLean
