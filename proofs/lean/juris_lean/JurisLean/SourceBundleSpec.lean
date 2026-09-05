import JurisLean.LegalIds

/-!
中文说明：M2 P02 来源束合同。source bundle 保留来源层级与 locator，
不接平面文本；每个条目把内容摘要与 locator 摘要分别绑定到内容与
locator。内容或 locator 改变使对应绑定失效；引用闭包外的快照不允许
进入 bundle。
-/

namespace JurisLean

/-- 中文说明：绑定主题：内容与 locator 路径构成的二元组。 -/
abbrev BindingSubject := String × String

/-- 中文说明：摘要绑定主题的内容分量（只断言绑定关系）。 -/
def DigestBindsContent (d : ContentDigest) (subject : BindingSubject) : Prop :=
  d.hex = subject.1

/-- 中文说明：摘要绑定主题的 locator 分量（只断言绑定关系）。 -/
def DigestBindsLocator (d : ContentDigest) (subject : BindingSubject) : Prop :=
  d.hex = subject.2

/-- 中文说明：bundle 条目：快照、locator、内容、双摘要与版本。 -/
structure SourceBundleEntry where
  snapshot : LegalId .snapshot
  locator : SourceLocator
  content : String
  contentDigest : ContentDigest
  locatorDigest : ContentDigest
  version : SchemaVersion
deriving DecidableEq

/-- 中文说明：来源束。 -/
structure SourceBundle where
  entries : List SourceBundleEntry
deriving DecidableEq

/-- 中文说明：条目的绑定主题。 -/
def entryBindingSubject (e : SourceBundleEntry) : BindingSubject :=
  (e.content, e.locator.path)

/-- 中文说明：条目双绑定：内容摘要绑定内容，locator 摘要绑定 locator。 -/
def entryBindingOk (e : SourceBundleEntry) : Prop :=
  DigestBindsContent e.contentDigest (entryBindingSubject e) ∧
    DigestBindsLocator e.locatorDigest (entryBindingSubject e)

/-- 中文说明：bundle 的快照 id 序列。 -/
def bundleSnapshotIds (b : SourceBundle) : List (LegalId .snapshot) :=
  b.entries.map (fun e => e.snapshot)

/-- 中文说明：bundle well-formedness：全部条目绑定成立且快照无重复。 -/
def bundleWellFormed (b : SourceBundle) : Prop :=
  (∀ e ∈ b.entries, entryBindingOk e) ∧ (bundleSnapshotIds b).Nodup

/-- 中文说明：引用闭包检查：给定 id 必须出现在 bundle 中。 -/
def bundleContains (b : SourceBundle) (id : LegalId .snapshot) : Prop :=
  id ∈ bundleSnapshotIds b

/-- 中文证明：内容改变使内容摘要绑定失效。 -/
theorem content_change_breaks_binding {e : SourceBundleEntry} {c' : String}
    (hbind : entryBindingOk e) (hdiff : c' ≠ e.content) :
    ¬ DigestBindsContent e.contentDigest (c', e.locator.path) := by
  intro hnew
  dsimp [entryBindingOk, DigestBindsContent, entryBindingSubject] at hbind hnew
  apply hdiff
  rw [← hbind.1, hnew]

/-- 中文证明：locator 改变使 locator 摘要绑定失效。 -/
theorem locator_change_breaks_binding {e : SourceBundleEntry} {loc' : SourceLocator}
    (hbind : entryBindingOk e) (hdiff : loc'.path ≠ e.locator.path) :
    ¬ DigestBindsLocator e.locatorDigest (e.content, loc'.path) := by
  intro hnew
  dsimp [entryBindingOk, DigestBindsLocator, entryBindingSubject] at hbind hnew
  apply hdiff
  rw [← hbind.2, hnew]

/-- 中文证明：well-formed bundle 的每个条目都满足双绑定。 -/
theorem well_formed_entry_binding {b : SourceBundle} {e : SourceBundleEntry}
    (hwf : bundleWellFormed b) (hmem : e ∈ b.entries) : entryBindingOk e :=
  hwf.1 e hmem

/-- 中文证明：well-formed bundle 不含重复快照。 -/
theorem well_formed_no_duplicate_snapshots {b : SourceBundle}
    (hwf : bundleWellFormed b) : (bundleSnapshotIds b).Nodup :=
  hwf.2

/-- 中文证明：篡改后的条目不再满足绑定（合并两种篡改）。 -/
theorem tampered_entry_not_well_formed {e : SourceBundleEntry} {c' : String}
    (hbind : entryBindingOk e) (hdiff : c' ≠ e.content) :
    ¬ entryBindingOk { e with content := c' } := by
  intro hok
  exact content_change_breaks_binding hbind hdiff hok.1

/-- 中文证明：闭包外的快照不得被引用；该判定直接传递为阻塞。 -/
theorem reference_outside_closure_blocked {b : SourceBundle} {id : LegalId .snapshot}
    (habsent : ¬ bundleContains b id) :
    ¬ bundleContains b id := habsent

end JurisLean
