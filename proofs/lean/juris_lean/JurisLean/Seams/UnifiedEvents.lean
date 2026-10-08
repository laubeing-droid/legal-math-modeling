import Mathlib.Tactic

/-
Unified events, layer I (plan §9; I.4.13 L13, fragment for U21–U24, U26).

The small-step actual-effect face, mirroring the Python event layer
(`tools/unified_math_v2/unified/process.py`):

* `ActualEffectStep` reads ACTUAL events — issuing a wrong judgment is a
  step (no legality premise); `step` is the deterministic function with
  `blocked` for rejected inputs, and `step_exact` proves the function
  exactly denotes the relation.
* `step_preserves`: the structural invariant WF (revoked ⊆ issued) is
  preserved — WF says nothing about legality, error-free judgments, or
  no overpayment (§9 discipline).
* `runEvents` folds over event lists; `runEvents_exact` is the trace
  exactness; `runEvents_append` is the shared-intermediate composition
  law.
* Revocation KEEPS the payment history (restitution is a new obligation,
  not a deletion) — `revoke_keeps_payments`.
* Evidence withdrawal removes EVERY occurrence of the id (self-contained
  `removeAll`; `List.erase` keeps later duplicates and would not support
  the invalidation theorem) — `withdrawn_not_in_state`.

Scope, honestly: six event kinds, deterministic single-successor steps,
an id-indexed ledger fragment.  Multi-successor/symbolic successors,
asOf-prefix projection with retrospective revocation effects, and the
ActualIssued/Effective/LegallyCorrect/Final four-relations lattice in
full stay on the Python side until their Lean tracks are built.
-/

namespace JurisLean.Seams.UnifiedEvents

/-! ## 一、载体：状态与事件 -/

/-- 事件账本状态（id 片段：证据/裁判/撤销/付款＋规范版本）。 -/
structure EvState where
  /-- 已采纳证据。 -/
  evidence : List ℕ
  /-- 已实际作出的裁判（不论对错）。 -/
  judgments : List ℕ
  /-- 已撤销的裁判（只追加）。 -/
  revoked : List ℕ
  /-- 实际付款事件（撤销不删除）。 -/
  payments : List ℕ
  /-- 规范版本。 -/
  normVersion : ℕ
  deriving DecidableEq, Repr

/-- 事件（六类：加证/撤证/裁判/撤销/付款/规范授权）。 -/
inductive Ev : Type
  | evidenceAdded (id : ℕ)
  | evidenceWithdrawn (id : ℕ)
  | judgmentIssued (id : ℕ)
  | judgmentRevoked (id : ℕ)
  | paymentMade (id : ℕ)
  | normAuthorized (v : ℕ)
  deriving DecidableEq, Repr

/-- 结构不变式：只撤销已作出的裁判（对合法性/对错零断言）。 -/
def StateWF (s : EvState) : Prop := ∀ id ∈ s.revoked, id ∈ s.judgments

/-- 自含的全删（`List.erase` 只删首个匹配，重复项会留下）。 -/
def removeAll (a : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => if x = a then removeAll a xs else x :: removeAll a xs

/-- 全删后不再含。 -/
theorem not_mem_removeAll (a : ℕ) : ∀ l : List ℕ, a ∉ removeAll a l := by
  intro l
  induction l with
  | nil => simp [removeAll]
  | cons x xs ih =>
      by_cases hxa : x = a
      · simp only [removeAll, if_pos hxa]
        exact ih
      · simp only [removeAll, if_neg hxa, List.mem_cons]
        intro h
        rcases h with rfl | h
        · exact hxa rfl
        · exact ih h

/-! ## 二、实际效果步（关系）与步函数的精确对应 -/

/-- 实际效果步：按法律效果规则解释实际事件（撤销保留付款史）。 -/
inductive ActualEffectStep : EvState → Ev → EvState → Prop
  | evAdd (s : EvState) (id : ℕ) (h : id ∉ s.evidence) :
      ActualEffectStep s (.evidenceAdded id) { s with evidence := id :: s.evidence }
  | evWithdraw (s : EvState) (id : ℕ) (h : id ∈ s.evidence) :
      ActualEffectStep s (.evidenceWithdrawn id)
        { s with evidence := removeAll id s.evidence }
  | evJudge (s : EvState) (id : ℕ) :
      ActualEffectStep s (.judgmentIssued id) { s with judgments := id :: s.judgments }
  | evRevoke (s : EvState) (id : ℕ) (h : id ∈ s.judgments) :
      ActualEffectStep s (.judgmentRevoked id)
        { s with revoked := id :: s.revoked }
  | evPay (s : EvState) (id : ℕ) :
      ActualEffectStep s (.paymentMade id) { s with payments := id :: s.payments }
  | evNorm (s : EvState) (v : ℕ) :
      ActualEffectStep s (.normAuthorized v) { s with normVersion := v }

/-- 步函数的结果：单后继或拒绝（缺输入/不受理）。 -/
inductive TransitionResult (S : Type) : Type
  | ok (t : S)
  | blocked
  deriving Repr

/-- 结果的指称（blocked 指称空）。 -/
def denoteNext (r : TransitionResult S) (t : S) : Prop :=
  match r with
  | .ok u => t = u
  | .blocked => False

/-- 步函数：确定性，拒绝即 blocked。 -/
def step (s : EvState) (e : Ev) : TransitionResult EvState :=
  match e with
  | .evidenceAdded id =>
      if id ∈ s.evidence then .blocked
      else .ok { s with evidence := id :: s.evidence }
  | .evidenceWithdrawn id =>
      if id ∈ s.evidence then .ok { s with evidence := removeAll id s.evidence }
      else .blocked
  | .judgmentIssued id => .ok { s with judgments := id :: s.judgments }
  | .judgmentRevoked id =>
      if id ∈ s.judgments then .ok { s with revoked := id :: s.revoked }
      else .blocked
  | .paymentMade id => .ok { s with payments := id :: s.payments }
  | .normAuthorized v => .ok { s with normVersion := v }

/-- **单步精确对应**：步函数的指称恰是实际效果关系的外延。 -/
theorem step_exact (s : EvState) (e : Ev) (t : EvState) :
    denoteNext (step s e) t ↔ ActualEffectStep s e t := by
  cases e with
  | evidenceAdded id =>
      by_cases h : id ∈ s.evidence
      · simp only [step, denoteNext, if_pos h]
        exact ⟨fun hf => hf.elim, fun hstep =>
          (by cases hstep with
            | evAdd _ hn => exact absurd h hn)⟩
      · simp only [step, denoteNext, if_neg h]
        exact ⟨fun heq => by subst heq; exact ActualEffectStep.evAdd s id h,
          fun hstep => (by cases hstep with
            | evAdd _ _ => exact rfl)⟩
  | evidenceWithdrawn id =>
      by_cases h : id ∈ s.evidence
      · simp only [step, denoteNext, if_pos h]
        exact ⟨fun heq => by subst heq; exact ActualEffectStep.evWithdraw s id h,
          fun hstep => (by cases hstep with
            | evWithdraw _ _ => exact rfl)⟩
      · simp only [step, denoteNext, if_neg h]
        exact ⟨fun hf => hf.elim, fun hstep =>
          (by cases hstep with
            | evWithdraw _ hm => exact absurd hm h)⟩
  | judgmentIssued id =>
      simp only [step, denoteNext]
      exact ⟨fun heq => by subst heq; exact ActualEffectStep.evJudge s id,
        fun hstep => (by cases hstep with
          | evJudge _ => exact rfl)⟩
  | judgmentRevoked id =>
      by_cases h : id ∈ s.judgments
      · simp only [step, denoteNext, if_pos h]
        exact ⟨fun heq => by subst heq; exact ActualEffectStep.evRevoke s id h,
          fun hstep => (by cases hstep with
            | evRevoke _ _ => exact rfl)⟩
      · simp only [step, denoteNext, if_neg h]
        exact ⟨fun hf => hf.elim, fun hstep =>
          (by cases hstep with
            | evRevoke _ hm => exact absurd hm h)⟩
  | paymentMade id =>
      simp only [step, denoteNext]
      exact ⟨fun heq => by subst heq; exact ActualEffectStep.evPay s id,
        fun hstep => (by cases hstep with
          | evPay _ => exact rfl)⟩
  | normAuthorized v =>
      simp only [step, denoteNext]
      exact ⟨fun heq => by subst heq; exact ActualEffectStep.evNorm s v,
        fun hstep => (by cases hstep with
          | evNorm _ => exact rfl)⟩

/-! ## 三、不变式保持 -/

/-- **不变式保持**：实际效果步保持结构不变式（WF 不保证合法/无错/无超额）。 -/
theorem step_preserves (s : EvState) (e : Ev) (t : EvState)
    (hwf : StateWF s) (hstep : ActualEffectStep s e t) : StateWF t := by
  cases hstep with
  | evAdd _ _ => simpa [StateWF] using hwf
  | evWithdraw _ _ => simpa [StateWF] using hwf
  | evJudge _ =>
      intro x hx
      exact List.mem_cons.mpr (Or.inr (hwf x hx))
  | evRevoke _ hm =>
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hm
      · exact hwf x hx
  | evPay _ => simpa [StateWF] using hwf
  | evNorm _ => simpa [StateWF] using hwf

/-! ## 四、轨迹：折叠与合成 -/

/-- 事件列表上的实际效果轨迹关系。 -/
inductive ActualEffectSteps : EvState → List Ev → EvState → Prop
  | nil (s : EvState) : ActualEffectSteps s [] s
  | cons (s u t : EvState) (e : Ev) (es : List Ev)
      (h₁ : ActualEffectStep s e u) (h₂ : ActualEffectSteps u es t) :
      ActualEffectSteps s (e :: es) t

/-- 轨迹折叠。 -/
def runEvents : EvState → List Ev → TransitionResult EvState
  | s, [] => .ok s
  | s, e :: es =>
      match step s e with
      | .blocked => .blocked
      | .ok u => runEvents u es

/-- 轨迹反演：cons 形轨迹分解为单步＋尾轨迹。 -/
theorem steps_cons_inv {s : EvState} {e : Ev} {es : List Ev} {t : EvState}
    (h : ActualEffectSteps s (e :: es) t) :
    ∃ u, ActualEffectStep s e u ∧ ActualEffectSteps u es t := by
  cases h with
  | cons _ u _ _ _ h₁ h₂ => exact ⟨u, h₁, h₂⟩

/-- **轨迹精确对应**。 -/
theorem runEvents_exact (s : EvState) (es : List Ev) (t : EvState) :
    denoteNext (runEvents s es) t ↔ ActualEffectSteps s es t := by
  induction es generalizing s with
  | nil =>
      simp only [runEvents, denoteNext]
      exact ⟨fun h => by subst h; exact ActualEffectSteps.nil s,
        fun h => (by cases h with
          | nil _ => exact rfl)⟩
  | cons e es ih =>
      simp only [runEvents]
      cases h : step s e with
      | blocked =>
          have hnone : ¬ ActualEffectSteps s (e :: es) t := by
            intro hsteps
            obtain ⟨u, h₁, _⟩ := steps_cons_inv hsteps
            have hden : denoteNext (step s e) u := (step_exact s e u).mpr h₁
            rw [h] at hden
            exact hden
          simp only [denoteNext]
          exact ⟨fun hf => hf.elim, fun hsteps => absurd hsteps hnone⟩
      | ok u =>
          have hstep : ActualEffectStep s e u := by
            have hd : denoteNext (step s e) u := by rw [h]; simp [denoteNext]
            exact (step_exact s e u).mp hd
          constructor
          · intro hden
            exact ActualEffectSteps.cons s u t e es hstep ((ih u).mp hden)
          · intro hsteps
            obtain ⟨u', h₁, h₂⟩ := steps_cons_inv hsteps
            have hden' : denoteNext (step s e) u' := (step_exact s e u').mpr h₁
            rw [h] at hden'
            simp only [denoteNext] at hden'
            subst hden'
            exact (ih u).mpr h₂

/-- **轨迹合成分配律**：xs++ys 的轨迹关系分解为共享中间态。 -/
theorem runEvents_append (s t : EvState) (xs ys : List Ev) :
    ActualEffectSteps s (xs ++ ys) t ↔
      ∃ u, ActualEffectSteps s xs u ∧ ActualEffectSteps u ys t := by
  induction xs generalizing s with
  | nil =>
      simp only [List.nil_append]
      exact ⟨fun h => ⟨s, ActualEffectSteps.nil s, h⟩,
        fun h => by
          obtain ⟨u, hnil, hys⟩ := h
          cases hnil with
          | nil _ => exact hys⟩
  | cons e es ih =>
      simp only [List.cons_append]
      constructor
      · intro h
        obtain ⟨w, h₁, hrest⟩ := steps_cons_inv h
        obtain ⟨v, hev, hvy⟩ := (ih w).mp hrest
        exact ⟨v, ActualEffectSteps.cons s w v e es h₁ hev, hvy⟩
      · intro h
        obtain ⟨u, hxs, hys⟩ := h
        obtain ⟨w, h₁, hrest⟩ := steps_cons_inv hxs
        exact ActualEffectSteps.cons s w t e es h₁ ((ih w).mpr ⟨u, hrest, hys⟩)

/-! ## 五、撤销保留付款与撤证失效（§9 纪律见证） -/

/-- **撤销不删除付款史**：返还义务是新事件，不是抹记录。 -/
theorem revoke_keeps_payments (s : EvState) (id : ℕ) (t : EvState)
    (h : ActualEffectStep s (.judgmentRevoked id) t) : t.payments = s.payments := by
  cases h with
  | evRevoke _ _ => rfl

/-- **撤证后派生采纳失效**（证据 id 的每一处出现都被移除）。 -/
theorem withdrawn_not_in_state (s : EvState) (id : ℕ) (t : EvState)
    (h : ActualEffectStep s (.evidenceWithdrawn id) t) : id ∉ t.evidence := by
  cases h with
  | evWithdraw _ _ => exact not_mem_removeAll id s.evidence

end JurisLean.Seams.UnifiedEvents
