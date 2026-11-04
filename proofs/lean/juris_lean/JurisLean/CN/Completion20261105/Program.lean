import JurisLean.CN.Completion20261105.Execution

/-!
Typed composition, retained alternatives and finite iteration of actual commands.
The interpreter carries the actual post-state into the next call. Every returned
branch has a history in the same graph, including rejected/unknown attempts.
-/
namespace JurisLean.CN.Completion20261105
open JurisLean.CN.Revision20261101

def joinReply {α β : Type} (r : Reply α)
    (next : α → Situation → List (Reply β)) : List (Reply β) :=
  match r.answer with
  | .success value => next value r.after
  | .rejected k => [⟨r.after, .rejected k⟩]
  | .unknown k => [⟨r.after, .unknown k⟩]
  | .conflict k => [⟨r.after, .conflict k⟩]
  | .blockedHuman => [⟨r.after, .blockedHuman⟩]

inductive Program : Type → Type 1
  | pure {α : Type} (value : α) : Program α
  | call {α : Type} (command : Command α) : Program α
  | bind {α β : Type} (first : Program α) (next : α → Program β) : Program β
  | choice {α : Type} (left right : Program α) : Program α

def runProgram {α : Type} : Program α → Situation → List (Reply α)
  | .pure value, s => [quiet s (.success value)]
  | .call c, s => [executeCommand s c]
  | .bind first next, s =>
    (runProgram first s).flatMap (fun r => joinReply r (fun v => runProgram (next v)))
  | .choice left right, s => runProgram left s ++ runProgram right s

def repeatProgram (body : Program Unit) : Nat → Program Unit
  | 0 => .pure ()
  | n + 1 => .bind body (fun _ => repeatProgram body n)

/- No infinite run is asserted terminating. Star is the collection of all
   finite repetitions; every executed finite branch still retains its order. -/
def FiniteStar (body : Program Unit) (a b : Situation) : Prop :=
  ∃ n r, r ∈ runProgram (repeatProgram body n) a ∧ r.after = b

def History.append {a b c : Situation} (left : History a b) :
    History b c → History a c
  | .nil _ => left
  | .snoc history command => .snoc (left.append history) command

theorem program_pure_left {α β : Type} (v : α) (next : α → Program β)
    (s : Situation) :
    runProgram (.bind (.pure v) next) s = runProgram (next v) s := rfl

theorem joinReply_assoc {α β γ : Type} (r : Reply α)
    (first : α → Situation → List (Reply β))
    (next : β → Situation → List (Reply γ)) :
    (joinReply r first).flatMap (fun q => joinReply q next) =
      joinReply r (fun v s => (first v s).flatMap (fun q => joinReply q next)) := by
  cases r with
  | mk after answer => cases answer <;> rfl

theorem program_bind_assoc {α β γ : Type} (p : Program α) (f : α → Program β)
    (g : β → Program γ) (s : Situation) :
    runProgram (.bind (.bind p f) g) s =
      runProgram (.bind p (fun v => .bind (f v) g)) s := by
  simp only [runProgram, List.flatMap_assoc]
  congr 1
  funext reply
  exact joinReply_assoc reply (fun v => runProgram (f v)) (fun v => runProgram (g v))

theorem program_unknown_stops {α β : Type} (s : Situation) (why : UnknownKind)
    (next : α → Situation → List (Reply β)) :
    joinReply (⟨s, .unknown why⟩ : Reply α) next =
      [⟨s, .unknown why⟩] := rfl

theorem program_conflict_stops {α β : Type} (s : Situation) (route : ReviewRoute)
    (next : α → Situation → List (Reply β)) :
    joinReply (⟨s, .conflict route⟩ : Reply α) next =
      [⟨s, .conflict route⟩] := rfl

/- Obligation: composition does not invent an ideal successor. The proof
   constructs the history of the same interpreter branch returned to callers. -/
theorem program_has_actual_history {α : Type} (p : Program α)
    (s : Situation) (r : Reply α) (h : r ∈ runProgram p s) :
    Nonempty (History s r.after) := by
  induction p generalizing s r with
  | pure value =>
    simp [runProgram] at h
    subst r
    exact ⟨.nil s⟩
  | call command =>
    simp [runProgram] at h
    subst r
    exact ⟨.snoc (.nil s) command⟩
  | choice left right hl hr =>
    simp only [runProgram, List.mem_append] at h
    rcases h with h | h
    · exact hl s r h
    · exact hr s r h
  | bind first next hf hn =>
    obtain ⟨middle, hm, hr⟩ := List.mem_flatMap.mp h
    obtain ⟨history⟩ := hf s middle hm
    cases ha : middle.answer with
    | success value =>
      have hd : r ∈ runProgram (next value) middle.after := by
        simpa [joinReply, ha] using hr
      obtain ⟨tail⟩ := hn value middle.after r hd
      exact ⟨history.append tail⟩
    | rejected why =>
      simp [joinReply, ha] at hr
      subst r
      exact ⟨history⟩
    | unknown why =>
      simp [joinReply, ha] at hr
      subst r
      exact ⟨history⟩
    | conflict route =>
      simp [joinReply, ha] at hr
      subst r
      exact ⟨history⟩
    | blockedHuman =>
      simp [joinReply, ha] at hr
      subst r
      exact ⟨history⟩

theorem finite_star_has_history (body : Program Unit) (a b : Situation)
    (h : FiniteStar body a b) : Nonempty (History a b) := by
  obtain ⟨n, r, hr, he⟩ := h
  rw [← he]
  exact program_has_actual_history (repeatProgram body n) a r hr

structure Snapshot (α : Type) where
  before : Situation
  program : Program α

def replaySnapshot {α : Type} (current : Situation) (snapshot : Snapshot α) :
    Reply (List (Reply α)) :=
  quiet current (.success (runProgram snapshot.program snapshot.before))

theorem replay_preserves_current {α : Type} (s : Situation) (snapshot : Snapshot α) :
    (replaySnapshot s snapshot).after = s := rfl

theorem replay_reads_full_snapshot {α : Type} (s : Situation) (snapshot : Snapshot α) :
    (replaySnapshot s snapshot).answer =
      .success (runProgram snapshot.program snapshot.before) := rfl

#print axioms program_pure_left
#print axioms joinReply_assoc
#print axioms program_bind_assoc
#print axioms program_unknown_stops
#print axioms program_conflict_stops
#print axioms program_has_actual_history
#print axioms finite_star_has_history
#print axioms replay_preserves_current
#print axioms replay_reads_full_snapshot
end JurisLean.CN.Completion20261105

