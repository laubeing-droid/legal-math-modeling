import JurisLean.Candidates.Final20261021.Interfaces

namespace JurisLean.Candidates.Final20261021.Transactions

structure Receipt (B P R : Type) where
  payload : P
  attempt : Nat
  before : B
  after : B
  beforeVersion : Nat
  afterVersion : Nat
  result : R

structure Store (B P R : Type) where
  business : B
  version : Nat
  committed : Nat → Option (Receipt B P R)
  cancelled : Nat → Bool

inductive Label where
  | commit (attempt key : Nat)
  | abort (attempt : Nat)
  | replay (attempt key : Nat)
  | conflict (attempt key : Nat)
  | idle
  deriving DecidableEq

variable {B P R : Type}

def commitStore (req : Nat → Nat × P) (s : Store B P R)
    (a : Nat) (b : B) (r : R) : Store B P R :=
  { business := b
    version := s.version + 1
    committed := fun k => if k = (req a).1 then
      some ⟨(req a).2, a, s.business, b, s.version, s.version + 1, r⟩
      else s.committed k
    cancelled := s.cancelled }

def abortStore (s : Store B P R) (a : Nat) : Store B P R :=
  { s with cancelled := fun x => if x = a then true else s.cancelled x }

inductive Step (req : Nat → Nat × P) (f : B → P → Option (B × R)) :
    Store B P R → Label → Store B P R → Prop where
  | commit (s : Store B P R) (a expected : Nat) (b : B) (r : R)
      (openAttempt : s.cancelled a = false)
      (absent : s.committed (req a).1 = none)
      (versionMatches : s.version = expected)
      (evaluation : f s.business (req a).2 = some (b, r)) :
      Step req f s (.commit a (req a).1) (commitStore req s a b r)
  | abort (s : Store B P R) (a : Nat)
      (notCommittedByAttempt : ∀ e, s.committed (req a).1 = some e → e.attempt ≠ a) :
      Step req f s (.abort a) (abortStore s a)
  | replay (s : Store B P R) (a : Nat) (e : Receipt B P R)
      (record : s.committed (req a).1 = some e) (samePayload : e.payload = (req a).2) :
      Step req f s (.replay a (req a).1) s
  | conflict (s : Store B P R) (a : Nat) (e : Receipt B P R)
      (record : s.committed (req a).1 = some e) (differentPayload : e.payload ≠ (req a).2) :
      Step req f s (.conflict a (req a).1) s
  | idle (s : Store B P R) : Step req f s .idle s

inductive Trace (req : Nat → Nat × P) (f : B → P → Option (B × R)) :
    Store B P R → List Label → Store B P R → Prop where
  | nil (s : Store B P R) : Trace req f s [] s
  | cons {s t u : Store B P R} {l : Label} {ls : List Label} :
      Step req f s l t → Trace req f t ls u → Trace req f s (l :: ls) u

def registered (s : Store B P R) (k : Nat) : Nat :=
  if (s.committed k).isSome then 1 else 0

def increment (k : Nat) : Label → Nat
  | .commit _ key => if k = key then 1 else 0
  | _ => 0

def commitCount (k : Nat) : List Label → Nat
  | [] => 0
  | l :: ls => increment k l + commitCount k ls

theorem step_count (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {s t : Store B P R} {l : Label} (h : Step req f s l t) (k : Nat) :
    registered t k = registered s k + increment k l := by
  cases h with
  | commit a expected b r ho hn hv hf =>
    by_cases hk : k = (req a).1
    · subst k
      simp [registered, commitStore, increment, hn]
    · simp [registered, commitStore, increment, hk]
  | abort a h => rfl
  | replay a e hd hp => rfl
  | conflict a e hd hp => rfl
  | idle => rfl

theorem trace_count (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {s t : Store B P R} {ls : List Label} (h : Trace req f s ls t) (k : Nat) :
    registered t k = registered s k + commitCount k ls := by
  induction h with
  | nil s => rfl
  | cons hs ht ih =>
    rw [ih, step_count req f hs k]
    exact Nat.add_assoc _ _ _

theorem registered_le_one (s : Store B P R) (k : Nat) : registered s k ≤ 1 := by
  cases h : s.committed k <;> simp [registered, h]

theorem at_most_once (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {s t : Store B P R} {ls : List Label} (h : Trace req f s ls t) (k : Nat) :
    commitCount k ls ≤ 1 := by
  have he := trace_count req f h k
  have hb := registered_le_one t k
  omega

theorem entry_preserved_step (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {s t : Store B P R} {l : Label} (h : Step req f s l t)
    (k : Nat) (e : Receipt B P R) (he : s.committed k = some e) :
    t.committed k = some e := by
  cases h with
  | commit a expected b r ho hn hv hf =>
    by_cases hk : k = (req a).1
    · subst k
      rw [hn] at he
      cases he
    · simp [commitStore, hk, he]
  | abort a h => exact he
  | replay a e hd hp => exact he
  | conflict a e hd hp => exact he
  | idle => exact he

theorem entry_preserved_trace (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {s t : Store B P R} {ls : List Label} (h : Trace req f s ls t)
    (k : Nat) (e : Receipt B P R) (he : s.committed k = some e) :
    t.committed k = some e := by
  induction h with
  | nil s => exact he
  | cons hs ht ih => exact ih (entry_preserved_step req f hs k e he)

theorem cancelled_preserved_step (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {s t : Store B P R} {l : Label} (h : Step req f s l t) (a : Nat)
    (ha : s.cancelled a = true) : t.cancelled a = true := by
  cases h with
  | commit j expected b r ho hn hv hf => exact ha
  | abort j h =>
    by_cases he : a = j
    · simp [abortStore, he]
    · simp [abortStore, he, ha]
  | replay j e hd hp => exact ha
  | conflict j e hd hp => exact ha
  | idle => exact ha

theorem cancelled_preserved_trace (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {s t : Store B P R} {ls : List Label} (h : Trace req f s ls t) (a : Nat)
    (ha : s.cancelled a = true) : t.cancelled a = true := by
  induction h with
  | nil s => exact ha
  | cons hs ht ih => exact ih (cancelled_preserved_step req f hs a ha)

theorem cancelled_cannot_commit (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {s t : Store B P R} (a k : Nat) (ha : s.cancelled a = true) :
    ¬ Step req f s (.commit a k) t := by
  intro h
  cases h with
  | commit a expected b r ho hn hv hf => simp_all

theorem noncommit_business_unchanged (req : Nat → Nat × P)
    (f : B → P → Option (B × R)) {s t : Store B P R} {l : Label}
    (h : Step req f s l t) (notCommit : ∀ a k, l ≠ .commit a k) :
    t.business = s.business ∧ t.version = s.version ∧ t.committed = s.committed := by
  cases h with
  | commit a expected b r ho hn hv hf => exact False.elim (notCommit a _ rfl)
  | abort a h => exact ⟨rfl, rfl, rfl⟩
  | replay a e hd hp => exact ⟨rfl, rfl, rfl⟩
  | conflict a e hd hp => exact ⟨rfl, rfl, rfl⟩
  | idle => exact ⟨rfl, rfl, rfl⟩

theorem step_version_monotone (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {s t : Store B P R} {label : Label} (h : Step req f s label t) :
    s.version ≤ t.version := by
  cases h <;> simp [commitStore, abortStore]

theorem trace_version_monotone (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {s t : Store B P R} {labels : List Label} (h : Trace req f s labels t) :
    s.version ≤ t.version := by
  induction h with
  | nil s => exact le_rfl
  | cons step rest ih => exact le_trans (step_version_monotone req f step) ih

theorem step_same_version_business (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {s t : Store B P R} {label : Label} (h : Step req f s label t)
    (sameVersion : t.version = s.version) : t.business = s.business := by
  cases h with
  | commit a expected b r ho hn hv hf => simp [commitStore] at sameVersion
  | abort a h => rfl
  | replay a e hd hp => rfl
  | conflict a e hd hp => rfl
  | idle => rfl

theorem trace_same_version_business (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {s t : Store B P R} {labels : List Label} (h : Trace req f s labels t)
    (sameVersion : t.version = s.version) : t.business = s.business := by
  induction h with
  | nil s => rfl
  | @cons s middle final label labels step rest ih =>
      have first := step_version_monotone req f step
      have last := trace_version_monotone req f rest
      have middleVersion : middle.version = s.version := by omega
      have finalVersion : final.version = middle.version := by omega
      exact (ih finalVersion).trans (step_same_version_business req f step middleVersion)

-- B is the entire read domain of f, including every relevant environment and
-- authority input. A protocol that versions only a projection does not meet
-- this contract; there is no assertion about untracked product writes.
theorem u02_2_complete_readset_CAS (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {snapshot current : Store B P R} {labels : List Label}
    (intervening : Trace req f snapshot labels current)
    (versionMatches : current.version = snapshot.version) (payload : P) :
    f current.business payload = f snapshot.business payload := by
  rw [trace_same_version_business req f intervening versionMatches]



end JurisLean.Candidates.Final20261021.Transactions

namespace JurisLean.Candidates.Final20261021.Transactions
variable {B P R : Type}

theorem commit_receipt_at_end (req : Nat → Nat × P) (f : B → P → Option (B × R))
    {s t : Store B P R} {ls : List Label} (h : Trace req f s ls t)
    (a k : Nat) (hm : Label.commit a k ∈ ls) :
    ∃ e, t.committed (req a).1 = some e ∧ e.attempt = a ∧
      e.payload = (req a).2 ∧ f e.before e.payload = some (e.after, e.result) ∧
      e.afterVersion = e.beforeVersion + 1 := by
  induction h with
  | nil s => simp at hm
  | @cons s u t l ls hs ht ih =>
    rcases List.mem_cons.mp hm with he | hm
    · subst l
      cases hs with
      | commit a expected b r ho hn hv hf =>
        let e : Receipt B P R := ⟨(req a).2, a, s.business, b, s.version, s.version + 1, r⟩
        have hd : (commitStore req s a b r).committed (req a).1 = some e := by
          simp [commitStore, e]
        exact ⟨e, entry_preserved_trace req f ht _ _ hd, rfl, rfl, hf, rfl⟩
    · exact ih hm

theorem abort_excludes_prior_commit (req : Nat → Nat × P)
    (f : B → P → Option (B × R)) {s t u : Store B P R} {ls : List Label}
    (h : Trace req f s ls t) (a : Nat) (ha : Step req f t (.abort a) u) :
    ∀ k, Label.commit a k ∉ ls := by
  intro k hm
  obtain ⟨e, hd, he, hp, hf, hv⟩ := commit_receipt_at_end req f h a k hm
  cases ha with
  | abort a noReceipt => exact noReceipt e hd he

theorem cancelled_excludes_trace_commit (req : Nat → Nat × P)
    (f : B → P → Option (B × R)) {s t : Store B P R} {ls : List Label}
    (h : Trace req f s ls t) (a : Nat) (ha : s.cancelled a = true) :
    ∀ k, Label.commit a k ∉ ls := by
  induction h with
  | nil s => simp
  | cons hs ht ih =>
    intro k hm
    rcases List.mem_cons.mp hm with he | hm
    · subst he
      exact cancelled_cannot_commit req f a k ha hs
    · exact ih (cancelled_preserved_step req f hs a ha) k hm

theorem abort_excludes_future_commit (req : Nat → Nat × P)
    (f : B → P → Option (B × R)) {s t u : Store B P R} {ls : List Label}
    (a : Nat) (ha : Step req f s (.abort a) t) (h : Trace req f t ls u) :
    ∀ k, Label.commit a k ∉ ls := by
  have cancelled : t.cancelled a = true := by
    cases ha with
    | abort a noReceipt => simp [abortStore]
  exact cancelled_excludes_trace_commit req f h a cancelled

end JurisLean.Candidates.Final20261021.Transactions
