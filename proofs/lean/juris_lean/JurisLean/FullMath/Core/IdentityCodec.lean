import JurisLean.FullMath.Core.Foundations

/-!
F02 / EXT02 — Structured component identity, lossless codec and composition
binding. String concatenation is not identity; the structured codec is
roundtrip-lossless, hence injective; composability requires full index
equality; hash values only locate records, they never identify them.
-/

namespace JurisLean.FullMath.Core

/-- Structured component identity: scope (domain/issue/stage/version), model,
scenario and semantic scope. -/
structure CompId where
  domain : Domain
  issue : String
  stage : String
  version : String
  model : String
  scenario : String
  semScope : String
  deriving DecidableEq

/-- Field-separated encoding; never an untyped concatenation. -/
def CompId.encode (c : CompId) : List String :=
  [c.domain.code, c.issue, c.stage, c.version, c.model, c.scenario, c.semScope]

/-- Decoding reconstructs the record or fails; no guessed defaults. -/
def CompId.decode : List String → Option CompId
  | ["C", i, st, v, m, sc, ss] => some ⟨.civil, i, st, v, m, sc, ss⟩
  | ["R", i, st, v, m, sc, ss] => some ⟨.criminal, i, st, v, m, sc, ss⟩
  | ["A", i, st, v, m, sc, ss] => some ⟨.administrative, i, st, v, m, sc, ss⟩
  | _ => none

/-- F02(a): the codec is roundtrip-lossless for every supported value. -/
theorem CompId.decode_encode (c : CompId) : CompId.decode c.encode = some c := by
  rcases c with ⟨d, i, st, v, m, sc, ss⟩
  cases d <;> simp [CompId.encode, CompId.decode, Domain.code]

/-- F02(b): roundtrip losslessness implies encoding injectivity (`congrArg decode`). -/
theorem CompId.encode_injective (a b : CompId) (h : a.encode = b.encode) : a = b := by
  have h2 := congrArg CompId.decode h
  rw [CompId.decode_encode, CompId.decode_encode] at h2
  exact Option.some.inj h2

/-- Two components are composable only under full index equality. -/
def composable (a b : CompId) : Bool := decide (a = b)

theorem composable_iff (a b : CompId) : composable a b = true ↔ a = b := by
  simp [composable]

/-- F02(c): any differing index forces the reject branch. -/
theorem composable_reject (a b : CompId) (h : a ≠ b) : composable a b = false := by
  simp [composable, h]

/-- Projections of composable components coincide. -/
theorem composable_projections (a b : CompId) (h : composable a b = true) :
    a.domain = b.domain ∧ a.issue = b.issue ∧ a.stage = b.stage ∧
    a.version = b.version ∧ a.model = b.model ∧ a.scenario = b.scenario ∧
    a.semScope = b.semScope := by
  have he : a = b := (composable_iff a b).mp h
  exact ⟨by rw [he], by rw [he], by rw [he], by rw [he], by rw [he], by rw [he], by rw [he]⟩

/-! Hashes locate, they do not identify. -/

/-- A hash/locator value; here the canonical example is a length. -/
def locator (l : List String) : ℕ := l.length

/-- F02(d): equal locators do not imply equal records — the locator is not an
identity. This is a concrete parameterized counterexample family. -/
theorem locator_not_identity :
    ∃ a b : List String, locator a = locator b ∧ a ≠ b :=
  ⟨["x", "y"], ["u", "v"], rfl, by simp⟩

/-! EXT02: scope migration keeps the main key and re-proves binding. -/

/-- Migrating a component to a new semantic scope keeps domain/issue/stage/
version/model/scenario and replaces only the semantic scope. -/
def migrate (c : CompId) (newSem : String) : CompId :=
  { c with semScope := newSem }

theorem migrate_main_key (c : CompId) (s : String) :
    (migrate c s).domain = c.domain ∧ (migrate c s).model = c.model ∧
    (migrate c s).scenario = c.scenario ∧ (migrate c s).semScope = s := by
  simp [migrate]

/-- Migrated components compose only when the migrated target scopes agree. -/
theorem migrate_composable_scope (a b : CompId) (s s' : String)
    (h : composable (migrate a s) (migrate b s') = true) : s = s' := by
  have he : migrate a s = migrate b s' := (composable_iff _ _).mp h
  exact congrArg CompId.semScope he

/-! New inputs never inherit old declarations. -/

/-- An input claim declares the identity it was verified for. -/
structure InputClaim where
  claimedId : CompId
  payload : String

/-- A claim is carried by an environment only under its declared identity. -/
def carries (claims : List InputClaim) (c : InputClaim) (i : CompId) : Prop :=
  c ∈ claims ∧ c.claimedId = i

/-- F02(e): a carried claim answers only for the identity it declared. -/
theorem carries_binds_identity (claims : List InputClaim) (c : InputClaim) (i j : CompId)
    (h : carries claims c i) (hcarried : carries claims c j) : i = j :=
  h.2.symm.trans hcarried.2

end JurisLean.FullMath.Core
