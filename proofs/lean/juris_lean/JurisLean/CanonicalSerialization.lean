import Mathlib.Data.List.Basic
import JurisLean.LegalIds

/-!
中文说明：M1 canonical serialization 层。canonical collection 自带无重复
证明；adjoin 对已存在元素是幂等的。serialization round-trip 保持
canonical semantic value。digest 仅作为内容绑定参数出现。
-/

namespace JurisLean

/-- 中文说明：canonical collection：条目序列携带无重复证明。 -/
structure CanonicalCollection where
  entries : List String
  nodupEntries : entries.Nodup

/-- 中文说明：空 canonical collection。 -/
def CanonicalCollection.empty : CanonicalCollection :=
  { entries := [], nodupEntries := List.nodup_nil }

/-- 中文说明：幂等并入：元素已存在时集合保持不变。 -/
def CanonicalCollection.adjoin (c : CanonicalCollection) (a : String) : CanonicalCollection :=
  if h : a ∈ c.entries then
    c
  else
    { entries := a :: c.entries, nodupEntries := List.nodup_cons.mpr ⟨h, c.nodupEntries⟩ }

/-- 中文说明：canonical token：序列化单元是 key-value 对。 -/
structure CanonicalToken where
  key : String
  value : String
deriving DecidableEq, Repr

/-- 中文说明：canonical token 序列化为稳定键值对序列。 -/
def serializeTokens (tokens : List CanonicalToken) : List (String × String) :=
  tokens.map (fun t => (t.key, t.value))

/-- 中文说明：从键值对序列解析回 canonical token。 -/
def parseTokens (pairs : List (String × String)) : List CanonicalToken :=
  pairs.map (fun p => { key := p.1, value := p.2 })

/-- 中文证明：对已存在元素 adjoin 幂等（canonicalization 幂等的核心情形）。 -/
theorem adjoin_idempotent_of_mem {c : CanonicalCollection} {a : String}
    (hmem : a ∈ c.entries) : c.adjoin a = c := by
  dsimp [CanonicalCollection.adjoin]
  split
  · rfl
  · contradiction

/-- 中文证明：两次 adjoin 同一元素与一次相同（幂等闭合）。 -/
theorem adjoin_adjoin_idempotent (c : CanonicalCollection) (a : String) :
    (c.adjoin a).adjoin a = c.adjoin a := by
  dsimp [CanonicalCollection.adjoin]
  split
  · rfl
  · rename_i hnot
    dsimp [CanonicalCollection.adjoin] at hnot
    split at hnot
    · contradiction
    · exfalso
      exact hnot (List.mem_cons.mpr (Or.inl rfl))

/-- 中文证明：已有条目在 adjoin 后仍然保留。 -/
theorem adjoin_preserves_membership {c : CanonicalCollection} (a x : String)
    (hmem : x ∈ c.entries) : x ∈ (c.adjoin a).entries := by
  dsimp [CanonicalCollection.adjoin]
  split
  · exact hmem
  · exact List.mem_cons.mpr (Or.inr hmem)

/-- 中文证明：被并入的元素必然出现在结果中。 -/
theorem adjoin_contains_element (c : CanonicalCollection) (a : String) :
    a ∈ (c.adjoin a).entries := by
  dsimp [CanonicalCollection.adjoin]
  split
  · assumption
  · exact List.mem_cons.mpr (Or.inl rfl)

/-- 中文证明：serialization round-trip 保持 canonical semantic value。 -/
theorem serialization_round_trip (tokens : List CanonicalToken) :
    parseTokens (serializeTokens tokens) = tokens := by
  induction tokens with
  | nil => rfl
  | cons t ts ih =>
    simp [serializeTokens, parseTokens, ih]

/-- 中文证明：round-trip 保持每个 token 的键与值（逐字段忠实）。 -/
theorem serialization_preserves_fields (t : CanonicalToken) :
    parseTokens (serializeTokens [t]) = [t] := by
  exact serialization_round_trip [t]

/-- 中文说明：内容绑定：digest 对 canonical token 序列的绑定只断言绑定关系。 -/
def TokensDigestBinding (d : ContentDigest) (tokens : List CanonicalToken)
    (canonicalSubject : String) : Prop :=
  DigestBinding d canonicalSubject

/-- 中文证明：同一 canonical subject 的两个绑定摘要一致。 -/
theorem tokens_binding_consistent {d1 d2 : ContentDigest}
    {tokens : List CanonicalToken} {subject : String}
    (h1 : TokensDigestBinding d1 tokens subject)
    (h2 : TokensDigestBinding d2 tokens subject) :
    d1.hex = d2.hex := by
  dsimp [TokensDigestBinding, DigestBinding] at h1 h2
  rw [h1, h2]

end JurisLean
