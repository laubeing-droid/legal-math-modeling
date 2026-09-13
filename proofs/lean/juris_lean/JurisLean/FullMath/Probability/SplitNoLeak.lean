import JurisLean.FullMath.Core.Foundations

/-!
P11 — One declared win-rate target and leakage-free splits: every row
carries the same target definition; a row may enter a part only when its
feature time strictly precedes its label time; cluster membership is a
deterministic function of the cluster id, so no cluster crosses parts;
and a time-violating row appears in no part at all.
-/

namespace JurisLean.FullMath.Probability

/-- A modeling row: cluster id, feature time, label time, binary target. -/
structure Row where
  cluster : ℕ
  featT : ℕ
  labelT : ℕ
  y : Bool

/-- The single declared win-rate target of a row. -/
def targetOf (r : Row) : Bool := r.y

/-- Rows whose feature is observed strictly before the label time. -/
def legalRows (data : List Row) : List Row :=
  data.filter (fun r => decide (r.featT < r.labelT))

/-- P11(a): the enforced split only keeps rows whose feature time precedes
the label time — no label-into-feature leakage. -/
theorem time_order_enforced (data : List Row) (r : Row)
    (h : r ∈ legalRows data) : r.featT < r.labelT := by
  simp only [legalRows, List.mem_filter] at h
  exact of_decide_eq_true h.2

/-- Cluster tag: a deterministic function of the cluster id only. -/
def tagOf (r : Row) : Bool := decide (r.cluster % 2 = 0)

/-- P11(b): rows in one cluster receive one tag — no cluster crosses
parts. -/
theorem no_cluster_cross (data : List Row) (r1 r2 : Row)
    (h1 : r1 ∈ legalRows data) (h2 : r2 ∈ legalRows data)
    (hcl : r1.cluster = r2.cluster) : tagOf r1 = tagOf r2 := by
  simp only [tagOf]
  rw [hcl]

/-- Parts are defined by the tag. -/
def partRows (b : Bool) (data : List Row) : List Row :=
  (legalRows data).filter (fun r => decide (tagOf r = b))

/-- P11(c): every part row is a legal row carrying the declared target —
the same target definition across all parts. -/
theorem part_target_preserved (data : List Row) (b : Bool) (r : Row)
    (hr : r ∈ partRows b data) : r ∈ legalRows data ∧ targetOf r = r.y := by
  simp only [partRows, List.mem_filter] at hr
  exact ⟨hr.2.1, rfl⟩

/-- P11(d): every legal row lands in its own part. -/
theorem parts_cover (data : List Row) (r : Row) (hr : r ∈ legalRows data) :
    r ∈ partRows (tagOf r) data := by
  simp only [partRows, List.mem_filter]
  exact ⟨hr, rfl⟩

/-- P11(e) adverse: a time-violating row appears in no part. -/
theorem illegal_row_in_no_part (data : List Row) (r : Row)
    (hle : r.labelT ≤ r.featT) (b : Bool) :
    r ∈ partRows b data → False := by
  intro h
  have hlegal := (part_target_preserved data b r h).1
  have hord := time_order_enforced data r hlegal
  omega

end JurisLean.FullMath.Probability
