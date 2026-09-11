import Mathlib

namespace JurisLean.ULM.UnifiedV21

-- Generated from the same field catalog as v21.context.ContextKey.
structure ContextKey where
  request : String
  jurisdiction : String
  event_time : String
  decision_time : String
  procedure : String
  stage : String
  party : String
  issue : String
  scenario : String
  profile : String
  law_version : String
  interpretation : String
  rulepack_version : String
  engine_version : String
  model_version : String
  evidence_version : String
  target : String
  semantic_scope : String
  assumptions : List String
  max_depth : Nat
  deriving DecidableEq

def toWire (c : ContextKey) : List String × List String × Nat :=
  ([c.request, c.jurisdiction, c.event_time, c.decision_time, c.procedure, c.stage, c.party, c.issue, c.scenario, c.profile, c.law_version, c.interpretation, c.rulepack_version, c.engine_version, c.model_version, c.evidence_version, c.target, c.semantic_scope], c.assumptions, c.max_depth)

theorem context_wire_injective : Function.Injective toWire := by
  intro a b h
  cases a
  cases b
  simp_all [toWire]

theorem context_model_preserved {a b : ContextKey} (h : toWire a = toWire b) :
    a.model_version = b.model_version := by
  exact congrArg ContextKey.model_version (context_wire_injective h)

theorem context_issue_preserved {a b : ContextKey} (h : toWire a = toWire b) :
    a.issue = b.issue := by
  exact congrArg ContextKey.issue (context_wire_injective h)

theorem context_join_transitive {a b c : ContextKey} (hab : a = b) (hbc : b = c) :
    a = c := hab.trans hbc

end JurisLean.ULM.UnifiedV21
