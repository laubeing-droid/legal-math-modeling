import Mathlib
import JurisLean.BusinessRoot.Semantics

/-!
ROOT03 (part 1) — Real guard-condition stack machine and its reflection.

The Python reference compiles a formula to a postfix opcode list and executes a
stack interpreter that is structurally different from the recursive denotation.
This file mirrors that machine and proves the two semantics coincide for every
guard and every scenario — by induction on the guard, not by testing examples.
-/

namespace JurisLean.BusinessRoot

/-- Postfix opcodes of the compiled guard program. -/
inductive Op where
  | pushTrue
  | pushFalse
  | load (name : String)
  | notI
  | andI
  | orI

def compile : Guard → List Op
  | .truthy => [.pushTrue]
  | .falsey => [.pushFalse]
  | .atom a => [.load a]
  | .neg a => compile a ++ [.notI]
  | .both a b => compile a ++ compile b ++ [.andI]
  | .either a b => compile a ++ compile b ++ [.orI]

/-- Stack interpreter over a scenario; malformed stacks evaluate to the empty
stack, which can never arise for a compiled program (see `machine_reflection`). -/
def exec (keys : List String) (vals : World) : List Op → List Bool → List Bool
  | [], s => s
  | .pushTrue :: k, s => exec keys vals k (true :: s)
  | .pushFalse :: k, s => exec keys vals k (false :: s)
  | .load a :: k, s => exec keys vals k (lookupVal keys vals a :: s)
  | .notI :: k, s =>
      match s with
      | x :: s' => exec keys vals k ((!x) :: s')
      | [] => []
  | .andI :: k, s =>
      match s with
      | x :: y :: s' => exec keys vals k ((y && x) :: s')
      | _ => []
  | .orI :: k, s =>
      match s with
      | x :: y :: s' => exec keys vals k ((y || x) :: s')
      | _ => []

/-- The specification of the machine state after compiling one guard: its
denotation sits on top of whatever stack came before. -/
def stackOf (keys : List String) (vals : World) (g : Guard) (s : List Bool) : List Bool :=
  g.denote keys vals :: s

theorem exec_compile (keys : List String) (vals : World) (g : Guard) :
    ∀ (c : List Op) (s : List Bool),
      exec keys vals (compile g ++ c) s = exec keys vals c (stackOf keys vals g s) := by
  induction g with
  | truthy => intro c s; simp [compile, exec, stackOf, Guard.denote]
  | falsey => intro c s; simp [compile, exec, stackOf, Guard.denote]
  | atom a => intro c s; simp [compile, exec, stackOf, Guard.denote]
  | neg a ih =>
      intro c s
      rw [List.append_assoc, ih ([.notI] ++ c) s]
      simp [exec, stackOf, Guard.denote]
  | both a b iha ihb =>
      intro c s
      rw [List.append_assoc, List.append_assoc,
        iha (compile b ++ ([.andI] ++ c)) s,
        ihb ([.andI] ++ c) (stackOf keys vals a s)]
      simp [exec, stackOf, Guard.denote]
  | either a b iha ihb =>
      intro c s
      rw [List.append_assoc, List.append_assoc,
        iha (compile b ++ ([.orI] ++ c)) s,
        ihb ([.orI] ++ c) (stackOf keys vals a s)]
      simp [exec, stackOf, Guard.denote]

/-- Reflection: running the compiled program of `g` on the empty stack leaves
exactly the denotation of `g`. The interpreter and the recursive semantics
agree for every guard and every scenario. -/
theorem machine_reflection (keys : List String) (vals : World) (g : Guard) :
    exec keys vals (compile g) [] = [g.denote keys vals] := by
  have h := exec_compile keys vals g [] []
  simpa [exec, stackOf] using h

/-- Evaluation of the whole machine equals the boolean guard semantics used by
the independent scenario domain. -/
theorem machine_boolean (keys : List String) (vals : World) (g : Guard) :
    exec keys vals (compile g) [] = [true] ↔ g.denote keys vals = true := by
  constructor
  · intro h
    rw [machine_reflection keys vals g] at h
    simpa using h
  · intro h
    rw [machine_reflection keys vals g, h]

end JurisLean.BusinessRoot
