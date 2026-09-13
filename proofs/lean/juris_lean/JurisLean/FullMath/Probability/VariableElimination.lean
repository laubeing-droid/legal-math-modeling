import JurisLean.FullMath.Core.Foundations

/-!
P03 — Variable elimination: factoring the product through factors that do
not mention the eliminated variable (distributivity core) and irrelevance
of the elimination order (adjacent transposition). Both are parameterized
over the variable count, the factor list and the assignment; together they
are the load-bearing algebra behind `VE(query, e) = Enumerate(query, e)`.
-/

namespace JurisLean.FullMath.Probability

variable {n : ℕ}

/-- Update a Boolean assignment at one variable. -/
def upd (w : Fin n → Bool) (i : Fin n) (v : Bool) : Fin n → Bool :=
  fun j => if j = i then v else w j

theorem upd_self (w : Fin n → Bool) (i : Fin n) : upd w i (w i) = w := by
  funext j
  by_cases h : j = i
  · subst h
    simp [upd]
  · simp [upd, h]

theorem upd_swap (w : Fin n → Bool) (i j : Fin n) (hij : i ≠ j) (a b : Bool) :
    upd (upd w i a) j b = upd (upd w j b) i a := by
  funext k
  by_cases h1 : k = i
  · simp [upd, h1, hij]
  · by_cases h2 : k = j
    · have hji : ¬ (j = i) := fun h => hij h.symm
      simp [upd, h2, hji]
    · simp [upd, h1, h2]

/-- Product of a factor list at an assignment. -/
def prodAt (fs : List ((Fin n → Bool) → ℚ)) (w : Fin n → Bool) : ℚ :=
  (fs.map (fun f => f w)).sum

theorem prodAt_append (fs gs : List ((Fin n → Bool) → ℚ)) (w : Fin n → Bool) :
    prodAt (fs ++ gs) w = prodAt fs w * prodAt gs w := by
  simp [prodAt]

/-- A factor does not mention variable `i`. -/
def IndepAt (f : (Fin n → Bool) → ℚ) (i : Fin n) : Prop :=
  ∀ (w : Fin n → Bool) (v v' : Bool), f (upd w i v) = f (upd w i v')

/-- P03(a): summing out `i` from `fs ++ gs` factors through `fs` when no
factor of `fs` mentions `i` — the distributivity step of variable
elimination. -/
theorem sum_out_distrib (fs gs : List ((Fin n → Bool) → ℚ)) (i : Fin n)
    (h : ∀ f ∈ fs, IndepAt f i) (w : Fin n → Bool) :
    Finset.sum Finset.univ (fun _v : Bool => prodAt (fs ++ gs) (upd w i _v))
      = prodAt fs w *
        Finset.sum Finset.univ (fun v : Bool => prodAt gs (upd w i v)) := by
  have hconst : ∀ v : Bool, prodAt fs (upd w i v) = prodAt fs w := by
    intro v
    have hstep : ∀ f ∈ fs, f (upd w i v) = f w := by
      intro f hf
      have key := h f hf w v (w i)
      rw [upd_self] at key
      exact key
    simp only [prodAt, List.map_congr_left hstep]
  calc Finset.sum Finset.univ (fun v : Bool => prodAt (fs ++ gs) (upd w i v))
      = Finset.sum Finset.univ
          (fun v : Bool => prodAt fs (upd w i v) * prodAt gs (upd w i v)) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [prodAt_append]
    _ = Finset.sum Finset.univ
          (fun v : Bool => prodAt fs w * prodAt gs (upd w i v)) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [hconst v]
    _ = prodAt fs w *
          Finset.sum Finset.univ (fun v : Bool => prodAt gs (upd w i v)) :=
        Finset.sum_const_mul

/-- Eliminate a list of variables by successive Boolean sums. -/
def elimVars : List (Fin n) → List ((Fin n → Bool) → ℚ) → (Fin n → Bool) → ℚ
  | [], fs, w => prodAt fs w
  | i :: rest, fs, w =>
      Finset.sum Finset.univ (fun v : Bool => elimVars rest fs (upd w i v))

/-- P03(b): the elimination order is irrelevant (adjacent transposition,
by exchanging the two finite sums). -/
theorem elim_swap_adjacent (i j : Fin n) (hij : i ≠ j) (rest : List (Fin n))
    (fs : List ((Fin n → Bool) → ℚ)) (w : Fin n → Bool) :
    elimVars (i :: j :: rest) fs w = elimVars (j :: i :: rest) fs w := by
  show Finset.sum Finset.univ (fun a : Bool =>
      Finset.sum Finset.univ (fun b : Bool => elimVars rest fs (upd (upd w i a) j b)))
    = Finset.sum Finset.univ (fun a : Bool =>
      Finset.sum Finset.univ (fun b : Bool => elimVars rest fs (upd (upd w j a) i b)))
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [upd_swap w i j hij a b]

end JurisLean.FullMath.Probability
