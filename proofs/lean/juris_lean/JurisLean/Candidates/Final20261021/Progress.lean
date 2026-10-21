import JurisLean.Candidates.Final20261021.Interfaces

namespace JurisLean.Candidates.Final20261021.Progress

inductive RankedPath {S : Type} (rank : S → Nat) : S → Nat → S → Prop where
  | nil (s : S) : RankedPath rank s 0 s
  | cons {s t u : S} {n : Nat} : rank t + 1 ≤ rank s →
      RankedPath rank t n u → RankedPath rank s (n + 1) u

theorem u10_3_rank_bounds_steps {S : Type} (rank : S → Nat) {s t : S} {n : Nat}
    (h : RankedPath rank s n t) : n ≤ rank s := by
  induction h with
  | nil s => omega
  | cons decrease rest ih => omega

theorem u10_3_simulation_length (lengths : List Nat) (K : Nat)
    (bounded : ∀ n ∈ lengths, n ≤ K) : lengths.sum ≤ lengths.length * K := by
  induction lengths with
  | nil => simp
  | cons k ks ih =>
      have hk := bounded k (by simp)
      have hs := ih (fun x hx => bounded x (by simp [hx]))
      simp only [List.sum_cons, List.length_cons]
      nlinarith

theorem multistep_simulation_not_one_step : ([2, 2] : List Nat).sum > [2, 2].length := by decide

theorem two_cycle_has_no_strict_rank (rank : Bool → Nat) :
    ¬ (rank true < rank false ∧ rank false < rank true) := by omega

end JurisLean.Candidates.Final20261021.Progress
