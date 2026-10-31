import JurisLean.Candidates.U06_4ConditionalInformation20261031

noncomputable section

open scoped BigOperators

/-!
Only the remaining original-06 finite examples.

Cash is evaluated at one fixed currency, unit and valuation time. The map
resolve is a supplied, resolved semantic payment identity, not a string key
or a claim that real entity resolution has been established.

Legal permission, physical feasibility, utility choice and identified outcome
laws remain declared inputs. No probability distribution over legal branches
is introduced here.
-/

namespace JurisLean.Candidates.U06_OriginalFiniteExamples20261031

/--
L91: adding a reference to an already represented semantic cash event does
not add cash. This is about alias insertion, not another actual payment.
-/
theorem adding_resolved_alias_preserves_cash
    {R E : Type*} [DecidableEq R] [DecidableEq E]
    (references : Finset R) (resolve : R → E) (cash : E → ℚ)
    (alias : R)
    (alreadyRepresented : resolve alias ∈ references.image resolve) :
    (∑ e ∈ (insert alias references).image resolve, cash e) =
      ∑ e ∈ references.image resolve, cash e := by
  rw [Finset.image_insert, Finset.insert_eq_of_mem alreadyRepresented]

/--
L91: three labels for one payment of 6 retain cash 6. Summing labels instead
would give 18. Two different actual payment identities of 6 retain cash 12.
The shared relationship is intentionally not the identity being deduplicated.
-/
theorem labels_and_actual_repayments_differ :
    (∑ e ∈ ({0, 1, 2} : Finset Nat).image (fun _ => (0 : Nat)),
      (6 : ℚ)) = 6 ∧
    (∑ _e ∈ ({0, 1, 2} : Finset Nat), (6 : ℚ)) = 18 ∧
    (∑ _e ∈ ({0, 1} : Finset Nat), (6 : ℚ)) = 12 := by
  norm_num

/-- L99: success probability alone does not order expected net cash. -/
theorem higher_success_probability_can_have_lower_expected_cash :
    (1 / 2 : ℝ) < 9 / 10 ∧
    ((9 / 10 : ℝ) * 1 + (1 - 9 / 10) * 0 - 0) <
      ((1 / 2 : ℝ) * 4 + (1 - 1 / 2) * 0 - 0) := by
  norm_num

/--
L99 utility, in utility units. The example's initial wealth is w=0 and its
wealth domain is [0,10].
-/
def concaveUtility (wealth : ℝ) : ℝ :=
  20 * wealth - wealth ^ 2

/-- The defining strict Jensen inequality on the declared wealth domain. -/
theorem concaveUtility_strict_jensen
    (x y a b : ℝ)
    (_domainX : x ∈ Set.Icc (0 : ℝ) 10)
    (_domainY : y ∈ Set.Icc (0 : ℝ) 10)
    (different : x ≠ y)
    (positiveA : 0 < a) (positiveB : 0 < b)
    (total : a + b = 1) :
    a * concaveUtility x + b * concaveUtility y <
      concaveUtility (a * x + b * y) := by
  have gap :
      concaveUtility (a * x + b * y) -
        (a * concaveUtility x + b * concaveUtility y) =
          a * b * (x - y) ^ 2 := by
    have hb : b = 1 - a := by linarith
    rw [hb]
    unfold concaveUtility
    ring
  have positiveGap :
      0 < a * b * (x - y) ^ 2 :=
    mul_pos (mul_pos positiveA positiveB)
      (sq_pos_of_ne_zero (sub_ne_zero.mpr different))
  linarith

/--
L99: with w=0, all terminal wealths are in [0,10]. Certain cash 5 and
cash 0/10 with probabilities 1/2 each have EV 5, but their expected
utilities are 75 and 50 respectively.
-/
theorem same_expected_cash_different_concave_utility :
    (0 : ℝ) ∈ Set.Icc (0 : ℝ) 10 ∧
    (5 : ℝ) ∈ Set.Icc (0 : ℝ) 10 ∧
    (10 : ℝ) ∈ Set.Icc (0 : ℝ) 10 ∧
    ((1 / 2 : ℝ) * 0 + (1 / 2 : ℝ) * 10) = 5 ∧
    concaveUtility (0 + 5) = 75 ∧
    ((1 / 2 : ℝ) * concaveUtility (0 + 0) +
      (1 / 2 : ℝ) * concaveUtility (0 + 10)) = 50 ∧
    ((1 / 2 : ℝ) * concaveUtility (0 + 0) +
      (1 / 2 : ℝ) * concaveUtility (0 + 10)) <
      concaveUtility (0 + 5) := by
  norm_num [Set.mem_Icc, concaveUtility]

/--
L107's fixed finite model: three common feasible policies and two legal
branches. Each branch's value may be realized by a deterministic terminal
law. The branches themselves have no prior.
-/
def branchValue (policy : Fin 3) (branch : Bool) : ℝ :=
  if policy = 0 then
    if branch then 0 else 10
  else if policy = 1 then
    if branch then 10 else 0
  else 4

/--
The branch optima are policy 0 and policy 1 respectively; each is unique.
The policy must be selected on the common policy set, not after reading
which legal branch is true.
-/
theorem distinct_unique_branch_optima (policy : Fin 3) :
    branchValue policy false ≤ branchValue 0 false ∧
    (branchValue policy false = branchValue 0 false ↔ policy = 0) ∧
    branchValue policy true ≤ branchValue 1 true ∧
    (branchValue policy true = branchValue 1 true ↔ policy = 1) := by
  fin_cases policy <;> norm_num [branchValue]

/--
The unique maximin policy is policy 2, with value 4. Both individual
branch-optimal policies have worst-branch value 0.
-/
theorem unique_robust_policy_differs_from_both_branch_optima
    (policy : Fin 3) :
    min (branchValue policy false) (branchValue policy true) ≤ 4 ∧
    (min (branchValue policy false) (branchValue policy true) = 4 ↔
      policy = 2) ∧
    min (branchValue 0 false) (branchValue 0 true) = 0 ∧
    min (branchValue 1 false) (branchValue 1 true) = 0 ∧
    branchValue 2 false = 4 ∧ branchValue 2 true = 4 := by
  fin_cases policy <;> norm_num [branchValue]

end JurisLean.Candidates.U06_OriginalFiniteExamples20261031
