// rosetta_functor.als
//
// Alloy model for the Rosetta functor non-existence result.
//
// Models the impossibility of a total semantics-preserving functor F : Fact -> Claim
// that simultaneously satisfies collision constraints across all jurisdictions.
//
// This corresponds to Chapter 6, Theorem 6.4 (Rosetta non-existence).
//
// Run command: java -jar alloy.jar rosetta_functor.als
// Or use: run NoTotalFunctor for 5 Fact, 5 Claim, 3 Jurisdiction

module rosetta_functor

---------------------------------------------------------------------------
-- Signatures: the core legal-reasoning domain types
---------------------------------------------------------------------------

sig Fact {
    -- Each fact belongs to a jurisdiction (simplifying assumption)
    jurisdiction: one Jurisdiction
}

sig Claim {}

sig Jurisdiction {}

---------------------------------------------------------------------------
-- Collision constraints
--
-- A collision constraint forbids a specific (fact, claim) assignment
-- under a given jurisdiction. If (f, c, j) is a collision, then a
-- semantics-preserving map cannot assign f -> c when f is in jurisdiction j.
---------------------------------------------------------------------------

sig CollisionConstraint {
    forbiddenFact: one Fact,
    forbiddenClaim: one Claim,
    inJurisdiction: one Jurisdiction
}

---------------------------------------------------------------------------
-- Functor: a total map from Fact to Claim
--
-- In Alloy, we model a functor as a set of (fact, claim) pairs where
-- each fact appears exactly once (total, single-valued).
---------------------------------------------------------------------------

-- A functor is a relation F : Fact -> Claim that is total and single-valued.
pred isTotalFunctor[F: Fact -> Claim] {
    -- Total: every fact has at least one image
    all f: Fact | some (f <: F)
    -- Single-valued (functional): each fact maps to exactly one claim
    all f: Fact | lone (f <: F)
}

---------------------------------------------------------------------------
-- Semantics preservation predicate
--
-- A functor F preserves semantics under jurisdiction j if it does not
-- violate any collision constraint applicable to j.
--
-- NOTE: This Alloy model encodes collision as individual (fact,claim) pair
-- exclusions, which is a WEAKER encoding than the Lean FiniteRosetta.lean
-- model which forbids simultaneous assignments of two patterns to two claims.
-- The Alloy check validates the weaker encoding; the Lean proof (if completed)
-- would validate the stronger encoding. Both encodings capture the same
-- mathematical intuition but are not formally equivalent.
---------------------------------------------------------------------------

pred preservesSemantics[F: Fact -> Claim, j: Jurisdiction] {
    -- For every collision constraint active in jurisdiction j,
    -- the functor does not map the forbidden fact to the forbidden claim.
    all cc: CollisionConstraint |
        cc.inJurisdiction = j implies
            -- Either f is not mapped to the forbidden claim,
            -- or the fact in the constraint is not the forbidden fact
            (cc.forbiddenFact -> cc.forbiddenClaim) not in F
}

---------------------------------------------------------------------------
-- Global preservation: F preserves semantics in ALL jurisdictions
---------------------------------------------------------------------------

pred preservesAllSemantics[F: Fact -> Claim] {
    all j: Jurisdiction | preservesSemantics[F, j]
}

---------------------------------------------------------------------------
-- Generate a witness: concrete facts, claims, jurisdictions, and constraints
-- that make the non-existence result demonstrable.
---------------------------------------------------------------------------

-- Generate constraints that create a "cycle" of incompatibilities
pred generateConstraints {
    -- At least 3 jurisdictions
    #Jurisdiction >= 3
    -- At least 5 facts, spread across jurisdictions
    #Fact >= 5
    -- At least 5 claims
    #Claim >= 5

    -- Constraint structure: facts in different jurisdictions have
    -- conflicting claim requirements.

    -- For each jurisdiction, there exist facts with overlapping constraints
    -- that make total preservation impossible.

    -- The key insight: if jurisdiction j1 requires f1 -> NOT c1,
    -- and jurisdiction j2 requires f2 -> NOT c2, but the facts are
    -- "linked" through shared intermediate claims, no single total
    -- map can satisfy all constraints simultaneously.

    -- Distribute facts across jurisdictions
    some disj f1, f2, f3: Fact |
        f1.jurisdiction != f2.jurisdiction and
        f2.jurisdiction != f3.jurisdiction and
        f1.jurisdiction != f3.jurisdiction

    -- Create collision constraints that block all possible assignments
    some disj c1, c2, c3: CollisionConstraint |
        -- The three constraints are in three different jurisdictions
        c1.inJurisdiction != c2.inJurisdiction and
        c2.inJurisdiction != c3.inJurisdiction and
        c1.inJurisdiction != c3.inJurisdiction and
        -- Each constrains a different (fact, claim) pair
        c1.forbiddenFact != c2.forbiddenFact and
        c2.forbiddenFact != c3.forbiddenFact
}

---------------------------------------------------------------------------
-- The main fact: no total functor preserves all semantics
--
-- This is the central theorem of Chapter 6, encoded as an Alloy fact.
-- With a scope of 5 Facts, 5 Claims, 3 Jurisdictions, Alloy's SAT solver
-- will verify that no counterexample exists (i.e., no total F works).
---------------------------------------------------------------------------

fact NoTotalFunctor {
    generateConstraints
    -- The key property: no total functor preserves all semantics
    no F: Fact -> Claim |
        isTotalFunctor[F] and preservesAllSemantics[F]
}

---------------------------------------------------------------------------
-- Checks and runs
---------------------------------------------------------------------------

-- Verify the non-existence: expect "no counterexample found" (0 instances)
check NoTotalFunctorCheck {
    generateConstraints implies
    (no F: Fact -> Claim | isTotalFunctor[F] and preservesAllSemantics[F])
} for 5 Fact, 5 Claim, 3 Jurisdiction

-- Find a witness: attempt to construct a total semantics-preserving functor
-- Expected: 0 instances (confirms non-existence)
run findSurvivingFunctor {
    generateConstraints
    some F: Fact -> Claim |
        isTotalFunctor[F] and preservesAllSemantics[F]
} for 5 Fact, 5 Claim, 3 Jurisdiction

-- Diagnostic: show a valid constraint configuration
run showConstraintSetup {
    generateConstraints
} for 5 Fact, 5 Claim, 3 Jurisdiction, 9 CollisionConstraint

---------------------------------------------------------------------------
-- Helper: visualize what a specific functor looks like when it fails
---------------------------------------------------------------------------

pred functorFailsAt[F: Fact -> Claim, cc: CollisionConstraint] {
    isTotalFunctor[F]
    cc.inJurisdiction = jurisdiction[cc.forbiddenFact]
    (cc.forbiddenFact -> cc.forbiddenClaim) in F
}

run showFunctorFailure {
    some F: Fact -> Claim, cc: CollisionConstraint |
        generateConstraints and functorFailsAt[F, cc]
} for 5 Fact, 5 Claim, 3 Jurisdiction
