---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, Sequences, TLC

CONSTANT Ingredients
CONSTANT Offers

\* =============================================================================
\* State variables
\* =============================================================================
VARIABLES smokers, offer

\* smokers: a mapping from each ingredient to a boolean indicating whether the
\*          smoker that owns that ingredient is currently smoking.
\* offer:   the current set of ingredients placed on the table.  It is either a
\*          non‑empty subset from Offers (meaning no one is smoking) or {} (meaning
\*          exactly one smoker is currently smoking).
VARIABLES smokers, offer

\* =============================================================================
\* Helper definitions
\* =============================================================================
AllIngredients == Ingredients

\* A smoker can smoke exactly when the current offer combined with his own
\* ingredient yields the complete set of ingredients.
CanSmoke(i) == i \in Ingredients /\ offer # {} /\ (offer \cup {i}) = AllIngredients

\* The set of smokers that are currently smoking.
SmokingSmokers == { i \in Ingredients : smokers[i] }

\* =============================================================================
\* Type correctness invariant
\* =============================================================================
TypeOK ==
    /\ smokers \in [Ingredients -> BOOLEAN]
    /\ offer \in SUBSET Ingredients

\* =============================================================================
\* Safety invariant: at most one smoker is smoking at any time.
\* =============================================================================
AtMostOne ==
    Cardinality SmokingSmokers <= 1

\* =============================================================================
\* Initial predicate
\* =============================================================================
Init ==
    /\ smokers = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* =============================================================================
\* Actions
\* =============================================================================
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
          /\ CanSmoke(i)
          /\ smokers' = [smokers EXCEPT ![i] = TRUE]
          /\ offer' = {}
    /\ UNCHANGED << >>

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
          /\ smokers[i] = TRUE
          /\ smokers' = [smokers EXCEPT ![i] = FALSE]
          /\ offer' \in Offers
    /\ UNCHANGED << >>

Next ==
    StartSmoking \/ StopSmoking

\* =============================================================================
\* Specification
\* =============================================================================
Spec == Init /\ [][Next]_<<smokers, offer>>

\* =============================================================================
\* The properties that the .cfg file will refer to
\* =============================================================================
PROPERTIES Spec

\* The invariants that the .cfg file will refer to
\* (they are defined above)
\* =============================================================================

====