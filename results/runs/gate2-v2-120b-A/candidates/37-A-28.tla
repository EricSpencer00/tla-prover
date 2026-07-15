---- MODULE CigaretteSmokers ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Ingredients, Offers

\* The three ingredients are assumed to be distinct; this is checked by TypeOK.
\* Each offer is a subset of Ingredients that is missing exactly one ingredient.
\* The constant Offers is expected to be the set of all such subsets.

VARIABLES smoking, offer

\*-----------------------------------------------------------------
\* Types
\*-----------------------------------------------------------------
SmokingType == [i \in Ingredients |-> BOOLEAN]

TypeOK ==
    /\ smoking \in SmokingType
    /\ offer \in Offers

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\*-----------------------------------------------------------------
\* Actions
\*-----------------------------------------------------------------
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
           /\ smoking[i] = FALSE
           /\ i \notin offer               \* i is the missing ingredient
           /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
           /\ smoking[i] = TRUE
           /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ offer' \in Offers

Next ==
    \/ StartSmoking
    \/ StopSmoking

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_<<smoking, offer>>

\*-----------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking at any time
\*-----------------------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : smoking[i] }) <= 1

\*-----------------------------------------------------------------
\* Theorem (optional, for readability)
\*-----------------------------------------------------------------
THEOREM Spec => []AtMostOne

====