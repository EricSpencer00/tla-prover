---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES smoking, offer

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
AllIngredients == Ingredients

\* ----------------------------------------------------------------------
\* Type definitions (for readability)
\* ----------------------------------------------------------------------
Smoking == [i \in Ingredients |-> BOOLEAN]
Offer   == SUBSET Ingredients

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
          /\ i \notin offer               \* i is the missing ingredient
          /\ smoking[i] = FALSE
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

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<smoking, offer>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smoking \in Smoking
    /\ offer \in SUBSET Ingredients

AtMostOne ==
    Cardinality({ i \in Ingredients : smoking[i] }) <= 1

\* ----------------------------------------------------------------------
\* Theorems (optional, but keep the module self‑contained)
\* ----------------------------------------------------------------------
THEOREM Spec => []AtMostOne

====