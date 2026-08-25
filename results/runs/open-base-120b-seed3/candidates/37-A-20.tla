---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, Offer

\* --------------------------------------------------------------
\* Type constraints
\* --------------------------------------------------------------

TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ Offer   \in SUBSET Ingredients

\* --------------------------------------------------------------
\* Initial state
\* --------------------------------------------------------------

Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ Offer   \in Offers

\* --------------------------------------------------------------
\* Actions
\* --------------------------------------------------------------

StartSmoking ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
          /\ i \notin Offer               \* the missing ingredient
          /\ smoking[i] = FALSE
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
          /\ Offer'   = {}
          /\ \A j \in Ingredients :
                (j # i) => smoking'[j] = smoking[j]

StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
          /\ smoking[i] = TRUE
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
          /\ Offer'   \in Offers
          /\ \A j \in Ingredients :
                (j # i) => smoking'[j] = smoking[j]

Next == StartSmoking \/ StopSmoking

\* --------------------------------------------------------------
\* Specification
\* --------------------------------------------------------------

vars == <<smoking, Offer>>

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* --------------------------------------------------------------
\* Safety invariants
\* --------------------------------------------------------------

AtMostOne ==
    \A i, j \in Ingredients :
        (smoking[i] /\ smoking[j]) => i = j

\* --------------------------------------------------------------
\* End of module
\* --------------------------------------------------------------

====