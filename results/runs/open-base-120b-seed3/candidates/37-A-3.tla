---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANT Ingredients, Offers

VARIABLES smoking, offer

\* ----------------------------------------------------------------------
\* State predicates
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in (Offers \cup {{}})

AtMostOne ==
    Cardinality({ i \in Ingredients : smoking[i] }) <= 1

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
          /\ i \notin offer                 \* the missing ingredient
          /\ smoking[i] = FALSE
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
          /\ offer'   = {}
          /\ \A j \in Ingredients :
                (j # i) => smoking'[j] = smoking[j]

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
          /\ smoking[i] = TRUE
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
          /\ offer'   \in Offers
          /\ \A j \in Ingredients :
                (j # i) => smoking'[j] = smoking[j]

Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<smoking, offer>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================