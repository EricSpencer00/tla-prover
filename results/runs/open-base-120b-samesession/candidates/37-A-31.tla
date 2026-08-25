---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
TypeOK == 
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in SUBSET Ingredients

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
        /\ i \notin offer
        /\ smoking[i] = FALSE
        /\ smoking' = [smoking EXCEPT ![i] = TRUE]
        /\ offer' = {}
        /\ \A j \in Ingredients : j # i => smoking'[j] = smoking[j]

StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients :
        /\ smoking[i] = TRUE
        /\ smoking' = [smoking EXCEPT ![i] = FALSE]
        /\ offer' \in Offers
        /\ \A j \in Ingredients : j # i => smoking'[j] = smoking[j]

Next == \/ StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<smoking, offer>> /\ WF_<<smoking, offer>>(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
AtMostOne == Cardinality({ i \in Ingredients : smoking[i] }) <= 1

====