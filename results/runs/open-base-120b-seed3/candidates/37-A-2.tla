---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokerState, offer

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ smokerState \in [Ingredients -> BOOLEAN]
    /\ (offer \in Offers) \/ (offer = {})

\* ----------------------------------------------------------------------
\* Initial state: no one is smoking and the dealer places a valid offer
Init ==
    /\ smokerState = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking
StartSmoking ==
    /\ offer \in Offers                \* an offer is present
    /\ \E i \in Ingredients :
          /\ i \notin offer            \* the missing ingredient belongs to this smoker
          /\ smokerState[i] = FALSE
          /\ smokerState' = [smokerState EXCEPT ![i] = TRUE]
          /\ offer' = {}

\* ----------------------------------------------------------------------
\* Action: the currently smoking smoker stops and a new offer is placed
StopSmoking ==
    /\ offer = {}                       \* a smoker is currently smoking
    /\ \E i \in Ingredients :
          /\ smokerState[i] = TRUE
          /\ smokerState' = [smokerState EXCEPT ![i] = FALSE]
          /\ offer' \in Offers

\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

vars == <<smokerState, offer>>

\* ----------------------------------------------------------------------
\* Specification with weak fairness on the whole next-state relation
Spec == Init /\ [] [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Safety: at most one smoker is smoking at any time
AtMostOne == Cardinality({ i \in Ingredients : smokerState[i] }) <= 1

====