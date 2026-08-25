---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokerState, offer

\* ----------------------------------------------------------------------
\* Helper definition for the set of currently smoking smokers
\* ----------------------------------------------------------------------
SmokingSmokers == { i \in Ingredients : smokerState[i] }

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smokerState \in [Ingredients -> BOOLEAN]
    /\ (offer \in Offers) \/ (offer = {})

\* ----------------------------------------------------------------------
\* Safety: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    Cardinality(SmokingSmokers) <= 1

\* ----------------------------------------------------------------------
\* Initial state: no one is smoking, dealer places a nondeterministic offer
\* ----------------------------------------------------------------------
Init ==
    /\ smokerState = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ offer # {}                                    \* there is an offer on the table
    /\ \E i \in Ingredients :
          /\ i \notin offer                         \* the missing ingredient
          /\ smokerState[i] = FALSE                \* not already smoking
          /\ (offer \cup {i}) = Ingredients         \* together they form the full set
          /\ smokerState' = [smokerState EXCEPT ![i] = TRUE]
          /\ offer' = {}
          
\* ----------------------------------------------------------------------
\* Action: the currently smoking smoker stops, dealer puts a new offer
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ offer = {}                                    \* a smoker is currently smoking
    /\ \E i \in Ingredients :
          /\ smokerState[i] = TRUE                  \* the smoker that is smoking
          /\ smokerState' = [smokerState EXCEPT ![i] = FALSE]
          /\ offer' \in Offers

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification: initial condition, temporal evolution, weak fairness
\* ----------------------------------------------------------------------
vars == <<smokerState, offer>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

=============================================================================