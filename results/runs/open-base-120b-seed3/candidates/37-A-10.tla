---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokerStatus, offer

\* ----------------------------------------------------------------------
\*  Helper definition of the state vector
\* ----------------------------------------------------------------------
vars == << smokerStatus, offer >>

\* ----------------------------------------------------------------------
\*  Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smokerStatus \in [Ingredients -> BOOLEAN]
    /\ offer \in (Offers \cup { {} })

\* ----------------------------------------------------------------------
\*  At most one smoker may be smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : smokerStatus[i] }) <= 1

\* ----------------------------------------------------------------------
\*  Initial state: nobody is smoking and the dealer places a valid offer
\* ----------------------------------------------------------------------
Init ==
    /\ smokerStatus = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* ----------------------------------------------------------------------
\*  Action: a smoker starts smoking
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ offer # {}                     \* an offer is present
    /\ offer \in Offers               \* it is a valid offer (missing exactly one)
    /\ \E i \in Ingredients :
          /\ i \notin offer
          /\ smokerStatus' = [j \in Ingredients |-> IF j = i THEN TRUE ELSE FALSE]
          /\ offer' = {}
          /\ UNCHANGED << >>          \* no other variables besides the two above

\* ----------------------------------------------------------------------
\*  Action: the currently smoking smoker stops and a new offer is placed
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ offer = {}                     \* someone is smoking (offer cleared)
    /\ \E i \in Ingredients : smokerStatus[i] = TRUE
    /\ LET i == CHOOSE j \in Ingredients : smokerStatus[j] = TRUE IN
          /\ smokerStatus' = [j \in Ingredients |-> FALSE]
          /\ offer' \in Offers
          /\ UNCHANGED << >>          \* no other variables besides the two above

\* ----------------------------------------------------------------------
\*  Next-state relation
\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\*  Specification: initial condition, temporal closure, and weak fairness
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====