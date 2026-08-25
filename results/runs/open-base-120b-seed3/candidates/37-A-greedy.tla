---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smokerStatus, offer

\*-------------------------------------------------
\* Type correctness
\*-------------------------------------------------
TypeOK ==
    /\ smokerStatus \in [Ingredients -> BOOLEAN]
    /\ offer \in Offers \/ offer = {}

\*-------------------------------------------------
\* At most one smoker is smoking
\*-------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : smokerStatus[i] }) <= 1

\*-------------------------------------------------
\* Initial state
\*-------------------------------------------------
Init ==
    /\ smokerStatus = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\*-------------------------------------------------
\* Action: a smoker starts smoking
\*-------------------------------------------------
StartSmoking ==
    /\ offer # {}
    /\ LET missing == Ingredients \ offer IN
          /\ missing \in Ingredients
          /\ smokerStatus[missing] = FALSE
       IN
          /\ smokerStatus' = [smokerStatus EXCEPT ![missing] = TRUE]
          /\ offer' = {}

\*-------------------------------------------------
\* Action: the current smoker stops smoking
\*-------------------------------------------------
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
          /\ smokerStatus[i] = TRUE
          /\ smokerStatus' = [smokerStatus EXCEPT ![i] = FALSE]
          /\ offer' \in Offers

\*-------------------------------------------------
\* Next-state relation
\*-------------------------------------------------
Next ==
    \/ StartSmoking
    \/ StopSmoking

\*-------------------------------------------------
\* Specification
\*-------------------------------------------------
vars == <<smokerStatus, offer>>

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

====