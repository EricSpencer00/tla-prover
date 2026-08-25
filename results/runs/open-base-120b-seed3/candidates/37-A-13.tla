---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

vars == <<Smoking, Offer>>

\* ----------------------------------------------------------------------
\* Type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ (Offer \in Offers \/ Offer = {})

\* ----------------------------------------------------------------------
\* Safety: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ Offer \in Offers                     \* a valid offer is on the table
    /\ \A i \in Ingredients : ~Smoking[i]   \* nobody is currently smoking
    /\ LET missing == { i \in Ingredients : i \notin Offer } IN
          /\ Cardinality(missing) = 1
          /\ \E i \in missing :
                /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
                /\ Offer' = {}
                /\ \A j \in Ingredients : (j # i) => Smoking'[j] = Smoking[j]

\* ----------------------------------------------------------------------
\* Action: the current smoker stops and dealer places a new offer
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ Offer = {}                             \* a smoker is currently smoking
    /\ LET smokingSet == { i \in Ingredients : Smoking[i] } IN
          /\ Cardinality(smokingSet) = 1
          /\ \E i \in smokingSet :
                /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
                /\ Offer' \in Offers
                /\ \A j \in Ingredients : (j # i) => Smoking'[j] = Smoking[j]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification with weak fairness
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====