---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ offer \in SUBSET Ingredients
    /\ (offer = {} \/ offer \in Offers)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients:
          /\ offer = Ingredients \ {i}
          /\ smoking[i] = FALSE
          /\ smoking' = [smoking EXCEPT ![i] = TRUE]
          /\ offer' = {}

\* ----------------------------------------------------------------------
\* Action: the current smoker stops and the dealer places a new offer
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients:
          /\ smoking[i] = TRUE
          /\ smoking' = [smoking EXCEPT ![i] = FALSE]
          /\ offer' \in Offers

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<smoking, offer>> /\ WF_<<smoking, offer>>(Next)

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : smoking[i] }) <= 1

====