---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == << Smoking, Offer >>

Missing(offer) == Ingredients \ offer

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ (Offer \in Offers) \/ (Offer = {})

\* ----------------------------------------------------------------------
\* Safety: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

\* ----------------------------------------------------------------------
\* Initial state: no smoker is smoking, dealer places a nondeterministic offer
\* ----------------------------------------------------------------------
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ Offer # {}
    /\ LET miss == Missing(Offer) IN
       /\ Cardinality(miss) = 1
       /\ \E i \in miss :
            /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
            /\ Offer' = {}

\* ----------------------------------------------------------------------
\* Action: the currently smoking smoker stops and dealer places a new offer
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
         /\ Smoking[i] = TRUE
         /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
         /\ Offer' \in Offers

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification with weak fairness on Next
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* SPECIFICATION formula
Spec

\* INVARIANTS
TypeOK
AtMostOne

====