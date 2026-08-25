---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Missing(o) == Ingredients \ o

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ Offer \subseteq Ingredients
    /\ (Offer = {} \/ Offer \in Offers)

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
    /\ Offer # {}
    /\ \E ing \in Ingredients :
        /\ Missing(Offer) = {ing}
        /\ Smoking[ing] = FALSE
        /\ Smoking' = [Smoking EXCEPT ![ing] = TRUE]
        /\ Offer' = {}

\* ----------------------------------------------------------------------
\* Action: the smoker stops and dealer places a new offer
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ Offer = {}
    /\ \E ing \in Ingredients :
        /\ Smoking[ing] = TRUE
        /\ Smoking' = [Smoking EXCEPT ![ing] = FALSE]
        /\ Offer' \in Offers

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<Smoking, Offer>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====