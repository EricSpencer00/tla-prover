---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

\* ----------------------------------------------------------------------
\* Type correctness predicate
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ Offer   \in SUBSET Ingredients

\* ----------------------------------------------------------------------
\* Initial state: no smoker is smoking and the dealer places a valid offer
\* ----------------------------------------------------------------------
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer   \in Offers

\* ----------------------------------------------------------------------
\* Helper: the (unique) ingredient missing from a valid offer
\* ----------------------------------------------------------------------
MissingIngredient(o) ==
    CHOOSE i \in Ingredients : Ingredients \ {i} = o

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking when the offer is non‑empty
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
        /\ Offer = Ingredients \ {i}            \* the offer is missing i
        /\ Smoking[i] = FALSE                  \* i is not already smoking
        /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
        /\ Offer'   = {}
        /\ \A j \in Ingredients : j # i => Smoking'[j] = Smoking[j]

\* ----------------------------------------------------------------------
\* Action: the currently smoking smoker stops and the dealer offers again
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
        /\ Smoking[i] = TRUE                   \* i is the one that is smoking
        /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
        /\ Offer'   \in Offers
        /\ \A j \in Ingredients : j # i => Smoking'[j] = Smoking[j]

\* ----------------------------------------------------------------------
\* Next‑state relation
\* ----------------------------------------------------------------------
Next == \/ StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Variable tuple used for the temporal operators
\* ----------------------------------------------------------------------
vars == << Smoking, Offer >>

\* ----------------------------------------------------------------------
\* Specification (includes weak fairness on Next)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    \A i, j \in Ingredients :
        (Smoking[i] /\ Smoking[j]) => i = j

====