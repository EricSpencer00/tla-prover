---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES smoking, Offer

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ smoking \in [Ingredients -> BOOLEAN]
    /\ (Offer \in Offers) \/ (Offer = {})

\* ----------------------------------------------------------------------
\* At most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    \A i, j \in Ingredients :
        (smoking[i] /\ smoking[j]) => i = j

\* ----------------------------------------------------------------------
\* Initial state: no one is smoking, dealer places a nondeterministic offer
\* ----------------------------------------------------------------------
Init ==
    /\ smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
        /\ i \notin Offer               \* the missing ingredient
        /\ Offer \cup {i} = Ingredients \* together they form the full set
        /\ smoking[i] = FALSE
        /\ smoking' = [smoking EXCEPT ![i] = TRUE]
        /\ Offer' = {}

\* ----------------------------------------------------------------------
\* Action: the current smoker stops and dealer places a new offer
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
        /\ smoking[i] = TRUE
        /\ smoking' = [smoking EXCEPT ![i] = FALSE]
        /\ Offer' \in Offers

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<smoking, Offer>>
        /\ WF_<<smoking, Offer>>(StartSmoking)
        /\ WF_<<smoking, Offer>>(StopSmoking)

====