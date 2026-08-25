---- MODULE CigaretteSmokers ----
EXTENDS Naturals, TLC

CONSTANTS Ingredients, Offers

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Smoking, Offer

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ Offer \in (Offers \cup {∅})

\* ----------------------------------------------------------------------
\* Safety invariant: at most one smoker is smoking
\* ----------------------------------------------------------------------
AtMostOne ==
    \A i, j \in Ingredients :
        (Smoking[i] /\ Smoking[j]) => i = j

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
    /\ Offer # ∅                           \* there is an offer on the table
    /\ \A i \in Ingredients : Smoking[i] = FALSE   \* nobody is smoking now
    /\ \E i \in Ingredients :
          /\ i \notin Offer                \* the missing ingredient
          /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
          /\ Offer'   = ∅
    /\ UNCHANGED << >>                     \* no other variables

\* ----------------------------------------------------------------------
\* Action: the smoking smoker stops and dealer puts a new offer
\* ----------------------------------------------------------------------
StopSmoking ==
    /\ Offer = ∅                           \* a smoker is currently smoking
    /\ \E i \in Ingredients :
          /\ Smoking[i] = TRUE
          /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
          /\ Offer'   \in Offers
    /\ UNCHANGED << >>                     \* no other variables

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ StartSmoking
    \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification with weak fairness on Next
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [] [][Next]_<<Smoking, Offer>> /\ WF_<<Smoking, Offer>>(Next)

\* ----------------------------------------------------------------------
\* The set of invariants to be checked by TLC
\* ----------------------------------------------------------------------
INVARIANT TypeOK, AtMostOne

====