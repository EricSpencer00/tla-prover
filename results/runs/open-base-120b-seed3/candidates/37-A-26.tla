---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ smoking \in [Ingredients -> BOOLEAN]
  /\ offer \in (Offers \cup {{} })

\* ----------------------------------------------------------------------
\* Initial state: no one is smoking, dealer places a valid offer
\* ----------------------------------------------------------------------
Init ==
  /\ smoking = [i \in Ingredients |-> FALSE]
  /\ offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking when the dealer's offer is present
\* ----------------------------------------------------------------------
StartSmoking ==
  /\ offer # {}
  /\ \E miss \in Ingredients \ offer :
        /\ smoking' = [smoking EXCEPT ![miss] = TRUE]
        /\ offer'   = {}

\* ----------------------------------------------------------------------
\* Action: the currently smoking smoker stops and dealer places a new offer
\* ----------------------------------------------------------------------
StopSmoking ==
  /\ offer = {}
  /\ \E i \in Ingredients : smoking[i] = TRUE
  /\ \LET i == CHOOSE j \in Ingredients : smoking[j] = TRUE IN
        /\ smoking' = [smoking EXCEPT ![i] = FALSE]
        /\ offer'   \in Offers

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<smoking, offer>> /\ WF_<<smoking, offer>>(Next)

\* ----------------------------------------------------------------------
\* Invariant: at most one smoker can be smoking at any time
\* ----------------------------------------------------------------------
AtMostOne ==
  \A i, j \in Ingredients :
    (smoking[i] /\ smoking[j]) => i = j

=============================================================================