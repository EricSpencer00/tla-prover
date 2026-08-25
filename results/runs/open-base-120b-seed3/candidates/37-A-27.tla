---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ Offer \in Offers \/ Offer = {}

\* ----------------------------------------------------------------------
\* At most one smoker may be smoking at any time
\* ----------------------------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

\* ----------------------------------------------------------------------
\* Initial state: no smoker is smoking and the dealer places a valid offer
\* ----------------------------------------------------------------------
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

\* ----------------------------------------------------------------------
\* Action: a smoker starts smoking
\* The dealer's offer must be a valid subset missing exactly the ingredient
\* that the smoker possesses. The offer is cleared.
\* ----------------------------------------------------------------------
Start ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
          /\ Offer = Ingredients \\ {i}          \* offer is missing i
          /\ Smoking[i] = FALSE
          /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
          /\ Offer' = {}
    /\ UNCHANGED {}

\* ----------------------------------------------------------------------
\* Action: the currently smoking smoker stops and the dealer places a new offer
\* ----------------------------------------------------------------------
Stop ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
          /\ Smoking[i] = TRUE
          /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
          /\ Offer' \in Offers
    /\ UNCHANGED {}

Next == Start \/ Stop

\* ----------------------------------------------------------------------
\* Specification (includes weak fairness on Next)
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<Smoking, Offer>> /\ WF_<<Smoking, Offer>>(Next)

=============================================================================