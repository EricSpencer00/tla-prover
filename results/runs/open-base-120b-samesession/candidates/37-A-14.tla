---- MODULE CigaretteSmokers ----
EXTENDS FiniteSets, Naturals

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ (Offer = {} \/ Offer \in Offers)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Missing == Ingredients \ Offer

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
StartSmoking ==
    /\ Offer # {}
    /\ \E i \in Ingredients :
          /\ i \notin Offer                \* the ingredient missing from the offer
          /\ Smoking[i] = FALSE
          /\ Smoking' = [Smoking EXCEPT ![i] = TRUE]
          /\ Offer' = {}
          /\ \A j \in Ingredients : (j # i) => Smoking'[j] = Smoking[j]

StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients :
          /\ Smoking[i] = TRUE
          /\ Smoking' = [Smoking EXCEPT ![i] = FALSE]
          /\ Offer' \in Offers
          /\ \A j \in Ingredients : (j # i) => Smoking'[j] = Smoking[j]

Next == \/ StartSmoking \/ StopSmoking

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<Smoking, Offer>> /\ WF_<<Smoking, Offer>>(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
AtMostOne ==
    Cardinality({ i \in Ingredients : Smoking[i] }) <= 1

\* ----------------------------------------------------------------------
\* The set of properties to be checked by TLC (if any)
\* ----------------------------------------------------------------------
PROPERTIES == Spec

=============================================================================