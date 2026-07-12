---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES Smoking, Offer

(*--- Initialization ---*)
Init ==
    /\ Smoking = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

(*--- Actions ---*)
StartSmoking ==
    /\ Offer \in Offers
    /\ Offer # {}
    /\ LET m == CHOOSE i \in Ingredients : i \notin Offer IN
           /\ Smoking' = [Smoking EXCEPT ![m] = TRUE]
           /\ Offer' = {}

StopSmoking ==
    /\ Offer = {}
    /\ \E i \in Ingredients : Smoking[i] = TRUE
    /\ LET m == CHOOSE i \in Ingredients : Smoking[i] = TRUE IN
           /\ Smoking' = [Smoking EXCEPT ![m] = FALSE]
           /\ Offer' \in Offers

Next == StartSmoking \/ StopSmoking

(*--- Specification ---*)
Spec == Init /\ [][Next]_vars

(*--- Type correctness ---*)
TypeOK ==
    /\ Smoking \in [Ingredients -> BOOLEAN]
    /\ Offer \in Offers \cup {{}}

(*--- Safety invariant: at most one smoker is smoking ---*)
AtMostOne ==
    # { i \in Ingredients : Smoking[i] } <= 1

(*--- Declare invariants for TLC ---*)
INVARIANT TypeOK, AtMostOne

====