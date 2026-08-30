---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

\* A smoker is identified by the single ingredient it has in infinite supply.
\* SmokingStatus maps each ingredient to the smoking flag of its smoker.
VARIABLES SmokingStatus, Offer

vars == <<SmokingStatus, Offer>>

TypeOK ==
    /\ SmokingStatus \in [Ingredients -> BOOLEAN]
    /\ Offer \in Offers \cup {"Empty"}

Init ==
    /\ SmokingStatus = [i \in Ingredients |-> FALSE]
    /\ Offer \in Offers

\* The dealer's offer always lacks exactly one ingredient; that missing one is
\* the only ingredient a sleeping smoker can contribute to a full set.
StartSmoking ==
    /\ Offer # "Empty"
    /\ \E i \in Ingredients :
         /\ Offer \cup {i} = Ingredients
         /\ SmokingStatus[i] = FALSE
         /\ SmokingStatus' = [SmokingStatus EXCEPT ![i] = TRUE]
    /\ Offer' = "Empty"

\* Fairness here (along with StartSmoking) forces every smoker through the
\* smoke-and-stop cycle repeatedly, giving progress.
StopSmoking ==
    /\ Offer = "Empty"
    /\ \E i \in Ingredients :
         /\ SmokingStatus[i] = TRUE
         /\ SmokingStatus' = [SmokingStatus EXCEPT ![i] = FALSE]
    /\ Offer' \in Offers

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne == Cardinality({i \in Ingredients : SmokingStatus[i]}) <= 1
====