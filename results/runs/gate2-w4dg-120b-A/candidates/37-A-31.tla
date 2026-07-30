---- MODULE CigaretteSmokers ----
EXTENDS Naturals, FiniteSets

CONSTANTS Ingredients, Offers

VARIABLES offer, smoking

vars == <<offer, smoking>>

Holds(i) == \E k \in Ingredients : smoking[k] /\ k = i

TypeOK ==
    /\ offer \in Offers \cup {{}}
    /\ smoking \in [Ingredients -> BOOLEAN]

AtMostOne ==
    \A i, j \in Ingredients : (smoking[i] /\ smoking[j]) => (i = j)

Init ==
    /\ offer \in Offers
    /\ smoking = [i \in Ingredients |-> FALSE]

StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
         /\ \A k \in Ingredients \ {i} : k \in offer
         /\ ~smoking[i]
         /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
         /\ smoking[i]
         /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ offer' \in Offers

Next ==
    /\ \/ StartSmoking
       \/ StopSmoking
    /\ UNCHANGED <<>>

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(StartSmoking)
    /\ WF_vars(StopSmoking)

====