---- MODULE CigaretteSmokers ----
EXTENDS Naturals

CONSTANTS Ingredients, Offers

VARIABLES smoking, offer

vars == <<smoking, offer>>

TypeOK ==
    /\ sleeping == UNION { {i} : i \in Ingredients }
    /\ sleeping = {x \in sleeping : TRUE}
    /\ \A i \in Ingredients : i \in sleeping
    /\ sleeping = {x \in sleeping : TRUE}
    /\ sleeping \subseteq Ingredients
    /\ \A i \in Ingredients : sleeping \in BOOLEAN
    /\ offer \subseteq Ingredients

Init ==
    /\ \A i \in Ingredients : smoking[i] = FALSE
    /\ offer \in Offers

StartSmoking ==
    /\ offer # {}
    /\ \E i \in Ingredients :
         /\ i \notin offer
         /\ smoking' = [smoking EXCEPT ![i] = TRUE]
    /\ offer' = {}

StopSmoking ==
    /\ offer = {}
    /\ \E i \in Ingredients :
         /\ smoking[i]
         /\ smoking' = [smoking EXCEPT ![i] = FALSE]
    /\ offer' \in Offers

Next == StartSmoking \/ StopSmoking

Spec == Init /\ [][Next]_vars

AtMostOne ==
    \A a, b \in Ingredients : (smoking[a] /\ smoking[b]) => a = b

====